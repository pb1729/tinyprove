from __future__ import annotations
from typing import List, Dict, Tuple

from .core import *
from .ir import *


class DefinitionError(Exception):
  pass


def pi_wrap(inner:IrNode, ctx:List[Tuple[str, IrNode]]):
  """ Wrap an inner type in a context. """
  ans = inner
  for nm, ty in ctx:
    ans = IrPi(nm, ty, ans)
  return ans

def app_wrap(fn:IrNode, args:List[IrNode]):
  ans = fn
  for arg in args:
    ans = IrApp(ans, arg)
  return ans

def ctx_to_names(ctx:List[Tuple[str, IrNode]]) -> List[str]:
  return [nm for nm, _ in ctx]

def names_unique(names:List[str]) -> bool:
  seen = set()
  for nm in names:
    if nm in seen: return False
    seen.add(nm)
  return True


class DefsExtend:
  """ Temporarily extend definitions with a dict of additional definitions. """
  def __init__(self, base_defns, new_defs_dict:dict):
    self.base_defns = base_defns
    self.new_defs_dict = new_defs_dict
    for key in self.new_defs_dict:
      assert key not in self.base_defns, "duplicate key {key}"
  def __getitem__(self, key:str) -> Term:
    if key in self.new_defs_dict:
      return self.new_defs_dict[key]
    return self.base_defns[key]
  def __contains__(self, key:str) -> bool:
    return key in self.new_defs_dict or key in self.base_defns
  def match_reduce(self, key:str, argchain: List[Term], defns:Definitions) -> Tuple[Term, List[Term]] | None:
    return self.base_defns.match_reduce(key, argchain, defns)


def typecheck_args(args:List[Tuple[str, IrNode]], ctx:List[Tuple[str, Term]], selfref_ir:IrNode, defns:Definitions):
  """ Given a list of args that might be type parameters or constructor args,
      check that they are all some kind of Sort. Returns a full ctx containing all args. """
  if len(args) == 0: return ctx
  (arg_nm, arg_ty_ir), *args_rest = args
  arg_ty = selfref_sub(arg_ty_ir, selfref_ir).to_term(ctx_to_names(ctx))
  arg_ty_ty = infer(arg_ty, ctx, defns)
  if not isinstance(arg_ty_ty, Sort):
    raise TypecheckError(f"Expected {arg_ty.str(ctx)} to be a Sort but found type {ty_ty.str(ctx)}.")
  return typecheck_args(args_rest, [(arg_nm, arg_ty)] + ctx, selfref_ir, defns)


@dataclass(frozen=True)
class IrInductiveSelfRef(IrNode):
  index_vals: List[IrNode]
  def to_term(self, ctx_nm):
    raise RuntimeError("Can't convert IrInductiveSelfRef to Term, you should use selfref_sub() to expand it first.")

@dataclass(frozen=True)
class IrConstructorDefinition(IrNode):
  name: str
  args: List[Tuple[str, IrNode]]
  output_indices: List[IrNode]
  def to_term(self, ctx_nm):
    raise RuntimeError("Can't convert IrConstructorDefinition to Term, it is intended for creating InductiveDef's only.")

@dataclass(frozen=True)
class IrInductiveDefinition(IrNode):
  name: str
  sort: IrSort
  params: List[Tuple[str, IrNode]]
  indices: List[Tuple[str, IrNode]]
  constructors:List[IrConstructorDefinition]
  def to_term(self, ctx_nm):
    raise RuntimeError("Can't convert IrInductiveDefinition to Term, it is intended for creating InductiveDef's only.")
  def to_definition(self, defns: Definitions):
    return InductiveDef(self.name, self.sort, self.params, self.indices, self.constructors, defns)

def selfref_sub(node:IrNode, selfref_ir:IrNode) -> IrNode:
  match node:
    case IrLam(param, A, body):
      return IrLam(param, selfref_sub(A, selfref_ir), selfref_sub(body, selfref_ir))
    case IrPi(param, A, B):
      return IrPi(param, selfref_sub(A, selfref_ir), selfref_sub(B, selfref_ir))
    case IrApp(fn, arg):
      return IrApp(selfref_sub(fn, selfref_ir), selfref_sub(arg, selfref_ir))
    case IrSort(level):
      return IrSort(level)
    case IrVar(nm):
      return IrVar(nm)
    case IrConst(name):
      return IrConst(name)
    case IrInductiveSelfRef(index_vals):
      return app_wrap(selfref_ir, index_vals)
    case _:
      raise DefinitionError("Unknown node type.")


def walk(indty_name: str, node:IrNode, polarity:bool=True) -> bool:
  """ Do a polarity check of node to ensure that self-references to our inductive type are positive only.
      polarity: True = positive, and False = negative """
  match node:
    case IrLam():
      raise DefinitionError("Lambdas not supported in constructor definition.")
    case IrPi(param, A, B):
      return walk(indty_name, A, not polarity) and walk(indty_name, B, polarity)
    case IrApp(fn, arg):
      return walk(indty_name, fn, polarity) and walk(indty_name, arg, polarity)
    case IrSort():
      return True
    case IrVar(nm):
      return True
    case IrConst(name):
      if name == indty_name:
        raise DefinitionError("Found an IrConst that refers back to the original inductive type! This should be done solely with IrInductiveSelfRef.")
      return True
    case IrInductiveSelfRef(index_vals):
      return polarity
    case _:
      raise DefinitionError("Unknown node type.")


class ConstructorDef:
  def __init__(self, indty:InductiveDef, name:str, args:List[Tuple[str, IrNode]], output_indices:List[IrNode]):
    if name == "ind": raise DefinitionError("ind is a reserved name and cannot be used as a constructor name.")
    self.indty = indty
    self.name = name
    assert names_unique(ctx_to_names(self.indty.params + args)), "constructor arguments should have unique names"
    self.args = args
    self.output_indices = output_indices
    # type & positivity checking:
    constructor_ctx = typecheck_args(self.args, self.indty.params_ctx, self.indty.selfref_ir, self.indty.defns_ext)
    self.check_positive()
    self.check_output_indices(constructor_ctx, self.indty.inds_ctx)
    # prep data that will be used by match-reduce
    self.matchred_sig = self.get_matchred_sig()
    self.arg_tys = [arg_ty for _, arg_ty in constructor_ctx[:len(self.args)]]
  def get_ty(self):
    return pi_wrap(
      pi_wrap(
        IrInductiveSelfRef(self.output_indices),
        self.args[::-1]),
      self.indty.params[::-1])
  def get_case_fn_ty(self):
    converted_args = [] # args list that will include any necessary recursion
    for arg_nm, arg_ty in self.args:
      converted_args.append((arg_nm, arg_ty)) # always use the arg itself
      if isinstance(arg_ty, IrInductiveSelfRef): # add inductive hypothesis for recursion
        rec_ty = IrApp(
          app_wrap(
            IrVar("@motive"),
            arg_ty.index_vals),
          IrVar(arg_nm))
        converted_args.append((f"@rec_{arg_nm}", rec_ty))
    applied_constructor_ty = app_wrap(
      app_wrap(
        IrConst(f"{self.indty.name}.{self.name}"),
        [IrVar(varnm) for varnm, _ in self.indty.params]),
      [IrVar(argnm) for argnm, _ in self.args])
    return pi_wrap(
      IrApp(
        app_wrap(
          IrVar("@motive"),
          self.output_indices),
        applied_constructor_ty),
      converted_args[::-1])
  def check_positive(self):
    for arg_nm, arg_ty in self.args:
      if not walk(self.indty.name, arg_ty):
        raise DefinitionError(f"Constructor {self.name} arg {arg_nm} fails positivity check.")
  def check_output_indices(self, constructor_ctx:List[Tuple[str, Term]], inds_ctx:List[Tuple[str, Term]]):
    num_inds = len(self.indty.indices)
    assert len(self.output_indices) == num_inds, f"Constructor {self.name} definition has incorrect number of output indices."
    for i in range(num_inds):
      output_index_i = self.output_indices[i].to_term(ctx_to_names(constructor_ctx))
      output_index_ty = infer(output_index_i, constructor_ctx, self.indty.defns_ext)
      target_nm, target_ty = inds_ctx[num_inds - 1 - i]
      if not conv(output_index_ty, target_ty, self.indty.defns):
        raise TypecheckError(f"Constructor {self.name} output index {target_nm} has the wrong type.")
  def get_matchred_sig(self):
    ans = []
    for i, (_, arg_ty) in enumerate(self.args):
      if isinstance(arg_ty, IrInductiveSelfRef):
        arg_names = [arg_nm for arg_nm, _ in reversed(self.indty.params + self.args[:i])] # reverse to make a ctx
        ans.append([index_val.to_term(arg_names) for index_val in arg_ty.index_vals])
      else:
        ans.append(None)
    return ans


def subst_args_as_term_ctx(t:Term, args:List[Term]):
  for i, arg in enumerate(args):
    depth = len(args) - i - 1
    t = t.subst(depth, arg)
  return t


class InductiveDef:
  def __init__(self,
      name:str, sort:IrSort,
      params:List[Tuple[str, IrNode]], indices:List[Tuple[str, IrNode]],
      constructors:List[IrConstructorDefinition],
      defns: Definitions):
    # general type setup:
    self.name = name
    self.sort = sort
    assert names_unique(ctx_to_names(params + indices))
    self.params = params
    self.indices = indices
    self.defns = defns
    # compute intermediate representations:
    self.ty_ir = self._get_ty()
    self.selfref_ir = self._get_selfref_ir()
    # type checking:
    self.params_ctx = typecheck_args(self.params, [], self.selfref_ir, self.defns)
    self.inds_ctx = typecheck_args(self.indices, self.params_ctx, self.selfref_ir, self.defns)
    self.ty = self.ty_ir.to_term([])
    self.defns_ext = DefsExtend(self.defns, {self.name: self.ty})
    # constructors setup:
    self.constructors = [
      ConstructorDef(self, constructor_ir.name, constructor_ir.args, constructor_ir.output_indices)
      for constructor_ir in constructors
    ]
    assert names_unique([constructor.name for constructor in self.constructors]), "Constructor names duplicate with each other."
    self.constructors_dict = {f"{self.name}.{self.constructors[i].name}": i for i in range(len(self.constructors))}
    # dicts containing Term types:
    self.constructor_tys = {
      constructor.name: selfref_sub(constructor.get_ty(), self.selfref_ir).to_term([])
      for constructor in self.constructors
    }
    self.ind_tys = {}
    self.used = find_used_defs(
      self.ty,
      *[self.constructor_tys[cons_nm] for cons_nm in self.constructor_tys])
    self.used.discard(self.name) # don't count self-reference as "use"
  def _get_ty(self):
    return pi_wrap(pi_wrap(self.sort, self.indices[::-1]), self.params[::-1])
  def _get_selfref_ir(self):
    return app_wrap(
      IrConst(self.name),
      [IrVar(nm) for nm, _ in self.params]
    )
  def get_index_vars(self) -> List[IrNode]:
    """ Get a list of vars corresponding to this inductive's indices.
        Note: Assumes that the vars will be present somewhere in the context. """
    return [IrVar(index_nm) for index_nm, _ in self.indices]
  def get_motive_ty(self, output_ty:IrNode) -> IrNode:
    """ get the type of a motive (inductive hypothesis) with a particular output type """
    return pi_wrap(
      IrPi("@instance",
        IrInductiveSelfRef(self.get_index_vars()),
        output_ty),
      self.indices[::-1])
  def get_ind_ty(self, sort:IrSort) -> IrNode:
    motive_ty = self.get_motive_ty(sort)
    ans_ty = self.get_motive_ty(
      IrApp(
        app_wrap(
          IrVar("@motive"),
          self.get_index_vars()),
        IrVar("@instance")))
    constructor_case_fns = [
      ("@case_" + constructor.name, constructor.get_case_fn_ty())
      for constructor in self.constructors
    ]
    ans_ty = pi_wrap(
      ans_ty,
      constructor_case_fns[::-1])
    return pi_wrap(
      IrPi("@motive", motive_ty, ans_ty),
      self.params[::-1])
  def get_type(self, key:List[str]) -> Term:
    match key:
      case ["ind", sortnum]:
        sortnum = to_positive_int(sortnum)
        if sortnum is None: raise IndexError("Induction for Type<n> is denoted by ind.<n> with n a non-negative integer.")
        if sortnum not in self.ind_tys:
          ind_ty_ir = self.get_ind_ty(IrSort(sortnum))
          self.ind_tys[sortnum] = selfref_sub(ind_ty_ir, self.selfref_ir).to_term([])
        return self.ind_tys[sortnum]
      case [constructor_name]:
        if constructor_name not in self.constructor_tys:
          raise IndexError(f"Constructor name {constructor_name} does not exist in this definition.")
        return self.constructor_tys[constructor_name]
      case []:
        return self.ty
    raise IndexError("InductiveDef couldn't find key {'.'.join(key)}.")
  def match_reduce(self, key:List[str], argchain: List[Term], defns:Definitions) -> Tuple[Term, List[Term]] | None:
    match key:
      case ["ind", sortnum]:
        sortnum = to_positive_int(sortnum)
        assert sortnum is not None, f"<n> should be a positive integer in {self.name}.ind.<n>"
        n_params = len(self.params)
        n_constructors = len(self.constructors)
        n_indices = len(self.indices)
        if len(argchain) < (n_params + 1 + n_constructors + n_indices + 1):
          return None # too few args
        # get induction arguments
        params, argchain = argchain[:n_params], argchain[n_params:]
        motive, argchain = argchain[0], argchain[1:]
        cases, argchain = argchain[:n_constructors], argchain[n_constructors:]
        indices, argchain = argchain[:n_indices], argchain[n_indices:]
        scrutinee, argchain = argchain[0], argchain[1:]
        # have to do recursive whnf on the scrutinee, just in case any redexes produce a construtor
        scru_head, scru_args = to_app_list(scrutinee)
        scru_head, scru_args = argchain_whnf(scru_head, scru_args, defns)
        # second part of checking for iota reduction is checking if scrutinee is a constructor
        match scru_head:
          case Const(name):
            if name not in self.constructors_dict: return None # not a constructor for this type
            cons_idx = self.constructors_dict[name]
            constructor = self.constructors[cons_idx]
            if len(scru_args) != n_params + len(constructor.matchred_sig):
              return None # too few or too many args
            case_fn_args = []
            for i, (scru_arg, rec_indices) in enumerate(zip(scru_args[n_params:], constructor.matchred_sig)):
              case_fn_args.append(scru_arg)
              if rec_indices is not None:
                recursive_call = Const(f"{self.name}.ind.{sortnum}")
                for param in params:
                  recursive_call = App(recursive_call, param)
                recursive_call = App(recursive_call, motive)
                for case_fn in cases:
                  recursive_call = App(recursive_call, case_fn)
                for idx_expr in rec_indices:
                  idx_val = subst_args_as_term_ctx(idx_expr, scru_args[:n_params + i])
                  recursive_call = App(recursive_call, idx_val)
                recursive_call = App(recursive_call, scru_arg)
                case_fn_args.append(recursive_call)
            case_fn = cases[cons_idx]
            return case_fn, case_fn_args + argchain
          case _: # not a constructor
            return None
      case _: # callee is not .ind
        return None





