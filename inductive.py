from typing import List, Dict, Tuple

from tinyprove import *
from ir import *


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
  def match_reduce(self, key:str, argchain: List[Term]) -> Tuple[Term, List[Term]] | None:
    return self.base_defns.match_reduce(key, argchain)


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


class InductiveDefHead:
  def __init__(self, name:str, sort:IrSort, params:List[Tuple[str, IrNode]], indices:List[Tuple[str, IrNode]], defns=None):
    self.name = name
    self.sort = sort
    assert names_unique(ctx_to_names(params + indices))
    self.params = params
    self.indices = indices
    self.defns = Definitions() if defns is None else defns
    # compute intermediate representations:
    self.ty_ir = self._get_ty()
    self.selfref_ir = self._get_selfref_ir()
    # type checking:
    typecheck_args(self.params + self.indices, [], self.selfref_ir, self.defns)
    self.ty = self.ty_ir.to_term([])
    self.defns_ext = DefsExtend(self.defns, {self.name: self.ty})
  def _get_ty(self):
    return pi_wrap(pi_wrap(self.sort, self.indices[::-1]), self.params[::-1])
  def _get_selfref_ir(self):
    return app_wrap(
      IrConst(self.name),
      [IrVar(nm) for nm, _ in self.params]
    )

@dataclass(frozen=True)
class IrInductiveSelfRef(IrNode):
  index_vals: List[IrNode]
  def to_term(self, ctx_nm):
    raise RuntimeError("Can't convert IrInductiveSelfRef to term, you should use selfref_sub() to expand it.")

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


def walk(head: InductiveDefHead, node:IrNode, polarity:bool=True) -> bool:
  """ Do a polarity check of node to ensure that self-references to our inductive type are positive only.
      polarity: True = positive, and False = negative """
  match node:
    case IrLam():
      raise DefinitionError("Lambdas not supported in constructor definition.")
    case IrPi(param, A, B):
      return walk(head, A, not polarity) and walk(head, B, polarity)
    case IrApp(fn, arg):
      return walk(head, fn, polarity) and walk(head, arg, polarity)
    case IrSort():
      return True
    case IrVar(nm):
      return True
    case IrConst(name):
      if name == head.name:
        raise DefinitionError("Found an IrConst that refers back to the original inductive type! This should be done solely with IrInductiveSelfRef.")
      return True
    case IrInductiveSelfRef(index_vals):
      return polarity
    case _:
      raise DefinitionError("Unknown node type.")


class ConstructorDef:
  def __init__(self, head:InductiveDefHead, name:str, args:List[Tuple[str, IrNode]], output_indices:List[IrNode]):
    if name == "ind": raise DefinitionError("ind is a reserved name and cannot be used as a constructor name.")
    self.head = head
    self.name = name
    assert names_unique(ctx_to_names(self.head.params + args)), "constructor arguments should have unique names"
    self.args = args
    self.output_indices = output_indices
    # type & positivity checking:
    params_ctx = typecheck_args(self.head.params, [], self.head.selfref_ir, self.head.defns)
    inds_ctx = typecheck_args(self.head.indices, params_ctx, self.head.selfref_ir, self.head.defns)
    constructor_ctx = typecheck_args(self.args, params_ctx, self.head.selfref_ir, self.head.defns_ext)
    self.check_positive()
    self.check_output_indices(constructor_ctx, inds_ctx)
  def get_ty(self):
    return pi_wrap(
      pi_wrap(
        IrInductiveSelfRef(self.output_indices),
        self.args[::-1]),
      self.head.params[::-1])
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
        IrConst(f"{self.head.name}.{self.name}"),
        [IrVar(varnm) for varnm, _ in self.head.params]),
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
      if not walk(self.head, arg_ty):
        raise DefinitionError(f"Constructor {self.name} arg {arg_nm} fails positivity check.")
  def check_output_indices(self, constructor_ctx:List[Tuple[str, Term]], inds_ctx:List[Tuple[str, Term]]):
    num_inds = len(self.head.indices)
    assert len(self.output_indices) == num_inds, f"Constructor {self.name} definition has incorrect number of output indices."
    for i in range(num_inds):
      output_index_i = self.output_indices[i].to_term(ctx_to_names(constructor_ctx))
      output_index_ty = infer(output_index_i, constructor_ctx, self.head.defns_ext)
      target_nm, target_ty = inds_ctx[num_inds - 1 - i]
      if not conv(output_index_ty, target_ty, self.head.defns):
        raise TypecheckError(f"Constructor {self.name} output index {target_nm} has the wrong type.")


class InductiveDef:
  def __init__(self, head:InductiveDefHead, constructors:List[ConstructorDef]):
    assert names_unique([constructor.name for constructor in constructors]), "Constructor names duplicate with each other."
    self.head = head
    self.constructors = constructors
    # dicts containing Term types:
    self.constructor_tys = {
      constructor.name: selfref_sub(constructor.get_ty(), self.head.selfref_ir).to_term([])
      for constructor in self.constructors
    }
    self.ind_tys = {}
    self.ty = self.head.ty
    self.used = find_used_defs(
      self.ty,
      *[self.constructor_tys[cons_nm] for cons_nm in self.constructor_tys])
    self.used.discard(self.head.name) # don't count self-reference as "use"
  @property
  def name(self) -> str:
    return self.head.name
  def get_index_vars(self) -> List[IrNode]:
    """ Get a list of vars corresponding to this inductive's indices.
        Note: Assumes that the vars will be present somewhere in the context. """
    return [IrVar(index_nm) for index_nm, _ in self.head.indices]
  def get_motive_ty(self, output_ty:IrNode) -> IrNode:
    """ get the type of a motive (inductive hypothesis) with a particular output type """
    return pi_wrap(
      IrPi("@instance",
        IrInductiveSelfRef(self.get_index_vars()),
        output_ty),
      self.head.indices[::-1])
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
      self.head.params[::-1])
  def get_type(self, key:List[str]) -> Term:
    match key:
      case ["ind", sortnum]:
        sortnum = to_positive_int(sortnum)
        if sortnum is None: raise IndexError("Induction for Type<n> is denoted by ind.<n> with n a non-negative integer.")
        if sortnum not in self.ind_tys:
          ind_ty_ir = self.get_ind_ty(IrSort(sortnum))
          self.ind_tys[sortnum] = selfref_sub(ind_ty_ir, self.head.selfref_ir).to_term([])
        return self.ind_tys[sortnum]
      case [constructor_name]:
        if constructor_name not in self.constructor_tys:
          raise IndexError(f"Constructor name {constructor_name} does not exist in this definition.")
        return self.constructor_tys[constructor_name]
      case []:
        return self.ty
    raise IndexError("InductiveDef couldn't find key {'.'.join(key)}.")
  def match_reduce(self, key:List[str], argchain: List[Term]) -> Tuple[Term, List[Term]] | None:
    return None # TODO: this should be changed to implement iota reduction!





