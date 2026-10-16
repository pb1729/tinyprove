from __future__ import annotations
from dataclasses import dataclass, field

from .ir import Binder, IrNode, IrSort, IrConst, IrVar, IrLam, IrPi, IrApp, IrLet
from .core import (
  Binding, Value, Term, Module, Env,
  LookupError, TypecheckError, DefinitionError, EvalError,
  TSort, TVar, TConst, TLam,
  VSort, VNeutral, VContainer,
  EmptyEnv, EnvEntry, LazyEnvMap, ann_name, ann_val, infer_sort, term_eval,
)


# Inductive info classes:

@dataclass(frozen=True)
class ConstructorInfo:
  ref: TConst
  nfields: int
  rule: Term

@dataclass(eq=False)
class InductiveInfo:
  """ Nominal identity, compiled rules, and the generated inductor submodule. """
  ref: TConst
  nparams: int
  nindices: int
  constructors: tuple[ConstructorInfo, ...] = ()


# Functions to create values for constructors and induction:

def get_ind_reduce(info:InductiveInfo, level:int) -> VContainer:
  """ Returns VContainer with correct fn to perform induction """
  i_motive = info.nparams # arglist offset for motive
  i_branches = i_motive + 1 # arglist offset for branches
  i_indices = i_branches + len(info.constructors) # arglist offset for indices of scrutinee
  i_scrutinee = i_indices + info.nindices # arglist offset for scrutinee
  arity = i_scrutinee + 1
  # use get_rec to obtain recursive call (indices and scrutinee removed)
  ind_selfref = TConst(info.ref.module, info.ref.path + (f"ind{level}",))
  def get_rec(fn, args:tuple[Binding]) -> VContainer:
    return VContainer(ind_selfref, arity, fn, args[:i_indices])
  def induct(rec, args:tuple[Binding, ...]) -> Value|None:
    assert len(args) == arity
    scrutinee = args[i_scrutinee].force()
    match scrutinee:
      case VNeutral(_, _):
        return None # evaluation blocked
      case VContainer(head_ref, nargs, fn, params_fields):
        for tag, cons_info in enumerate(info.constructors):
          if head_ref._get_def_id() == cons_info.ref._get_def_id():
            val_rec = get_rec(rec, args)
            branch = args[i_branches + tag]
            env = EnvEntry(EnvEntry(EmptyEnv(), val_rec), branch)
            for binding in params_fields:
              env = EnvEntry(env, binding)
            result = term_eval(cons_info.rule, env)
            return result
        return None # evaluation blocked
      case _:
        raise EvalError(f"Induction requires a constructor or blocked computation.")
  return VContainer(ind_selfref, arity, induct)

def blocked_noforce(rec, args:tuple[Binding, ...]) -> Value|None:
  """ For VContainer's that should always be considered blocked """
  return None


# new IR node types:

@dataclass(frozen=True)
class IrInductiveSelfRef(IrNode):
  index_vals: list[IrNode]

@dataclass(frozen=True)
class IrConstructorDefinition(IrNode):
  name: str
  args: list[tuple[Binder, IrNode]]
  output_indices: list[IrNode]

@dataclass(frozen=True)
class IrInductiveDefinition(IrNode):
  name: str
  sort: IrSort
  params: list[tuple[Binder, IrNode]]
  indices: list[tuple[Binder, IrNode]]
  constructors: list[IrConstructorDefinition]
  def apply(self, module:Module):
    define_inductive(module, self)


# IR manipulation:

def pi_wrap(inner:IrNode, ctx:list[tuple[Binder, IrNode]]) -> IrNode:
  """ Wrap an inner type in a context. """
  ans = inner
  for binder, ty in ctx[::-1]: # reverse wrapping order to get correct nesting
    ans = IrPi(binder, ty, ans)
  return ans

def lam_wrap(inner:IrNode, ctx:list[tuple[Binder, IrNode]]) -> IrNode:
  ans = inner
  for binder, _ in ctx[::-1]: # reverse wrapping order to get correct nesting
    ans = IrLam(binder, None, ans) # ignores type info in ctx and omits domain type annotation
  return ans

def app_wrap(fn:IrNode, args:list[IrNode]) -> IrNode:
  ans = fn
  for arg in args:
    ans = IrApp(ans, arg)
  return ans

def selfref_sub(node:IrNode|None, selfref_ir:IrNode, allow_selfref:bool=True) -> IrNode:
  """ Replace self-references with given IR, raises error if indices of selfref contain self-reference """
  match node:
    case None: # Type annotations are sometimes None in Lam and Let
      return None
    case IrLam(param, A, body):
      return IrLam(param,
        selfref_sub(A, selfref_ir, allow_selfref=allow_selfref),
        selfref_sub(body, selfref_ir, allow_selfref=allow_selfref))
    case IrLet(name, A, rhs, body):
      return IrLet(name,
        selfref_sub(A, selfref_ir, allow_selfref=allow_selfref),
        selfref_sub(rhs, selfref_ir, allow_selfref=allow_selfref),
        selfref_sub(body, selfref_ir, allow_selfref=allow_selfref))
    case IrPi(param, A, B):
      return IrPi(param,
        selfref_sub(A, selfref_ir, allow_selfref=allow_selfref),
        selfref_sub(B, selfref_ir, allow_selfref=allow_selfref))
    case IrApp(fn, arg):
      return IrApp(
        selfref_sub(fn, selfref_ir, allow_selfref=allow_selfref),
        selfref_sub(arg, selfref_ir, allow_selfref=allow_selfref))
    case IrInductiveSelfRef(index_vals): # SUBSTITUTE!
      if not allow_selfref: raise DefinitionError("Indices of a self-reference cannot contain self-reference.")
      subbed_indices = [
        selfref_sub(idx_val, selfref_ir, allow_selfref=False)
        for idx_val in index_vals
      ]
      return app_wrap(selfref_ir, subbed_indices)
    case _: # leaf node
      return node


# ...

@dataclass
class InductiveModule(Module):
  ind_info: InductiveInfo
  # The sole free variable is the motive's universe, supplied on demand.
  ind_type: Term
  cache: dict[int, tuple[Binding, Value]] = field(default_factory=dict)
  def __getitem__(self, path:tuple[str, ...]) -> tuple[Binding, Value]:
    if len(path) != 1 or not path[0].startswith("ind"):
      raise LookupError("Expected ind<n> with n a non-negative integer.")
    digits = path[0][3:]
    if not digits.isascii() or not digits.isdigit():
      raise LookupError("Expected ind<n> with n a non-negative integer.")
    level = int(digits)
    if level not in self.cache:
      ctx = EnvEntry(EmptyEnv(), (VSort(level), VSort(level + 1), "@sort"))
      infer_sort(self.ind_type, ctx)
      ty = term_eval(self.ind_type, LazyEnvMap(ctx, ann_val))
      ind_reduce = get_ind_reduce(self.ind_info, level)
      self.cache[level] = (ind_reduce, ty)
    return self.cache[level]
  def add(self, name, entry):
    raise RuntimeError("Inductive module cannot accept new definitions!")


def env_map(env:Env, fn) -> Env:
  match env:
    case EmptyEnv():
      return EmptyEnv()
    case EnvEntry(prev, val):
      return EnvEntry(
        env_map(prev, fn),
        fn(val))


@dataclass(frozen=True)
class GetIHResult:
  """ Result type for the function get_ih.
      copy: None if field_ty contains self-reference, a copy of field_ty otherwise.
      ih: I.H. data (args, scrut, indices) if there's an I.H., None otherwise.
      args: The arguments of the I.H. function.
      scrut: The scrutinee for the I.H.
      indices: The indices for the I.H.
      Invariant: (copy != None) implies (ih == None) because can't have I.H. without self-reference. """
  copy: IrNode|None
  ih: tuple[List[tuple[Binder, IrNode]], IrNode, tuple[IrNode, ...]]|None

def get_ih(arg_ty:IrNode, original_arg:IrNode, domain_depth:int=0) -> GetIHResult:
  """ This function recursively walks the entire arg_ty syntax tree.
      We raise a definition error if we encounter something disallowed.
      domain_depth allows us to perform positivity checking, & distinguish strict positivity. """
  match arg_ty:
    case IrLam(_, _, _):
      raise DefinitionError("Lambdas are not allowed in constructor field types.")
    case IrLet(_, _, _, _):
      raise DefinitionError("Let statements are not allowed in constructor field types.")
    case IrSort(level):
      return GetIHResult(IrSort(level), None)
    case IrConst(path):
      return GetIHResult(IrConst(path), None)
    case IrVar(binder):
      return GetIHResult(IrVar(binder), None)
    case IrApp(fn, arg):
      fn_res = get_ih(fn, original_arg, domain_depth=domain_depth)
      arg_res = get_ih(arg, original_arg, domain_depth=domain_depth)
      if fn_res.copy is None or arg_res.copy is None:
        raise DefinitionError("Self-references can't appear in function applications.")
      return GetIHResult(IrApp(fn_res.copy, arg_res.copy), None)
    case IrPi(param, A, B):
      A_res = get_ih(A, original_arg, domain_depth=domain_depth + 1)
      B_res = get_ih(B, IrApp(original_arg, IrVar(param)), domain_depth=domain_depth)
      if A_res.copy is None or B_res.copy is None:
        copy = None
      else:
        copy = IrPi(param, A_res.copy, B_res.copy)
      if A_res.copy is None or B_res.ih is None:
        ih = None
      else:
        B_args, B_scrut, B_indices = B_res.ih
        B_args = [(param, A_res.copy)] + B_args
        ih = (B_args, B_scrut, B_indices)
      return GetIHResult(copy, ih)
    case IrInductiveSelfRef(indices):
      copy = None # self-reference means we can't copy this
      if domain_depth % 2 == 1:
        raise DefinitionError("Negative appearance of self-reference: Positivity check failed.")
      elif domain_depth == 0: # strictly positive appearance
        ih = ([], original_arg, indices)
      else:
        ih = None
      return GetIHResult(copy, ih)
    case _:
      raise DefinitionError(f"Unexpected IrNode type {type(arg_ty)}.")


def define_inductive(module:Module, declaration:IrInductiveDefinition) -> InductiveInfo:
  """ Check and install an inductive. Roll back all entries if checking fails.

  Parameters are uniform. Recursive fields must be written as I[indices];
  function-valued, nested, and mutual recursion are not supported yet.
  """
  name, params, indices = declaration.name, declaration.params, declaration.indices
  constructors, sort = declaration.constructors, declaration.sort
  if not isinstance(sort, IrSort) or sort.level < 0:
    raise DefinitionError("Inductive type must end in a non-negative universe.")
  
  def extend(
    binders:list[tuple[Binder, IrNode]], typing_ctx:Env, binder_ctx:Env,
    selfref:IrNode|None=None, constrain_level:bool=False,
  ) -> Env:
    depth = len(typing_ctx)
    for (binder, type_ir) in binders:
      if selfref is not None: # re-write self references if available
        type_ir = selfref_sub(type_ir, selfref)
      ty = type_ir.to_term(module, binder_ctx)
      level = infer_sort(ty, typing_ctx)
      domain = term_eval(ty, LazyEnvMap(typing_ctx, ann_val))
      if constrain_level and level > sort.level:
        raise TypecheckError(f"Constructor field {name} exceeds Type{sort.level}.")
      # update the context and names map
      ann = (VNeutral(depth, ()), domain, binder.name)
      typing_ctx = EnvEntry(typing_ctx, ann)
      binder_ctx = EnvEntry(binder_ctx, binder)
      depth += 1
    return typing_ctx, binder_ctx
  
  # check inductive params and indices
  param_ctx, param_binder_ctx = extend(params, EmptyEnv(), EmptyEnv())
  extend(indices, param_ctx, param_binder_ctx)
  
  # overall type of the inductive family
  family_ty_ir = pi_wrap(sort, (params + indices))
  family_ty_term = family_ty_ir.to_term(module, EmptyEnv())
  infer_sort(family_ty_term, EmptyEnv())
  family_ty = term_eval(family_ty_term, EmptyEnv())
  
  # initialize the InductiveInfo (with constructors to be populated later)
  info = InductiveInfo(TConst(module, (name,)), len(params), len(indices), ())
  module.add(name, (
    VContainer(info.ref, len(params) + len(indices), blocked_noforce),
    family_ty
  ))
  
  # Give ourselves selfref access now that the family has been added to the module
  param_refs = [IrVar(binder) for binder, _ in params]
  selfref = app_wrap(IrConst((name,)), param_refs)
  
  # Check the constructors
  constructor_infos = []
  cases = []
  binder_motive = Binder("@motive")
  var_motive = IrVar(binder_motive)
  for tag, constructor in enumerate(constructors):
    # constructor typechecking
    cons_ctx = extend(constructor.args, param_ctx, param_binder_ctx, selfref=selfref, constrain_level=True)
    if len(constructor.output_indices) != len(indices):
      raise DefinitionError(f"Constructor {constructor.name} has the wrong number of output indices.")
    cons_ty_ir = pi_wrap(
      IrInductiveSelfRef(constructor.output_indices),
      (params + constructor.args))
    cons_ty_ir = selfref_sub(cons_ty_ir, selfref)
    cons_ty = cons_ty_ir.to_term(module, EmptyEnv())
    infer_sort(cons_ty, EmptyEnv())
    
    # build the rule and the branch fn arg dtypes for this constructor
    binder_rec = Binder("@rec")
    binder_case = Binder("@case")
    rule_names = EnvEntry(EnvEntry(EmptyEnv(), binder_rec), binder_case)
    for param_binder, _ in params: # indices can reference params, so we add them to the env
      rule_names = EnvEntry(rule_names, param_binder)
    var_rec = IrVar(binder_rec) # partially applied (still missing indices and scrutinee) induction
    rule = IrVar(binder_case)  # case handling function
    case_args = []
    for binder, type_ir in constructor.args:
      arg_var = IrVar(binder)
      # update rule
      rule_names = EnvEntry(rule_names, binder)
      rule = IrApp(rule, arg_var)
      # update case args
      case_args.append((binder, type_ir))
      ih_result = get_ih(type_ir, arg_var)
      if ih_result.ih is not None:
        args, scrut, ih_indices = ih_result.ih
        # update rule with recursion
        recursive_call = IrApp(app_wrap(var_rec, ih_indices), scrut)
        rule = IrApp(rule, lam_wrap(recursive_call, args))
        # update case args with recursion
        ih = pi_wrap(IrApp(app_wrap(var_motive, ih_indices), scrut), args)
        case_args.append((Binder(f"@ih_{binder.name}"), ih))
    # finalize rule for this constructor
    constructor_info = ConstructorInfo(TConst(module, (constructor.name,)),
      len(constructor.args), rule.to_term(module, rule_names))
    constructor_infos.append(constructor_info)
    # finalize branch dtype for this constructor
    constructed = app_wrap(IrConst((constructor.name,)),
        param_refs + [IrVar(binder) for binder, _ in constructor.args])
    case_result = app_wrap(var_motive, constructor.output_indices + [constructed])
    cases.append((
      Binder(f"@case{tag}_{constructor.name}"),
      pi_wrap(case_result, case_args)
    ))
    # add this constructor to the module
    module.add(constructor.name, (
      VContainer(constructor_info.ref, info.nparams + constructor_info.nfields, blocked_noforce),
      term_eval(cons_ty, EmptyEnv())
    ))
  
  # update the constructor info now
  info.constructors = tuple(constructor_infos)
  
  # motive type
  binder_sort = Binder("@sort")
  var_sort = IrVar(binder_sort) # an extra variable that we add to make induction generic over sorts
  index_vars = [IrVar(binder) for binder, _ in indices]
  instance_ty = IrInductiveSelfRef(index_vars)
  motive_ty = pi_wrap(IrPi(Binder("@instance"), instance_ty, var_sort), indices)
  
  # build the inductor type
  ind_args = []
  for binder, type_ir in params:
    ind_args.append((binder, type_ir))
  ind_args.append((binder_motive, motive_ty))
  for binder, type_ir in cases:
    ind_args.append((binder, type_ir))
  for binder, type_ir in indices:
    ind_args.append((binder, type_ir))
  scrutinee_ty = IrInductiveSelfRef(index_vars)
  scrut_binder = Binder("@scrutinee")
  var_scrutinee = IrVar(scrut_binder)
  ind_args.append((scrut_binder, scrutinee_ty))
  result_ty = IrApp(app_wrap(var_motive, index_vars), var_scrutinee)
  ind_ty = pi_wrap(result_ty, ind_args)
  # do selfref substitution
  ind_ty = selfref_sub(ind_ty, selfref)
  
  # make the InductiveModule
  ind_module = InductiveModule(info, ind_ty.to_term(module, EnvEntry(EmptyEnv(), binder_sort)))
  module.add(name, ind_module)
  
  return info



