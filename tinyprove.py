from dataclasses import dataclass
from typing import List, Dict, Tuple


class BetaReductionError(Exception):
  pass

class TypecheckError(Exception):
  pass

class DefinitionError(Exception):
  pass


# ---- Term AST and DeBruijn Manipulations: ----

class Term:
  """ Base class for tinyprove AST. """
  def __str__(self):
    return self.str([])

@dataclass(frozen=True)
class Sort(Term):
  level: int
  def str(self, ctx):
    return f"Type{self.level}"
  def shift(self, shift, keep=0):
    return self
  def subst(self, j, term):
    return self

@dataclass(frozen=True)
class Const(Term):
  name: str
  def str(self, ctx):
    return self.name
  def shift(self, shift, keep=0):
    return self
  def subst(self, j, term):
    return self

@dataclass(frozen=True)
class Var(Term):
  depth:int
  def str(self, ctx):
    if self.depth < len(ctx):
      return ctx[self.depth][0]
    else:
      return f"^{self.depth}"
  def shift(self, shift, keep=0):
    if self.depth < keep: return self
    return Var(self.depth + shift)
  def subst(self, j, term):
    if self.depth == j:
      return term
    if self.depth > j:
      return Var(self.depth - 1) # substitution removes a variable
    return self

@dataclass(frozen=True)
class Pi(Term):
  param: str
  A: Term
  B: Term
  def str(self, ctx):
    return f"(Π {self.param}:{self.A.str(ctx)} => {self.B.str([(self.param, None)] + ctx)})"
  def shift(self, shift, keep=0):
    return Pi(self.param, self.A.shift(shift, keep), self.B.shift(shift, keep + 1)) # keep param
  def subst(self, j, term):
    return Pi(self.param, self.A.subst(j, term), self.B.subst(j + 1, term.shift(1)))

@dataclass(frozen=True)
class Lam(Term):
  param: str
  A: Term
  body: Term
  def str(self, ctx):
    return f"(λ {self.param}:{self.A.str(ctx)} -> {self.body.str([(self.param, None)] + ctx)})"
  def shift(self, shift, keep=0):
    return Lam(self.param, self.A.shift(shift, keep), self.body.shift(shift, keep + 1)) # keep param
  def subst(self, j, term):
    return Lam(self.param, self.A.subst(j, term), self.body.subst(j + 1, term.shift(1)))

@dataclass(frozen=True)
class App(Term):
  fn: Term
  arg: Term
  def str(self, ctx):
    return f"({self.fn.str(ctx)} {self.arg.str(ctx)})"
  def shift(self, shift, keep=0):
    return App(self.fn.shift(shift, keep), self.arg.shift(shift, keep))
  def subst(self, j, term):
    return App(self.fn.subst(j, term), self.arg.subst(j, term))


# ---- Axioms and Inductive Definitions: ----

def pi_wrap(inner:Term, ctx:List[Tuple[str, Term]]):
  """ Wrap an inner type in a context. inner may contain DeBruijn indices pointing out to ctx. """
  ans = inner
  for nm, ty in ctx:
    ans = Pi(nm, ty, ans)
  return ans

def sub_const(expr:Term, name:str, val:Term, depth=0):
  """ substitute Const(name) for val in expr """
  match expr:
    case Lam(param, A, body):
      return Lam(param, sub_const(A, name, val, depth), sub_const(body, name, val, depth + 1))
    case Pi(param, A, B):
      return Pi(param, sub_const(A, name, val, depth), sub_const(B, name, val, depth + 1))
    case App(fn, arg):
      return App(sub_const(fn, name, val, depth), sub_const(arg, name, val, depth))
    case Var() | Sort():
      return expr
    case Const(name):
      if name == name:
        return val.shift(depth)
      else:
        return expr

class InductiveDef:
  def __init__(self, name:str, params:List[Tuple[str, Term]], constructors:Dict[str, List[Tuple[str, Term]]]):
    self.name = name
    self.params = params
    self.constructors = constructors
    # check definition validity and construct types
    self._check_positive()
    self._build_ctx()
    self._build_ty()
    self._build_parametrized_ty()
    self._build_cons_tys()
    self._build_ind_ty()
  def _check_ty_is_sort(self, ty:Term, ctx, axioms=None):
    ty_ty = infer(ty, ctx, axioms)
    if not isinstance(ty_ty, Sort):
      raise TypecheckError(f"Expected {ty.str(ctx)} to be a Sort but found type {ty_ty.str(ctx)}.")
  def _build_ctx(self):
    ctx = []
    for param_nm, param_ty in self.params:
      self._check_ty_is_sort(param_ty, ctx)
      ctx = [(param_nm, param_ty)] + ctx
    self._ctx = ctx
  def _check_positive(self, curr_sign=1):
    for cons_name in self.constructors:
      if cons_name == "ind": raise DefinitionError("ind is a reserved name and cannot be used as a constructor name.")
      cons = self.constructors[cons_name]
      for param_name, param_ty in cons:
        positive = self._walk(param_ty)
        if not positive:
          raise DefinitionError(f"Constructor {cons_name} parameter {param_name} fails positivity check.")
  def _walk(self, term:Term, polarity:int=1):
    match term:
      case Lam():
        raise DefinitionError("Lambdas not supported in constructor definition.")
      case Pi(param, A, B):
        return self._walk(A, -polarity) and self._walk(B, polarity)
      case App(fn, arg):
        return self._walk(fn, polarity) and self._walk(arg, polarity)
      case Var() | Sort():
        return True
      case Const(name):
        if name == self.name: # recursion
          return polarity == 1
        else:
          # TODO: allow refs to previously existing definitions?
          raise DefinitionError("Const {name}: Constants that are not direct recursive references not supported in constructor definition.")
  def _check_constructor_args(self):
    for cons_name in self.constructors:
      cons = self.constructors[cons_name]
      ctx = self._ctx
      for param_nm, param_ty in cons:
        self._check_ty_is_sort(param_ty, ctx)
        ctx = [(param_nm, param_ty)] + ctx
  def _build_ty(self):
    self.ty = pi_wrap(Sort(0), self._ctx) # TODO: inductive defs being Type0 is hardcoded here, maybe want to change...
  def _build_parametrized_ty(self):
    # build up constructor codomain (fully parametrized guy)
    parametrized_ty = Const(self.name)
    depth = len(self.params)
    for param_nm, param_ty in self.params:
      depth -= 1
      parametrized_ty = App(parametrized_ty, Var(depth)) # the DeBruijn indices for these vars will be dangling until we call pi_wrap on it
    self._parametrized_ty = parametrized_ty
  def _build_cons_tys(self):
    axioms = {self.name: self.ty} # need this to typecheck constructors
    self.cons_tys = {}
    # typecheck each constructor arg and then build the constructor type
    for cons_name in self.constructors:
      cons = self.constructors[cons_name]
      ctx = self._ctx
      depth = 0
      for param_nm, param_ty in cons:
        # expand appearance of the type with it's properly parametrized version
        param_ty = sub_const(param_ty, self.name, self._parametrized_ty, depth=depth)
        depth += 1
        # typecheck and add to context
        self._check_ty_is_sort(param_ty, ctx, axioms)
        ctx = [(param_nm, param_ty)] + ctx
      self.cons_tys[cons_name] = pi_wrap(self._parametrized_ty.shift(len(cons)), ctx)
  def _build_ind_ty(self):
    motive_ty = Pi("x", self._parametrized_ty, Sort(0)) # TODO: universe hardcoded to Type0 here. maybe bad?
    depth = 1
    ctx = [("Motive", motive_ty)] + self._ctx
    for cons_name in self.constructors:
      cons = self.constructors[cons_name]
      # the next x value built by the constructor
      x_next = Const(f"{self.name}.{cons_name}") # global reference to this constructor
      for i in range(len(self._ctx))[::-1]: # type parameters, count down so we go from outermost vars first
        x_next = App(x_next, Var(i + depth + len(cons)))
      for i in range(len(cons))[::-1]: # constructor args, count down so we go from outermost vars first
        x_next = App(x_next, Var(i))
      # create type of branch fn
      branch_ty = pi_wrap(
        App(
          Var(len(cons) + depth - 1), # points to `Motive` in ctx
          x_next),
        [(nm, ty.shift(depth, keep=i)) for i, (nm, ty) in enumerate(cons)][::-1] # account for context lengthening
      )
      ctx = [(f"branch_{cons_name}", branch_ty)] + ctx
      depth += 1
    ans = Pi("x", self._parametrized_ty.shift(depth), App(Var(depth), Var(0)))
    self.ind_ty = pi_wrap(ans, ctx)
  def query(self, key:str) -> Term:
    base, *rest = key.split(".")
    if base != self.name: raise IndexError()
    if len(rest) == 0:
      return self.ty
    if len(rest) > 1: raise IndexError()
    if rest[0] == "ind":
      return self.ind_ty
    return self.cons_tys[rest[0]]

class AxiomDef:
  def __init__(self, name:str, subname:str, ax_type:Term):
    self.name = name
    self.subname = subname
    self._ax_ty = ax_type
  def query(self, key:str) -> Term:
    if key == f"{self.name}.{self.subname}":
      return self._ax_ty
    raise IndexError()

class Definitions:
  def __init__(self):
    self.defns = []
    self._index = {}
  def _reindex_defs(self):
    self._index = {defn.name: defn for defn in self.defns}
  def add_defn(self, defn):
    if defn.name in self._index:
      raise DefinitionError(f"{defn.name} already defined.")
    pass # TODO: put some kind of typechecking here!!!
    self.defns.append(defn)
    self._reindex_defs()
  def __getitem__(self, key:str) -> Term:
    name = key.split(".")[0]
    if name not in self._index:
      raise IndexError(f"Unknown name {name}.")
    return self._index[name].query(key)
  def __contains__(self, key:str) -> bool:
    try:
      self[key]
    except IndexError:
      return False
    else:
      return True


# ---- WHNF Reduction and Type-checking / Inference: ----

def whnf(term:Term):
  """ Reduce term to weak head normal form. """
  match term:
    case App(fn, arg):
      fn = whnf(fn)
      if isinstance(fn, Lam):
        return whnf(fn.body.subst(0, arg))
      else:
        return App(fn, arg)
    case _:
      return term

def conv(t1:Term, t2:Term):
  t1 = whnf(t1)
  t2 = whnf(t2)
  match t1, t2:
    case Sort(l1), Sort(l2):
      return l1 == l2
    case Var(depth1), Var(depth2):
      return depth1 == depth2
    case Const(name1), Const(name2):
      return name1 == name2
    case App(fn1, arg1), App(fn2, arg2):
      return conv(fn1, fn2) and conv(arg1, arg2)
    case Pi(_, A1, B1), Pi(_, A2, B2):
      return conv(A1, A2) and conv(B1, B2)
    case Lam(_, A1, body1), Lam(_, A2, body2):
      return conv(A1, A2) and conv(body1, body2)
    case _:
      return False # mismatched shapes

def infer(term, ctx, defns=None):
  if defns is None:
    defns = {}
  match term:
    case Sort(level):
      return Sort(level + 1)
    case Const(name):
      if name not in defns:
        raise TypecheckError(f"Unknown constant {name}.")
      return defns[name]
    case Var(depth):
      if 0 <= depth < len(ctx):
        name, var_ty = ctx[depth]
        return var_ty.shift(depth + 1)
      else:
        raise TypecheckError(f"Tried to lookup a varible with depth {depth} in context of size {len(ctx)}")
    case Pi(param, A, B):
      A_ty = whnf(infer(A, ctx, defns))
      if not isinstance(A_ty, Sort):
        raise TypecheckError(f"Expected A in Pi type {term.str(ctx)} to be a Sort, but found {A_ty.str(ctx)}.")
      ctx_B = [(param, A)] + ctx
      B_ty = whnf(infer(B, ctx_B, defns))
      if not isinstance(B_ty, Sort):
        raise TypecheckError(f"Expected B in Pi type {term.str(ctx)} to be a Sort, but found {B_ty.str(ctx_B)}.")
      return Sort(max(A_ty.level, B_ty.level))
    case Lam(param, A, body):
      A_ty = whnf(infer(A, ctx, defns))
      if not isinstance(A_ty, Sort):
        raise TypecheckError(f"Expected A in Lam {term.str(ctx)} to be a Sort, but found {A_ty.str(ctx)}")
      ctx_body = [(param, A)] + ctx
      body_ty = infer(body, ctx_body, defns)
      return Pi(param, A, body_ty)
    case App(fn, arg):
      fn_ty = whnf(infer(fn, ctx, defns))
      match fn_ty:
        case Pi(param, A, B):
          check(arg, A, ctx, defns)
          ctx_B = [(param, A)] + ctx
          return whnf(B.subst(0, arg))
        case _:
          raise TypecheckError(f"Expected type of fn in application {term.str(ctx)} to be a Pi type, but found {fn_ty.str(ctx)}.")
    case _:
      raise TypecheckError(f"Failed to recognize term {term}")

def check(term, expected, ctx, defns=None):
  if defns is None:
    defns = {}
  term_ty = infer(term, ctx, defns)
  if not conv(term_ty, expected):
    raise TypecheckError(f"Expected term {term.str(ctx)} to have type {expected.str(ctx)} but found {term_ty.str(ctx)}.")




