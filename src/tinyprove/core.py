from __future__ import annotations
from dataclasses import dataclass, field


class LookupError(Exception):
  pass
class EvalError(Exception):
  pass
class TypecheckError(Exception):
  pass
class DefinitionError(Exception):
  pass


# Base classes:

class Binding:
  """ Value or Thunk or Axiom """
  pass

class Value(Binding):
  """ Base class for the result of an expression """
  def force(self) -> Value:
    return self

class Axiom(Binding):
  """ A binding with no constructive/computational content. Raises an Error when forced. """
  def force(self) -> Value:
    raise EvalError("Can't force an Axiom.")

class Elimination:
  """ An Elimination is something that can be blocked by a free variable. """
  pass

class Term:
  """ Base class for an expression in the language """
  pass

class Env:
  """ environments are trees of upwards refs, rooted at EmptyEnv() """
  def __getitem__(self, idx):
    return self.at(idx)


# Term concrete classes:

@dataclass(frozen=True)
class TSort(Term):
  level: int
  def str(self, ctx:Env):
    return f"Type{self.level}"

@dataclass(frozen=True)
class TConst(Term):
  module: Module
  path: tuple[str, ...]
  def str(self, ctx:Env):
    return f"[Module {id(self.module)}].{'.'.join(self.path)}"
  def _get_def_id(self):
    """ Use python's id builtin to get this definition's unique id. """
    return id(self.module[self.path])

@dataclass(frozen=True)
class TVar(Term):
  idx: int
  def str(self, ctx:Env):
    name = ctx[self.idx]
    skipped = sum(ctx[i] == name for i in range(self.idx))
    return name + "'" * skipped # add ticks to disambiguate collisions

@dataclass(frozen=True)
class TNatLit(Term):
  val: int # Requirement: must be non-negative
  def str(self, ctx:Env):
    return f"{self.val}"

@dataclass(frozen=True)
class TNat(Term):
  def str(self, ctx:Env):
    return "ℕ"

@dataclass(frozen=True)
class TSucc(Term):
  def str(self, ctx:Env):
    return "σ"

@dataclass(frozen=True)
class TApp(Term):
  head: Term
  arg: Term
  def str(self, ctx:Env):
    return f"({self.head.str(ctx)} {self.arg.str(ctx)})"

@dataclass(frozen=True)
class TLam(Term):
  param: str = field(compare=False)
  A: Term | None
  body: Term
  def str(self, ctx:Env):
    ctx_new = EnvEntry(ctx, self.param)
    body_str = self.body.str(ctx_new)
    annotation = "" if self.A is None else f": {self.A.str(ctx)}"
    return f"(λ {self.param}{annotation} -> {body_str})"

@dataclass(frozen=True)
class TPi(Term):
  param: str = field(compare=False)
  A: Term
  B: Term
  def str(self, ctx:Env):
    ctx_new = EnvEntry(ctx, self.param)
    return f"(Π {self.param}: {self.A.str(ctx)} => {self.B.str(ctx_new)})"

@dataclass(frozen=True)
class TLet(Term):
  name: str = field(compare=False)
  A: Term | None
  rhs: Term
  body: Term
  def str(self, ctx:Env):
    ctx_new = EnvEntry(ctx, self.name)
    rhs_str = self.rhs.str(ctx)
    body_str = self.body.str(ctx_new)
    annotation = "" if self.A is None else f": {self.A.str(ctx)}"
    return f"{{ {self.name}{annotation} = {rhs_str},\n{body_str} }}"


# Env concrete classes:

@dataclass(frozen=True)
class EmptyEnv(Env):
  def at(self, idx:int) -> object:
    raise LookupError(f"Tried to look up {idx} from EmptyEnv.")
  def __len__(self) -> int:
    return 0
  def index_of(self, val:object, ans:int=0) -> int:
    return -1 # not found

@dataclass(frozen=True)
class EnvEntry(Env):
  prev: Env
  val: object
  def at(self, idx:int) -> object:
    if idx == 0:
      return self.val
    else:
      return self.prev.at(idx - 1)
  def __len__(self) -> int:
    return 1 + len(self.prev)
  def index_of(self, val:object, ans:int=0) -> int:
    if val == self.val:
      return ans
    else:
      return self.prev.index_of(val, 1 + ans)

@dataclass(frozen=True)
class LazyEnvMap:
  """ Maps an Env to another effective env via a mapping function.
      The mapping function is called only when an element is retrieved.
      Duck types to Env. """
  env: Env
  mapfn: object # callable
  def at(self, idx:int) -> object:
    return self.mapfn(self.env.at(idx))
  def __len__(self) -> int:
    return len(self.env)
  def __getitem__(self, idx):
    return self.at(idx)

# Environment types:
#   - Value environment.      val: Binding
#   - Typing context.         val: (Binding, Value, str)
#   - Variable name context.  val: str

# a context annotation is a (value, type, name) tuple
def ann_val(ann:tuple[Binding, Value, str]) -> Binding:
  value, ty, name = ann
  return value
def ann_ty(ann:tuple[Binding, Value, str]) -> Value:
  value, ty, name = ann
  return ty
def ann_name(ann:tuple[Binding, Value, str]) -> str:
  value, ty, name = ann
  return name

# Modules

class Module:
  """ Constants are (Binding, Value) pairs. They and submodules have separate namespaces.
      Submodules must subclass Module and support tuple-path lookup via __getitem__. """
  def __init__(self):
    self.entries = {}
    self.submodules = {}
  def __getitem__(self, path:tuple[str, ...]) -> tuple[Binding, Value]:
    if not path:
      raise LookupError("A constant path must be nonempty.")
    name, *rest = path
    if rest:
      if name not in self.submodules:
        raise LookupError(f"No submodule named {name}.")
      return self.submodules[name][tuple(rest)]
    else:
      if name not in self.entries:
        raise LookupError(f"No constant named {name}.")
      return self.entries[name]
  def add(self, name:str, entry:tuple[Binding, Value]|Module):
    """ Add an already checked entry or an imported module.
        MUTATES self. """
    if isinstance(entry, Module):
      if name in self.submodules:
        raise DefinitionError(f"A submodule named {name} already exists.")
      self.submodules[name] = entry
    else:
      if name in self.entries:
        raise DefinitionError(f"A constant named {name} already exists.")
      self.entries[name] = entry

# a def in a Module is a (value, type) pair
def def_val(defn:tuple[Value, Value]) -> Value:
  val, ty = defn
  return val
def def_ty(defn:tuple[Value, Value]) -> Value:
  val, ty = defn
  return ty

def define(module:Module, name:str, term:Term, expected:Term|None):
  """ Check a closed definition and add it to module.
      MUTATES module. """
  if expected is None:
    ty = infer(term, EmptyEnv())
  else:
    infer_sort(expected, EmptyEnv())
    ty = term_eval(expected, EmptyEnv())
    check(term, ty, EmptyEnv())
  entry = (Thunk(term, EmptyEnv()), ty)
  module.add(name, entry)
  return entry


# Thunks and Closures

@dataclass
class Cache:
  """ Saves an answer computed once for later. """
  full:bool = False
  data:object|None = None
  def is_empty(self):
    return not self.full
  def set(self, data:object):
    assert not self.full, "Can't overwrite full Cache"
    self.full = True
    self.data = data
  def get(self):
    assert self.full, "Can't retrieve from empty Cache"
    return self.data

@dataclass
class Thunk(Binding):
  """ A term with its local environment, evaluated lazily. """
  term: Term
  env: Env
  cache:Cache = field(default_factory=Cache)
  def force(self) -> Value:
    if self.cache.is_empty():
      self.cache.set(term_eval(self.term, self.env))
    return self.cache.get()

@dataclass(frozen=True)
class Closure:
  """ A term with its local environment; accepts an argument. """
  term: Term
  env: Env
  def apply(self, arg:Binding) -> Value:
    return term_eval(self.term, EnvEntry(self.env, arg))


# Elimination concrete classes:

@dataclass(frozen=True)
class EApp(Elimination):
  arg: Binding

@dataclass(frozen=True)
class EInd(Elimination):
  ind_ref: TConst
  args: tuple[Binding]

@dataclass(frozen=True)
class EAdd(Elimination):
  a: int


# Value concrete classes:

@dataclass(frozen=True)
class VSort(Value):
  level: int

@dataclass(frozen=True)
class VNatLit(Value):
  val: int # Requirement: must be non-negative

@dataclass(frozen=True)
class VNat(Value):
  pass

@dataclass(frozen=True)
class VLam(Value):
  body: Closure

@dataclass(frozen=True)
class VPi(Value):
  A: Binding
  B: Closure

@dataclass(frozen=True)
class VNeutral(Value):
  """ An expression that cannot be reduced due to occurence of a free variable in the head """
  head_level: int
  args: tuple[Elimination, ...]
  def add(self, n:int) -> VNeutral:
    """ Apply σ n times to this VNeutral.
        Invariant: EAdd(a) always has a > 0
        Invariant: Two EAdd's never appear in a row (they're combined instead) """
    if n == 0: return self
    if len(self.args) > 0:
      match self.args[-1]:
        case EAdd(a):
          new_args = self.args[:-1] + (EAdd(a + n),)
          return VNeutral(self.head_level, new_args)
    new_args = self.args + (EAdd(n),)
    return VNeutral(self.head_level, new_args)

@dataclass(frozen=True)
class VCons(Value):
  cons_ref: TConst
  tag: int
  params_fields: tuple[Binding, ...]

@dataclass(frozen=True)
class VIndType(Value):
  ref: TConst
  params_indices: tuple[Binding, ...]

@dataclass(frozen=True)
class VPartial(Value):
  """ A VPartial represents a multi-argument function that does not have all
      of its arguments yet. We apply the python function fn when we do have them.
      The function accepts a copy of itself and a tuple of Bindings and returns
      a Value. The copy of itself is to allow recursive functions to be used.
      For quoting purposes, there is head_ref, which gives the Term for the fn
      when 0 args are applied.
      Typing convention: A VPartial where len(args) == nargs is considered to be
      a Binding only, not a Value. """
  head_ref: TConst
  nargs: int
  fn: object
  args: tuple[Binding, ...] = ()
  cache: Cache = field(default_factory=Cache)
  def force(self) -> Value:
    if self.cache.is_empty():
      if len(self.args) == self.nargs:
        result = self.fn(self.fn, self.args)
      else: # partially applied VPartial just gives us a VPartial
        result = self
      self.cache.set(result)
    return self.cache.get()
  def apply(self, arg:Binding) -> Value:
    newargs = self.args + (arg,)
    return VPartial(self.head_ref, self.nargs, self.fn, newargs).force()


# ...

def add_to(a:int, n:Binding) -> Value:
  n = n.force()
  match n:
    case VNatLit(nn):
      return VNatLit(a + nn)
    case VNeutral(_, _):
      return n.add(a)
    case _:
      raise EvalError(f"Can't add to value {n}")

def get_partial_for_succ() -> VPartial:
  def succ(rec, args:tuple[Binding, ...]) -> Value:
    n, = args
    return add_to(1, n)
  return VPartial(TSucc(), 1, succ)

def get_partial_for_nat(val:int, P:Binding) -> VPartial:
  """ makes a given VNatLit as a VPartial, with first P arg already applied.
      this is a hack so we can make Nat literals callable. """
  def iterate(rec, args:tuple[Binding, ...]) -> Value:
    P, f, b = args
    if val == 0:
      return b.force()
    f = f.force()
    for i in range(val):
      b = vapp(f, b)
    return b
  return VPartial(TNatLit(val), 3, iterate, (P,))

def vapp(fn:Value, arg:Binding) -> Value:
  match fn:
    case VLam(body):
      return body.apply(arg)
    case VNeutral(head_level, args):
      return VNeutral(head_level, args + (EApp(arg),))
    case VPartial(_, _, _, _, _):
      return fn.apply(arg)
    case VNatLit(val):
      return get_partial_for_nat(val, arg)
    case _:
      raise EvalError(f"Uncallable value {fn}")

def term_eval(term:Term, env:Env) -> Value:
  match term:
    case TSort(level) if level >= 0:
      return VSort(level)
    case TConst(module, path):
      return def_val(module[path]).force()
    case TVar(idx):
      return env.at(idx).force()
    case TNatLit(val):
      return VNatLit(val)
    case TNat():
      return VNat()
    case TSucc():
      return get_partial_for_succ()
    case TApp(head, arg):
      head_val = term_eval(head, env)
      arg_bind = Thunk(arg, env)
      return vapp(head_val, arg_bind)
    case TLam(_, _, body):
      return VLam(Closure(body, env))
    case TPi(_, A, B):
      return VPi(Thunk(A, env), Closure(B, env))
    case TLet(_, _, rhs, body):
      rhs_bind = Thunk(rhs, env)
      return Closure(body, env).apply(rhs_bind)
    case _:
      raise EvalError(f"Unknown term {term}")


def quote_apps(head:Term, args:tuple[Binding, ...], depth:int) -> Term:
  for arg in args:
    head = TApp(head, quote(arg, depth))
  return head

def quote_elims(head:Term, elims:tuple[Elimination, ...], depth:int) -> Term:
  for elim in elims:
    match elim:
      case EApp(arg):
        head = TApp(head, quote(arg, depth))
      case EInd(ind_ref, args):
        icall = ind_ref
        for arg in args:
          icall = TApp(icall, quote(arg, depth))
        head = TApp(icall, head) # for inductive elimination, the head is the scrutinee
      case EAdd(a):
        head = TApp(TApp(TApp(TNatLit(a), TNat()), TSucc()), head)
      case _:
        raise EvalError(f"Unrecognized elimination {elim}")
  return head

def quote(val:Binding, depth:int=0) -> Term:
  """ Reify a value. Quoted lambdas need an expected type when checked. """
  val = val.force() # convert to Value
  match val:
    case VSort(level):
      return TSort(level)
    case VNatLit(n):
      return TNatLit(n)
    case VNat():
      return TNat()
    case VLam(body):
      arg = VNeutral(depth, ())
      return TLam(f"x{depth}", None, quote(body.apply(arg), depth + 1)) # codomain is unknown
    case VPi(A, B):
      arg = VNeutral(depth, ())
      return TPi(f"x{depth}", quote(A, depth), quote(B.apply(arg), depth + 1))
    case VNeutral(head_level, elims):
      assert 0 <= head_level < depth
      idx = depth - head_level - 1
      return quote_elims(TVar(idx), elims, depth)
    case VCons(cons_ref, tag, params_fields):
      return quote_apps(cons_ref, params_fields, depth)
    case VIndType(ref, params_indices):
      return quote_apps(ref, params_indices, depth)
    case VPartial(head_ref, _, _, args, _):
      return quote_apps(head_ref, args, depth)
    case _:
      raise EvalError(f"Unknown value {val}")


def is_fn(fn: Value) -> bool:
  match fn:
    case VLam(_):
      return True
    case VPartial(_, _, _, _, _): # fn is a Value, not Binding, so we know it's not fully applied
      return True
  return False


def conv(a:Binding, b:Binding, depth:int=0, accept_assignable:bool=False) -> bool:
  """ Check structural equality for two values. The check is exact and symmetric by
      default. If accept_assignable is True, we instead check if `a` is assignable to `b`. """
  a, b = a.force(), b.force()
  # first we compare callable values
  if is_fn(a) or is_fn(b):
    x = VNeutral(depth, ()) # introduce a fresh neutral
    return conv(vapp(a, x), vapp(b, x), depth + 1)
  # now we compare all the other kinds of things
  match a, b:
    case VSort(i), VSort(j):
      return i == j or (accept_assignable and i <= j)
    case VNatLit(n), VNatLit(m):
      return n == m
    case VNat(), VNat():
      return True
    case VNeutral(i, xs), VNeutral(j, ys):
      return i == j and conv_elims(xs, ys, depth)
    case VPi(A, B), VPi(C, D):
      x = VNeutral(depth, ())
      return ( # NOTE: we preserve the accept_assignable flag for Pi types
        conv(C, A, depth, accept_assignable) and  # swap argument order to ensure contravariance
        conv(B.apply(x), D.apply(x), depth + 1, accept_assignable) # same order for covariance
      )
    case VCons(ref_a, tag_a, params_fields_a), VCons(ref_b, tag_b, params_fields_b):
      return (ref_a._get_def_id() == ref_b._get_def_id() and tag_a == tag_b and
        conv_args(params_fields_a, params_fields_b, depth))
    case VIndType(ref_a, params_indices_a), VIndType(ref_b, params_indices_b):
      return (ref_a._get_def_id() == ref_b._get_def_id() and
        conv_args(params_indices_a, params_indices_b, depth))
  return False

def conv_args(xs:tuple[Binding, ...], ys:tuple[Binding, ...], depth:int) -> bool:
  return (len(xs) == len(ys) and
    all(
      conv(x, y, depth)
      for x, y in zip(xs, ys)
    ))

def conv_elim(x:Elim, y:Elim, depth:int) -> bool:
  match x, y:
    case EApp(a), EApp(b):
      return conv(a, b, depth)
    case EInd(ref_x, args_x), EInd(ref_y, args_y):
      return (ref_x._get_def_id() == ref_y._get_def_id() and
        conv_args(args_x, args_y, depth))
    case EAdd(a), EAdd(b):
      return a == b
  return False

def conv_elims(xs:tuple[Elim, ...], ys:tuple[Elim, ...], depth:int) -> bool:
  return (len(xs) == len(ys) and
    all(
      conv_elim(x, y, depth)
      for x, y in zip(xs, ys)
    ))
  


def debug_str(term:Term, ctx:Env) -> str:
  return term.str(LazyEnvMap(ctx, ann_name))


def infer_sort(term:Term, ctx:Env) -> int:
  ty = infer(term, ctx)
  if not isinstance(ty, VSort):
    raise TypecheckError(f"Expected a type, got {debug_str(term, ctx)}.")
  return ty.level


def get_let_body_term(let_term:TLet, ctx:Env) -> tuple[Term, Env]:
  """ Typecheck the assignment part of a let statement.
      Returns the body term and an updated ctx containing the rhs. """
  match let_term:
    case TLet(name, A, rhs, body):
      env = LazyEnvMap(ctx, ann_val)
      if A is None:
        domain = infer(rhs, ctx)
      else:
        infer_sort(A, ctx)
        domain = term_eval(A, env)
        check(rhs, domain, ctx)
      rhs_bind = Thunk(rhs, env)
      body_ctx = EnvEntry(ctx, (rhs_bind, domain, name))
      return body, body_ctx
    case _:
      raise TypecheckError(f"Invalid Let term {let_term!r}.")


def infer(term:Term, ctx:Env) -> Value:
  """ Infer a semantic type.
      Context entries are (value, type, name) annotations. """
  depth = len(ctx)
  match term:
    case TSort(level) if level >= 0:
      return VSort(level + 1)
    case TConst(module, path):
      try:
        return def_ty(module[path])
      except LookupError as error:
        raise TypecheckError(f"Cannot resolve {'.'.join(path)}: {error}") from error
    case TVar(idx):
      if not 0 <= idx < depth:
        raise TypecheckError(f"Variable index {idx} outside context of size {depth}.")
      return ann_ty(ctx[idx])
    case TNatLit(_):
      return VNat()
    case TNat():
      return VSort(0)
    case TSucc():
      return VPi(VNat(), Closure(TNat(), EmptyEnv()))
    case TPi(param, A, B):
      level_A = infer_sort(A, ctx)
      domain = term_eval(A, LazyEnvMap(ctx, ann_val))
      level_B = infer_sort(B, EnvEntry(ctx, (VNeutral(depth, ()), domain, param)))
      return VSort(max(level_A, level_B))
    case TLam(_, None, _):
      raise TypecheckError(f"Cannot infer an unannotated lambda: {debug_str(term, ctx)}.")
    case TLam(param, A, body):
      env = LazyEnvMap(ctx, ann_val)
      infer_sort(A, ctx)
      domain = term_eval(A, env)
      body_ty = infer(body, EnvEntry(ctx, (VNeutral(depth, ()), domain, param)))
      return VPi(domain, Closure(quote(body_ty, depth + 1), env)) # call quote because Closure needs a Term
    case TApp(fn, arg):
      fn_ty = infer(fn, ctx)
      match fn_ty:
        case VPi(A, B): # usual case: fn is a function
          check(arg, A.force(), ctx)
          return B.apply(Thunk(arg, LazyEnvMap(ctx, ann_val)))
        case VNat(): # typing logic to make Nat's callable
          env = LazyEnvMap(ctx, ann_val)
          infer_sort(arg, ctx)
          P = term_eval(arg, env)
          # make (P => P) => P => P
          P_wrap_1 = Closure(quote(P, depth + 1), env)
          P_wrap_2 = Closure(quote(VPi(P, P_wrap_1), depth + 1), env) # TODO: repeat twice? yuck.
          return VPi(VPi(P, P_wrap_1), P_wrap_2)
        case _:
          raise TypecheckError(f"Expected a function, got {debug_str(fn, ctx)}.")
    case TLet(_, _, _, _):
      body, body_ctx = get_let_body_term(term, ctx)
      return infer(body, body_ctx)
    case _:
      raise TypecheckError(f"Invalid term {term!r}.")


def check(term:Term, expected:Value, ctx:Env):
  """ Check against a well-formed semantic type.
      Lambdas use the expected codomain directly; other terms use inference. """
  depth = len(ctx)
  match term, expected:
    case TLam(param, A, body), VPi(C, D): # bi-directional checking
      if A is None:
        domain = C.force() # infer domain from the expected type
      else:
        infer_sort(A, ctx)
        domain = term_eval(A, LazyEnvMap(ctx, ann_val))
        # Preserve Pi assignability: the expected domain is assignable to A.
        if not conv(C, domain, depth, accept_assignable=True):
          raise TypecheckError(f"Parameter type {debug_str(A, ctx)} does not accept the expected domain.")
      x = VNeutral(depth, ())
      check(body, D.apply(x), EnvEntry(ctx, (x, domain, param)))
    case TLet(_, _, _, _), _:
      # expected type must be able to pass through let expressions for bi-directionality
      body, body_ctx = get_let_body_term(term, ctx)
      check(body, expected, body_ctx)
    case _: # infer-and-compare checking
      actual = infer(term, ctx)
      if not conv(actual, expected, depth, accept_assignable=True):
        raise TypecheckError(f"Expected {debug_str(quote(expected, depth), ctx)}, "
          f"inferred {debug_str(quote(actual, depth), ctx)}.")



