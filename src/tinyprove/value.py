from dataclasses import dataclass, field


class LookupError(Exception):
  pass
class EvalError(Exception):
  pass
class TypecheckError(Exception):
  pass


# Base classes:

class Binding:
  """ Value or Thunk """
  pass

class Value(Binding):
  """ Base class for the result of an expression """
  def force(self):
    return self

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
class TVar(Term):
  idx: int
  def str(self, ctx:Env):
    name = ctx[self.idx]
    skipped = sum(ctx[i] == name for i in range(self.idx))
    return name + "'" * skipped

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


# Env concrete classes:

@dataclass(frozen=True)
class EmptyEnv(Env):
  def at(self, idx:int) -> object:
    raise LookupError(f"Tried to look up {idx} from EmptyEnv.")
  def __len__(self) -> int:
    return 0

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


# Thunks and Closures

@dataclass
class Thunk(Binding):
  """ A term and its environment, with cache for lazy and repeated evaluation. """
  term: Term
  env: Env
  cached:(Value|None) = None
  def force(self):
    if self.cached is None:
      self.cached = term_eval(self.term, self.env)
    return self.cached

@dataclass(frozen=True)
class Closure:
  """ A term and its environment, accepts an argument """
  term: Term
  env: Env
  def apply(self, arg:Binding) -> Value:
    return term_eval(self.term, EnvEntry(self.env, arg))


# Value concrete classes:

@dataclass(frozen=True)
class VSort(Value):
  level: int

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
  args: tuple[Binding, ...]


# ...

def vapp(fn:Value, arg:Binding) -> Value:
  match fn:
    case VLam(body):
      return body.apply(arg)
    case VNeutral(head_level, args):
      return VNeutral(head_level, args + (arg,))
    case _:
      raise EvalError(f"Unknown value {fn}")

def term_eval(term: Term, env: Env) -> Value:
  match term:
    case TSort(level) if level >= 0:
      return VSort(level)
    case TVar(idx):
      return env.at(idx).force()
    case TApp(head, arg):
      head_val = term_eval(head, env)
      arg_bind = Thunk(arg, env)
      return vapp(head_val, arg_bind)
    case TLam(_, _, body):
      return VLam(Closure(body, env))
    case TPi(_, A, B):
      return VPi(Thunk(A, env), Closure(B, env))
    case _:
      raise EvalError(f"Unknown term {term}")

def quote(val:Binding, depth:int=0) -> Term:
  """ Reify a value. Quoted lambdas need an expected type when checked. """
  val = val.force() # convert to Value
  match val:
    case VSort(level):
      return TSort(level)
    case VLam(body):
      arg = VNeutral(depth, ())
      return TLam(f"x{depth}", None, quote(body.apply(arg), depth + 1)) # codomain is unknown
    case VPi(A, B):
      arg = VNeutral(depth, ())
      return TPi(f"x{depth}", quote(A, depth), quote(B.apply(arg), depth + 1))
    case VNeutral(head_level, args):
      assert 0 <= head_level < depth
      idx = depth - head_level - 1
      ans = TVar(idx)
      for arg in args:
        ans = TApp(ans, quote(arg, depth))
      return ans
    case _:
      raise EvalError(f"Unknown value {val}")


def conv(a:Binding, b:Binding, depth:int=0, accept_assignable:bool=False) -> bool:
  """ Check structural equality for two values. The check is exact and symmetric by
      default. If accept_assignable is True, we instead check if `a` is assignable to `b`. """
  a, b = a.force(), b.force()
  match a, b:
    case VSort(i), VSort(j):
      return i == j or (accept_assignable and i <= j)
    case VNeutral(i, xs), VNeutral(j, ys):
      return i == j and len(xs) == len(ys) and all(
        conv(x, y, depth) for x, y in zip(xs, ys))
    case VPi(A, B), VPi(C, D):
      x = VNeutral(depth, ())
      return ( # NOTE: we preserve the accept_assignable flag for Pi types
        conv(C, A, depth, accept_assignable) and  # swap argument order to ensure contravariance
        conv(B.apply(x), D.apply(x), depth + 1, accept_assignable) # same order for covariance
      )
    case VLam(body), VLam(other):
      x = VNeutral(depth, ())
      return conv(body.apply(x), other.apply(x), depth + 1)
    case _:
      return False


# a context annotation is a (value, type, name) tuple
def ann_val(ann):
  value, ty, name = ann
  return value
def ann_ty(ann):
  value, ty, name = ann
  return ty
def ann_name(ann):
  value, ty, name = ann
  return name


def debug_str(term:Term, ctx:Env) -> str:
  return term.str(LazyEnvMap(ctx, ann_name))


def infer_sort(term:Term, ctx:Env) -> int:
  ty = infer(term, ctx)
  if not isinstance(ty, VSort):
    raise TypecheckError(f"Expected a type, got {debug_str(term, ctx)}.")
  return ty.level


def infer(term:Term, ctx:Env=EmptyEnv()) -> Value:
  """ Infer a semantic type.
      Context entries are (value, type, name) annotations. """
  depth = len(ctx)
  match term:
    case TSort(level) if level >= 0:
      return VSort(level + 1)
    case TVar(idx):
      if not 0 <= idx < depth:
        raise TypecheckError(f"Variable index {idx} outside context of size {depth}.")
      return ann_ty(ctx[idx])
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
      if not isinstance(fn_ty, VPi):
        raise TypecheckError(f"Expected a function, got {debug_str(fn, ctx)}.")
      check(arg, fn_ty.A.force(), ctx)
      return fn_ty.B.apply(Thunk(arg, LazyEnvMap(ctx, ann_val)))
    case _:
      raise TypecheckError(f"Invalid term {term!r}.")


def check(term:Term, expected:Value, ctx:Env=EmptyEnv()):
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
    case _: # infer-and-compare checking
      actual = infer(term, ctx)
      if not conv(actual, expected, depth, accept_assignable=True):
        raise TypecheckError(f"Expected {debug_str(quote(expected, depth), ctx)}, "
          f"inferred {debug_str(quote(actual, depth), ctx)}.")


# TODO: add let statements.
# syntax: { a = expr, b = expr, ..., result_expr }
# maybe allow annotations?
# also, for top level defs, we should not require the δ. now that things are comma separated.
# that way it's consistent with let statement syntax



