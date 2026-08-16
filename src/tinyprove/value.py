from dataclasses import dataclass


class LookupError(Exception):
  pass
class EvalError(Exception):
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
  pass


# Term concrete classes:

@dataclass(frozen=True)
class TVar(Term):
  idx: int
  def str(self, ctx:list[str]):
    return ctx[len(ctx) - 1 - self.idx]

@dataclass(frozen=True)
class TApp(Term):
  head: Term
  arg: Term
  def str(self, ctx:list[str]):
    return f"({self.head.str(ctx)} {self.arg.str(ctx)})"

@dataclass(frozen=True)
class TLam(Term):
  body: Term
  def str(self, ctx:list[str]):
    param_nm = f"x{len(ctx)}"
    ctx_new = ctx + [param_nm]
    body_str = self.body.str(ctx_new)
    return f"(λ {param_nm} -> {body_str})"


# Env concrete classes:

@dataclass(frozen=True)
class EmptyEnv(Env):
  def at(self, idx:int):
    raise LookupError(f"Tried to look up {idx} from EmptyEnv.")

@dataclass(frozen=True)
class EnvEntry(Env):
  prev: Env
  val: Binding
  def at(self, idx:int):
    if idx == 0:
      return self.val
    else:
      return self.prev.at(idx - 1)


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
class VLam(Value):
  body: Closure

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
    case TVar(idx):
      return env.at(idx).force()
    case TApp(head, arg):
      head_val = term_eval(head, env)
      arg_bind = Thunk(arg, env)
      return vapp(head_val, arg_bind)
    case TLam(body):
      return VLam(Closure(body, env))
    case _:
      raise EvalError(f"Unknown term {term}")

def quote(val:Binding, depth:int=0) -> Term:
  val = val.force() # convert to Value
  match val:
    case VLam(body):
      arg = VNeutral(depth, ())
      return TLam(quote(body.apply(arg), depth + 1))
    case VNeutral(head_level, args):
      idx = depth - head_level - 1
      ans = TVar(idx)
      for arg in args:
        ans = TApp(ans, quote(arg, depth))
      return ans














# TESTS


I = TLam(TVar(0))
K = TLam(TLam(TVar(1)))
S = TLam(TLam(TLam(TApp(TApp(TVar(2), TVar(0)), TApp(TVar(1), TVar(0))))))

term = TApp(
  TApp(
    TLam(
      TLam(TVar(1))      # λx.λy.x
    ),
    I
  ),
  K
)

print(quote(term_eval(term, EmptyEnv())).str([]))


term = TApp(
  TLam(
    TApp(
      TLam(
        TApp(TVar(0), I)
      ),
      TLam(TVar(1))
    )
  ),
  K
)

print(quote(term_eval(term, EmptyEnv())).str([]))

A = TLam(TLam(TVar(1)))

term = TApp(
  TApp(
    TApp(S, K),
    I
  ),
  A
)

print(quote(term_eval(term, EmptyEnv())).str([]))


omega_half = TLam(
  TApp(TVar(0), TVar(0))
)

Omega = TApp(omega_half, omega_half)

term = TApp(
  TApp(K, I),
  Omega
)

print(quote(term_eval(term, EmptyEnv())).str([]))

term = TLam(
  TLam(
    TApp(TVar(1), TVar(0))
  )
)
print(quote(term_eval(term, EmptyEnv())).str([]))


# Y combinator stuff

inner = TLam(
    TApp(
        TVar(1),                   # f
        TApp(TVar(0), TVar(0))     # x x
    )
)

Y = TLam(
    TApp(inner, inner)
)

F = TLam(I)  # λr. λx. x

term = TApp(Y, F)

print(quote(term_eval(term, EmptyEnv())).str([]))

