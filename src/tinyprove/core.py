from dataclasses import dataclass
from typing import List, Dict, Tuple, Set
from enum import Enum



class TypecheckError(Exception):
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
  depth: int
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
    return f"(Π {self.param}: {self.A.str(ctx)} => {self.B.str([(self.param, None)] + ctx)})"
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
    return f"(λ {self.param}: {self.A.str(ctx)} -> {self.body.str([(self.param, None)] + ctx)})"
  def shift(self, shift, keep=0):
    return Lam(self.param, self.A.shift(shift, keep), self.body.shift(shift, keep + 1)) # keep param
  def subst(self, j, term):
    return Lam(self.param, self.A.subst(j, term), self.body.subst(j + 1, term.shift(1)))

'''
@dataclass(frozen=True)
class Let(Term):
  param:str
  val: Term
  body: Term
  def str(self, ctx):
    return f"let {self.param} = {self.val.str(ctx)}; {self.body.str([(self.param, None)] + ctx)}"
  def shift(self, shift, keep=0):
    return Let(self.param, self.val.shift(shift, keep), self.body.shift(shift, keep + 1))
  def subst(self, j, term):
    return Let(self.param, self.val.subst(j, term), self.body.subst(j + 1, term.shift(1)))
'''

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


# ---- Proof Environment: ----

class Definitions:
  """ An environment class that holds various kinds of definitions that are referenced by Const terms. """
  def __init__(self):
    self.defs = {}
  def add(self, definition):
    def_name = definition.name
    if "." in def_name:
      raise RuntimeError(f"{def_name} is not a legal definition name, as these cannot contain the `.` separator.")
    if def_name in self.defs:
      raise RuntimeError(f"Can't add another definition with the same name ({def_name}) as an existing one.")
    self.defs[def_name] = definition
  def remove(self, def_name:str):
    if def_name not in self.defs:
      raise RuntimeError(f"No definition named {def_name} was found.")
    is_being_used = any(
      def_name in definition.used
      for definition in self.defs.values()
    )
    if is_being_used:
      raise RuntimeError(f"Definition {def_name} is currently in use by other definitions in this environment.")
    del self.defs[def_name]
  def __getitem__(self, key:str) -> Term:
    assert isinstance(key, str)
    name, *rest = key.split(".")
    return self.defs[name].get_type(rest)
  def __contains__(self, key:str) -> bool:
    try:
      self[key]
    except KeyError:
      return False
    else:
      return True
  def match_reduce(self, key:str, argchain: List[Term], defns) -> Tuple[Term, List[Term]] | None:
    name, *rest = key.split(".")
    return self.defs[name].match_reduce(rest, argchain, defns)


# ---- WHNF Reduction and Type-checking / Inference: ----

def to_app_list(term:Term) -> Tuple[Term, List[Term]]:
  match term:
    case App(fn, arg):
      head, args = to_app_list(fn)
      args.append(arg)
      return head, args
    case other:
      return other, []

def argchain_whnf(head:Term, args:List[Term], defns:Definitions) -> Tuple[Term, List[Term]]:
  """ Workhorse function of whnf reduction. Terms are represented as a non-App head and a list of args.
      beta reduction is built-in, and defns can supply other reductions through .match_reduce() """
  # make head not an App by adding arguments to args
  head, new_args = to_app_list(head)
  args = new_args + args
  # reduce if we can, otherwise return
  match head:
    case Lam(param, A, body):
      if len(args) >= 1: # lambdas can be reduced if there is an arg to apply them to
        head = body.subst(0, args[0])
        args = args[1:] # first argument was used up
      else:
        return head, args
    case Const(name):
      subst = defns.match_reduce(name, args, defns)
      if subst is None: # no reduction supplied
        return head, args
      else:
        head, args = subst # we use the reduction supplied by defns
    case _: # nothing else can be reduced
      return head, args
  # we've done a reduction so head could be an App now
  return argchain_whnf(head, args, defns) # recursive call

def whnf(term:Term, defns:Definitions) -> Term:
  """ Reduce term to weak head normal form. """
  head, args = argchain_whnf(term, [], defns)
  ans = head
  while len(args) > 0:
    ans = App(ans, args[0])
    args = args[1:]
  return ans


def conv(t1:Term, t2:Term, defns:Definitions) -> bool:
  t1 = whnf(t1, defns)
  t2 = whnf(t2, defns)
  match t1, t2:
    case Sort(l1), Sort(l2):
      return l1 == l2
    case Var(depth1), Var(depth2):
      return depth1 == depth2
    case Const(name1), Const(name2):
      return name1 == name2
    case App(fn1, arg1), App(fn2, arg2):
      return conv(fn1, fn2, defns) and conv(arg1, arg2, defns)
    case Pi(_, A1, B1), Pi(_, A2, B2):
      return conv(A1, A2, defns) and conv(B1, B2, defns)
    case Lam(_, A1, body1), Lam(_, A2, body2):
      return conv(A1, A2, defns) and conv(body1, body2, defns)
    case _:
      return False # mismatched shapes

def infer(term:Term, ctx, defns:Definitions) -> Term:
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
      A_ty = whnf(infer(A, ctx, defns), defns)
      if not isinstance(A_ty, Sort):
        raise TypecheckError(f"Expected A in Pi type {term.str(ctx)} to be a Sort, but found {A_ty.str(ctx)}.")
      ctx_B = [(param, A)] + ctx
      B_ty = whnf(infer(B, ctx_B, defns), defns)
      if not isinstance(B_ty, Sort):
        raise TypecheckError(f"Expected B in Pi type {term.str(ctx)} to be a Sort, but found {B_ty.str(ctx_B)}.")
      return Sort(max(A_ty.level, B_ty.level))
    case Lam(param, A, body):
      A_ty = whnf(infer(A, ctx, defns), defns)
      if not isinstance(A_ty, Sort):
        raise TypecheckError(f"Expected A in Lam {term.str(ctx)} to be a Sort, but found {A_ty.str(ctx)}")
      ctx_body = [(param, A)] + ctx
      body_ty = infer(body, ctx_body, defns)
      return Pi(param, A, body_ty)
    case App(fn, arg):
      fn_ty = whnf(infer(fn, ctx, defns), defns)
      match fn_ty:
        case Pi(param, A, B):
          check(arg, A, ctx, defns)
          ctx_B = [(param, A)] + ctx
          return whnf(B.subst(0, arg), defns)
        case _:
          raise TypecheckError(f"Expected type of fn in application {term.str(ctx)} to be a Pi type, but found {fn_ty.str(ctx)}.")
    case _:
      raise TypecheckError(f"Failed to recognize term {term}")

def check(term, expected, ctx, defns:Definitions):
  term_ty = infer(term, ctx, defns)
  if not conv(term_ty, expected, defns):
    raise TypecheckError(f"Expected term {term.str(ctx)} to have type {expected.str(ctx)} but found {term_ty.str(ctx)}.")



# ---- Definition Classes: ----

def find_used_defs(*terms:Tuple[Term]) -> Set[str]:
  terms = list(terms)
  ans = set()
  i = 0 # do a BFS of the Term tree
  while i < len(terms):
    term_i = terms[i]
    match term_i:
      case Pi(param, A, B):
        terms.append(A)
        terms.append(B)
      case Lam(param, A, body):
        terms.append(A)
        terms.append(body)
      case App(fn, arg):
        terms.append(fn)
        terms.append(arg)
      case Const(name): # if it's a Const, it uses other definitions!
        ans.add(name.split(".")[0])
    i += 1
  return ans

class AxiomDefinition:
  def __init__(self, name:str, axioms:Dict[str, Term], defns:Definitions):
    self.name = name
    self.axioms = axioms
    axiom_terms = []
    for axiom_name in self.axioms:
      axiom = self.axioms[axiom_name]
      axiom_ty = whnf(infer(axiom, [], defns), defns)
      if not isinstance(axiom_ty, Sort):
        raise TypecheckError(f"Expected type of axiom {self.name}.{axiom_name} to be a Sort.")
      axiom_terms.append(axiom)
    self.used = find_used_defs(*axiom_terms)
  def get_type(self, key:List[str]) -> Term:
    match key:
      case [axiom_name]:
        if axiom_name in self.axioms:
          return self.axioms[axiom_name]
    raise IndexError(f"Couldn't find key {self.name}.{'.'.join(key)}.")
  def match_reduce(self, key:List[str], argchain: List[Term], defns:Definitions) -> Tuple[Term, List[Term]] | None:
    return None

class ConstDefinition:
  def __init__(self, name:str, value:Term, defns:Definitions):
    self.name = name
    self.value = whnf(value, defns)
    self.type = whnf(infer(self.value, [], defns), defns)
    self.used = find_used_defs(self.value)
  def get_type(self, key:List[str]) -> Term:
    match key:
      case []:
        return self.type
    raise IndexError(f"Couldn't find key {self.name}.{'.'.join(key)}.")
  def match_reduce(self, key:List[str], argchain: List[Term], defns:Definitions) -> Tuple[Term, List[Term]] | None:
    match key:
      case []:
        return self.value, argchain
    raise IndexError(f"Couldn't find key {self.name}.{'.'.join(key)}.")


