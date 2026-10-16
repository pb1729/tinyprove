from typing import List, Tuple

from .parser import parse
from .core import Module, TConst, Binding, Value, VContainer, EvalError, EmptyEnv, term_eval
from .ir import Binder, IrSort, IrConst, IrVar, IrPi, IrApp
from .inductive import InductiveModule


USUAL_AXIOMS_SRC = """

# false
ι ⊥ () [] : Type0 {},

# true
ι ⊤ () [] : Type0 {
  unit() => ⊤[]
},

# negation
¬ = λ A: Type0 -> (Π a: A => ⊥),

# and
ι & (A: Type0, B: Type0) [] : Type0 {
  &in (a: A, b: B) => &[]
},

# or
ι | (A: Type0, B: Type0) [] : Type0 {
  |inl (a: A) => |[],
  |inr (b: B) => |[]
},

# equality
ι ≡ (A: Type0, x: A) [y: A] : Type0 {
  refl () => ≡[x]
},

# existential quantification
ι Exists (A: Type0, P: (Π a: A => Type0)) [] : Type0 {
  exists (a: A, pa: (P a)) => Exists[]
},

# natural numbers
ι Nat () [] : Type0 {
  Z () => Nat[],
  S (n: Nat[]) => Nat[]
},

"""


def flat_import(module:Module, mod_from:Module):
  """ add all constants from mod_from to module
      MUTATES module
      WARNING: If this operation fails, module could be in inconsistent state! """
  assert not isinstance(module, InductiveModule), "Can't import into InductiveModule."
  assert not isinstance(mod_from, InductiveModule), "Can't flat-import InductiveModule."
  for name in mod_from.entries:
    module.add(name, mod_from.entries[name])
  for name in mod_from.submodules:
    module.add(name, mod_from.submodules[name])

def def_module(src:str, imports:List[Tuple[str, Module]]|None=None) -> Module:
  ans = Module()
  # parse source
  definitions = parse(src)
  # perform imports
  imports = [] if imports is None else imports
  for name, module in imports:
    if name == "":
      flat_import(ans, module)
    else:
      ans.add(name, module)
  # new definitions from source code
  for definition in definitions:
    definition.apply(ans)
  return ans

def force_axiom(name:str, ty:Value, module:Module):
  """ MUTATES module
      WARNING: Overrides type checking and can break soundness! """
  ref = TConst(module, (name,))
  def instant_fail(rec, args:tuple[Binding]): # VContainer fn that immediately throws an error
    raise EvalError(f"Cannot concretely instantiate axiom {name}.")
  val = VContainer(ref, 0, instant_fail)
  module.add(name, (val, ty))

def get_lem(module: Module) -> Value:
  """ Assumes the host Module has the usual definitions of `|`, `¬`. """
  A = Binder("A")
  neg, logical_or = IrConst(("¬",)), IrConst(("|",))
  lem_ir = IrPi(A, IrSort(0), IrApp(IrApp(logical_or, IrVar(A)), IrApp(neg, IrVar(A))))
  lem_term = lem_ir.to_term(module, EmptyEnv())
  return term_eval(lem_term, EmptyEnv())
  

def get_usual_axioms(classical:bool=False) -> Module:
  ans = def_module(USUAL_AXIOMS_SRC)
  if classical:
    force_axiom("LEM", get_lem(ans), ans)
  return ans





