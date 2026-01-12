from .ir import *
from .parser import parse
from .core import Definitions, AxiomDefinition
from .inductive import InductiveDef, IrConstructorDefinition, IrInductiveSelfRef



def get_usual_axioms():
  ans = Definitions()

  # Constructive:

  ans.add(InductiveDef("False", IrSort(0), [], [], [], ans))

  ans.add(InductiveDef("Unit", IrSort(0), [], [],
    [
      IrConstructorDefinition("in", [], []),
    ], ans))

  ans.add(InductiveDef("And", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [],
    [
      IrConstructorDefinition("in", [("a", IrVar("A")), ("b", IrVar("B"))], []),
    ], ans))

  ans.add(InductiveDef("Or", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [],
    [
      IrConstructorDefinition("inl", [("a", IrVar("A"))], []),
      IrConstructorDefinition("inr", [("b", IrVar("B"))], []),
    ], ans))

  ans.add(InductiveDef("Eq", IrSort(0), [("A", IrSort(0)), ("x", IrVar("A"))], [("y", IrVar("A"))],
    [
      IrConstructorDefinition("refl", [], [IrVar("x")]),
    ], ans))

  ans.add(InductiveDef("Exists", IrSort(0), [("A", IrSort(0)), ("P", IrPi("a", IrVar("A"), IrSort(0)))], [],
    [
      IrConstructorDefinition("in", [("a", IrVar("A")), ("pa", IrApp(IrVar("P"), IrVar("a")))], []),
    ], ans))

  ans.add(InductiveDef("Nat", IrSort(0), [], [],
    [
      IrConstructorDefinition("Z", [], []),
      IrConstructorDefinition("S", [("n", IrInductiveSelfRef([]))], []),
    ], ans))


  # Non-constructive:

  ans.add(AxiomDefinition(
    "",
    {
      "em": parse("Π A: Type0 => (Or A (Π a: A => False))")
    },
    ans))

  return ans





