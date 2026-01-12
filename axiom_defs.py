from ir import *
from parser import parse
from tinyprove import Definitions, AxiomDefinition
from inductive import InductiveDef, IrConstructorDefinition, IrInductiveSelfRef


DEFNS = Definitions()


# Constructive:

DEFNS.add(InductiveDef("False", IrSort(0), [], [], [], DEFNS))

DEFNS.add(InductiveDef("Unit", IrSort(0), [], [],
  [
    IrConstructorDefinition("in", [], []),
  ], DEFNS))

DEFNS.add(InductiveDef("And", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [],
  [
    IrConstructorDefinition("in", [("a", IrVar("A")), ("b", IrVar("B"))], []),
  ], DEFNS))

DEFNS.add(InductiveDef("Or", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [],
  [
    IrConstructorDefinition("inl", [("a", IrVar("A"))], []),
    IrConstructorDefinition("inr", [("b", IrVar("B"))], []),
  ], DEFNS))

DEFNS.add(InductiveDef("Eq", IrSort(0), [("A", IrSort(0)), ("x", IrVar("A"))], [("y", IrVar("A"))],
  [
    IrConstructorDefinition("refl", [], [IrVar("x")]),
  ], DEFNS))

DEFNS.add(InductiveDef("Exists", IrSort(0), [("A", IrSort(0)), ("P", IrPi("a", IrVar("A"), IrSort(0)))], [],
  [
    IrConstructorDefinition("in", [("a", IrVar("A")), ("pa", IrApp(IrVar("P"), IrVar("a")))], []),
  ], DEFNS))

DEFNS.add(InductiveDef("Nat", IrSort(0), [], [],
  [
    IrConstructorDefinition("Z", [], []),
    IrConstructorDefinition("S", [("n", IrInductiveSelfRef([]))], []),
  ], DEFNS))


# Non-constructive:

DEFNS.add(AxiomDefinition(
  "",
  {
    "em": parse("Π A: Type0 => (Or A (Π a: A => False))")
  },
  DEFNS))







