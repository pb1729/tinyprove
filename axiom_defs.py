from ir import *
from parser import parse
from tinyprove import Definitions, AxiomDefinition
from inductive import InductiveDef, ConstructorDef, InductiveDefHead, IrInductiveSelfRef


DEFNS = Definitions()


# Constructive:

false_head = InductiveDefHead("False", IrSort(0), [], [])
DEFNS.add(InductiveDef(false_head, []))

unit_head = InductiveDefHead("Unit", IrSort(0), [], [])
DEFNS.add(InductiveDef(unit_head, [
    ConstructorDef(unit_head, "in", [], [])
  ]))

and_head = InductiveDefHead("And", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [])
DEFNS.add(InductiveDef(and_head, [
    ConstructorDef(and_head, "in", [("a", IrVar("A")), ("b", IrVar("B"))], [])
  ]))

or_head = InductiveDefHead("Or", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [])
DEFNS.add(InductiveDef(or_head, [
    ConstructorDef(or_head, "inl", [("a", IrVar("A"))], []),
    ConstructorDef(or_head, "inr", [("b", IrVar("B"))], []),
  ]))

eq_head = InductiveDefHead("Eq", IrSort(0), [("A", IrSort(0)), ("x", IrVar("A"))], [("y", IrVar("A"))])
DEFNS.add(InductiveDef(eq_head, [
    ConstructorDef(eq_head, "refl", [], [IrVar("x")])
  ]))

exists_head = InductiveDefHead("Exists", IrSort(0), [("A", IrSort(0)), ("P", IrPi("a", IrVar("A"), IrSort(0)))], [])
DEFNS.add(InductiveDef(exists_head, [
    ConstructorDef(exists_head, "in", [("a", IrVar("A")), ("pa", IrApp(IrVar("P"), IrVar("a")))], [])
  ]))

nat_head = InductiveDefHead("Nat", IrSort(0), [], [])
DEFNS.add(InductiveDef(nat_head, [
    ConstructorDef(nat_head, "Z", [], []),
    ConstructorDef(nat_head, "S", [("n", IrInductiveSelfRef([]))], [])
  ]))


# Non-constructive:

DEFNS.add(AxiomDefinition(
  "",
  {
    "em": parse("Π A: Type0 => (Or A (Π a: A => False))")
  },
  DEFNS))







