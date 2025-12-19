from ir import *
from parser import parse
from tinyprove import Definitions, AxiomsDef
from inductive import InductiveDef, ConstructorDef, InductiveDefHead, IrInductiveSelfRef


DEFNS = Definitions()


# Constructive:

false_head = InductiveDefHead("False", IrSort(0), [], [])
DEFNS["False"] = InductiveDef(false_head, [])

and_head = InductiveDefHead("And", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [])
DEFNS["And"] = InductiveDef(and_head, [
    ConstructorDef(and_head, "in", [("a", IrVar("A")), ("b", IrVar("B"))], [])
  ])

or_head = InductiveDefHead("Or", IrSort(0), [("A", IrSort(0)), ("B", IrSort(0))], [])
DEFNS["Or"] = InductiveDef(or_head, [
    ConstructorDef(or_head, "inl", [("a", IrVar("A"))], []),
    ConstructorDef(or_head, "inr", [("b", IrVar("B"))], []),
  ])

eq_head = InductiveDefHead("Eq", IrSort(0), [("A", IrSort(0)), ("x", IrVar("A"))], [("y", IrVar("A"))])
DEFNS["Eq"] = InductiveDef(eq_head, [
    ConstructorDef(eq_head, "refl", [], [IrVar("x")])
  ])

exists_head = InductiveDefHead("Exists", IrSort(0), [("A", IrSort(0)), ("P", IrPi("a", IrVar("A"), IrSort(0)))], [])
DEFNS["Exists"] = InductiveDef(exists_head, [
    ConstructorDef(exists_head, "in", [("a", IrVar("A")), ("pa", IrApp(IrVar("P"), IrVar("a")))], [])
  ])

nat_head = InductiveDefHead("Nat", IrSort(0), [], [])
DEFNS["Nat"] = InductiveDef(nat_head, [
    ConstructorDef(nat_head, "Z", [], []),
    ConstructorDef(nat_head, "S", [("n", IrInductiveSelfRef(nat_head, []))], [])
  ])


# Non-constructive:

DEFNS[""] = AxiomsDef({
    "em": parse("Π A: Type0 => (Or A (Π a: A => False))")
  })







