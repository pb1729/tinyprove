from tinyprove import *
from parser import parse

DEFNS = Definitions()

DEFNS.add_defn(InductiveDef(
  "False",
  [],
  {}
))

DEFNS.add_defn(InductiveDef(
  "And",
  [("A", Sort(0)), ("B", Sort(0))],
  {
    "in": [("a", Var(1)), ("b", Var(1))],
  }
))

DEFNS.add_defn(InductiveDef(
  "Or",
  [("A", Sort(0)), ("B", Sort(0))],
  {
    "inl": [("a", Var(1))],
    "inr": [("b", Var(0))],
  }
))

DEFNS.add_defn(InductiveDef(
  "Exists",
  [("A", Sort(0)), ("P", Pi("a", Var(0), Sort(0)))],
  {
    "in": [("a", Var(1)), ("pa", App(Var(1), Var(0)))],
  }
))

DEFNS.add_defn(InductiveDef(
  "Nat",
  [],
  {
    "Z": [],
    "S": [("n", Const("Nat"))],
  }
))

DEFNS.add_defn(AxiomDef(
  "", "em",
  parse("Π A: Type0 => (Or A (Π a: A => False))")
))



