from ir import *
from inductive import InductiveDef, ConstructorDef, InductiveDefHead, IrInductiveSelfRef
from axiom_defs import DEFNS


vec_head = InductiveDefHead("Vec", IrSort(0), [("A", IrSort(0))], [("len", IrConst("Nat"))], defns=DEFNS)
DEFNS.add(InductiveDef(vec_head, [
    ConstructorDef(vec_head, "empty", [], [IrConst("Nat.Z")]),
    ConstructorDef(vec_head, "append", [("l", IrConst("Nat")), ("a", IrVar("A")), ("rest", IrInductiveSelfRef([IrVar("l")]))], [IrApp(IrConst("Nat.S"), IrVar("l"))])
  ]))

# TODO: define an "add" function that can be used in bintree instead of 
DEFNS.add(ConstDefinition("add",
  IrLam("a", IrConst("Nat"),
        IrLam("b", IrConst("Nat"),
          IrApp(IrApp(IrApp(IrApp(IrConst("Nat.ind.0"),
            IrLam("_", IrConst("Nat"), IrConst("Nat"))),
            IrVar("b")),
            IrLam("n", IrConst("Nat"),
              IrLam("r", IrConst("Nat"), IrApp(IrConst("Nat.S"), IrVar("r"))))),
            IrVar("a"))
    )).to_term([]),
  DEFNS))

bintree_head = InductiveDefHead("Bintree", IrSort(0), [], [("size", IrConst("Nat"))], defns=DEFNS)
DEFNS.add(InductiveDef(bintree_head, [
    ConstructorDef(bintree_head, "leaf", [], [IrApp(IrConst("Nat.S"), IrConst("Nat.Z"))]),
    ConstructorDef(bintree_head, "branch", [
        ("sz_l", IrConst("Nat")),
        ("sz_r", IrConst("Nat")),
        ("left",  IrInductiveSelfRef([IrVar("sz_l")])),
        ("right", IrInductiveSelfRef([IrVar("sz_r")])),
      ],
      [
        IrApp(IrApp(IrConst("add"), IrVar("sz_l")), IrVar("sz_r")),
      ])
  ]))


# (Π n: Nat => (Π @rec_n: Nat => Nat))
# (Π r: Nat => Nat)

