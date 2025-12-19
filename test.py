from parser import parse
from tinyprove import check
from axiom_defs import DEFNS


def test(name, ctx, thm_str, proof_str):
  print(f"\n\ntesting ??? {name} ???")
  print("  context:")
  for i, (nm, ty) in enumerate(ctx[::-1]):
    print(f"    {nm}   \t{ty.str(ctx[-(i + 1):])}")
  thm = parse(thm_str, ctx)
  print(f"\n  theorem:\n    {thm.str(ctx)}")
  proof = parse(proof_str, ctx)
  print(f"\n  proof:\n    {proof.str(ctx)}")
  check(proof, thm, ctx, DEFNS)
  print(f"\n✓ {name} type-checks\n")


test("Identity Lemma",
  [("A", parse("Type0"))],
  "Π x: A => A",
  "λ x: A -> x")


test("Modus Ponens",
  [("A", parse("Type0")), ("B", parse("Type0"))],
  "Π a: A => Π a_to_b: (Π ai:A => B) => B",
  "λ a: A -> λ a_to_b: (Π ai:A => B) -> (a_to_b a)")

test("Or Left",
  [("A", parse("Type0")), ("B", parse("Type0"))],
  "Π a: A => (Or A B)",
  "λ a: A -> (Or.inl A B a)")

test("Or Right",
  [("A", parse("Type0")), ("B", parse("Type0"))],
  "Π b: B => (Or A B)",
  "λ b: B -> (Or.inr A B b)")

test("And Implies Or",
  [("A", parse("Type0")), ("B", parse("Type0"))],
  "Π a_and_b: (And A B) => (Or A B)",
  "λ a_and_b: (And A B) ->" # introduce the assumption
  "And.ind.0 A B" # eliminate And
  "(λ x: (And A B) -> (Or A B))" # motive: (Or A B)
  "(λ a: A -> λ b: B -> (Or.inl A B a))" # And.in branch
  "a_and_b" # pass assumption
)

test("Double-Negation Elimination",
  [("A", parse("Type0"))],
  "Π nnA: (Π na: (Π a:A => False) => False) => A",
  "λ nnA: (Π na: (Π a: A => False) => False) -> " # introduce assumption of ~~A
    "(Or.ind.0 A (Π a: A => False)" # Or.ind for or elimination on excluded middle
    "(λ x: (Or A (Π a: A => False)) -> A)" # motive: A
    "(λ a:A -> a)" # easy case: we already have A
    "(λ notA: (Π a: A => False) -> (" # hard case: we need to use principle of explosion
      "False.ind.0" # principle of explosion using False.ind
      "(λ x: False -> A)" # motive: A
      " (nnA notA)" # pass False (made by ~A -> False, ~A)
    "))"
    "(.em A))" # pass .em axiom (excluded middle)
)


