from parser import parse
from tinyprove import check, ConstDefinition
from axiom_defs import DEFNS


def test(name, thm_str, proof_str):
  print(f"\n\ntesting ??? {name} ???")
  thm = parse(thm_str)
  print(f"\n  theorem:\n    {thm.str([])}")
  proof = parse(proof_str)
  print(f"\n  proof:\n    {proof.str([])}")
  check(proof, thm, [], DEFNS)
  print(f"\n✓ {name} type-checks\n")


test("Identity Lemma",
  "Π A: Type0 => Π x: A => A",
  "λ A: Type0 -> λ x: A -> x")


test("Modus Ponens",
  "Π A: Type0 => Π B: Type0 => Π a: A => Π a_to_b: (Π ai:A => B) => B",
  "λ A: Type0 -> λ B: Type0 -> λ a: A -> λ a_to_b: (Π ai:A => B) -> (a_to_b a)")

test("Or Left",
  "Π A: Type0 => Π B: Type0 => Π a: A => (Or A B)",
  "λ A: Type0 -> λ B: Type0 -> λ a: A -> (Or.inl A B a)")

test("Or Right",
  "Π A: Type0 => Π B: Type0 => Π b: B => (Or A B)",
  "λ A: Type0 -> λ B: Type0 -> λ b: B -> (Or.inr A B b)")

test("And Implies Or",
  "Π A: Type0 => Π B: Type0 =>Π a_and_b: (And A B) => (Or A B)",
  "λ A: Type0 -> λ B: Type0 -> λ a_and_b: (And A B) ->" # introduce the assumption
  "And.ind.0 A B" # eliminate And
  "(λ x: (And A B) -> (Or A B))" # motive: (Or A B)
  "(λ a: A -> λ b: B -> (Or.inl A B a))" # And.in branch
  "a_and_b" # pass assumption
)

# guide to Eq.ind.0:
#   Π A: Type0 => Π x: A =>
#       Π @motive: (Π y: A => Π @instance: (Eq A x y) => Type0) =>
#       Π @case_refl: (@motive x (Eq.refl A x)) =>
#       Π y: A =>
#       Π @instance: (Eq A x y) => (@motive y @instance)

test("Function of equals are equal",
  # Theorem:
  "Π A: Type0 => Π B: Type0 => Π f: (Π a:A => B) => "
  "Π a1: A => Π a2: A => "
  "Π a1_eq_a2: (Eq A a1 a2) => "
  "(Eq B (f a1) (f a2))",
  # Proof
  "λ A: Type0 -> λ B: Type0 -> λ f: (Π a:A => B) -> "
  "λ a1: A -> λ a2:A -> "
  "λ a1_eq_a2: (Eq A a1 a2) -> "
  "(Eq.ind.0 A a1 " # use equality induction
    "(λ a1_idx: A -> λ instance: (Eq A a1 a1_idx) -> (Eq B (f a1) (f a1_idx))) " # motive
    "(Eq.refl B (f a1)) " # case refl
    "a2 "
    "a1_eq_a2 " # apply hypothesis
  ")"
  )

test("Equality is symmetric",
  # Theorem:
  "Π A: Type0 => Π x: A => Π y: A => Π x_eq_y: (Eq A x y) => (Eq A y x)",
  # Proof:
  "λ A: Type0 -> λ x: A -> λ y: A -> " # introduce background vars
  "λ x_eq_y: (Eq A x y) -> " # introduce the assumption
  "(Eq.ind.0 A x " # use equality induction
    "(λ x_idx: A -> λ instance: (Eq A x x_idx) -> (Eq A x_idx x)) " # motive
    "(Eq.refl A x) " # case refl
    "y "
    "x_eq_y)" # pass hypothesis
  )

test("Equality is transitive",
  # Theorem:
  "Π A: Type0 => Π x: A => Π y: A => Π z: A => Π x_eq_y: (Eq A x y) => Π y_eq_z: (Eq A y z) => (Eq A x z)",
  # Proof:
  "λ A: Type0 -> λ x: A -> λ y: A -> λ z: A -> " # introduce background vars
  "λ x_eq_y: (Eq A x y) -> λ y_eq_z: (Eq A y z) -> " # introduce assumptions
  "((Eq.ind.0 A x " # use equality induction on x_eq_y
    "(λ y_idx: A -> λ instance: (Eq A x y_idx) -> (Π z_idx: A => Π y_eq_z_idx: (Eq A y_idx z_idx) => (Eq A x z_idx))) " # motive
    "(λ z_idx: A -> λ x_eq_z_idx: (Eq A x z_idx) -> x_eq_z_idx) " # case refl
    "y "
    "x_eq_y) "
  "z y_eq_z)" # apply to z and y_eq_z
  )

test("Double-Negation Elimination",
  "Π A: Type0 => Π nnA: (Π na: (Π a:A => False) => False) => A",
  "λ A: Type0 -> " # A is a type
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


# define addition
DEFNS.add(ConstDefinition("add",
  parse("λ a: Nat -> λ b: Nat -> (Nat.ind.0 (λ _: Nat -> Nat) b (λ n: Nat -> λ r: Nat -> (Nat.S r)) a)"),
  DEFNS))

DEFNS.add(ConstDefinition("id_Nat",
  parse("λ n: Nat -> n"),
  DEFNS))

test("id_Nat equals its input (delta-reduction required)",
  "Π n: Nat => (Eq Nat (id_Nat n) n)",
  "λ n: Nat -> (Eq.refl Nat n)")

