from tinyprove import *


DEFNS = get_usual_axioms()


def test(name, thm_str, proof_str):
  thm = parse(thm_str)
  print(f"\ntheorem {name}:\n    {thm.str([])}")
  proof = parse(proof_str)
  check(proof, thm, [], DEFNS)
  print(f"    ✓ {name} type-checks\n")


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
"""λ A: Type0 -> λ B: Type0 -> λ a_and_b: (And A B) -> # introduce the assumption
    And.ind.0 A B # eliminate And
    (λ x: (And A B) -> (Or A B)) # motive: (Or A B)
    (λ a: A -> λ b: B -> (Or.inl A B a)) # And.in branch
    a_and_b # pass assumption
""")

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
extend_definitions(DEFNS, [
  """
    δ add: Π a: Nat => Π b: Nat => Nat =
      λ a: Nat -> λ b: Nat -> (Nat.ind.0 (λ _: Nat -> Nat) b (λ n: Nat -> λ r: Nat -> (Nat.S r)) a)
  """, """
    δ id_Nat = λ n: Nat -> n
  """
])

test("id_Nat equals its input (delta-reduction required)",
  "Π n: Nat => (Eq Nat (id_Nat n) n)",
  "λ n: Nat -> (Eq.refl Nat n)")

# try some evalutions that use iota reduction

extend_definitions(DEFNS, [
  """
    δ x2 = (λ x: Nat -> (Nat.ind.0 (λ n: Nat -> Nat) Nat.Z (λ n: Nat -> λ rec:Nat -> (Nat.S (Nat.S rec))) x))
  """, """
    δ zero_x2 = (x2 Nat.Z)
  """, """
    δ one_x2 = (x2 (Nat.S Nat.Z))
  """, """
    δ bi_inc =
      λ x: Nat -> λ y: Nat -> λ eq_x_y: (Eq Nat x y) -> (Eq.ind.0 Nat x (λ x_idx: Nat -> λ instance: (Eq Nat x x_idx) -> (Eq Nat (Nat.S x) (Nat.S x_idx))) (Eq.refl Nat (Nat.S x)) y eq_x_y)
  """, """
    δ eq_1_1 =
      (bi_inc Nat.Z Nat.Z (Eq.refl Nat Nat.Z))
  """, """
    δ eq_2_2 =
      (bi_inc (Nat.S Nat.Z) (Nat.S Nat.Z) eq_1_1)
  """
])

print(DEFNS.defs["zero_x2"].value.str([]))
print(DEFNS.defs["one_x2"].value.str([]))
print(DEFNS.defs["bi_inc"].type.str([]))
print(DEFNS.defs["eq_1_1"].type.str([]))
print(DEFNS.defs["eq_2_2"].type.str([]))


print("\n\nSTART IOTA INDICES TESTING\n")

extend_definitions(DEFNS, [
  """
    ι Vec (A: Type0) [l: Nat] : Type0
      | empty () => Vec[Nat.Z]
      | append (l: Nat, a: A, rest: Vec[l]) => Vec[(Nat.S l)]  
  """, """
    # bullshit inductive type that is both recursive and has multiple indices for testing purposes:
    ι Blorb () [n: Nat, m: Nat] : Type0
      | base () => Blorb[Nat.Z, Nat.Z]
      | inl (n: Nat, m: Nat, child: Blorb[n, m]) => Blorb[(Nat.S n), m]
      | inr (n: Nat, m: Nat, child: Blorb[n, m]) => Blorb[n, (Nat.S m)]
  """, """
    ι Mat (A: Type0) [n: Nat, m: Nat] : Type0
      | empty (n: Nat) => Mat[n, Nat.Z]
      | append (n: Nat, m: Nat, row: (Vec A n), rest: Mat[n, m]) => Mat[n, (Nat.S m)]
  """, """
    δ inc_vec =
      λ len: Nat -> λ v: (Vec Nat len) ->
      (Vec.ind.0 Nat
        (λ _l: Nat -> λ inst: (Vec Nat _l) -> (Vec Nat _l))
        (Vec.empty Nat)
        (λ l: Nat -> λ head: Nat -> λ rest: (Vec Nat l) -> λ rec_rest: (Vec Nat l) ->
          (Vec.append Nat l (Nat.S head) rec_rest))
        len
        v)
  """, """
    δ use_inc_vec_eg_1 = (inc_vec (Nat.S Nat.Z) (Vec.append Nat Nat.Z (Nat.S Nat.Z) (Vec.empty Nat)))
  """, """
    δ mirror_blorb = 
      λ n: Nat -> λ m: Nat -> λ blorb: (Blorb n m) ->
      (Blorb.ind.0
        (λ _n: Nat -> λ _m: Nat -> λ scrut: (Blorb _n _m) -> (Blorb _m _n)) # motive: blorb with flipped inds
        (Blorb.base) # base case
        (λ nn: Nat -> λ mm: Nat -> λ child: (Blorb nn mm) -> λ rec_child: (Blorb mm nn) -> (Blorb.inr mm nn rec_child)) # inl case makes inr
        (λ nn: Nat -> λ mm: Nat -> λ child: (Blorb nn mm) -> λ rec_child: (Blorb mm nn) -> (Blorb.inl mm nn rec_child)) # inr case makes inl
        n m # indices
        blorb
      )
  """, """
    δ use_mirror_blorb_eg_1 = 
      (mirror_blorb
        (Nat.S Nat.Z) (Nat.S Nat.Z)
        (Blorb.inl Nat.Z (Nat.S Nat.Z) (Blorb.inr Nat.Z Nat.Z Blorb.base))
      )
  """, """
    δ inc_mat = 
      λ n: Nat -> λ m: Nat -> λ mat: (Mat Nat n m) ->
      (Mat.ind.0 Nat
        (λ _n: Nat -> λ _m: Nat -> λ inst: (Mat Nat _n _m) -> (Mat Nat _n _m))

        # case_empty: Π nn:Nat, motive nn 0 (empty nn)
        (λ nn: Nat -> (Mat.empty Nat nn))

        # case_append:
        (λ nn: Nat -> λ mm: Nat ->
         λ row:  (Vec Nat nn) ->
         λ rest: (Mat Nat nn mm) ->
         λ rec_rest: (Mat Nat nn mm) ->
           (Mat.append Nat nn mm (inc_vec nn row) rec_rest))

        n
        m
        mat)
  """, """
    δ use_inc_mat_eg_1 = 
      (inc_mat
        (Nat.S (Nat.S Nat.Z))         # n = 2
        (Nat.S (Nat.S Nat.Z))         # m = 2
        (Mat.append Nat
          (Nat.S (Nat.S Nat.Z))       # nn = 2
          (Nat.S Nat.Z)               # mm = 1
          (Vec.append Nat
            (Nat.S Nat.Z)             # len = 1
            (Nat.S (Nat.S (Nat.S Nat.Z)))   # 3
            (Vec.append Nat
              Nat.Z
              (Nat.S (Nat.S (Nat.S (Nat.S Nat.Z))))  # 4
              (Vec.empty Nat)))
          (Mat.append Nat
            (Nat.S (Nat.S Nat.Z))     # nn = 2
            Nat.Z                     # mm = 0
            (Vec.append Nat
              (Nat.S Nat.Z)
              (Nat.S Nat.Z)           # 1
              (Vec.append Nat
                Nat.Z
                (Nat.S (Nat.S Nat.Z)) # 2
                (Vec.empty Nat)))
            (Mat.empty Nat (Nat.S (Nat.S Nat.Z))))))
  """
])

print(DEFNS.defs["use_inc_vec_eg_1"].value.str([]))
print(DEFNS.defs["use_mirror_blorb_eg_1"].value.str([]))
print(DEFNS.defs["use_inc_mat_eg_1"].value.str([]))




# ------------------------------------------------------------
# 1) (add 1 1) = 2
# ------------------------------------------------------------

test("add 1 1 = 2",
  # Theorem:
  "(Eq Nat (add (Nat.S Nat.Z) (Nat.S Nat.Z)) (Nat.S (Nat.S Nat.Z)))",
  # Proof:
  "(Eq.refl Nat (add (Nat.S Nat.Z) (Nat.S Nat.Z)))"
)


# ------------------------------------------------------------
# 2) 1 != 0   (i.e. Eq Nat 1 0 -> False)
# ------------------------------------------------------------

extend_definitions(DEFNS, [
  """
    δ isSucc =
      λ n: Nat ->
      (Nat.ind.1
        (λ _: Nat -> Type0)
        False
        (λ _: Nat -> λ rec: Type0 -> Unit)
        n
      )
  """
])

test("1 != 0",
# Theorem:
"Π p: (Eq Nat (Nat.S Nat.Z) Nat.Z) => False",
# Proof:
"""
λ p: (Eq Nat (Nat.S Nat.Z) Nat.Z) ->
  # use equality induction on p
  (Eq.ind.0 Nat (Nat.S Nat.Z)
    (λ y: Nat -> λ instance: (Eq Nat (Nat.S Nat.Z) y) -> (isSucc y))   # motive
    Unit.in                                                            # case refl : isSucc 1, reduces to Unit
    Nat.Z"                                                             # y := 0
    p
  )
"""
)


# ------------------------------------------------------------
# 3) addition is associative
#     Π a b c, add (add a b) c = add a (add b c)
# ------------------------------------------------------------

test("add associative",
  # Theorem:
  "Π a: Nat => Π b: Nat => Π c: Nat => "
  "(Eq Nat (add (add a b) c) (add a (add b c)))",
  # Proof:
  "("
    # local helper: apS (congruence for Nat.S)
    "(λ apS: (Π x: Nat => Π y: Nat => Π p: (Eq Nat x y) => (Eq Nat (Nat.S x) (Nat.S y))) -> "
      # main proof by induction on a
      "(λ a: Nat -> "
        "(Nat.ind.0 "
          "(λ a_idx: Nat -> Π b: Nat => Π c: Nat => "
            "(Eq Nat (add (add a_idx b) c) (add a_idx (add b c)))"
          ") "
          # base a = 0
          "(λ b: Nat -> λ c: Nat -> "
            "(Eq.refl Nat (add b c))"
          ") "
          # step a = S n
          "(λ n: Nat -> "
            "λ ih: (Π b: Nat => Π c: Nat => "
              "(Eq Nat (add (add n b) c) (add n (add b c)))"
            ") -> "
            "λ b: Nat -> λ c: Nat -> "
              "(apS (add (add n b) c) (add n (add b c)) (ih b c))"
          ") "
          "a"
        ")"
      ")"
    ") "
    # apS definition using Eq.ind.0
    "(λ x: Nat -> λ y: Nat -> λ p: (Eq Nat x y) -> "
      "(Eq.ind.0 Nat x "
        "(λ y_idx: Nat -> λ instance: (Eq Nat x y_idx) -> "
          "(Eq Nat (Nat.S x) (Nat.S y_idx))"
        ") "
        "(Eq.refl Nat (Nat.S x)) "
        "y "
        "p"
      ")"
    ")"
  ")"
)


# ------------------------------------------------------------
# 4) cool extra: right identity  add n 0 = n
# ------------------------------------------------------------

test("add n 0 = n",
  # Theorem:
  "Π n: Nat => (Eq Nat (add n Nat.Z) n)",
  # Proof:
  "("
    # local helper: apS (congruence for Nat.S)
    "(λ apS: (Π x: Nat => Π y: Nat => Π p: (Eq Nat x y) => (Eq Nat (Nat.S x) (Nat.S y))) -> "
      "(λ n: Nat -> "
        "(Nat.ind.0 "
          "(λ n_idx: Nat -> (Eq Nat (add n_idx Nat.Z) n_idx)) "
          # base n = 0
          "(Eq.refl Nat (add Nat.Z Nat.Z)) "
          # step n = S k
          "(λ k: Nat -> λ ih: (Eq Nat (add k Nat.Z) k) -> "
            "(apS (add k Nat.Z) k ih)"
          ") "
          "n"
        ")"
      ")"
    ") "
    # apS definition using Eq.ind.0
    "(λ x: Nat -> λ y: Nat -> λ p: (Eq Nat x y) -> "
      "(Eq.ind.0 Nat x "
        "(λ y_idx: Nat -> λ instance: (Eq Nat x y_idx) -> "
          "(Eq Nat (Nat.S x) (Nat.S y_idx))"
        ") "
        "(Eq.refl Nat (Nat.S x)) "
        "y "
        "p"
      ")"
    ")"
  ")"
)


# ----------------------------
#   Multiplication, etc
# ----------------------------

# define multiplication
extend_definitions(DEFNS, [
  """
    δ mul: Π a: Nat => Π b: Nat => Nat =
      λ a: Nat -> λ b: Nat -> (Nat.ind.0 (λ _: Nat -> Nat) Nat.Z (λ n: Nat -> λ r: Nat -> (add b r)) a)
  """
])

test("mul 2 2 = 4",
  # Theorem:
  "(Eq Nat (mul (Nat.S (Nat.S Nat.Z)) (Nat.S (Nat.S Nat.Z))) (Nat.S (Nat.S (Nat.S (Nat.S Nat.Z)))))",
  # Proof:
  "(Eq.refl Nat (mul (Nat.S (Nat.S Nat.Z)) (Nat.S (Nat.S Nat.Z))))"
)


# ----------------------------
#   Equality helpers
# ----------------------------

extend_definitions(DEFNS, [
  """
    δ apS =
      λ x: Nat -> λ y: Nat -> λ p: (Eq Nat x y) -> (Eq.ind.0 Nat x (λ y_idx: Nat -> λ instance: (Eq Nat x y_idx) -> (Eq Nat (Nat.S x) (Nat.S y_idx))) (Eq.refl Nat (Nat.S x)) y p)
  """, """
    δ symm =
      λ A: Type0 -> λ x: A -> λ y: A -> λ p: (Eq A x y) -> (Eq.ind.0 A x (λ y_idx: A -> λ instance: (Eq A x y_idx) -> (Eq A y_idx x)) (Eq.refl A x) y p)
  """, """
    δ trans =
      λ A: Type0 -> λ x: A -> λ y: A -> λ z: A -> λ p: (Eq A x y) -> λ q: (Eq A y z) -> ((Eq.ind.0 A x (λ y_idx: A -> λ instance: (Eq A x y_idx) -> Π z2: A => Π q2: (Eq A y_idx z2) => (Eq A x z2)) (λ z2: A -> λ q2: (Eq A x z2) -> q2) y p) z q)
  """, """
    δ ap =
      λ A: Type0 -> λ B: Type0 -> λ f: (Π a: A => B) -> λ a1: A -> λ a2: A -> λ p: (Eq A a1 a2) -> (Eq.ind.0 A a1 (λ a2_idx: A -> λ instance: (Eq A a1 a2_idx) -> (Eq B (f a1) (f a2_idx))) (Eq.refl B (f a1)) a2 p)
  """
])


# ----------------------------
#   Addition lemmas
# ----------------------------
extend_definitions(DEFNS, [
  """
    δ add_zero_right =
      λ n: Nat -> (Nat.ind.0 (λ n_idx: Nat -> (Eq Nat (add n_idx Nat.Z) n_idx)) (Eq.refl Nat (add Nat.Z Nat.Z)) (λ k: Nat -> λ ih: (Eq Nat (add k Nat.Z) k) -> (apS (add k Nat.Z) k ih)) n)
  """, """
    δ add_succ_right =
      λ b: Nat -> λ a: Nat -> (Nat.ind.0 (λ b_idx: Nat -> (Eq Nat (add b_idx (Nat.S a)) (Nat.S (add b_idx a)))) (Eq.refl Nat (add Nat.Z (Nat.S a))) (λ k: Nat -> λ ih: (Eq Nat (add k (Nat.S a)) (Nat.S (add k a))) -> (apS (add k (Nat.S a)) (Nat.S (add k a)) ih)) b)
  """, """
    δ add_assoc =
      λ a: Nat -> (Nat.ind.0 (λ a_idx: Nat -> Π b: Nat => Π c: Nat => (Eq Nat (add (add a_idx b) c) (add a_idx (add b c)))) (λ b: Nat -> λ c: Nat -> (Eq.refl Nat (add b c))) (λ n: Nat -> λ ih: (Π b: Nat => Π c: Nat => (Eq Nat (add (add n b) c) (add n (add b c)))) -> λ b: Nat -> λ c: Nat -> (apS (add (add n b) c) (add n (add b c)) (ih b c))) a)
  """, """
    δ add_comm =
      λ a: Nat -> (Nat.ind.0 (λ a_idx: Nat -> Π b: Nat => (Eq Nat (add a_idx b) (add b a_idx))) (λ b: Nat -> (symm Nat (add b Nat.Z) b (add_zero_right b))) (λ n: Nat -> λ ih: (Π b: Nat => (Eq Nat (add n b) (add b n))) -> λ b: Nat -> (trans Nat (Nat.S (add n b)) (Nat.S (add b n)) (add b (Nat.S n)) (apS (add n b) (add b n) (ih b)) (symm Nat (add b (Nat.S n)) (Nat.S (add b n)) (add_succ_right b n)))) a)
  """, """
    δ add_shuffle =
      λ x: Nat -> λ y: Nat -> λ u: Nat -> λ v: Nat -> (trans Nat (add (add x y) (add u v)) (add x (add y (add u v))) (add (add x u) (add y v)) (add_assoc x y (add u v)) (trans Nat (add x (add y (add u v))) (add x (add (add y u) v)) (add (add x u) (add y v)) (ap Nat Nat (λ t: Nat -> add x t) (add y (add u v)) (add (add y u) v) (symm Nat (add (add y u) v) (add y (add u v)) (add_assoc y u v))) (trans Nat (add x (add (add y u) v)) (add (add x (add y u)) v) (add (add x u) (add y v)) (symm Nat (add (add x (add y u)) v) (add x (add (add y u) v)) (add_assoc x (add y u) v)) (trans Nat (add (add x (add y u)) v) (add (add (add x u) y) v) (add (add x u) (add y v)) (ap Nat Nat (λ t: Nat -> add t v) (add x (add y u)) (add (add x u) y) (trans Nat (add x (add y u)) (add x (add u y)) (add (add x u) y) (ap Nat Nat (λ t: Nat -> add x t) (add y u) (add u y) (add_comm y u)) (symm Nat (add (add x u) y) (add x (add u y)) (add_assoc x u y)))) (add_assoc (add x u) y v)))))
  """
])




# ----------------------------
#   Distributive law
# ----------------------------

test("distributive law",
  # Theorem
  "Π a: Nat => Π x: Nat => Π y: Nat => "
  "(Eq Nat (mul a (add x y)) (add (mul a x) (mul a y)))",
  # Proof:
  "λ a: Nat -> λ x: Nat -> λ y: Nat -> "
  "("
    "Nat.ind.0 "
      "(λ a_idx: Nat -> Π x1: Nat => Π y1: Nat => "
        "(Eq Nat (mul a_idx (add x1 y1)) (add (mul a_idx x1) (mul a_idx y1)))"
      ") "
      # base a=0
      "(λ x0: Nat -> λ y0: Nat -> "
        "(Eq.refl Nat (mul Nat.Z (add x0 y0)))"
      ") "
      # step a = S n
      "(λ n: Nat -> "
        "λ ih: (Π x1: Nat => Π y1: Nat => "
          "(Eq Nat (mul n (add x1 y1)) (add (mul n x1) (mul n y1)))"
        ") -> "
        "λ x1: Nat -> λ y1: Nat -> "
          "(trans Nat "
            "(add (add x1 y1) (mul n (add x1 y1))) "
            "(add (add x1 y1) (add (mul n x1) (mul n y1))) "
            "(add (add x1 (mul n x1)) (add y1 (mul n y1))) "
            "(ap Nat Nat "
              "(λ t: Nat -> add (add x1 y1) t) "
              "(mul n (add x1 y1)) "
              "(add (mul n x1) (mul n y1)) "
              "(ih x1 y1)"
            ") "
            "(add_shuffle x1 y1 (mul n x1) (mul n y1))"
          ")"
      ") "
      "a"
    ") x y"
)


extend_definitions(DEFNS, [
  """
    δ pred =
      λ n: Nat -> (Nat.ind.0 (λ _: Nat -> Nat) Nat.Z (λ k: Nat -> λ r: Nat -> k) n)
  """, """
    δ injS =
      λ x: Nat -> λ y: Nat -> λ p: (Eq Nat (Nat.S x) (Nat.S y)) ->
        (ap Nat Nat pred (Nat.S x) (Nat.S y) p)
  """
])


# ----------------------------
#   Cancellation: add a b = add a c -> b = c
# ----------------------------

test("add left cancellation",
  # Theorem:
  "Π a: Nat => Π b: Nat => Π c: Nat => "
  "Π p: (Eq Nat (add a b) (add a c)) => "
  "(Eq Nat b c)",
  # Proof:
  """
λ a: Nat -> λ b: Nat -> λ c: Nat ->
λ p: (Eq Nat (add a b) (add a c)) ->
(
  (Nat.ind.0
    (λ a_idx: Nat ->
      Π b1: Nat => Π c1: Nat =>
      Π p1: (Eq Nat (add a_idx b1) (add a_idx c1)) =>
      (Eq Nat b1 c1)
    )
    # base: a = 0, add 0 b = b, add 0 c = c
    (λ b0: Nat -> λ c0: Nat ->
      λ p0: (Eq Nat (add Nat.Z b0) (add Nat.Z c0)) ->
      p0
    )
    # step: a = S n
    (λ n: Nat ->
      λ ih:
        (Π b1: Nat => Π c1: Nat =>
         Π p1: (Eq Nat (add n b1) (add n c1)) =>
         (Eq Nat b1 c1)
        ) ->
      λ b1: Nat -> λ c1: Nat ->
      λ p1: (Eq Nat (add (Nat.S n) b1) (add (Nat.S n) c1)) ->
        (ih b1 c1 (injS (add n b1) (add n c1) p1))
    )
    a
  ) b c p
)
"""
)




# ----------------------------------
#   Show all current definitions
# ----------------------------------

PADWIDTH:int = 24

def rightpad(s:str) -> str:
  diff = PADWIDTH - len(s)
  assert diff >= 0
  return s + " "*diff

def show_definition(defs_obj):
  print(f"\n    defs for {name}:")
  print(f"    used: {', '.join(defs_obj.used)}")
  if isinstance(defs_obj, AxiomDefinition):
    for subname in defs_obj.axioms:
      print(rightpad(f"{name}.{subname}"), defs_obj.get_type([subname]))
  elif isinstance(defs_obj, ConstDefinition):
    print(rightpad(name), defs_obj.get_type([]))
  else:
    print(rightpad(f"{name}"), defs_obj.get_type([]))
    for constructor in defs_obj.constructors:
      print(rightpad(f"{name}.{constructor.name}"), defs_obj.get_type([constructor.name]))
    print(rightpad(f"{name}.ind.0"), defs_obj.get_type(["ind", "0"]))

for name in DEFNS.defs:
  defs_obj = DEFNS.defs[name]
  show_definition(defs_obj)
  


# TODO: add negative tests!!!!!




