"""Proof checking and computation tests using primitive natural numbers."""

import unittest

from tinyprove import NAT_MODULE, def_module, get_usual_axioms, parse
from tinyprove.core import EmptyEnv, check, conv, infer, quote, term_eval


# The arithmetic proofs use primitive addition; multiplication is defined
# through built-in Nat induction. Indexed inductives also use ℕ indices.
DEFINITIONS = """
add : (Π a: ℕ => (Π b: ℕ => ℕ))
  = NAT.+,

id_Nat
  = (λ n: ℕ -> n),

x2
  = (λ x: ℕ -> (x (λ n: ℕ -> ℕ) (λ n: ℕ -> (λ rec: ℕ -> (NAT.+ 1 (NAT.+ 1 rec)))) 0)),

zero_x2
  = (x2 0),

one_x2
  = (x2 1),

bi_inc
  = (λ x: ℕ ->
      (λ y: ℕ ->
        (λ eq_x_y: (≡ ℕ x y) ->
          (≡.ind0
            ℕ
            x
            (λ x_idx: ℕ -> (λ instance: (≡ ℕ x x_idx) -> (≡ ℕ (NAT.+ 1 x) (NAT.+ 1 x_idx))))
            (refl ℕ (NAT.+ 1 x))
            y
            eq_x_y)))),

eq_1_1
  = (bi_inc 0 0 (refl ℕ 0)),

eq_2_2
  = (bi_inc 1 1 eq_1_1),

ι Vec (A: Type0) [l: ℕ] : Type0 {
  vec_empty () => Vec[0],
  vec_append (l: ℕ, a: A, rest: Vec[l]) => Vec[(NAT.+ 1 l)]
},

ι Blorb () [n: ℕ, m: ℕ] : Type0 {
  blorb_base () => Blorb[0, 0],
  blorb_inl (n: ℕ, m: ℕ, child: Blorb[n, m]) => Blorb[(NAT.+ 1 n), m],
  blorb_inr (n: ℕ, m: ℕ, child: Blorb[n, m]) => Blorb[n, (NAT.+ 1 m)]
},

ι Mat (A: Type0) [n: ℕ, m: ℕ] : Type0 {
  mat_empty (n: ℕ) => Mat[n, 0],
  mat_append (n: ℕ, m: ℕ, row: (Vec A n), rest: Mat[n, m]) => Mat[n, (NAT.+ 1 m)]
},

inc_vec
  = (λ len: ℕ ->
      (λ v: (Vec ℕ len) ->
        (Vec.ind0
          ℕ
          (λ _l: ℕ -> (λ inst: (Vec ℕ _l) -> (Vec ℕ _l)))
          (vec_empty ℕ)
          (λ l: ℕ ->
            (λ head: ℕ ->
              (λ rest: (Vec ℕ l) ->
                (λ rec_rest: (Vec ℕ l) -> (vec_append ℕ l (NAT.+ 1 head) rec_rest)))))
          len
          v))),

use_inc_vec_eg_1
  = (inc_vec 1 (vec_append ℕ 0 1 (vec_empty ℕ))),

mirror_blorb
  = (λ n: ℕ ->
      (λ m: ℕ ->
        (λ blorb: (Blorb n m) ->
          (Blorb.ind0
            (λ _n: ℕ -> (λ _m: ℕ -> (λ scrut: (Blorb _n _m) -> (Blorb _m _n))))
            blorb_base
            (λ nn: ℕ ->
              (λ mm: ℕ ->
                (λ child: (Blorb nn mm) ->
                  (λ rec_child: (Blorb mm nn) -> (blorb_inr mm nn rec_child)))))
            (λ nn: ℕ ->
              (λ mm: ℕ ->
                (λ child: (Blorb nn mm) ->
                  (λ rec_child: (Blorb mm nn) -> (blorb_inl mm nn rec_child)))))
            n
            m
            blorb)))),

use_mirror_blorb_eg_1
  = (mirror_blorb 1 1 (blorb_inl 0 1 (blorb_inr 0 0 blorb_base))),

inc_mat
  = (λ n: ℕ ->
      (λ m: ℕ ->
        (λ mat: (Mat ℕ n m) ->
          (Mat.ind0
            ℕ
            (λ _n: ℕ -> (λ _m: ℕ -> (λ inst: (Mat ℕ _n _m) -> (Mat ℕ _n _m))))
            (λ nn: ℕ -> (mat_empty ℕ nn))
            (λ nn: ℕ ->
              (λ mm: ℕ ->
                (λ row: (Vec ℕ nn) ->
                  (λ rest: (Mat ℕ nn mm) ->
                    (λ rec_rest: (Mat ℕ nn mm) -> (mat_append ℕ nn mm (inc_vec nn row) rec_rest))))))
            n
            m
            mat)))),

use_inc_mat_eg_1
  = (inc_mat
      2
      2
      (mat_append
        ℕ
        2
        1
        (vec_append
          ℕ
          1
          3
          (vec_append ℕ 0 4 (vec_empty ℕ)))
        (mat_append
          ℕ
          2
          0
          (vec_append
            ℕ
            1
            1
            (vec_append ℕ 0 2 (vec_empty ℕ)))
          (mat_empty ℕ 2)))),

isSucc
  = (λ n: ℕ -> (n (λ _: ℕ -> Type0) (λ _: ℕ -> (λ rec: Type0 -> ⊤)) ⊥)),

mul : (Π a: ℕ => (Π b: ℕ => ℕ))
  = (λ a: ℕ -> (λ b: ℕ -> (a (λ _: ℕ -> ℕ) (λ n: ℕ -> (λ r: ℕ -> (add b r))) 0))),

apS
  = (λ x: ℕ ->
      (λ y: ℕ ->
        (λ p: (≡ ℕ x y) ->
          (≡.ind0
            ℕ
            x
            (λ y_idx: ℕ -> (λ instance: (≡ ℕ x y_idx) -> (≡ ℕ (NAT.+ 1 x) (NAT.+ 1 y_idx))))
            (refl ℕ (NAT.+ 1 x))
            y
            p)))),

symm
  = (λ A: Type0 ->
      (λ x: A ->
        (λ y: A ->
          (λ p: (≡ A x y) ->
            (≡.ind0 A x (λ y_idx: A -> (λ instance: (≡ A x y_idx) -> (≡ A y_idx x))) (refl A x) y p))))),

trans
  = (λ A: Type0 ->
      (λ x: A ->
        (λ y: A ->
          (λ z: A ->
            (λ p: (≡ A x y) ->
              (λ q: (≡ A y z) ->
                (≡.ind0
                  A
                  x
                  (λ y_idx: A ->
                    (λ instance: (≡ A x y_idx) -> (Π z2: A => (Π q2: (≡ A y_idx z2) => (≡ A x z2)))))
                  (λ z2: A -> (λ q2: (≡ A x z2) -> q2))
                  y
                  p
                  z
                  q))))))),

ap
  = (λ A: Type0 ->
      (λ B: Type0 ->
        (λ f: (Π a: A => B) ->
          (λ a1: A ->
            (λ a2: A ->
              (λ p: (≡ A a1 a2) ->
                (≡.ind0
                  A
                  a1
                  (λ a2_idx: A -> (λ instance: (≡ A a1 a2_idx) -> (≡ B (f a1) (f a2_idx))))
                  (refl B (f a1))
                  a2
                  p))))))),

add_zero_right
  = (λ n: ℕ ->
      (n
        (λ n_idx: ℕ -> (≡ ℕ (add n_idx 0) n_idx))
        (λ k: ℕ -> (λ ih: (≡ ℕ (add k 0) k) -> (apS (add k 0) k ih)))
        (refl ℕ (add 0 0)))),

add_succ_right
  = (λ b: ℕ ->
      (λ a: ℕ ->
        (b
          (λ b_idx: ℕ -> (≡ ℕ (add b_idx (NAT.+ 1 a)) (NAT.+ 1 (add b_idx a))))
          (λ k: ℕ ->
            (λ ih: (≡ ℕ (add k (NAT.+ 1 a)) (NAT.+ 1 (add k a))) ->
              (apS (add k (NAT.+ 1 a)) (NAT.+ 1 (add k a)) ih)))
          (refl ℕ (add 0 (NAT.+ 1 a)))))),

add_assoc
  = (λ a: ℕ ->
      (a
        (λ a_idx: ℕ -> (Π b: ℕ => (Π c: ℕ => (≡ ℕ (add (add a_idx b) c) (add a_idx (add b c))))))
        (λ n: ℕ ->
          (λ ih: (Π b: ℕ => (Π c: ℕ => (≡ ℕ (add (add n b) c) (add n (add b c))))) ->
            (λ b: ℕ -> (λ c: ℕ -> (apS (add (add n b) c) (add n (add b c)) (ih b c))))))
        (λ b: ℕ -> (λ c: ℕ -> (refl ℕ (add b c)))))),

add_comm
  = (λ a: ℕ ->
      (a
        (λ a_idx: ℕ -> (Π b: ℕ => (≡ ℕ (add a_idx b) (add b a_idx))))
        (λ n: ℕ ->
          (λ ih: (Π b: ℕ => (≡ ℕ (add n b) (add b n))) ->
            (λ b: ℕ ->
              (trans
                ℕ
                (NAT.+ 1 (add n b))
                (NAT.+ 1 (add b n))
                (add b (NAT.+ 1 n))
                (apS (add n b) (add b n) (ih b))
                (symm ℕ (add b (NAT.+ 1 n)) (NAT.+ 1 (add b n)) (add_succ_right b n))))))
        (λ b: ℕ -> (symm ℕ (add b 0) b (add_zero_right b))))),

add_shuffle
  = (λ x: ℕ ->
      (λ y: ℕ ->
        (λ u: ℕ ->
          (λ v: ℕ ->
            (trans
              ℕ
              (add (add x y) (add u v))
              (add x (add y (add u v)))
              (add (add x u) (add y v))
              (add_assoc x y (add u v))
              (trans
                ℕ
                (add x (add y (add u v)))
                (add x (add (add y u) v))
                (add (add x u) (add y v))
                (ap
                  ℕ
                  ℕ
                  (λ t: ℕ -> (add x t))
                  (add y (add u v))
                  (add (add y u) v)
                  (symm ℕ (add (add y u) v) (add y (add u v)) (add_assoc y u v)))
                (trans
                  ℕ
                  (add x (add (add y u) v))
                  (add (add x (add y u)) v)
                  (add (add x u) (add y v))
                  (symm
                    ℕ
                    (add (add x (add y u)) v)
                    (add x (add (add y u) v))
                    (add_assoc x (add y u) v))
                  (trans
                    ℕ
                    (add (add x (add y u)) v)
                    (add (add (add x u) y) v)
                    (add (add x u) (add y v))
                    (ap
                      ℕ
                      ℕ
                      (λ t: ℕ -> (add t v))
                      (add x (add y u))
                      (add (add x u) y)
                      (trans
                        ℕ
                        (add x (add y u))
                        (add x (add u y))
                        (add (add x u) y)
                        (ap ℕ ℕ (λ t: ℕ -> (add x t)) (add y u) (add u y) (add_comm y u))
                        (symm ℕ (add (add x u) y) (add x (add u y)) (add_assoc x u y))))
                    (add_assoc (add x u) y v))))))))),

pred
  = (λ n: ℕ -> (n (λ _: ℕ -> ℕ) (λ k: ℕ -> (λ r: ℕ -> k)) 0)),

injS
  = (λ x: ℕ ->
      (λ y: ℕ -> (λ p: (≡ ℕ (NAT.+ 1 x) (NAT.+ 1 y)) -> (ap ℕ ℕ pred (NAT.+ 1 x) (NAT.+ 1 y) p)))),
"""


THEOREMS = (
    (
        'Identity Lemma',
        """
        (Π A: Type0 => (Π x: A => A))
        """,
        """
        (λ A: Type0 -> (λ x: A -> x))
        """,
    ),
    (
        'Modus Ponens',
        """
        (Π A: Type0 => (Π B: Type0 => (Π a: A => (Π a_to_b: (Π ai: A => B) => B))))
        """,
        """
        (λ A: Type0 -> (λ B: Type0 -> (λ a: A -> (λ a_to_b: (Π ai: A => B) -> (a_to_b a)))))
        """,
    ),
    (
        'Or Left',
        """
        (Π A: Type0 => (Π B: Type0 => (Π a: A => (| A B))))
        """,
        """
        (λ A: Type0 -> (λ B: Type0 -> (λ a: A -> (|inl A B a))))
        """,
    ),
    (
        'Or Right',
        """
        (Π A: Type0 => (Π B: Type0 => (Π b: B => (| A B))))
        """,
        """
        (λ A: Type0 -> (λ B: Type0 -> (λ b: B -> (|inr A B b))))
        """,
    ),
    (
        'And Implies Or',
        """
        (Π A: Type0 => (Π B: Type0 => (Π a_and_b: (& A B) => (| A B))))
        """,
        """
        (λ A: Type0 ->
          (λ B: Type0 ->
            (λ a_and_b: (& A B) ->
              (&.ind0 A B (λ x: (& A B) -> (| A B)) (λ a: A -> (λ b: B -> (|inl A B a))) a_and_b))))
        """,
    ),
    (
        'Function of equals are equal',
        """
        (Π A: Type0 =>
          (Π B: Type0 =>
            (Π f: (Π a: A => B) =>
              (Π a1: A => (Π a2: A => (Π a1_eq_a2: (≡ A a1 a2) => (≡ B (f a1) (f a2))))))))
        """,
        """
        (λ A: Type0 ->
          (λ B: Type0 ->
            (λ f: (Π a: A => B) ->
              (λ a1: A ->
                (λ a2: A ->
                  (λ a1_eq_a2: (≡ A a1 a2) ->
                    (≡.ind0
                      A
                      a1
                      (λ a1_idx: A -> (λ instance: (≡ A a1 a1_idx) -> (≡ B (f a1) (f a1_idx))))
                      (refl B (f a1))
                      a2
                      a1_eq_a2)))))))
        """,
    ),
    (
        'Equality is symmetric',
        """
        (Π A: Type0 => (Π x: A => (Π y: A => (Π x_eq_y: (≡ A x y) => (≡ A y x)))))
        """,
        """
        (λ A: Type0 ->
          (λ x: A ->
            (λ y: A ->
              (λ x_eq_y: (≡ A x y) ->
                (≡.ind0
                  A
                  x
                  (λ x_idx: A -> (λ instance: (≡ A x x_idx) -> (≡ A x_idx x)))
                  (refl A x)
                  y
                  x_eq_y)))))
        """,
    ),
    (
        'Equality is transitive',
        """
        (Π A: Type0 =>
          (Π x: A =>
            (Π y: A => (Π z: A => (Π x_eq_y: (≡ A x y) => (Π y_eq_z: (≡ A y z) => (≡ A x z)))))))
        """,
        """
        (λ A: Type0 ->
          (λ x: A ->
            (λ y: A ->
              (λ z: A ->
                (λ x_eq_y: (≡ A x y) ->
                  (λ y_eq_z: (≡ A y z) ->
                    (≡.ind0
                      A
                      x
                      (λ y_idx: A ->
                        (λ instance: (≡ A x y_idx) ->
                          (Π z_idx: A => (Π y_eq_z_idx: (≡ A y_idx z_idx) => (≡ A x z_idx)))))
                      (λ z_idx: A -> (λ x_eq_z_idx: (≡ A x z_idx) -> x_eq_z_idx))
                      y
                      x_eq_y
                      z
                      y_eq_z)))))))
        """,
    ),
    (
        'Double-Negation Elimination',
        """
        (Π A: Type0 => (Π nnA: (Π na: (Π a: A => ⊥) => ⊥) => A))
        """,
        """
        (λ A: Type0 ->
          (λ nnA: (Π na: (Π a: A => ⊥) => ⊥) ->
            (|.ind0
              A
              (Π a: A => ⊥)
              (λ x: (| A (Π a: A => ⊥)) -> A)
              (λ a: A -> a)
              (λ notA: (Π a: A => ⊥) -> (⊥.ind0 (λ x: ⊥ -> A) (nnA notA)))
              (LEM A))))
        """,
    ),
    (
        'id_Nat equals its input (delta-reduction required)',
        """
        (Π n: ℕ => (≡ ℕ (id_Nat n) n))
        """,
        """
        (λ n: ℕ -> (refl ℕ n))
        """,
    ),
    (
        'add 1 1 = 2',
        """
        (≡ ℕ (add 1 1) 2)
        """,
        """
        (refl ℕ (add 1 1))
        """,
    ),
    (
        '1 != 0',
        """
        (Π p: (≡ ℕ 1 0) => ⊥)
        """,
        """
        (λ p: (≡ ℕ 1 0) ->
          (≡.ind0
            ℕ
            1
            (λ y: ℕ -> (λ instance: (≡ ℕ 1 y) -> (isSucc y)))
            unit
            0
            p))
        """,
    ),
    (
        'add associative',
        """
        (Π a: ℕ => (Π b: ℕ => (Π c: ℕ => (≡ ℕ (add (add a b) c) (add a (add b c))))))
        """,
        """
        ((λ apS: (Π x: ℕ => (Π y: ℕ => (Π p: (≡ ℕ x y) => (≡ ℕ (NAT.+ 1 x) (NAT.+ 1 y))))) -> (λ a: ℕ -> (a (λ a_idx: ℕ -> (Π b: ℕ => (Π c: ℕ => (≡ ℕ (add (add a_idx b) c) (add a_idx (add b c)))))) (λ n: ℕ -> (λ ih: (Π b: ℕ => (Π c: ℕ => (≡ ℕ (add (add n b) c) (add n (add b c))))) -> (λ b: ℕ -> (λ c: ℕ -> (apS (add (add n b) c) (add n (add b c)) (ih b c)))))) (λ b: ℕ -> (λ c: ℕ -> (refl ℕ (add b c)))))))
          (λ x: ℕ ->
            (λ y: ℕ ->
              (λ p: (≡ ℕ x y) ->
                (≡.ind0
                  ℕ
                  x
                  (λ y_idx: ℕ -> (λ instance: (≡ ℕ x y_idx) -> (≡ ℕ (NAT.+ 1 x) (NAT.+ 1 y_idx))))
                  (refl ℕ (NAT.+ 1 x))
                  y
                  p)))))
        """,
    ),
    (
        'add n 0 = n',
        """
        (Π n: ℕ => (≡ ℕ (add n 0) n))
        """,
        """
        ((λ apS: (Π x: ℕ => (Π y: ℕ => (Π p: (≡ ℕ x y) => (≡ ℕ (NAT.+ 1 x) (NAT.+ 1 y))))) -> (λ n: ℕ -> (n (λ n_idx: ℕ -> (≡ ℕ (add n_idx 0) n_idx)) (λ k: ℕ -> (λ ih: (≡ ℕ (add k 0) k) -> (apS (add k 0) k ih))) (refl ℕ (add 0 0)))))
          (λ x: ℕ ->
            (λ y: ℕ ->
              (λ p: (≡ ℕ x y) ->
                (≡.ind0
                  ℕ
                  x
                  (λ y_idx: ℕ -> (λ instance: (≡ ℕ x y_idx) -> (≡ ℕ (NAT.+ 1 x) (NAT.+ 1 y_idx))))
                  (refl ℕ (NAT.+ 1 x))
                  y
                  p)))))
        """,
    ),
    (
        'mul 2 2 = 4',
        """
        (≡
          ℕ
          (mul 2 2)
          4)
        """,
        """
        (refl ℕ (mul 2 2))
        """,
    ),
    (
        'distributive law',
        """
        (Π a: ℕ => (Π x: ℕ => (Π y: ℕ => (≡ ℕ (mul a (add x y)) (add (mul a x) (mul a y))))))
        """,
        """
        (λ a: ℕ ->
          (λ x: ℕ ->
            (λ y: ℕ ->
              (a
                (λ a_idx: ℕ ->
                  (Π x1: ℕ =>
                    (Π y1: ℕ => (≡ ℕ (mul a_idx (add x1 y1)) (add (mul a_idx x1) (mul a_idx y1))))))
                (λ n: ℕ ->
                  (λ ih: (Π x1: ℕ => (Π y1: ℕ => (≡ ℕ (mul n (add x1 y1)) (add (mul n x1) (mul n y1))))) ->
                    (λ x1: ℕ ->
                      (λ y1: ℕ ->
                        (trans
                          ℕ
                          (add (add x1 y1) (mul n (add x1 y1)))
                          (add (add x1 y1) (add (mul n x1) (mul n y1)))
                          (add (add x1 (mul n x1)) (add y1 (mul n y1)))
                          (ap
                            ℕ
                            ℕ
                            (λ t: ℕ -> (add (add x1 y1) t))
                            (mul n (add x1 y1))
                            (add (mul n x1) (mul n y1))
                            (ih x1 y1))
                          (add_shuffle x1 y1 (mul n x1) (mul n y1)))))))
                (λ x0: ℕ -> (λ y0: ℕ -> (refl ℕ (mul 0 (add x0 y0)))))
                x
                y))))
        """,
    ),
    (
        'add left cancellation',
        """
        (Π a: ℕ => (Π b: ℕ => (Π c: ℕ => (Π p: (≡ ℕ (add a b) (add a c)) => (≡ ℕ b c)))))
        """,
        """
        (λ a: ℕ ->
          (λ b: ℕ ->
            (λ c: ℕ ->
              (λ p: (≡ ℕ (add a b) (add a c)) ->
                (a
                  (λ a_idx: ℕ ->
                    (Π b1: ℕ =>
                      (Π c1: ℕ => (Π p1: (≡ ℕ (add a_idx b1) (add a_idx c1)) => (≡ ℕ b1 c1)))))
                  (λ n: ℕ ->
                    (λ ih: (Π b1: ℕ => (Π c1: ℕ => (Π p1: (≡ ℕ (add n b1) (add n c1)) => (≡ ℕ b1 c1)))) ->
                      (λ b1: ℕ ->
                        (λ c1: ℕ ->
                          (λ p1: (≡ ℕ (add (NAT.+ 1 n) b1) (add (NAT.+ 1 n) c1)) ->
                            (ih b1 c1 (injS (add n b1) (add n c1) p1)))))))
                  (λ b0: ℕ -> (λ c0: ℕ -> (λ p0: (≡ ℕ (add 0 b0) (add 0 c0)) -> p0)))
                  b
                  c
                  p)))))
        """,
    ),
)


def term(source, module):
    """The parser consumes declarations; extract a declaration's value term."""
    declaration, = parse(f"probe = {source},")
    return declaration.value.to_term(module, EmptyEnv())


def vector(values):
    result = "(vec_empty ℕ)"
    for length, value in enumerate(reversed(values)):
        result = f"(vec_append ℕ {length} {value} {result})"
    return result


class KernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Double-negation elimination explicitly depends on excluded middle.
        cls.module = def_module(
            DEFINITIONS,
            imports=[("", get_usual_axioms(classical=True)), ("NAT", NAT_MODULE)])

    def test_theorems(self):
        for name, theorem, proof in THEOREMS:
            with self.subTest(theorem=name):
                # A checked declaration validates both the proposition's sort
                # and the proof against its evaluated expected type.
                def_module(
                    f"proof : {theorem}\n= {proof}\n,",
                    imports=[("", self.module)])

    def test_computations(self):
        expected_matrix = (
            f"(mat_append ℕ 2 1 {vector([4, 5])} "
            f"(mat_append ℕ 2 0 {vector([2, 3])} "
            "(mat_empty ℕ 2)))")
        cases = [
            ("zero_x2", "0"),
            ("one_x2", "2"),
            ("eq_1_1", "refl ℕ 1"),
            ("eq_2_2", "refl ℕ 2"),
            ("use_inc_vec_eg_1", vector([2])),
            ("use_mirror_blorb_eg_1", "blorb_inr 1 0 (blorb_inl 0 0 blorb_base)"),
            ("use_inc_mat_eg_1", expected_matrix),
            ("add 1 1", "2"),
            ("mul 2 2", "4"),
        ]
        for source, expected in cases:
            with self.subTest(expression=source):
                original = term(source, self.module)
                expected_term = term(expected, self.module)
                expected_type = infer(original, EmptyEnv())
                check(expected_term, expected_type, EmptyEnv())
                actual = term_eval(original, EmptyEnv())
                self.assertTrue(conv(actual, term_eval(expected_term, EmptyEnv())))
                check(quote(actual), expected_type, EmptyEnv())


if __name__ == "__main__":
    unittest.main()
