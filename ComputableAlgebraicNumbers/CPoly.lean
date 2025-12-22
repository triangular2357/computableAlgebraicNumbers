import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace CPolynomial

def normalized {R : Type*} [Ring R] : List R → Prop
  | []     => True
  | x :: _ => x ≠ 0

structure CPoly (R : Type*) [Ring R] where
  coefs : List R
  norm : normalized coefs.reverse

def normalize' {R : Type*} [Ring R] [DecidableEq R] : List R → List R
  | []      => []
  | x :: xs => if x = 0 then normalize' xs else x :: xs

lemma normaized_normalize {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : normalized (normalize' l) := by
  induction l with
  | nil => trivial
  | cons x xs ih =>
    unfold normalize'
    rw [apply_ite normalized]
    by_cases h : x = 0
    · rwa [if_pos h]
    · rwa [if_neg h]

def normalize {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : CPoly R :=
  ⟨(normalize' l.reverse).reverse, by
    rw [List.reverse_reverse]
    apply normaized_normalize
  ⟩

end CPolynomial
