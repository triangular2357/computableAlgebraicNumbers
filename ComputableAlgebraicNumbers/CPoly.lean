import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace CPolynomial

def noLeadingZero {R : Type*} [Ring R] : List R → Prop
  | []     => True
  | x :: _ => x ≠ 0

structure CPoly (R : Type*) [Ring R] where
  coefs : List R
  norm : noLeadingZero coefs.reverse

def removeLeadingZeros {R : Type*} [Ring R] [DecidableEq R] : List R → List R
  | []      => []
  | x :: xs => if x = 0 then removeLeadingZeros xs else x :: xs

lemma noLeadingZero_removeLeadingZeros {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : noLeadingZero (removeLeadingZeros l) := by
  induction l with
  | nil => trivial
  | cons x xs ih =>
    unfold removeLeadingZeros
    rw [apply_ite noLeadingZero]
    by_cases h : x = 0
    · rwa [if_pos h]
    · rwa [if_neg h]

def normalize {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : CPoly R :=
  ⟨(removeLeadingZeros l.reverse).reverse, by
    rw [List.reverse_reverse]
    apply noLeadingZero_removeLeadingZeros
  ⟩

end CPolynomial
