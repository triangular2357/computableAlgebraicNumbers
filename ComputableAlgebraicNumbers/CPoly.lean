import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace CPolynomial


private def _noLeadingZero {R : Type*} [Ring R] : List R → Prop
  | []     => True
  | x :: _ => x ≠ 0

def noTailingZero {R : Type*} [Ring R] (i : List R) : Prop :=
  _noLeadingZero i.reverse

structure CPoly (R : Type*) [Ring R] where
  coefs : List R
  norm : noTailingZero coefs

private def _removeLeadingZeros {R : Type*} [Ring R] [DecidableEq R] : List R → List R
  | []      => []
  | x :: xs => if x = 0 then _removeLeadingZeros xs else x :: xs

private lemma _noLeadingZero_removeLeadingZeros {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : _noLeadingZero (_removeLeadingZeros l) := by
  induction l with
  | nil => trivial
  | cons x xs ih =>
    unfold _removeLeadingZeros
    rw [apply_ite _noLeadingZero]
    by_cases h : x = 0
    · rwa [if_pos h]
    · rwa [if_neg h]

def removeTailingZeros {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : CPoly R :=
  ⟨(_removeLeadingZeros l.reverse).reverse, by
    unfold noTailingZero
    rw [List.reverse_reverse]
    apply _noLeadingZero_removeLeadingZeros
  ⟩

end CPolynomial
