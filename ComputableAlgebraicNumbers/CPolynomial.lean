--import Mathlib
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Field.LemmasLean
-- section
-- source https://github.com/leanprover-community/mathlib4/wiki/Computation-models-for-polynomials-and-finitely-supported-functions

open scoped DirectSum

abbrev CPolynomial (R) [Ring R] := ⨁ i : ℕ, R
abbrev CPolynomial.X {R} [Ring R] : CPolynomial R := .single 1 1

unsafe instance {R} [Ring R] [Repr R] : Repr (CPolynomial R) where
  reprPrec x prec :=
    let l := x.support'.unquot.1.sort (· ≤ ·)
    Std.Format.joinSep (l.map fun
      | 0 => repr (x 0)
      | 1 => f!"{repr (x 1)}*X"
      | i => f!"{repr (x i)}*X^{i}") f!" + "

open CPolynomial

#eval (3*X^2 + 1 : CPolynomial Int)
#eval (3*X^2 + 3*X^2 : CPolynomial Int)
#eval (4*X + 23*X + 3*X^2 + 3*X^2 + 4*X + 1*X^2 : CPolynomial Int)
#check ((4*X + 23*X + 3*X^2 + 3*X^2 + 4*X + 1*X^2): CPolynomial Int)


#synth AddCommGroup (CPolynomial ℚ)
def CPolynomial.mul {R} [Ring R] (a:CPolynomial R) (b:CPolynomial R) :=

  have product [Ring R]:CPolynomial R:= .single 0 0

  product

instance {R} [Ring R] : Ring (CPolynomial R) where
  add a b := a+b
  add_assoc := by
    simp only [add_assoc, implies_true]
  zero := .single 0 0
  zero_add := by
    intro p
    rw??

    simp

  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := sorry
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  npow := sorry
  npow_zero := sorry
  npow_succ := sorry
  neg := sorry
  sub := sorry
  sub_eq_add_neg := sorry
  zsmul := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  intCast := sorry
  intCast_ofNat := sorry
  intCast_negSucc := sorry

/-
  add a b := a+b
  add_assoc := sorry
  zero :=
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := sorry
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
-/


example :
    ∀ p ∈ ({3*X^2, 2*X^3, 3*X + 1} : Finset (CPolynomial Int)), p ≠ 0 := by
  decide

-- end

structure RealAlgebraicPreNumber where
  min_poly : CPolynomial ℚ
  min_poly_irr : Irreducible min_poly
  --min_poly_monic : min_poly.Monic
  lower : ℚ
  upper : ℚ
  --unique : ∃! x : ℝ, lower ≤ x ∧ x ≤ upper ∧ (min_poly.map $ algebraMap ℚ ℝ).eval x = 0
/-
def bound_invariance : Setoid RealAlgebraicPreNumber where
  r := λ ⟨mp₁, _, _, l₁, u₁, _⟩ ⟨mp₂, _, _, l₂, u₂, _⟩
    ↦ mp₁ = mp₂ ∧ ∃ x : ℝ, max l₁ l₂ ≤ x ∧ x ≤ min u₁ u₂ ∧ (mp₁.map $ algebraMap ℚ ℝ).eval x = 0
  iseqv := {
    refl a := by
      constructor; rfl
      obtain ⟨x, ⟨h₁, h₂, h₃⟩, _⟩ := a.unique
      use x
      constructor; simp[h₁]
      constructor; simp[h₂]
      exact h₃
    symm := by
      intro a b ⟨h₁, ⟨x, h₂, h₃, _⟩⟩
      constructor; exact h₁.symm
      use x
      constructor; grw[max_comm, h₂]
      constructor; grw[min_comm, h₃]
      rwa[←h₁]
    trans := by
      intro a b c ⟨heq₁, ⟨x₁, hl₁, hu₁, hr₁⟩⟩ ⟨heq₂, ⟨x₂, hl₂, hu₂, hr₂⟩⟩
      push_cast at *
      constructor; exact heq₁.trans heq₂
      have : x₁ = x₂ := by
        obtain ⟨x, h, h'⟩ := b.unique
        trans x
        · apply h' x₁
          constructor; exact (sup_le_iff.1 hl₁).2
          constructor; exact (le_inf_iff.1 hu₁).2
          rwa[← heq₁]
        · symm
          apply h' x₂
          constructor; exact (sup_le_iff.1 hl₂).1
          constructor; exact (le_inf_iff.1 hu₂).1
          assumption
      rw[← this] at hl₂ hu₂
      use x₁
      constructor; exact sup_le_iff.2 ⟨(sup_le_iff.1 hl₁).1, (sup_le_iff.1 hl₂).2⟩
      constructor; exact le_inf_iff.2 ⟨(le_inf_iff.1 hu₁).1, (le_inf_iff.1 hu₂).2⟩
      assumption
  }
def RealAlgebraicNumber := Quotient bound_invariance

structure AlgebraicNumber where
  re : RealAlgebraicNumber
  im : RealAlgebraicNumber

notation "𝔸" => AlgebraicNumber

instance : Coe ℚ RealAlgebraicNumber where
  coe s := ⟦{
    min_poly := Polynomial.monomial 1 1 + Polynomial.monomial 0 (-s)
    min_poly_irr := by
      apply Polynomial.irreducible_of_degree_eq_one
      admit
    min_poly_monic := by
      unfold Polynomial.Monic Polynomial.leadingCoeff
      admit
    lower := s
    upper := s
    unique := by
      use s
      simp
      intros
      linarith
  }⟧


-/
#min_imports
