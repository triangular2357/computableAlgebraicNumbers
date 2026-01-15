import Mathlib
import ComputableAlgebraicNumbers.CPoly
import ComputableAlgebraicNumbers.ApproximationType

structure PreRealAlgebraicNumber where
  min_poly : CPoly ℚ
  irr : Irreducible min_poly
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper
  ivt_condition : min_poly.eval lower * min_poly.eval upper ≤ 0
  deriv_nzero : ∀ x ∈ Set.Icc lower upper, (min_poly.deriv.liftTo ℝ).eval x ≠ 0


instance : ApproximationType PreRealAlgebraicNumber where
  improve a :=
    let midpoint := (a.lower + a.upper) / 2
    have hbetween : a.lower ≤ midpoint ∧ midpoint ≤ a.upper := by
      have := a.lower_le_upper
      unfold midpoint
      constructor <;> linarith
    if h : a.min_poly.eval a.lower * a.min_poly.eval midpoint ≤ 0
    then {
      min_poly := a.min_poly
      irr := a.irr
      lower := a.lower
      upper := midpoint
      lower_le_upper := hbetween.1
      ivt_condition := h
      deriv_nzero := fun x hx ↦ a.deriv_nzero x <|
        Set.Icc_subset_Icc (le_refl a.lower) hbetween.2 hx
    } else {
      min_poly := a.min_poly
      irr := a.irr
      lower := midpoint
      upper := a.upper
      lower_le_upper := hbetween.2
      ivt_condition := by
        apply lt_of_not_ge at h
        by_cases hl : a.min_poly.eval a.lower = 0
        · rw [hl, zero_mul] at h
          simp at h
        · refine nonpos_of_mul_nonpos_left ?_ (mul_self_pos.2 hl)
          have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt h) a.ivt_condition
          ring_nf at this ⊢
          assumption
      deriv_nzero := fun x hx ↦ a.deriv_nzero x <|
        Set.Icc_subset_Icc hbetween.1 (le_refl a.upper) hx
    }

#print axioms PreRealAlgebraicNumber
