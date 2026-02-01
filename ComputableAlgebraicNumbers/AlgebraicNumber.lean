import Mathlib
import ComputableAlgebraicNumbers.CPoly
import ComputableAlgebraicNumbers.ApproximationType

structure PreRealAlgebraicNumber where
  min_poly : CPoly ℚ
  squarefree : Squarefree min_poly
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper
  ivt_condition : min_poly.eval lower * min_poly.eval upper ≤ 0
  deriv_nzero : ∀ x ∈ Set.Icc lower upper, (min_poly.deriv.liftTo ℝ).eval x ≠ 0

open ApproximationType

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
      squarefree := a.squarefree
      lower := a.lower
      upper := midpoint
      lower_le_upper := hbetween.1
      ivt_condition := h
      deriv_nzero := fun x hx ↦ a.deriv_nzero x <|
        Set.Icc_subset_Icc (le_refl a.lower) hbetween.2 hx
    } else {
      min_poly := a.min_poly
      squarefree := a.squarefree
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

abbrev intervalLength (p : PreRealAlgebraicNumber) : ℚ := p.upper - p.lower

lemma intervalLength_improve (p : PreRealAlgebraicNumber) :
  intervalLength p / 2 = intervalLength (improve p) := by
  unfold intervalLength improve instApproximationTypePreRealAlgebraicNumber
  simp only
  split_ifs <;> ring

lemma intervalLength_iterate_improve (p : PreRealAlgebraicNumber) (n : ℕ) :
  intervalLength p / (2 ^ n) = intervalLength (improve^[n] p) := by
  induction n with
  | zero => simp only [pow_zero, div_one, Function.iterate_zero, id_eq]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← intervalLength_improve, ← ih]
    ring

instance (ε : ℚ) (h : ε > 0) :
  isExact (fun (p : PreRealAlgebraicNumber) ↦ intervalLength p < ε) where
    reachable := by
      intro p
      let m := Real.logb 2 (intervalLength p / ε)
      let n : ℕ := Nat.ceil (m + 1)
      have : n > m := calc
          _ ≥ m + 1 := Nat.le_ceil _
          _ > m := lt_add_one m
      use n
      rw [← intervalLength_iterate_improve]
      apply Real.ratCast_lt.1
      by_cases h' : intervalLength p > 0
      · subst m
        unfold intervalLength at h'
        by_contra h''
        simp only [not_lt] at h''
        grw [h''] at this
        · simp at this
          grw [Real.logb_lt_iff_lt_rpow] at this
          · apply ne_of_lt this
            field_simp
            rw [mul_comm, mul_div_assoc, div_self (ne_of_gt (by norm_cast)),
              mul_one, Real.rpow_natCast]
          · simp only [Nat.one_lt_ofNat]
          · apply div_pos
            · norm_cast
            · apply div_pos
              · norm_cast
              · simp only [Nat.ofNat_pos, pow_pos]
        · simp only [Nat.one_lt_ofNat]
      · have := p.lower_le_upper
        unfold intervalLength
        simp only [gt_iff_lt, sub_pos, not_lt] at h'
        have : p.lower = p.upper := le_antisymm this h'
        simp only [this, sub_self, zero_div, Rat.cast_zero, Rat.cast_pos, h]
    stable := by
      intro p hp
      grw [← intervalLength_improve, hp]
      simp only [half_lt_self_iff, h]

structure PolyLevelFun' (rootFun : ℝ → ℝ) where
  semiMonotone : ∀ x a b, x ∈ Set.uIcc a b → rootFun x ∈ Set.uIcc (rootFun a) (rootFun b)
  polyFun : CPoly ℚ → CPoly ℚ
  neZero : ∀ p, p ≠ 0 → polyFun p ≠ 0
  preservesRoots : ∀ x f, (f.liftTo ℝ).eval x = 0 → ((polyFun f).liftTo ℝ).eval (rootFun x) = 0

structure PolyLevelFun (rootFun : ℝ → ℝ) extends PolyLevelFun' (rootFun : ℝ → ℝ) where
  squarefree : ∀ p, p ≠ 0 → Squarefree (polyFun p)

def squarefreeify {rootFun : ℝ → ℝ} (plf : PolyLevelFun' (rootFun : ℝ → ℝ)) :
  PolyLevelFun (rootFun : ℝ → ℝ) where
  semiMonotone := plf.semiMonotone
  polyFun p := plf.polyFun p / gcd (plf.polyFun p) (plf.polyFun p).deriv
  neZero := by
    intro p hp
    have := CPoly.squarefree_div_gcd_deriv (plf.polyFun p) (plf.neZero p hp)
    exact Squarefree.ne_zero this
  preservesRoots := by
    intro x f hf
    apply CPoly.eval_div_gcd_deriv_eq_zero_of_eval_eq_zero
    exact plf.preservesRoots x f hf
  squarefree := by
    intro p hp
    apply CPoly.squarefree_div_gcd_deriv (plf.polyFun p) (plf.neZero p hp)
