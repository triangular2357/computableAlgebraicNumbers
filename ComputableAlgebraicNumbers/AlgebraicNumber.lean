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
  deriv_nzero : ∀ x ∈ Set.Icc ↑lower ↑upper, (min_poly.deriv.liftTo ℝ).eval x ≠ 0

lemma PreRealAlgebraicNumber.min_poly_ne_zero (a : PreRealAlgebraicNumber) : a.min_poly ≠ 0 :=
  Squarefree.ne_zero a.squarefree

lemma coe_eq_algebraMap (x : ℚ) : ↑x = (algebraMap ℚ ℝ) x := rfl

lemma liftTo_eval (f : CPoly ℚ) (x : ℚ) : f.eval x = (f.liftTo ℝ).eval x := by
  rw [CPoly.toPolynomial_liftTo_eval_eq_eval₂, CPoly.toPolynomial_eval, coe_eq_algebraMap,
    coe_eq_algebraMap, Polynomial.eval₂_at_apply]

lemma liftTo_hasderivAt (f : CPoly ℚ) (x : ℝ) :
  HasDerivAt (f.liftTo ℝ).eval ((f.deriv.liftTo ℝ).eval x) x := by
  rw [CPoly.toPolynomial_liftTo_eval_eq_eval₂, ← Polynomial.eval_map, CPoly.toPolynomial_deriv,
    show (f.liftTo ℝ).eval = fun y ↦ (Polynomial.eval y (Polynomial.map (algebraMap ℚ ℝ)
    f.toPolynomial)) by funext y; rw [CPoly.toPolynomial_liftTo_eval_eq_eval₂,
    ← Polynomial.eval_map], ← Polynomial.derivative_map]
  apply Polynomial.hasDerivAt

lemma poly_ivt (f : CPoly ℚ) (a b : ℝ) (hab : a ≤ b) (ha : (f.liftTo ℝ).eval a ≤ 0)
  (hb : (f.liftTo ℝ).eval b ≥ 0) : ∃ ξ ∈ Set.Icc a b, (f.liftTo ℝ).eval ξ = 0 := by
  apply intermediate_value_Icc hab ?_ ⟨ha, hb⟩
  apply Continuous.continuousOn
  rw [show (f.liftTo ℝ).eval = fun y ↦ (Polynomial.eval y (Polynomial.map (algebraMap ℚ ℝ)
  f.toPolynomial)) by funext y; rw [CPoly.toPolynomial_liftTo_eval_eq_eval₂,
  ← Polynomial.eval_map]]
  apply Polynomial.continuous_eval₂

lemma poly_ivt' (f : CPoly ℚ) (a b : ℝ) (hab : a ≤ b) (ha : (f.liftTo ℝ).eval a ≥ 0)
  (hb : (f.liftTo ℝ).eval b ≤ 0) : ∃ ξ ∈ Set.Icc a b, (f.liftTo ℝ).eval ξ = 0 := by
  apply intermediate_value_Icc' hab ?_ ⟨hb, ha⟩
  apply Continuous.continuousOn
  rw [show (f.liftTo ℝ).eval = fun y ↦ (Polynomial.eval y (Polynomial.map (algebraMap ℚ ℝ)
  f.toPolynomial)) by funext y; rw [CPoly.toPolynomial_liftTo_eval_eq_eval₂,
  ← Polynomial.eval_map]]
  apply Polynomial.continuous_eval₂

lemma uniqueRoot_of_root_of_deriv_ne_zero (f : CPoly ℚ) (l u : ℚ)
  (h_nz : ∀ x ∈ Set.Icc ↑l ↑u, (f.deriv.liftTo ℝ).eval x ≠ 0) :
  (∃ x ∈ Set.Icc ↑l ↑u, (f.liftTo ℝ).eval x = 0) →
  ∃! x ∈ Set.Icc ↑l ↑u, (f.liftTo ℝ).eval x = 0 := by
  intro ⟨x, h_mem, h_root⟩
  use x, ⟨h_mem, h_root⟩
  intro y ⟨h₁, h₂⟩
  by_cases h : u = l
  · have := h_mem
    rw [h, Set.mem_Icc] at h₁ this
    trans ↑l <;> apply le_antisymm
    · exact h₁.2
    · exact h₁.1
    · exact this.1
    · exact this.2
  · by_contra h'
    have := exists_deriv_eq_zero (f := (f.liftTo ℝ).eval) (a := min y x)
      (b := max y x) (min_lt_max.2 h') <| by
      simp_rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ (S := ℝ) f)]
      apply Continuous.continuousOn
      apply Polynomial.continuous_eval₂
    obtain ⟨c, hc, h'c⟩ := this <| by
      by_cases h'' : y ≤ x
      · rw [min_eq_left h'', max_eq_right h'', h₂, h_root]
      · rw [min_eq_right (le_of_not_ge h''), max_eq_left (le_of_not_ge h''), h₂, h_root]
    have := h_mem
    apply h_nz c
    · simp only [Set.mem_Ioo, Set.mem_Icc] at hc h₁ this ⊢
      constructor
      · calc
          _ ≤ min y x := by
            apply le_min h₁.1 this.1
          _ ≤ _ := le_of_lt hc.1
      · calc
          _ ≤ max y x := le_of_lt hc.2
          _ ≤ _ := by
            apply max_le h₁.2 this.2
    · simp_rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ (S := ℝ) f.deriv),
        CPoly.toPolynomial_deriv, ← Polynomial.eval_map, ← Polynomial.derivative_map,
        ← Polynomial.deriv, Polynomial.eval_map, ]
      simp_rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ (S := ℝ) f)] at h'c
      assumption

lemma lower_mul_upper_le_zero_iff_unique_root_of_deriv_non_zero
  (f : CPoly ℚ) (l u : ℚ) (hlu : l ≤ u)
  (h_nz : ∀ x ∈ Set.Icc ↑l ↑u, (f.deriv.liftTo ℝ).eval x ≠ 0) :
  f.eval l * f.eval u ≤ 0 ↔ ∃! x ∈ Set.Icc ↑l ↑u, (f.liftTo ℝ).eval x = 0 := by
  constructor
  · intro ivt_condition
    have has_root : ∃ x ∈ Set.Icc ↑l ↑u, (f.liftTo ℝ).eval x = 0 := by
      have := intermediate_value_uIcc (a := ↑l) (b := ↑u)
        (f := (f.liftTo ℝ).eval) <| by
        simp_rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ (S := ℝ) f)]
        apply Continuous.continuousOn
        apply Polynomial.continuous_eval₂
      have := @this 0 <| by
        apply Set.mem_Icc.2
        simp_rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ (S := ℝ) f),
          ← Polynomial.eval_map, show ∀ r, ↑r = (algebraMap ℚ ℝ) r from fun _ ↦ rfl,
          Polynomial.eval_map_apply, ← show ∀ r, ↑r = (algebraMap ℚ ℝ) r from fun _ ↦ rfl,
          ← CPoly.toPolynomial_eval]
        norm_cast
        by_cases h : 0 < f.eval l
        · constructor
          · apply min_le_of_right_le
            apply nonpos_of_mul_nonpos_right ivt_condition h
          · apply le_max_of_le_left (le_of_lt h)
        · rw [not_lt] at h
          constructor
          · apply min_le_of_left_le h
          · by_cases h' : f.eval l = 0
            · apply le_max_of_le_left (le_of_eq h'.symm)
            · apply le_max_of_le_right
              apply nonneg_of_mul_nonpos_right ivt_condition
              apply lt_of_le_of_ne h h'
      rwa [← Set.uIcc_of_le (Rat.cast_le.2 hlu)]
    apply uniqueRoot_of_root_of_deriv_ne_zero
    · apply h_nz
    · apply has_root
  · intro ⟨x, ⟨h₁x, h₂x⟩, h'x⟩
    rify
    by_cases h : x = l
    · subst x
      rw [liftTo_eval, h₂x]
      simp only [zero_mul, le_refl]
    by_cases h' : x = u
    · subst x
      rw [liftTo_eval f u, h₂x]
      simp only [mul_zero, le_refl]
    simp only [Set.mem_Icc] at h₁x
    have hlx := lt_of_le_of_ne h₁x.1 (fun hh ↦ h hh.symm)
    have hxu := lt_of_le_of_ne h₁x.2 h'
    simp_rw [liftTo_eval]
    by_cases h : (f.deriv.liftTo ℝ).eval x < 0
    · apply mul_nonpos_of_nonneg_of_nonpos
        <;> by_contra h'
        <;> apply not_le.1 at h'
      · have ⟨y, ⟨hly, hyx⟩, hslope⟩: ∃ y ∈ Set.Ioo ↑l x, (f.deriv.liftTo ℝ).eval y =
          ((f.liftTo ℝ).eval x - (f.liftTo ℝ).eval l) / (x - l) := by
          apply exists_hasDerivAt_eq_slope
          · exact hlx
          · apply Continuous.continuousOn
            rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ f)]
            apply Polynomial.continuous_eval₂
          · intros
            apply liftTo_hasderivAt
        have : (f.deriv.liftTo ℝ).eval y > 0 := by
          grw [hslope, h₂x]
          apply div_pos
          · simp only [zero_sub, Left.neg_pos_iff, h']
          · simp only [sub_pos, hlx]
        have ⟨ξ, ⟨hyξ, hξx⟩, hξ⟩ := poly_ivt' f.deriv y x (le_of_lt hyx)
          (le_of_lt this) (le_of_lt h)
        apply h_nz ξ ⟨(le_of_lt hly).trans hyξ, hξx.trans (le_of_lt hxu)⟩ hξ
      · have ⟨y, ⟨hxy, hyu⟩, hslope⟩: ∃ y ∈ Set.Ioo x ↑u, (f.deriv.liftTo ℝ).eval y =
          ((f.liftTo ℝ).eval u - (f.liftTo ℝ).eval x) / (u - x) := by
          apply exists_hasDerivAt_eq_slope
          · exact hxu
          · apply Continuous.continuousOn
            rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ f)]
            apply Polynomial.continuous_eval₂
          · intros
            apply liftTo_hasderivAt
        have : (f.deriv.liftTo ℝ).eval y > 0 := by
          grw [hslope, h₂x]
          apply div_pos
          · simp only [sub_zero, h']
          · simp only [sub_pos, hxu]
        have ⟨ξ, ⟨hxξ, hξy⟩, hξ⟩ := poly_ivt f.deriv x y (le_of_lt hxy)
          (le_of_lt h) (le_of_lt this)
        apply h_nz ξ ⟨(le_of_lt hlx).trans hxξ, hξy.trans (le_of_lt hyu)⟩ hξ
    · have h := lt_of_le_of_ne (not_lt.1 h) <| fun h ↦ by
        simp only [Set.mem_Icc, ne_eq, and_imp] at h_nz
        exact h_nz x h₁x.1 h₁x.2 h.symm
      apply mul_nonpos_of_nonpos_of_nonneg
        <;> by_contra h'
        <;> apply not_le.1 at h'
      · have ⟨y, ⟨hly, hyx⟩, hslope⟩: ∃ y ∈ Set.Ioo ↑l x, (f.deriv.liftTo ℝ).eval y =
          ((f.liftTo ℝ).eval x - (f.liftTo ℝ).eval l) / (x - l) := by
          apply exists_hasDerivAt_eq_slope
          · exact hlx
          · apply Continuous.continuousOn
            rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ f)]
            apply Polynomial.continuous_eval₂
          · intros
            apply liftTo_hasderivAt
        have : (f.deriv.liftTo ℝ).eval y < 0 := by
          grw [hslope, h₂x]
          apply div_neg_of_neg_of_pos
          · simp only [zero_sub, Left.neg_neg_iff, h']
          · simp only [sub_pos, hlx]
        have ⟨ξ, ⟨hyξ, hξx⟩, hξ⟩ := poly_ivt f.deriv y x (le_of_lt hyx)
          (le_of_lt this) (le_of_lt h)
        apply h_nz ξ ⟨(le_of_lt hly).trans hyξ, hξx.trans (le_of_lt hxu)⟩ hξ
      · have ⟨y, ⟨hxy, hyu⟩, hslope⟩: ∃ y ∈ Set.Ioo x ↑u, (f.deriv.liftTo ℝ).eval y =
          ((f.liftTo ℝ).eval u - (f.liftTo ℝ).eval x) / (u - x) := by
          apply exists_hasDerivAt_eq_slope
          · exact hxu
          · apply Continuous.continuousOn
            rw [funext (CPoly.toPolynomial_liftTo_eval_eq_eval₂ f)]
            apply Polynomial.continuous_eval₂
          · intros
            apply liftTo_hasderivAt
        have : (f.deriv.liftTo ℝ).eval y < 0 := by
          grw [hslope, h₂x]
          apply div_neg_of_neg_of_pos
          · simp only [sub_zero, h']
          · simp only [sub_pos, hxu]
        have ⟨ξ, ⟨hxξ, hξy⟩, hξ⟩ := poly_ivt' f.deriv x y (le_of_lt hxy)
          (le_of_lt h) (le_of_lt this)
        apply h_nz ξ ⟨(le_of_lt hlx).trans hxξ, hξy.trans (le_of_lt hyu)⟩ hξ

lemma PreRealAlgebraicNumber.existsUnique_root (a : PreRealAlgebraicNumber) :
  ∃! x ∈ Set.Icc ↑a.lower ↑a.upper, (a.min_poly.liftTo ℝ).eval x = 0 :=
  (lower_mul_upper_le_zero_iff_unique_root_of_deriv_non_zero a.min_poly a.lower
  a.upper a.lower_le_upper a.deriv_nzero).1 a.ivt_condition

lemma PreRealAlgebraicNumber.has_root (a : PreRealAlgebraicNumber) :
  ∃ x ∈ Set.Icc ↑a.lower ↑a.upper, (a.min_poly.liftTo ℝ).eval x = 0 :=
  a.existsUnique_root.exists

noncomputable def PreRealAlgebraicNumber.toReal (a : PreRealAlgebraicNumber) : ℝ :=
  a.has_root.choose

lemma PreRealAlgebraicNumber.toReal_mem_Icc (a : PreRealAlgebraicNumber) :
  a.toReal ∈ Set.Icc ↑a.lower ↑a.upper :=
  a.has_root.choose_spec.1

lemma PreRealAlgebraicNumber.toReal_isRoot (a : PreRealAlgebraicNumber) :
  (a.min_poly.liftTo ℝ).eval a.toReal = 0 :=
  a.has_root.choose_spec.2

lemma PreRealAlgebraicNumber.uniqueRoot (a : PreRealAlgebraicNumber) (y : ℝ)
  (h₁ : y ∈ Set.Icc ↑a.lower ↑a.upper) (h₂ : (a.min_poly.liftTo ℝ).eval y = 0) :
  y = a.toReal := by
  obtain ⟨x, hx, hu⟩ := a.existsUnique_root
  trans x
  · apply hu
    exact ⟨h₁, h₂⟩
  · symm
    apply hu
    exact ⟨a.toReal_mem_Icc, a.toReal_isRoot⟩

instance (a : PreRealAlgebraicNumber) : Decidable (a.toReal = 0) := by
  have : a.toReal = 0 ↔ 0 ∈ Set.Icc a.lower a.upper ∧ a.min_poly.eval 0 = 0 := by
    constructor
    · intro h
      constructor
      · rw [Set.mem_Icc]
        rify
        rw [← Set.mem_Icc, ← h]
        apply a.toReal_mem_Icc
      · rify
        rw [liftTo_eval, Rat.cast_zero]
        apply h ▸ a.toReal_isRoot
    · intro ⟨⟨h1, h2⟩, h3⟩
      symm
      apply a.uniqueRoot
      · simp only [Set.mem_Icc, Rat.cast_nonpos, h1, Rat.cast_nonneg, h2, and_self]
      · rw [← Rat.cast_zero, ← liftTo_eval]
        simp only [h3, Rat.cast_zero]
  rw [this]
  infer_instance

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
        Set.Icc_subset_Icc (Rat.cast_le.2 (le_refl a.lower)) (Rat.cast_le.2 hbetween.2) hx
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
        Set.Icc_subset_Icc (Rat.cast_le.2 hbetween.1) (Rat.cast_le.2 (le_refl a.upper)) hx
    }

lemma improve_min_poly (a : PreRealAlgebraicNumber) : (improve a).min_poly = a.min_poly := by
  unfold improve instApproximationTypePreRealAlgebraicNumber
  dsimp only
  split_ifs <;> rfl

lemma improve_lower_mem (a : PreRealAlgebraicNumber) :
  (improve a).lower ∈ Set.Icc a.lower a.upper := by
  unfold improve instApproximationTypePreRealAlgebraicNumber
  dsimp only
  have := a.lower_le_upper
  split_ifs
  · simp only [Set.mem_Icc, le_refl, this, and_self]
  · simp only [Set.mem_Icc]
    constructor <;> linarith

lemma improve_upper_mem (a : PreRealAlgebraicNumber) :
  (improve a).upper ∈ Set.Icc a.lower a.upper := by
  unfold improve instApproximationTypePreRealAlgebraicNumber
  dsimp only
  have := a.lower_le_upper
  split_ifs
  · simp only [Set.mem_Icc]
    constructor <;> linarith
  · simp only [Set.mem_Icc, le_refl, this, and_self]

lemma improve_Icc_subset_Icc (a : PreRealAlgebraicNumber) :
  Set.Icc (improve a).lower (improve a).upper ⊆ Set.Icc a.lower a.upper :=
  HasSubset.Subset.trans Set.Icc_subset_uIcc
  (Set.uIcc_subset_Icc (improve_lower_mem a) (improve_upper_mem a))

lemma improve_toReal (a : PreRealAlgebraicNumber) : (improve a).toReal = a.toReal := by
  apply a.uniqueRoot
  · have := improve_Icc_subset_Icc a
    rw [Set.Icc_subset_Icc_iff (improve a).lower_le_upper] at this
    rify at this
    rw [← Set.Icc_subset_Icc_iff (Rat.cast_le.2 (improve a).lower_le_upper)] at this
    apply this
    exact (improve a).toReal_mem_Icc
  · rw [← improve_min_poly]
    exact (improve a).toReal_isRoot

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

structure PolyLevelNum (root : ℝ) where
  root' : ℚ
  root_eq_root' : root' = root
  poly : CPoly ℚ
  neZero : poly ≠ 0
  preservesRoot : (poly.liftTo ℝ).eval root = 0
  squarefree : Squarefree poly

def PolyLevelNum.apply {root : ℝ} (pln : PolyLevelNum root) : PreRealAlgebraicNumber where
  min_poly := pln.poly
  squarefree := pln.squarefree
  lower := pln.root'
  upper := pln.root'
  lower_le_upper := le_refl _
  ivt_condition := by
    rify
    rw [liftTo_eval, pln.root_eq_root', pln.preservesRoot]
    simp only [mul_zero, le_refl]
  deriv_nzero := by
    intro x hx
    apply CPoly.deriv_root_ne_zero_of_squarefree
    · exact pln.squarefree
    · simp only [Set.Icc_self, Set.mem_singleton_iff, pln.root_eq_root'] at hx
      exact hx ▸ pln.preservesRoot

lemma PolyLevelNum.apply_toReal {root : ℝ} (pln : PolyLevelNum root)
  : (pln.apply).toReal = root := by
  symm
  unfold PolyLevelNum.apply
  apply PreRealAlgebraicNumber.uniqueRoot
  · simp only [Set.Icc_self, ← pln.root_eq_root', Set.mem_singleton_iff]
  · simp only [pln.preservesRoot]

structure PolyLevelFun' (rootFun : ℝ → ℝ) where
  cont : Continuous rootFun
  semiMonotone : ∀ x a b, x ∈ Set.uIcc a b → rootFun x ∈ Set.uIcc (rootFun a) (rootFun b)
  rootFun' : ℚ → ℚ
  rootFun_eq_rootFun' : ∀ x : ℚ , rootFun' x = rootFun x
  polyFun : CPoly ℚ → CPoly ℚ
  neZero : ∀ p, p ≠ 0 → polyFun p ≠ 0
  preservesRoots : ∀ x f, (f.liftTo ℝ).eval x = 0 → ((polyFun f).liftTo ℝ).eval (rootFun x) = 0

structure PolyLevelFun (rootFun : ℝ → ℝ) extends PolyLevelFun' (rootFun : ℝ → ℝ) where
  squarefree : ∀ p, p ≠ 0 → Squarefree (polyFun p)

def squarefreeify {rootFun : ℝ → ℝ} (plf : PolyLevelFun' (rootFun : ℝ → ℝ)) :
  PolyLevelFun (rootFun : ℝ → ℝ) where
  cont := plf.cont
  rootFun' := plf.rootFun'
  rootFun_eq_rootFun' := plf.rootFun_eq_rootFun'
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

def isNonzeroWitness (f : CPoly ℚ) (l u : ℚ) : Prop :=
  f.lipschitz l u * (u - l) < |f.eval l|

instance (f : CPoly ℚ) (l u : ℚ) : Decidable (isNonzeroWitness f l u) := by
  unfold isNonzeroWitness
  infer_instance

lemma neZero_of_isNonzeroWitness (f : CPoly ℚ) (l u : ℚ) (hl : l ≤ u)
  (h : isNonzeroWitness f l u) : ∀ x ∈ Set.Icc ↑l ↑u, (f.liftTo ℝ).eval x ≠ 0 := by
  intro x hx h0
  have := lipschitzOnWith_iff_dist_le_mul.1 <| CPoly.lipschitz_lipschitz (f := f) (l := l) (u := u)
  specialize this l (Set.left_mem_Icc.2 (Rat.cast_le.2 hl)) x hx
  revert this
  simp only [Set.mem_Icc, h0, dist_zero_right, Real.norm_eq_abs, NNReal.coe_mk, Real.dist_eq,
    imp_false, not_le] at hx ⊢
  calc ↑(f.lipschitz l u) * |↑l - x|
  _ ≤ f.lipschitz l u * (u - l) := by
    gcongr
    · apply CPoly.lipschitz_nonneg
    · rw [abs_sub_comm, abs_of_nonneg]
      · gcongr
        exact hx.2
      · exact sub_nonneg_of_le hx.1
  _ < _ := by
    apply lt_of_lt_of_eq (by have := Real.ratCast_lt.2 h; push_cast at this; exact this)
    rw [CPoly.toPolynomial_liftTo_eval_eq_eval₂]
    simp only [toPolynomialSimp]
    rw [← Polynomial.eval_map, show ↑l = (algebraMap ℚ ℝ) l from rfl,
      Polynomial.eval_map_apply (algebraMap ℚ ℝ)]
    rfl

def isNonzeroWitness_monotone {f : CPoly ℚ} {l₁ l₂ u₁ u₂} (h : Set.Icc l₂ u₂ ⊆ Set.Icc l₁ u₁) :
  isNonzeroWitness f l₁ u₁ → isNonzeroWitness f l₂ u₂ := by
  have h_ := h
  unfold isNonzeroWitness
  intro h'
  have trivial_case : u₂ ≤ l₂ → f.lipschitz l₂ u₂ * (u₂ - l₂) < |f.eval l₂| := by
    by_cases h'' : u₂ = l₂
    · intro
      subst u₂
      ring_nf
      apply abs_pos.2
      rify
      rw [liftTo_eval]
      have : l₂ ∈ Set.Icc l₁ u₁ := by
        apply h
        exact ⟨le_refl l₂, le_refl l₂⟩
      apply neZero_of_isNonzeroWitness f l₁ u₁
      · revert this
        contrapose
        simp only [not_le, Set.mem_Icc, not_and]
        exact Trans.trans
      · exact h'
      · simp at this ⊢
        assumption
    · intro h
      have := lt_of_le_of_ne h h''
      grw [← abs_nonneg]
      apply mul_neg_of_pos_of_neg
      · rify
        apply CPoly.lipschitz_pos
      · linarith
  by_cases h'' : u₁ < l₁
  · apply trivial_case
    rw [Set.Icc_eq_empty (not_le.2 h''), Set.subset_empty_iff, Set.Icc_eq_empty_iff] at h
    apply le_of_lt
    exact not_le.1 h
  · have h_lip := (CPoly.lipschitz_lipschitz (f := f) (l := l₁) (u := u₁)).dist_le_mul l₁
      ⟨Rat.cast_le.2 (le_refl l₁), Rat.cast_le.2 (not_lt.1 h'')⟩ l₂
    by_cases h''' : u₂ ≤ l₂
    · exact trivial_case h'''
    · rw [not_lt] at h''
      rw [not_le] at h'''
      rw [Set.Icc_subset_Icc_iff (le_of_lt h''')] at h
      rify at *
      specialize h_lip <| by
        exact ⟨h.1, (le_of_lt h''').trans h.2⟩
      simp_rw [Real.dist_eq] at h_lip
      rw [abs_sub_comm (l₁ : ℝ) (l₂), abs_of_nonneg (sub_nonneg_of_le h.1)] at h_lip
      obtain ⟨h₁, h₂⟩ := h
      have : Set.uIcc l₂ u₂ ⊆ Set.uIcc l₁ u₁ := by
        simp only [Rat.cast_le, Rat.cast_lt] at h'' h'''
        rwa [Set.uIcc_of_le h'', Set.uIcc_of_lt h''']
      have h_mon := CPoly.lipschitz_monotone f _ _ _ _ this
      rify at h_mon
      grw [h_mon, show (u₂ : ℝ) - l₂ ≤ u₁ - l₁ - (l₂ - l₁) by linarith, mul_sub]
      · apply lt_sub_iff_add_lt.1
        simp only [sub_neg_eq_add]
        obtain h'' := Trans.trans h₁ (Trans.trans h''' h₂)
        apply Trans.trans (s := LE.le) h'
        grw [← h_lip, liftTo_eval, liftTo_eval, add_comm]
        apply sub_le_iff_le_add.1
        apply abs_sub_abs_le_abs_sub
      · apply CPoly.lipschitz_nonneg
      · linarith

def lower_mul_upper_subset_of_root_of_deriv_ne_zero (f : CPoly ℚ) (a b a' b' : ℚ)
  (h_ss : Set.uIcc a' b' ⊆ Set.uIcc a b) (h_er : ∃ x ∈ Set.uIcc ↑a' ↑b', (f.liftTo ℝ).eval x = 0)
  (h_nz : ∀ x ∈ Set.uIcc ↑a ↑b, (f.deriv.liftTo ℝ).eval x ≠ 0) : f.eval a' * f.eval b' ≤ 0 := by
  have : ∀ x ∈ Set.Icc ↑(min a' b') ↑(max a' b'), (f.deriv.liftTo ℝ).eval x ≠ 0 := by
    intro x ⟨hx₁, hx₂⟩
    apply h_nz x
    unfold Set.uIcc at *
    rw [Set.Icc_subset_Icc_iff min_le_max] at h_ss
    rify at *
    exact ⟨h_ss.1.trans hx₁, hx₂.trans h_ss.2⟩
  have := (lower_mul_upper_le_zero_iff_unique_root_of_deriv_non_zero f (min a' b') (max a' b')
    min_le_max this).2  (uniqueRoot_of_root_of_deriv_ne_zero f (min a' b') (max a' b') this ?_)
  · by_cases h : a' < b'
    · rwa [min_eq_left_of_lt h, max_eq_right_of_lt h] at this
    · rw [not_lt] at h
      rwa [min_eq_right h, max_eq_left h, mul_comm] at this
  · push_cast
    exact h_er

def isSufficientlyApproximated {rootFun : ℝ → ℝ}
  (plf : PolyLevelFun rootFun) (a : PreRealAlgebraicNumber) : Prop :=
  letI f := plf.polyFun a.min_poly
  isNonzeroWitness f.deriv (min (plf.rootFun' a.lower) (plf.rootFun' a.upper))
    (max (plf.rootFun' a.lower) (plf.rootFun' a.upper))

instance {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun) (a : PreRealAlgebraicNumber) :
  Decidable (isSufficientlyApproximated plf a) := by
  unfold isSufficientlyApproximated
  infer_instance

lemma PolyLevelFun.uIcc_subset {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun)
  (a : PreRealAlgebraicNumber) :
  Set.uIcc (plf.rootFun' (improve a).lower) (plf.rootFun' (improve a).upper) ⊆
  Set.uIcc (plf.rootFun' a.lower) (plf.rootFun' a.upper) := by
  apply Set.uIcc_subset_uIcc
    <;> rw [Set.mem_uIcc]
    <;> rify
    <;> simp_rw [← Set.mem_uIcc, plf.rootFun_eq_rootFun']
    <;> apply plf.semiMonotone
    <;> rw [Set.mem_uIcc]
    <;> norm_cast
    <;> rw [← Set.mem_uIcc, Set.uIcc_of_le a.lower_le_upper]
  · apply improve_lower_mem
  · apply improve_upper_mem

instance {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun) :
  isExact (isSufficientlyApproximated plf) where
  reachable := sorry
  stable a := by
    intro h
    unfold isSufficientlyApproximated
    rw [improve_min_poly]
    refine isNonzeroWitness_monotone ?_ h
    simp_rw [Set.Icc_min_max]
    apply plf.uIcc_subset

def PolyLevelFun.apply' {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun)
  (a : PreRealAlgebraicNumber) (h : isSufficientlyApproximated plf a)
  : PreRealAlgebraicNumber where
    min_poly := plf.polyFun a.min_poly
    squarefree := plf.squarefree a.min_poly a.min_poly_ne_zero
    lower := min (plf.rootFun' a.lower) (plf.rootFun' a.upper)
    upper := max (plf.rootFun' a.lower) (plf.rootFun' a.upper)
    lower_le_upper := min_le_max
    ivt_condition := by
      have := (neZero_of_isNonzeroWitness _ _ _ min_le_max h)
      apply (lower_mul_upper_le_zero_iff_unique_root_of_deriv_non_zero (plf.polyFun a.min_poly)
        (min (plf.rootFun' a.lower) (plf.rootFun' a.upper)) (max (plf.rootFun' a.lower)
        (plf.rootFun' a.upper)) min_le_max this).2
      apply uniqueRoot_of_root_of_deriv_ne_zero _ _ _ this
      refine ⟨rootFun a.toReal, ?_, ?_⟩
      · rify
        rw [Set.Icc_min_max, plf.rootFun_eq_rootFun', plf.rootFun_eq_rootFun']
        apply plf.semiMonotone
        rw [Set.uIcc_of_le <| Rat.cast_le.2 a.lower_le_upper]
        apply a.toReal_mem_Icc
      · apply plf.preservesRoots
        apply a.toReal_isRoot
    deriv_nzero := neZero_of_isNonzeroWitness _ _ _ min_le_max h

def PolyLevelFun.apply {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun)
  (a : PreRealAlgebraicNumber) : PreRealAlgebraicNumber :=
    letI a' := ApproximationType.approximate (isSufficientlyApproximated plf) a
    haveI ha' := ApproximationType.approximate_spec (isSufficientlyApproximated plf) a
    plf.apply' a' ha'

lemma PolyLevelFun.apply_toReal {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun)
  (a : PreRealAlgebraicNumber) : (plf.apply a).toReal = rootFun a.toReal := by
  unfold PolyLevelFun.apply
  rw [ApproximationType.approximate_rec (p := (isSufficientlyApproximated plf))
    (motive := fun x ↦ a.toReal = x.toReal) rfl fun hb ↦ hb ▸ (improve_toReal _).symm]
  symm
  letI a' := ApproximationType.approximate (isSufficientlyApproximated plf) a
  have h' : ApproximationType.approximate (isSufficientlyApproximated plf) a = a' := rfl
  simp_rw [h']
  unfold PolyLevelFun.apply'
  apply PreRealAlgebraicNumber.uniqueRoot
  · simp only [Rat.cast_min, Rat.cast_max, plf.rootFun_eq_rootFun', Set.Icc_min_max]
    apply plf.semiMonotone
    rw [Set.uIcc_of_le (Rat.cast_le.2 a'.lower_le_upper)]
    exact a'.toReal_mem_Icc
  · apply plf.preservesRoots
    apply a'.toReal_isRoot

structure PolyLevelFun'₂ (rootFun : ℝ → ℝ → ℝ) where
  cont : Continuous (Prod.rec rootFun)
  semiMonotone : ∀ x a b, x ∈ Set.uIcc a b → ∀ y c d, y ∈ Set.uIcc c d → rootFun x y ∈ Set.Icc
    (min (min (rootFun a c) (rootFun a d)) (min (rootFun b c) (rootFun b d)))
    (max (max (rootFun a c) (rootFun a d)) (max (rootFun b c) (rootFun b d)))
  rootFun' : ℚ → ℚ → ℚ
  rootFun_eq_rootFun' : ∀ x y : ℚ , rootFun' x y = rootFun x y
  polyFun : CPoly ℚ → CPoly ℚ → CPoly ℚ
  neZero : ∀ p, p ≠ 0 → ∀ q, q ≠ 0 → polyFun p q ≠ 0
  preservesRoots : ∀ x f, (f.liftTo ℝ).eval x = 0 → ∀ y g, (g.liftTo ℝ).eval y = 0 →
    ((polyFun f g).liftTo ℝ).eval (rootFun x y) = 0

structure PolyLevelFun₂ (rootFun : ℝ → ℝ → ℝ) extends PolyLevelFun'₂ (rootFun : ℝ → ℝ → ℝ) where
  squarefree : ∀ p, p ≠ 0 → ∀ q, q ≠ 0 → Squarefree (polyFun p q)

def squarefreeify₂ {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun'₂ (rootFun : ℝ → ℝ → ℝ)) :
  PolyLevelFun₂ (rootFun : ℝ → ℝ → ℝ) where
  cont := plf.cont
  rootFun' := plf.rootFun'
  rootFun_eq_rootFun' := plf.rootFun_eq_rootFun'
  semiMonotone := plf.semiMonotone
  polyFun p q := plf.polyFun p q / gcd (plf.polyFun p q) (plf.polyFun p q).deriv
  neZero := by
    intro p hp q hq
    have := CPoly.squarefree_div_gcd_deriv (plf.polyFun p q) (plf.neZero p hp q hq)
    exact Squarefree.ne_zero this
  preservesRoots := by
    intro x f hf y g hg
    apply CPoly.eval_div_gcd_deriv_eq_zero_of_eval_eq_zero
    exact plf.preservesRoots x f hf y g hg
  squarefree := by
    intro p hp q hq
    apply CPoly.squarefree_div_gcd_deriv (plf.polyFun p q) (plf.neZero p hp q hq)

def isSufficientlyApproximated₂ {rootFun : ℝ → ℝ → ℝ}
  (plf : PolyLevelFun₂ rootFun) (ab : PreRealAlgebraicNumber × PreRealAlgebraicNumber) : Prop :=
  letI a := ab.1
  letI b := ab.2
  letI f := plf.polyFun a.min_poly b.min_poly
  letI lower := (min (min (plf.rootFun' a.lower b.lower) (plf.rootFun' a.lower b.upper))
    (min (plf.rootFun' a.upper b.lower) (plf.rootFun' a.upper b.upper)))
  letI upper := (max (max (plf.rootFun' a.lower b.lower) (plf.rootFun' a.lower b.upper))
    (max (plf.rootFun' a.upper b.lower) (plf.rootFun' a.upper b.upper)))
  isNonzeroWitness f.deriv lower upper

instance {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun₂ rootFun)
  (ab : PreRealAlgebraicNumber × PreRealAlgebraicNumber) :
  Decidable (isSufficientlyApproximated₂ plf ab) := by
  unfold isSufficientlyApproximated₂
  infer_instance

instance {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun₂ rootFun) :
  isExact (isSufficientlyApproximated₂ plf) where
  reachable := sorry
  stable := sorry

def PolyLevelFun₂.apply' {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun₂ rootFun)
  (a b : PreRealAlgebraicNumber) (h : isSufficientlyApproximated₂ plf (a, b))
  : PreRealAlgebraicNumber where
    min_poly := plf.polyFun a.min_poly b.min_poly
    squarefree := plf.squarefree a.min_poly a.min_poly_ne_zero b.min_poly b.min_poly_ne_zero
    lower := (min (min (plf.rootFun' a.lower b.lower) (plf.rootFun' a.lower b.upper))
    (min (plf.rootFun' a.upper b.lower) (plf.rootFun' a.upper b.upper)))
    upper := (max (max (plf.rootFun' a.lower b.lower) (plf.rootFun' a.lower b.upper))
    (max (plf.rootFun' a.upper b.lower) (plf.rootFun' a.upper b.upper)))
    lower_le_upper := by
      simp only [le_sup_iff, inf_le_iff, le_refl, true_or, or_true, or_self]
    ivt_condition := by
      have := neZero_of_isNonzeroWitness _ _ _
        (by simp only [le_sup_iff, inf_le_iff, le_refl, true_or, or_true, or_self]) h
      apply (lower_mul_upper_le_zero_iff_unique_root_of_deriv_non_zero
        (plf.polyFun a.min_poly b.min_poly) (min (min (plf.rootFun' a.lower b.lower)
        (plf.rootFun' a.lower b.upper)) (min (plf.rootFun' a.upper b.lower)
        (plf.rootFun' a.upper b.upper))) (max (max (plf.rootFun' a.lower b.lower)
        (plf.rootFun' a.lower b.upper)) (max (plf.rootFun' a.upper b.lower)
        (plf.rootFun' a.upper b.upper)))
        (by simp only [le_sup_iff, inf_le_iff, le_refl, true_or, or_true, or_self]) this).2
      apply uniqueRoot_of_root_of_deriv_ne_zero _ _ _ this
      refine ⟨rootFun a.toReal b.toReal, ?_, ?_⟩
      · rify
        simp_rw [plf.rootFun_eq_rootFun']
        apply plf.semiMonotone
        · rw [Set.uIcc_of_le <| Rat.cast_le.2 a.lower_le_upper]
          apply a.toReal_mem_Icc
        · rw [Set.uIcc_of_le <| Rat.cast_le.2 b.lower_le_upper]
          apply b.toReal_mem_Icc
      · dsimp only
        apply plf.preservesRoots
        · apply a.toReal_isRoot
        · apply b.toReal_isRoot
    deriv_nzero := neZero_of_isNonzeroWitness _ _ _
      (by simp only [le_sup_iff, inf_le_iff, le_refl, true_or, or_true, or_self]) h

def PolyLevelFun₂.apply {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun₂ rootFun)
  (a b : PreRealAlgebraicNumber) : PreRealAlgebraicNumber :=
    letI ab := ApproximationType.approximate (isSufficientlyApproximated₂ plf) (a, b)
    haveI hab := ApproximationType.approximate_spec (isSufficientlyApproximated₂ plf) (a, b)
    plf.apply' ab.1 ab.2 hab

lemma PolyLevelFun₂.apply_toReal {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun₂ rootFun)
  (a b : PreRealAlgebraicNumber) : (plf.apply a b).toReal = rootFun a.toReal b.toReal := by
  have := (plf.apply a b).lower_le_upper
  unfold PolyLevelFun₂.apply at this ⊢
  rw [ApproximationType.approximate_rec (p := (isSufficientlyApproximated₂ plf)) (a0 := (a, b))
    (motive := fun x ↦ a.toReal = x.1.toReal) rfl fun hb ↦ hb ▸ (improve_toReal _).symm,
    ApproximationType.approximate_rec (p := (isSufficientlyApproximated₂ plf)) (a0 := (a, b))
    (motive := fun x ↦ b.toReal = x.2.toReal) rfl fun hb ↦ hb ▸ (improve_toReal _).symm]
  symm
  letI ab := ApproximationType.approximate (isSufficientlyApproximated₂ plf) (a, b)
  have h' : ApproximationType.approximate (isSufficientlyApproximated₂ plf) (a, b) = ab := rfl
  simp_rw [h'] at this ⊢
  unfold PolyLevelFun₂.apply' at this ⊢
  apply PreRealAlgebraicNumber.uniqueRoot
  · simp only [Rat.cast_min, Rat.cast_max, plf.rootFun_eq_rootFun'] at this ⊢
    apply plf.semiMonotone
    · rw [Set.uIcc_of_le (Rat.cast_le.2 ab.1.lower_le_upper)]
      exact ab.1.toReal_mem_Icc
    · rw [Set.uIcc_of_le (Rat.cast_le.2 ab.2.lower_le_upper)]
      exact ab.2.toReal_mem_Icc
  · simp only
    apply plf.preservesRoots
    · apply ab.1.toReal_isRoot
    · apply ab.2.toReal_isRoot

def zero_pln : PolyLevelNum 0 where
  root' := 0
  root_eq_root' := Rat.cast_zero
  poly := CPoly.X
  neZero := by decide
  preservesRoot := by
    rw [← Rat.cast_zero, ← liftTo_eval]
    simp only [CPoly.toPolynomial_eval, CPoly.toPolynomial_X, Polynomial.eval_X, Rat.cast_zero]
  squarefree := by
    simp [toPolynomialSimp]
    apply Irreducible.squarefree
    apply Polynomial.irreducible_X

def add_plf : PolyLevelFun₂ (· + ·) := squarefreeify₂ {
  cont := by continuity
  semiMonotone := sorry
  rootFun' := (· + ·)
  rootFun_eq_rootFun' := Rat.cast_add
  polyFun := sorry
  neZero := sorry
  preservesRoots := sorry
}

def neg_plf : PolyLevelFun (-·) := squarefreeify {
  cont := by continuity
  semiMonotone := by
    intro a b c
    unfold Set.uIcc
    simp only [Set.mem_Icc, inf_le_iff, le_sup_iff, neg_le_neg_iff, and_imp]
    tauto
  rootFun' := (-·)
  rootFun_eq_rootFun' := Rat.cast_neg
  polyFun := fun p ↦ (p.liftTo (CPoly ℚ)).eval (- CPoly.X : CPoly ℚ)
  neZero := sorry
  preservesRoots := sorry
}

def one_pln : PolyLevelNum 1 where
  root' := 1
  root_eq_root' := Rat.cast_one
  poly := CPoly.X - CPoly.const 1
  neZero := by decide
  preservesRoot := by
    rw [← Rat.cast_one (α := ℝ), ← liftTo_eval]
    simp only [toPolynomialSimp, map_one, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_one, sub_self, Rat.cast_zero]
  squarefree := by
    apply Irreducible.squarefree
    rw [CPoly.toPolynomial_Irreducible]
    apply Polynomial.irreducible_of_degree_eq_one
    rw [← CPoly.toPolynomial_degree]
    decide

def mul_plf : PolyLevelFun₂ (· * ·) := squarefreeify₂ {
  cont := by continuity
  semiMonotone := sorry
  rootFun' := (· * ·)
  rootFun_eq_rootFun' := Rat.cast_mul
  polyFun := sorry
  neZero := sorry
  preservesRoots := sorry
}

def equiv : Setoid PreRealAlgebraicNumber where
  r a b := a.toReal = b.toReal
  iseqv := InvImage.equivalence _ _ eq_equivalence

abbrev RealAlgebraicNumber := Quotient equiv

noncomputable def RealAlgebraicNumber.toReal (x : RealAlgebraicNumber) : ℝ :=
  Quotient.liftOn x PreRealAlgebraicNumber.toReal fun _ _ ↦ id

lemma RealAlgebraicNumber.toReal_injective : Function.Injective RealAlgebraicNumber.toReal := by
  intro a b ha
  induction a, b using Quotient.ind₂ with
  | h a b => exact Quotient.sound ha

def PolyLevelNum.lift {root : ℝ} (pln : PolyLevelNum root) : RealAlgebraicNumber := ⟦pln.apply⟧

lemma PolyLevelNum.lift_toReal {root : ℝ} (pln : PolyLevelNum root) : pln.lift.toReal = root :=
  pln.apply_toReal

def PolyLevelFun.lift {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun) :
  RealAlgebraicNumber → RealAlgebraicNumber := Quotient.lift (fun x ↦ ⟦plf.apply x⟧) <| by
    intro a b ha
    apply Quotient.sound' (s₁ := equiv)
    change (plf.apply a).toReal = (plf.apply b).toReal
    simp_rw [plf.apply_toReal]
    apply congrArg rootFun ha

lemma PolyLevelFun.lift_toReal {rootFun : ℝ → ℝ} (plf : PolyLevelFun rootFun)
  (a : RealAlgebraicNumber) : (plf.lift a).toReal = rootFun a.toReal := by
  induction a using Quotient.ind
  apply plf.apply_toReal

def PolyLevelFun₂.lift {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun₂ rootFun) :
  RealAlgebraicNumber → RealAlgebraicNumber → RealAlgebraicNumber :=
  Quotient.lift₂ (fun x y ↦ ⟦plf.apply x y⟧) <| by
    intro a₁ b₁ a₂ b₂ ha hb
    apply Quotient.sound' (s₁ := equiv)
    change (plf.apply a₁ b₁).toReal = (plf.apply a₂ b₂).toReal
    simp_rw [plf.apply_toReal]
    apply congrArg₂ rootFun ha hb

lemma PolyLevelFun₂.lift_toReal {rootFun : ℝ → ℝ → ℝ} (plf : PolyLevelFun₂ rootFun)
  (a b : RealAlgebraicNumber) : (plf.lift a b).toReal = rootFun a.toReal b.toReal := by
  induction a, b using Quotient.ind₂
  apply plf.apply_toReal

namespace RealAlgebraicNumber

instance : Zero RealAlgebraicNumber where
  zero := zero_pln.lift

lemma zero_def : 0 = zero_pln.lift := rfl

instance : Add RealAlgebraicNumber where
  add := add_plf.lift

lemma add_def (a b : RealAlgebraicNumber) : a + b = add_plf.lift a b := rfl

instance : Neg RealAlgebraicNumber where
  neg := neg_plf.lift

lemma neg_def (a : RealAlgebraicNumber) : -a = neg_plf.lift a := rfl

instance : One RealAlgebraicNumber where
  one := one_pln.lift

lemma one_def : 1 = one_pln.lift := rfl

instance : Mul RealAlgebraicNumber where
  mul := mul_plf.lift

lemma mul_def (a b : RealAlgebraicNumber) : a * b = mul_plf.lift a b := rfl

instance : CommRing RealAlgebraicNumber where
  add_assoc := by
    intro a b c
    induction a, b, c using Quotient.inductionOn₃
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [add_def, add_plf.lift_toReal]
    ring
  zero_add := by
    intro a
    induction a using Quotient.inductionOn
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [add_def, add_plf.lift_toReal, zero_def, zero_pln.lift_toReal]
    ring
  add_zero := by
    intro a
    induction a using Quotient.inductionOn
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [add_def, add_plf.lift_toReal, zero_def, zero_pln.lift_toReal]
    ring
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    intro a
    induction a using Quotient.inductionOn
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [add_def, add_plf.lift_toReal, zero_def, zero_pln.lift_toReal, neg_def,
      neg_plf.lift_toReal]
    ring
  add_comm := by
    intro a b
    induction a, b using Quotient.inductionOn₂
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [add_def, add_plf.lift_toReal]
    ring
  left_distrib := by
    intro a b c
    induction a, b, c using Quotient.inductionOn₃
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal, add_def, add_plf.lift_toReal, mul_plf.lift_toReal]
    ring
  right_distrib := by
    intro a b c
    induction a, b, c using Quotient.inductionOn₃
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal, add_def, add_plf.lift_toReal, mul_plf.lift_toReal]
    ring
  zero_mul := by
    intro a
    induction a using Quotient.inductionOn
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal, zero_def, zero_pln.lift_toReal]
    ring
  mul_zero := by
    intro a
    induction a using Quotient.inductionOn
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal, zero_def, zero_pln.lift_toReal]
    ring
  mul_assoc :=  by
    intro a b c
    induction a, b, c using Quotient.inductionOn₃
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal]
    ring
  one_mul := by
    intro a
    induction a using Quotient.inductionOn
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal, one_def, one_pln.lift_toReal]
    ring
  mul_one := by
    intro a
    induction a using Quotient.inductionOn
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal, one_def, one_pln.lift_toReal]
    ring
  mul_comm := by
    intro a b
    induction a, b using Quotient.inductionOn₂
    apply RealAlgebraicNumber.toReal_injective
    simp_rw [mul_def, mul_plf.lift_toReal]
    ring

instance : DecidableEq RealAlgebraicNumber := by
  intro a b
  rw [← sub_eq_zero]
  induction a - b using Quotient.recOnSubsingleton
  · rw [zero_def, ← toReal_injective.eq_iff, zero_pln.lift_toReal, toReal, Quotient.liftOn_mk]
    infer_instance
  · infer_instance







end RealAlgebraicNumber
