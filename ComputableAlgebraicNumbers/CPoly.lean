import Mathlib

namespace CPoly

private def _noLeadingZero {R : Type*} [CommSemiring R] : List R → Prop
  | []     => True
  | x :: _ => x ≠ 0

def noTailingZero {R : Type*} [CommSemiring R] (l : List R) : Prop :=
  _noLeadingZero l.reverse

end CPoly

@[ext]
structure CPoly (R : Type*) [CommSemiring R] where
  coefs : List R -- `[c₀,c₁,c₂,...,cₙ]` and then `∑ Xⁱcᵢ`
  condition : CPoly.noTailingZero coefs

namespace CPoly

private def _removeLeadingZeros {R : Type*} [DecidableEq R] [CommSemiring R] : List R → List R
  | []      => []
  | x :: xs => if x = 0 then _removeLeadingZeros xs else x :: xs


private lemma _removeLeadingZeros_nil {R : Type*} [DecidableEq R] [CommSemiring R]
  : _removeLeadingZeros (R := R) [] = [] := rfl


private lemma _removeLeadingZeros_cons {R : Type*} [DecidableEq R] [CommSemiring R]
  {x : R} {xs : List R}
  : _removeLeadingZeros (x :: xs) = if x = 0 then _removeLeadingZeros xs else x :: xs := rfl


private lemma _noLeadingZero_removeLeadingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
    (l : List R) : _noLeadingZero (_removeLeadingZeros l) := by
  induction l with
  | nil => trivial
  | cons x xs ih =>
    unfold _removeLeadingZeros
    rw [apply_ite _noLeadingZero]
    by_cases h : x = 0
    · rwa [if_pos h]
    · rwa [if_neg h]

private lemma _eq_removeLeadingZeros_of_noLeading_zeros {R : Type*} [DecidableEq R] [CommSemiring R]
    {l : List R} (h : _noLeadingZero l) : l = _removeLeadingZeros l := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
  unfold _removeLeadingZeros
  rw [if_neg h]

def removeTailingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
    (l : List R) : List R :=
  (_removeLeadingZeros l.reverse).reverse


lemma noTailingZero_removeTailingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
    {l : List R} : noTailingZero (removeTailingZeros l) := by
  unfold noTailingZero removeTailingZeros
  rw [List.reverse_reverse]
  apply _noLeadingZero_removeLeadingZeros


def toCPoly {R : Type*} [DecidableEq R] [CommSemiring R]
  (l : List R) : CPoly R :=
  ⟨removeTailingZeros l, noTailingZero_removeTailingZeros⟩

lemma noTailingZero_iff {R : Type*} [DecidableEq R] [CommSemiring R] {l : List R}
  : noTailingZero l ↔ l = removeTailingZeros l := ⟨
    (List.reverse_eq_iff.1 <| _eq_removeLeadingZeros_of_noLeading_zeros ·),
    (· ▸ noTailingZero_removeTailingZeros)
  ⟩

lemma noTailingZero_iff' {R : Type*} [DecidableEq R] [CommSemiring R] {l : List R}
  : noTailingZero l ↔ l = (toCPoly l).coefs := noTailingZero_iff


lemma coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : CPoly R}
  : removeTailingZeros a.coefs = a.coefs := (noTailingZero_iff'.1 a.condition).symm


lemma removeTailingZeros_removeTailingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
  {l : List R} : removeTailingZeros (removeTailingZeros l) = removeTailingZeros l :=
  (noTailingZero_iff.1 noTailingZero_removeTailingZeros).symm


private lemma _removeLeadingZeros_removeLeadingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
  (l : List R) : _removeLeadingZeros (_removeLeadingZeros l) = _removeLeadingZeros l := by
  rw [←l.reverse_reverse]
  refine List.reverse_inj.1 (Eq.trans ?_ removeTailingZeros_removeTailingZeros)
  simp only [List.reverse_reverse, removeTailingZeros]


lemma removeTailingZeros_nil {R : Type*} [DecidableEq R] [CommSemiring R]
  : removeTailingZeros (R := R) [] = [] := rfl

private lemma _removeLeadingZeros_append_ne_zero {R : Type*} [DecidableEq R] [CommSemiring R]
  (a : R) {as : List R} (h : a ≠ 0)
  : _removeLeadingZeros (as ++ [a]) = _removeLeadingZeros as ++ [a] := by
  induction as with
  | nil => simp only [List.nil_append, _removeLeadingZeros_cons, h, ↓reduceIte,
    _removeLeadingZeros_nil]
  | cons head tail ih =>
  by_cases h' : head = 0
  · simp only [h', List.cons_append, _removeLeadingZeros_cons, ↓reduceIte, ih]
  · simp only [List.cons_append, _removeLeadingZeros_cons, h', ↓reduceIte]

lemma removeTailingZeros_cons_of_ne_zero {R : Type*} [DecidableEq R] [CommSemiring R]
  {a : R} {as : List R} (h : a ≠ 0)
  : removeTailingZeros (a :: as) = a :: removeTailingZeros as := by
  simp only [removeTailingZeros, List.reverse_cons, List.reverse_eq_cons_iff, List.reverse_reverse]
  exact _removeLeadingZeros_append_ne_zero a h

private lemma _removeLeadingZeros_append_zero_ite {R : Type*} [DecidableEq R] [CommSemiring R]
  (as : List R) : _removeLeadingZeros (as ++ [0]) =
    if _removeLeadingZeros as = []
    then []
    else _removeLeadingZeros as ++ [0]
  := by
  induction as with
  | nil => simp only [List.nil_append, _removeLeadingZeros_cons, ↓reduceIte,
    _removeLeadingZeros_nil]
  | cons head tail ih =>
    by_cases h₁ : _removeLeadingZeros tail = []
    · rw [if_pos h₁] at ih
      by_cases h₂ : head = 0
      · simp only [h₂, List.cons_append, _removeLeadingZeros_cons, ↓reduceIte, ih, h₁]
      · simp only [List.cons_append, _removeLeadingZeros_cons, h₂, ↓reduceIte, reduceCtorEq]
    · rw [if_neg h₁] at ih
      by_cases h₂ : head = 0
      · simp only [h₂, List.cons_append, _removeLeadingZeros_cons, ↓reduceIte, ih, h₁]
      · simp only [List.cons_append, _removeLeadingZeros_cons, h₂, ↓reduceIte, reduceCtorEq]

lemma removeTailingZeros_zero_cons_ite {R : Type*} [DecidableEq R] [CommSemiring R]
  {as : List R} : removeTailingZeros (0 :: as) =
    if removeTailingZeros as = []
    then []
    else 0 :: removeTailingZeros as
  := by
  have h₁ : removeTailingZeros (0 :: as) = (_removeLeadingZeros (as.reverse ++ [0])).reverse := by
    simp only [removeTailingZeros, List.reverse_cons]
  have h₂ : removeTailingZeros as = (_removeLeadingZeros as.reverse).reverse := by
    simp only [removeTailingZeros]
  have h₃ : 0 :: removeTailingZeros as = (_removeLeadingZeros as.reverse ++ [0]).reverse := by
    simp only [removeTailingZeros, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
  rw [h₃, h₂, h₁]
  apply List.reverse_injective
  rw [apply_ite List.reverse]
  simp only [List.reverse_reverse, List.reverse_eq_nil_iff, List.reverse_nil]
  apply _removeLeadingZeros_append_zero_ite


lemma removeTailingZeros_zero_cons_of_removeTailingZeros
  {R : Type*} [DecidableEq R] [CommSemiring R]
  {as : List R} (h : removeTailingZeros as = []) : removeTailingZeros (0 :: as) = [] := by
  rw [removeTailingZeros_zero_cons_ite, if_pos h]


lemma cons_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {as : List R}
  : removeTailingZeros (a :: removeTailingZeros as) = removeTailingZeros (a :: as) := by
  by_cases h : a = 0
  · simp only [h, removeTailingZeros_zero_cons_ite, removeTailingZeros_removeTailingZeros]
  · simp only [removeTailingZeros_cons_of_ne_zero h, removeTailingZeros_removeTailingZeros]

lemma cons_coh' {R : Type*} [DecidableEq R] [CommSemiring R]
  {a b : R} {as bs : List R} (h : a = b) (hs : removeTailingZeros as = removeTailingZeros bs)
  : removeTailingZeros (a :: as) = removeTailingZeros (b :: bs) := by
  rw [h, ←cons_coh, hs, cons_coh]

lemma noTailingZero_tail {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) (as : List R) :
  CPoly.noTailingZero (a :: as) → CPoly.noTailingZero as := by
  simp only [CPoly.noTailingZero_iff]
  intro h
  by_cases h0 : a = 0
  · rw [h0, CPoly.removeTailingZeros_zero_cons_ite] at h
    split_ifs at h
    exact (List.cons_inj_right 0).1 h
  · rw [CPoly.removeTailingZeros_cons_of_ne_zero h0] at h
    exact (List.cons_inj_right a).1 h

lemma removeTailingZero_tail {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) (as : List R) :
  removeTailingZeros (a :: as) = [] → removeTailingZeros as = [] := by
  intro h
  by_cases h0 : a = 0
  · subst a
    rw [CPoly.removeTailingZeros_zero_cons_ite] at h
    split_ifs at h
    assumption
  · rw [CPoly.removeTailingZeros_cons_of_ne_zero h0] at h
    contradiction

lemma coefs_toCPoly {R : Type*} [DecidableEq R] [CommSemiring R] (a : List R) :
  (toCPoly a).coefs = removeTailingZeros a := rfl

lemma getLast_ne_zero_of_noTailingZero {R : Type*} [DecidableEq R] [CommSemiring R] (a : List R)
  (ha : CPoly.noTailingZero a) (h_ne_nil : a ≠ []) : a.getLast h_ne_nil ≠ 0 := by
  induction a with
  | nil => contradiction
  | cons head tail ih =>
    by_cases h : tail = []
    · subst tail
      simp only [List.getLast_singleton, ne_eq]
      intro h
      subst head
      simp only [CPoly.noTailingZero_iff, CPoly.removeTailingZeros_nil,
        CPoly.removeTailingZeros_zero_cons_of_removeTailingZeros, List.cons_ne_self] at ha
    · specialize ih (noTailingZero_tail head tail ha) h
      rwa [List.getLast_cons h]

lemma length_le_of_finsupp_eq {R : Type*} [DecidableEq R] [CommSemiring R] (a b : List R)
  (ha : CPoly.noTailingZero a) (h : a.toFinsupp = b.toFinsupp) :
  a.length ≤ b.length := by
    by_contra h'
    simp only [not_le] at h'
    have a_ne_nil : a ≠ [] := by
      intro h''
      have := (h'' ▸ List.length_nil) ▸ h'
      contradiction
    have : a.getLast a_ne_nil ≠ 0 := getLast_ne_zero_of_noTailingZero a ha a_ne_nil
    have : a.length - 1 ∈ a.toFinsupp.support := by
      rw [List.getLast_eq_getElem] at this
      simp only [Finsupp.mem_support_iff, List.toFinsupp_apply, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (Nat.sub_one_lt_of_lt h')]
      simp only [Option.getD_some, ne_eq, this, not_false_eq_true]
    have := h ▸ this
    revert this
    have : a.length - 1 ≥ b.length := Nat.le_sub_one_of_lt h'
    simp only [Finsupp.mem_support_iff, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none this, Option.getD_none, ne_eq, not_true_eq_false, imp_self]

lemma getD_eq_non_of_removeTailingZero_eq_nil {R : Type*} [CommSemiring R] [DecidableEq R]
  (a : List R) (h : CPoly.removeTailingZeros a = []) (n : ℕ) : a[n]?.getD 0 = 0 := by
  induction a generalizing n with
  | nil => rfl
  | cons head tail ih =>
    specialize ih (removeTailingZero_tail head tail h)
    induction n with
    | zero =>
      simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        getElem?_pos, List.getElem_cons_zero, Option.getD_some]
      by_contra h'
      rw [CPoly.removeTailingZeros_cons_of_ne_zero h'] at h
      contradiction
    | succ n _ => simp only [List.getElem?_cons_succ, ih n]

lemma toFinsupp_coh {R : Type*} [CommSemiring R] [DecidableEq R] (a : List R) :
  (CPoly.removeTailingZeros a).toFinsupp = a.toFinsupp := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    ext n
    induction n with
    | zero =>
      by_cases h' : head = 0
      · subst head
        simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.length_cons,
          lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos,
          List.getElem_cons_zero, Option.getD_some, CPoly.removeTailingZeros_zero_cons_ite]
        split_ifs
        · simp only [List.length_nil, lt_self_iff_false, not_false_eq_true, getElem?_neg,
          Option.getD_none]
        · simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
          getElem?_pos, List.getElem_cons_zero, Option.getD_some]
      · simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.length_cons,
        lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, CPoly.removeTailingZeros_cons_of_ne_zero h']
    | succ n _ =>
      have : tail.toFinsupp n = (CPoly.removeTailingZeros tail).toFinsupp n := congrFun
        (congrArg DFunLike.coe ih.symm) n
      simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD] at this
      by_cases h' : head = 0
      · subst head
        simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
          CPoly.removeTailingZeros_zero_cons_ite]
        split_ifs with h
        · simp only [getD_eq_non_of_removeTailingZero_eq_nil tail h, Option.getD_none,
          List.length_nil, not_lt_zero', not_false_eq_true, getElem?_neg]
        · simp only [this, List.getElem?_cons_succ]
      · simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, this,
          CPoly.removeTailingZeros_cons_of_ne_zero h']

def toPolynomial {R : Type*} [CommSemiring R] [DecidableEq R] (a : CPoly R) :
  Polynomial R := ⟨a.coefs.toFinsupp⟩

lemma toPolynomial_inj {R : Type*} [CommSemiring R] [DecidableEq R] :
  Function.Injective (CPoly.toPolynomial (R := R)) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ heq
  unfold toPolynomial at heq
  rw [Polynomial.ofFinsupp.injEq] at heq
  simp only at heq
  have hlen : a.length = b.length := by
    apply le_antisymm <;> apply length_le_of_finsupp_eq <;> try assumption
    exact heq.symm
  ext i r
  simp only
  by_cases h : i < a.length
  · have h' := hlen ▸ h
    rwa [← List.getElem_eq_iff h, ← List.toFinsupp_apply_lt,
      ← List.getElem_eq_iff, ← List.toFinsupp_apply_lt, heq]
  · rw [List.getElem?_eq_none (not_lt.1 h), List.getElem?_eq_none (hlen ▸ not_lt.1 h)]

lemma toPolynomial_sur {R : Type*} [CommSemiring R] [DecidableEq R] :
  Function.Surjective (CPoly.toPolynomial (R := R)) := by
  intro p
  let a := (List.range p.natDegree.succ).map p.toFinsupp
  use toCPoly a
  ext n
  unfold toPolynomial toCPoly Polynomial.coeff
  subst a
  simp only [Nat.succ_eq_add_one, toFinsupp_coh, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  by_cases h : p.natDegree + 1 ≤ n
  · rw [List.getElem?_eq_none (List.length_range (n := p.natDegree + 1).symm ▸ h)]
    simp only [Option.map_none, Option.getD_none]
    unfold Polynomial.natDegree Polynomial.degree at h
    let deg := p.support.max
    have : deg = p.support.max := rfl
    rw [← this] at h
    revert h this
    induction deg with
    | bot =>
      simp only [WithBot.unbotD_bot, _root_.zero_add]
      intro h h'
      have h'' := Finset.max_eq_bot.1 h'.symm
      unfold Polynomial.support at h''
      simp only [Finsupp.support_eq_empty] at h''
      rw [h'', Finsupp.zero_apply]
    | coe a =>
      simp only [WithBot.unbotD_coe]
      intro h h'
      symm
      by_contra h''
      rw [← ne_eq, ← Finsupp.mem_support_iff] at h''
      unfold Polynomial.support at h'
      have := WithBot.coe_le_coe.1 (h' ▸ Finset.le_max h'')
      linarith
  · simp only [List.getElem?_eq_getElem (List.length_range (n := p.natDegree + 1).symm ▸
      not_le.1 h), List.getElem_range, Option.map_some, Option.getD_some]

lemma toPolynomial_bij {R : Type*} [CommSemiring R] [DecidableEq R] :
  Function.Bijective (CPoly.toPolynomial (R := R)) := ⟨toPolynomial_inj, toPolynomial_sur⟩

noncomputable def toPolynomial_Equiv {R : Type*} [CommSemiring R] [DecidableEq R] :
  CPoly R ≃ Polynomial R := Equiv.ofBijective toPolynomial toPolynomial_bij

def list_add (R : Type*) [CommSemiring R] : List R → List R → List R
  | []     , bs      => bs
  | as     , []      => as
  | a :: as, b :: bs => (a + b) :: (list_add R as bs)


lemma nil_list_add {R : Type*} [CommSemiring R] {a : List R} : list_add R [] a = a := rfl


lemma list_add_nil {R : Type*} [CommSemiring R] {a : List R} : list_add R a [] = a :=
  a.rec rfl (fun _ _ _ ↦ rfl)


lemma cons_list_add_cons {R : Type*} [CommSemiring R] {a b : R} {as bs : List R}
  : list_add R (a :: as) (b :: bs) = (a + b) :: (list_add R as bs) := rfl

lemma list_add_toFinsupp {R : Type*} [CommSemiring R] [DecidableEq R] (a b : List R) (n : ℕ) :
  (list_add R a b).toFinsupp n = a.toFinsupp n + b.toFinsupp n := by
  induction a generalizing b n with
  | nil => simp only [nil_list_add, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
    List.toFinsupp_nil, Finsupp.coe_zero, Pi.zero_apply, zero_add]
  | cons a0 as ih =>
  induction b generalizing n with
  | nil => simp only [list_add_nil, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
    List.toFinsupp_nil, Finsupp.coe_zero, Pi.zero_apply, add_zero]
  | cons b0 bs _ =>
  induction n with
  | zero => rfl
  | succ n _ =>
  simp only [cons_list_add_cons, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ] at ih ⊢
  apply ih


def add {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_add R a.coefs b.coefs)

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Add (CPoly R) := ⟨add⟩


lemma add_def {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : a + b = add a b := rfl

@[simp]
lemma toPolynomial_add {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) :
  toPolynomial (a + b) = toPolynomial a + toPolynomial b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  unfold toPolynomial
  ext n
  simp only [add_def, add, Polynomial.coeff_ofFinsupp, Polynomial.coeff_add]
  refine coefs_toCPoly (list_add R a b) ▸ ?_
  rw [toFinsupp_coh, list_add_toFinsupp]


def zero {R : Type*} [DecidableEq R] [CommSemiring R] : CPoly R := ⟨[], trivial⟩

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Zero (CPoly R) := ⟨zero⟩


lemma zero_def {R : Type*} [DecidableEq R] [CommSemiring R] : (0 : CPoly R) = zero := rfl

@[simp]
lemma toPolynomial_zero {R : Type*} [DecidableEq R] [CommSemiring R] :
  toPolynomial (0 : CPoly R) = 0 := by
  simp only [toPolynomial, zero_def, zero, List.toFinsupp_nil, Polynomial.ofFinsupp_zero]

def list_smul (R : Type*) [CommSemiring R] : R → List R → List R
  | _,      [] => []
  | r, a :: as => (r*a) :: (list_smul R r as)


lemma list_smul_nil {R : Type*} [CommSemiring R] {a : R}
  : list_smul R a [] = [] := rfl


lemma list_smul_cons {R : Type*} [CommSemiring R] {a b : R} {bs : List R}
  : list_smul R a (b :: bs) = a * b :: list_smul R a bs := rfl

lemma list_smul_toFinsupp {R : Type*} [CommSemiring R] [DecidableEq R] (a : R) (b : List R)
  (n : ℕ) : (list_smul R a b).toFinsupp n = a * b.toFinsupp n := by
  induction b generalizing n with
  | nil => simp only [list_smul_nil, List.toFinsupp_nil, Finsupp.coe_zero, Pi.zero_apply, mul_zero]
  | cons head tail ih =>
  induction n with
  | zero => rfl
  | succ n _ =>
  simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, list_smul_cons,
    List.getElem?_cons_succ] at ih ⊢
  apply ih


def smul {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) (b : CPoly R) : CPoly R :=
  toCPoly (list_smul R a b.coefs)

instance {R : Type*} [DecidableEq R] [CommSemiring R] : SMul R (CPoly R) := ⟨smul⟩


lemma smul_def {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) (b : CPoly R)
  : a • b = smul a b := rfl

@[simp]
lemma toPolynomial_smul {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) (b : CPoly R) :
  toPolynomial (a • b) = a • toPolynomial b := by
  obtain ⟨b, hb⟩ := b
  unfold toPolynomial
  ext n
  simp only [smul_def, smul, Polynomial.coeff_ofFinsupp, Polynomial.coeff_smul, smul_eq_mul]
  refine coefs_toCPoly (list_smul R a b) ▸ ?_
  rw [toFinsupp_coh, list_smul_toFinsupp]

def list_mul (R : Type*) [CommSemiring R] : List R → List R → List R
  | []     , _  => []
  | a :: as, bs => list_add R (list_smul R a bs) (0 :: list_mul R as bs)


lemma nil_list_mul {R : Type*} [CommSemiring R] {a : List R} : list_mul R [] a = [] := rfl


lemma cons_list_mul {R : Type*} [CommSemiring R] {a : R} {as bs : List R}
  : list_mul R (a :: as) bs = list_add R (list_smul R a bs) (0 :: list_mul R as bs) := rfl

lemma list_mul_toFinsupp {R : Type*} [CommSemiring R] [DecidableEq R] (a b : List R) (n : ℕ) :
  (list_mul R a b).toFinsupp n =
  ∑ x ∈ Finset.antidiagonal n, a.toFinsupp x.1 * b.toFinsupp x.2 := by
  induction a generalizing n with
  | nil => simp only [nil_list_mul, List.toFinsupp_nil, Finsupp.coe_zero, Pi.zero_apply,
    List.toFinsupp_apply, List.getD_eq_getElem?_getD, zero_mul, Finset.sum_const_zero]
  | cons head tail ih =>
    rw [cons_list_mul, list_add_toFinsupp, list_smul_toFinsupp]
    induction n with
    | zero => rfl
    | succ n _ =>
    simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_cons_succ] at ih ⊢
    rw [ih n, Finset.Nat.antidiagonal_succ, Finset.sum_cons]
    simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
      getElem?_pos, List.getElem_cons_zero, Option.getD_some, Finset.sum_map,
      Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst,
      Nat.succ_eq_add_one, List.getElem?_cons_succ, Prod.map_snd, Function.Embedding.refl_apply]


def mul {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_mul R a.coefs b.coefs)

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Mul (CPoly R) := ⟨mul⟩


lemma mul_def {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : a * b = mul a b := rfl

@[simp]
lemma toPolynomial_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) :
  toPolynomial (a * b) = toPolynomial a * toPolynomial b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  ext n
  simp only [toPolynomial, mul_def, mul, Polynomial.coeff_ofFinsupp, Polynomial.coeff_mul]
  refine coefs_toCPoly (list_mul R a b) ▸ ?_
  rw [toFinsupp_coh, list_mul_toFinsupp]


def one {R : Type*} [DecidableEq R] [CommSemiring R] : CPoly R := toCPoly [1]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : One (CPoly R) := ⟨one⟩


lemma one_def {R : Type*} [DecidableEq R] [CommSemiring R] : (1 : CPoly R) = one := rfl

@[simp]
lemma toPolynomial_one {R : Type*} [DecidableEq R] [CommSemiring R] :
  toPolynomial (1 : CPoly R) = 1 := by
  unfold toPolynomial
  ext n
  simp only [one_def, one, Polynomial.coeff_ofFinsupp, coefs_toCPoly, toFinsupp_coh,
    Polynomial.coeff_one, List.toFinsupp_apply, List.getD_eq_getElem?_getD]
  induction n with
  | zero => rfl
  | succ n _ =>
    simp only [List.length_cons, List.length_nil, zero_add, add_lt_iff_neg_right, not_lt_zero',
      not_false_eq_true, getElem?_neg, Option.getD_none, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ↓reduceIte]

def list_neg (R : Type*) [CommRing R] : List R → List R
  | []      => []
  | a :: as => -a :: list_neg R as

lemma list_neg_nil {R : Type*} [CommRing R] : list_neg R [] = [] := rfl

lemma list_neg_cons {R : Type*} [CommRing R] {a : R} {as : List R}
  : list_neg R (a :: as) = -a :: list_neg R as := rfl

lemma list_neg_toFinsupp {R : Type*} [CommRing R] [DecidableEq R] (a : List R) (n : ℕ) :
  (list_neg R a).toFinsupp n = -a.toFinsupp n := by
  induction a generalizing n with
  | nil => simp only [list_neg_nil, List.toFinsupp_nil, Finsupp.coe_zero, Pi.zero_apply, neg_zero]
  | cons head tail ih =>
  induction n with
  | zero => rfl
  | succ n _ =>
  simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, list_neg_cons,
    List.getElem?_cons_succ] at ih ⊢
  apply ih


def neg {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) : CPoly R :=
  toCPoly (list_neg R a.coefs)

instance {R : Type*} [DecidableEq R] [CommRing R] : Neg (CPoly R) := ⟨neg⟩


lemma neg_def {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) : -a = neg a := rfl

@[simp]
lemma toPolynomial_neg {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) :
  toPolynomial (-a) = -toPolynomial a := by
  obtain ⟨a, ha⟩ := a
  unfold toPolynomial
  ext n
  simp only [neg_def, neg, Polynomial.coeff_ofFinsupp, Polynomial.coeff_neg]
  refine coefs_toCPoly (list_neg R a) ▸ ?_
  rw [toFinsupp_coh, list_neg_toFinsupp]

def list_sub (R : Type*) [CommRing R] : List R → List R → List R
  | []     , bs      => list_neg R bs
  | as     , []      => as
  | a :: as, b :: bs => (a - b) :: (list_sub R as bs)


lemma nil_list_sub {R : Type*} [CommRing R] {a : List R} : list_sub R [] a = list_neg R a := rfl


lemma list_sub_nil {R : Type*} [CommRing R] {a : List R} : list_sub R a [] = a :=
  a.rec rfl (fun _ _ _ ↦ rfl)


lemma cons_list_sub_cons {R : Type*} [CommRing R] {a b : R} {as bs : List R}
  : list_sub R (a :: as) (b :: bs) = (a - b) :: (list_sub R as bs) := rfl

lemma list_sub_toFinsupp {R : Type*} [CommRing R] [DecidableEq R] (a b : List R) (n : ℕ) :
  (list_sub R a b).toFinsupp n = a.toFinsupp n - b.toFinsupp n := by
  induction a generalizing b n with
  | nil =>
    rw [nil_list_sub, list_neg_toFinsupp]
    simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.toFinsupp_nil,
      Finsupp.coe_zero, Pi.zero_apply, zero_sub]
  | cons a0 as ih =>
  induction b generalizing n with
  | nil => simp only [list_sub_nil, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
    List.toFinsupp_nil, Finsupp.coe_zero, Pi.zero_apply, sub_zero]
  | cons b0 bs _ =>
  induction n with
  | zero => rfl
  | succ n _ =>
  simp only [cons_list_sub_cons, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ] at ih ⊢
  apply ih


def sub {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_sub R a.coefs b.coefs)

instance {R : Type*} [DecidableEq R] [CommRing R] : Sub (CPoly R) := ⟨sub⟩


lemma sub_def {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R) : a - b = sub a b := rfl

@[simp]
lemma toPolynomial_sub {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R) :
  toPolynomial (a - b) = toPolynomial a - toPolynomial b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  unfold toPolynomial
  ext n
  simp only [sub_def, sub, Polynomial.coeff_ofFinsupp, Polynomial.coeff_sub]
  refine coefs_toCPoly (list_sub R a b) ▸ ?_
  rw [toFinsupp_coh, list_sub_toFinsupp]

def list_eval (R : Type*) [CommSemiring R] : List R → R → R
  | [] => 0
  | a :: as => fun r ↦ a + r * list_eval R as r

def list_eval_nil {R : Type*} [CommSemiring R] {a : R} : list_eval R [] a = 0 := rfl

def list_eval_cons {R : Type*} [CommSemiring R] {a b : R} {as : List R}
  : list_eval R (a :: as) b = a + b * list_eval R as b := rfl

def list_eval_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : List R} {b : R}
  : list_eval R (removeTailingZeros a) b = list_eval R a b := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [list_eval_cons]
    by_cases h : head = 0
    · rw [h, removeTailingZeros_zero_cons_ite]
      by_cases h : removeTailingZeros tail = []
      · rw [if_pos h, ←ih, h, zero_add, list_eval_nil, mul_zero]
      · rw [if_neg h, list_eval_cons, ih]
    · rw [removeTailingZeros_cons_of_ne_zero h, list_eval_cons, ih]

def list_eval_list_add {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R} {x : R}
  : list_eval R (list_add R a b) x = list_eval R a x + list_eval R b x := by
  induction a generalizing b with
  | nil => simp only [nil_list_add, list_eval_nil, zero_add]
  | cons a₀ a' ih =>
  induction  b with
  | nil => simp only [list_add_nil, list_eval_nil, add_zero]
  | cons b₀ b' _ =>
    simp only [cons_list_add_cons, list_eval_cons, ih]
    ring

def list_eval_list_smul {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {b : List R} {x : R}
  : list_eval R (list_smul R a b) x = a * list_eval R b x := by
  induction b with
  | nil => simp only [list_smul_nil, list_eval_nil, mul_zero]
  | cons head tail ih =>
    simp only [list_smul_cons, list_eval_cons, ih]
    ring

def list_eval_list_mul {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R} {x : R}
  : list_eval R (list_mul R a b) x = list_eval R a x * list_eval R b x := by
  induction a with
  | nil => simp only [nil_list_mul, list_eval_nil, zero_mul]
  | cons head tail ih =>
    simp only [cons_list_mul, list_eval_list_add, list_eval_list_smul, list_eval_cons, ih, zero_add]
    ring

def eval {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) (b : R) : R :=
  list_eval R a.coefs b

lemma add_assoc {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a + b + c = a + (b + c) := by
    apply toPolynomial_inj
    simp only [toPolynomial_add]
    exact _root_.add_assoc a.toPolynomial b.toPolynomial c.toPolynomial

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddSemigroup (CPoly R) := ⟨add_assoc⟩

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZero (CPoly R) := ⟨⟩

lemma zero_add {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 0 + a = a := by
    apply toPolynomial_inj
    simp only [toPolynomial_add, toPolynomial_zero, _root_.zero_add]

lemma add_zero {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a + 0 = a := by
    apply toPolynomial_inj
    simp only [toPolynomial_add, toPolynomial_zero, _root_.add_zero]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZeroClass (CPoly R)
  := ⟨zero_add, add_zero⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddMonoid (CPoly R) where
  nsmul := nsmulRec

lemma add_comm {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R)
  : a + b = b + a := by
    apply toPolynomial_inj
    simp only [toPolynomial_add]
    exact AddCommMagma.add_comm a.toPolynomial b.toPolynomial

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMagma (CPoly R) := ⟨add_comm⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommSemigroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMonoid (CPoly R) where

lemma zero_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 0 * a = 0 := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul, toPolynomial_zero, MulZeroClass.zero_mul]

lemma mul_zero {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a * 0 = 0 := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul, toPolynomial_zero, MulZeroClass.mul_zero]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroClass (CPoly R)
  := ⟨zero_mul, mul_zero⟩

lemma mul_assoc {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a * b * c = a * (b * c) := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul]
    exact _root_.mul_assoc a.toPolynomial b.toPolynomial c.toPolynomial

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semigroup (CPoly R) := ⟨mul_assoc⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : SemigroupWithZero (CPoly R) where

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOne (CPoly R) := ⟨⟩

lemma one_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 1 * a = a := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul, toPolynomial_one, _root_.one_mul]

lemma mul_one {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a * 1 = a := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul, toPolynomial_one, _root_.mul_one]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOneClass (CPoly R) := ⟨one_mul, mul_one⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroOneClass (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Monoid (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MonoidWithZero (CPoly R) where

lemma mul_comm {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R)
  : a * b = b * a := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul]
    exact CommMonoid.mul_comm a.toPolynomial b.toPolynomial

instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommMagma (CPoly R) := ⟨mul_comm⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommSemigroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommMonoid (CPoly R) where

lemma mul_add {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a * (b + c) = a * b + a * c := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul, toPolynomial_add]
    exact LeftDistribClass.left_distrib a.toPolynomial b.toPolynomial c.toPolynomial

lemma add_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : (a + b) * c = a * c + b * c := by
    apply toPolynomial_inj
    simp only [toPolynomial_mul, toPolynomial_add]
    exact RightDistribClass.right_distrib a.toPolynomial b.toPolynomial c.toPolynomial

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Distrib (CPoly R) := ⟨mul_add, add_mul⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalNonAssocSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonAssocSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommSemiring (CPoly R) where

def const {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) : CPoly R := toCPoly [a]

@[simp]
def toPolynomial_const {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) :
  toPolynomial (const a) = Polynomial.C a := by
  unfold const toPolynomial
  rw [coefs_toCPoly, toFinsupp_coh, List.toFinsupp_singleton]
  ext n
  simp only [Polynomial.ofFinsupp_single, Polynomial.monomial_zero_left]

lemma sub_eq_add_neg {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R)
  : a - b = a + -b := by
    apply toPolynomial_inj
    simp only [toPolynomial_sub, toPolynomial_add, toPolynomial_neg]
    exact rfl

instance {R : Type*} [DecidableEq R] [CommRing R] : SubNegMonoid (CPoly R) where
  sub_eq_add_neg := sub_eq_add_neg
  zsmul := zsmulRec

lemma neg_add_cancel {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) : -a + a = 0 := by
    apply toPolynomial_inj
    simp only [toPolynomial_add, toPolynomial_neg, _root_.neg_add_cancel, toPolynomial_zero]

instance {R : Type*} [DecidableEq R] [CommRing R] : AddGroup (CPoly R) := ⟨neg_add_cancel⟩
instance {R : Type*} [DecidableEq R] [CommRing R] : AddCommGroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommRing R] : Ring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommRing R] : CommRing (CPoly R) where

noncomputable def toPolynomial_ringEquiv {R : Type*} [CommSemiring R] [DecidableEq R] :
  CPoly R ≃+* Polynomial R where
  toFun := toPolynomial
  invFun := toPolynomial_Equiv.invFun
  left_inv := toPolynomial_Equiv.left_inv
  right_inv := toPolynomial_Equiv.right_inv
  map_mul' := toPolynomial_mul
  map_add' := toPolynomial_add

def map {R S : Type*} [CommSemiring R] [CommSemiring S] [DecidableEq R] [DecidableEq S]
  (f : R →+* S) (a : CPoly R) : CPoly S := toCPoly (a.coefs.map f)

@[simp]
lemma toPolynomial_map {R S : Type*} [CommSemiring R] [CommSemiring S]
  [DecidableEq R] [DecidableEq S] (f : R →+* S) (a : CPoly R) :
  (a.map f).toPolynomial = a.toPolynomial.map f := by
  unfold map toPolynomial
  ext n
  simp only [coefs_toCPoly, Polynomial.coeff_ofFinsupp, Polynomial.coeff_map]
  rw [toFinsupp_coh]
  simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [← f.map_zero, Option.getD_map]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : DecidableEq (CPoly R) :=
  fun p q ↦ decidable_of_iff (p.coefs = q.coefs) (Iff.symm CPoly.ext_iff)

def lift {R S : Type*} [CommSemiring R] [CommSemiring S] [DecidableEq R] [DecidableEq S]
  (f : R →+* S) : CPoly R →+* CPoly S where
    toFun := map f
    map_one' := by
      apply toPolynomial_inj
      simp only [toPolynomial_map, toPolynomial_one, Polynomial.map_one]
    map_mul' x y := by
      apply toPolynomial_inj
      simp only [toPolynomial_map, toPolynomial_mul, Polynomial.map_mul]
    map_zero' := by
      apply toPolynomial_inj
      simp only [toPolynomial_map, toPolynomial_zero, Polynomial.map_zero]
    map_add' x y := by
      apply toPolynomial_inj
      simp only [toPolynomial_map, toPolynomial_add, Polynomial.map_add]

def liftTo {R : Type*} [DecidableEq R] [CommSemiring R] (f : CPoly R) (S : Type*)
  [DecidableEq S] [CommSemiring S] [inst : Algebra R S] : CPoly S :=
    (lift (inst.algebraMap)).toFun f

def list_deriv_n {R : Type*} [CommSemiring R] : ℕ →  List R → List R
  | _, []      => [0]
  | n, a :: as => n * a :: list_deriv_n (n + 1) as

lemma list_deriv_n_toFinsupp {R : Type*} [CommSemiring R] [DecidableEq R] (a : List R)
  (m : ℕ) (n : ℕ) : (list_deriv_n m a).toFinsupp n = (m + n) * a.toFinsupp n := by
  induction a generalizing n m with
  | nil =>
    simp only [list_deriv_n, List.toFinsupp_apply, List.getD_eq_getElem?_getD,
      List.getElem?_getD_singleton_default_eq, List.toFinsupp_nil, Finsupp.coe_zero, Pi.zero_apply,
      MulZeroClass.mul_zero]
  | cons head tail ih =>
    unfold list_deriv_n
    induction n with
    | zero => simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.length_cons,
      lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, List.getElem_cons_zero,
      Option.getD_some, Nat.cast_zero, _root_.add_zero]
    | succ n _ =>
      simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        Nat.cast_add, Nat.cast_one] at ih ⊢
      simp only [ih, Nat.cast_add, Nat.cast_one]
      congr 1
      ring

abbrev list_deriv {R : Type*} [CommSemiring R] (l : List R) : List R := (list_deriv_n 0 l).tail

lemma list_deriv_toFinsupp {R : Type*} [CommSemiring R] [DecidableEq R] (a : List R) (n : ℕ) :
  (list_deriv a).toFinsupp n = (n + 1) * a.toFinsupp (n + 1) := by
  unfold list_deriv
  have := list_deriv_n_toFinsupp a 0 (n + 1)
  simp only [List.toFinsupp_apply, List.getD_eq_getElem?_getD, Nat.cast_zero, Nat.cast_add,
    Nat.cast_one, _root_.zero_add, List.getElem?_tail] at this ⊢
  assumption

def deriv {R : Type*} [DecidableEq R] [CommSemiring R] (f : CPoly R) : CPoly R :=
  toCPoly (list_deriv f.coefs)

@[simp]
lemma toPolynomial_deriv {R : Type*} [DecidableEq R] [CommSemiring R] (f : CPoly R) :
  f.deriv.toPolynomial = f.toPolynomial.derivative := by
  obtain ⟨a, _⟩ := f
  ext n
  unfold toPolynomial deriv
  simp only [coefs_toCPoly, toFinsupp_coh, Polynomial.coeff_ofFinsupp, list_deriv_toFinsupp,
    Polynomial.coeff_derivative]
  ring

def degree {R : Type*} [DecidableEq R] [CommSemiring R] : CPoly R → WithBot ℕ
  | ⟨[], _⟩      => ⊥
  | ⟨_a :: as, _⟩ => as.length

@[simp]
lemma toPolynomial_degree {R : Type*} [DecidableEq R] [CommSemiring R] (f : CPoly R) :
  f.degree = f.toPolynomial.degree := by
  obtain ⟨a, ha⟩ := f
  unfold degree toPolynomial
  split <;> expose_names
  · rw [heq]
    simp only [List.toFinsupp_nil, Polynomial.ofFinsupp_zero, Polynomial.degree_zero]
  · obtain heq := congrArg coefs heq
    simp only at heq
    subst a
    unfold Polynomial.degree List.toFinsupp
    simp only [List.getD_eq_getElem?_getD, ne_eq, List.length_cons, Polynomial.support_ofFinsupp]
    apply le_antisymm
    · apply Finset.le_max
      simp only [Nat.cast_id, Finset.mem_filter, Finset.mem_range, lt_add_iff_pos_right,
        zero_lt_one, List.length_cons, getElem?_pos, Option.getD_some, true_and]
      have := getLast_ne_zero_of_noTailingZero (_a :: as) ha (List.cons_ne_nil _ _)
      simp only [List.getLast_eq_getElem (List.cons_ne_nil _ _), List.length_cons,
        add_tsub_cancel_right, ne_eq] at this
      assumption
    · apply Finset.max_le
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      apply WithBot.coe_le_coe.2 (Nat.le_of_lt_succ hi.1)

end CPoly
