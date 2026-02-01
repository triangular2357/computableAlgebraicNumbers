import Mathlib
import ComputableAlgebraicNumbers.toPolynomialSimpSet

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

@[toPolynomialSimp]
lemma toPolynomial_eq {R : Type*} [DecidableEq R] [CommSemiring R] {a b : CPoly R} :
  (a = b) = (toPolynomial a = toPolynomial b) :=
    propext toPolynomial_Equiv.apply_eq_iff_eq.symm

@[toPolynomialSimp]
lemma toPolynomial_ne {R : Type*} [DecidableEq R] [CommSemiring R] {a b : CPoly R} :
  (a ≠ b) = (toPolynomial a ≠ toPolynomial b) := congrArg Not toPolynomial_eq

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

@[toPolynomialSimp]
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

@[toPolynomialSimp]
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

@[toPolynomialSimp]
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

@[toPolynomialSimp]
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

@[toPolynomialSimp]
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

@[toPolynomialSimp]
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

@[toPolynomialSimp]
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
  : a + b + c = a + (b + c) := by simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddSemigroup (CPoly R) := ⟨add_assoc⟩

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZero (CPoly R) := ⟨⟩

lemma zero_add {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 0 + a = a := by
    simp only [toPolynomialSimp]; ring

lemma add_zero {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a + 0 = a := by
    simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZeroClass (CPoly R)
  := ⟨zero_add, add_zero⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddMonoid (CPoly R) where
  nsmul := nsmulRec

lemma add_comm {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R)
  : a + b = b + a := by simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMagma (CPoly R) := ⟨add_comm⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommSemigroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMonoid (CPoly R) where

lemma zero_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 0 * a = 0 := by
    simp only [toPolynomialSimp]; ring

lemma mul_zero {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a * 0 = 0 := by
    simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroClass (CPoly R)
  := ⟨zero_mul, mul_zero⟩

lemma mul_assoc {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a * b * c = a * (b * c) := by simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semigroup (CPoly R) := ⟨mul_assoc⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : SemigroupWithZero (CPoly R) where

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOne (CPoly R) := ⟨⟩

lemma one_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 1 * a = a := by
    simp only [toPolynomialSimp]; ring

lemma mul_one {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a * 1 = a := by
    simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOneClass (CPoly R) := ⟨one_mul, mul_one⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroOneClass (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Monoid (CPoly R) where

@[toPolynomialSimp]
lemma toPolynomial_npow {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) (n : ℕ) :
  toPolynomial (a ^ n) = toPolynomial a ^ n := by
  induction n with
  | zero => exact toPolynomial_one
  | succ n ih =>
    change (a ^ n * a).toPolynomial = a.toPolynomial ^ n * a.toPolynomial
    simp only [toPolynomialSimp, ih]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MonoidWithZero (CPoly R) where

lemma mul_comm {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R)
  : a * b = b * a := by simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommMagma (CPoly R) := ⟨mul_comm⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommSemigroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommMonoid (CPoly R) where

lemma mul_add {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a * (b + c) = a * b + a * c := by simp only [toPolynomialSimp]; ring

lemma add_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : (a + b) * c = a * c + b * c := by simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Distrib (CPoly R) := ⟨mul_add, add_mul⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalNonAssocSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonAssocSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommSemiring (CPoly R) where

def const {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) : CPoly R := toCPoly [a]

@[toPolynomialSimp]
def toPolynomial_const {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) :
  toPolynomial (const a) = Polynomial.C a := by
  unfold const toPolynomial
  rw [coefs_toCPoly, toFinsupp_coh, List.toFinsupp_singleton]
  ext n
  simp only [Polynomial.ofFinsupp_single, Polynomial.monomial_zero_left]

lemma sub_eq_add_neg {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R)
  : a - b = a + -b := by simp only [toPolynomialSimp]; ring

instance {R : Type*} [DecidableEq R] [CommRing R] : SubNegMonoid (CPoly R) where
  sub_eq_add_neg := sub_eq_add_neg
  zsmul := zsmulRec

lemma neg_add_cancel {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) : -a + a = 0 := by
    simp only [toPolynomialSimp]; ring

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

@[toPolynomialSimp]
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

def X {R : Type*} [DecidableEq R] [CommSemiring R] : CPoly R := toCPoly [0, 1]

@[toPolynomialSimp]
lemma toPolynomial_X {R : Type*} [DecidableEq R] [CommSemiring R] :
  toPolynomial (X : CPoly R) = Polynomial.X := by
  ext n
  unfold X toPolynomial
  rw [coefs_toCPoly, toFinsupp_coh, Polynomial.coeff_X]
  by_cases n = 0
  · subst n; rfl
  by_cases n = 1;
  · subst n; rfl
  have : n ≥ 2 := Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨‹n ≠ 0›, ‹n ≠ 1›⟩
  simp only [Polynomial.coeff_ofFinsupp, List.toFinsupp_apply, List.getD_eq_getElem?_getD]
  rw [if_neg ‹n ≠ 1›.symm, List.getElem?_eq_none this, Option.getD_none]

instance {R : Type*} [CommSemiring R] [DecidableEq R] [Repr R] : Repr (CPoly R) where
  reprPrec x _ :=
    if x = 0
    then f!"const {repr (0 : R)}"
    else
      let l := (x.coefs.zip (List.range x.coefs.length)).reverse.filter (·.1 ≠ 0)
      Std.Format.joinSep (l.map fun
        | (a, 0) => f!"const {repr a}"
        | (a, 1) => if a = 1 then f!"X" else f!"{repr a}*X"
        | (a, i) => if a = 1 then f!"X^{i}" else f!"{repr a}*X^{i}"
      ) f!" + "

def lift {R S : Type*} [CommSemiring R] [CommSemiring S] [DecidableEq R] [DecidableEq S]
  (f : R →+* S) : CPoly R →+* CPoly S where
    toFun := map f
    map_one' := by simp only [toPolynomialSimp, Polynomial.map_one]
    map_mul' x y := by simp only [toPolynomialSimp, Polynomial.map_mul]
    map_zero' := by simp only [toPolynomialSimp, Polynomial.map_zero]
    map_add' x y := by simp only [toPolynomialSimp, Polynomial.map_add]

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

@[toPolynomialSimp]
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

@[toPolynomialSimp]
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

def natDegree {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) : ℕ :=
  (degree p).unbotD 0

@[toPolynomialSimp]
lemma toPolynomial_natDegree {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) :
  p.natDegree = p.toPolynomial.natDegree := by
  unfold natDegree Polynomial.natDegree
  simp only [toPolynomialSimp]

def leadingCoeff {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) : R :=
  p.toPolynomial.coeff p.natDegree

@[toPolynomialSimp]
lemma toPolynomial_leadingCoeff {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) :
  p.leadingCoeff = p.toPolynomial.leadingCoeff := by
  unfold leadingCoeff Polynomial.leadingCoeff
  simp only [toPolynomialSimp]

def Monic {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) :=
  p.leadingCoeff = (1 : R)

@[toPolynomialSimp]
lemma toPolynomial_Monic {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) :
  p.Monic = p.toPolynomial.Monic := by
  unfold Monic Polynomial.Monic
  simp only [toPolynomialSimp]

def divByMonic_n {R : Type*} [DecidableEq R] [CommRing R] (q : CPoly R) (hq : q.Monic) :
  ∀ (n : ℕ) (p : CPoly R), p.degree ≤ n → CPoly R
  | 0, p, hp =>
    if h : q.degree ≤ p.degree ∧ p ≠ 0 then p else 0
  | n + 1, p, hp =>
    if h : q.degree ≤ p.degree ∧ p ≠ 0 then
      letI z := p.leadingCoeff • X ^ (p.natDegree - q.natDegree)
      letI div := divByMonic_n q hq n (p - q * z) <| by
        unfold z
        have ⟨h₁, h₂⟩ := h
        simp only [toPolynomialSimp] at *
        rw [Polynomial.smul_eq_C_mul]
        have := calc
          _ < _ := Polynomial.div_wf_lemma h hq
          _ ≤ _ := hp
        exact Order.le_of_lt_succ this
      z + div
    else 0

lemma zero_divByMonic_n {R : Type*} [DecidableEq R] [CommRing R] [Nontrivial R]
  (q : CPoly R) (hq : q.Monic) (n : ℕ) : divByMonic_n q hq n 0 bot_le = 0 := by
  unfold divByMonic_n
  induction n with
  | zero => simp only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte]
  | succ n _ => simp only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte]

lemma divByMonic_n_0 {R : Type*} [DecidableEq R] [CommRing R] (q : CPoly R) (hq : q.Monic)
  (n : ℕ) (p : CPoly R) (hn : p.degree ≤ n) (h0 : p.degree ≤ 0) :
  divByMonic_n q hq n p hn = divByMonic_n q hq 0 p h0 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
  unfold divByMonic_n
  split_ifs with h
  · have : (p - q * (const p.leadingCoeff * X ^ (p.natDegree - q.natDegree))).degree ≤ 0 := by
      simp only [toPolynomialSimp] at h hq h0 ⊢
      exact le_of_lt <| calc
        _ < _ := Polynomial.div_wf_lemma h hq
        _ ≤ _ := h0
    specialize ih (p - q * p.leadingCoeff • X ^ (p.natDegree - q.natDegree)) <| by
      simp only [toPolynomialSimp] at h hq h0 this ⊢
      trans 0
      · rwa [Polynomial.smul_eq_C_mul]
      · exact Nat.WithBot.coe_nonneg
    specialize ih <| by
      simp only [toPolynomialSimp] at this ⊢
      rwa [Polynomial.smul_eq_C_mul]
    rw [ih]
    unfold divByMonic_n
    have : q = 1 := by
      have hle0 := h.1.trans h0
      simp only [toPolynomialSimp] at hq hle0 this ⊢
      exact Polynomial.eq_one_of_monic_natDegree_zero hq
        (Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 hle0)
    rw [this]
    split_ifs with h'
    · ring_nf
    · simp only [toPolynomialSimp] at *
      rw [Polynomial.eq_C_of_degree_le_zero h0]
      simp only [Polynomial.leadingCoeff_C, Polynomial.natDegree_C, Polynomial.natDegree_one,
        tsub_self, pow_zero, Polynomial.smul_eq_C_mul, _root_.mul_one, _root_.add_zero]
  · rfl

lemma divByMonic_n_m {R : Type*} [DecidableEq R] [CommRing R] (q : CPoly R) (hq : q.Monic)
  (n m : ℕ) (h : m ≤ n) (p : CPoly R) (hn : p.degree ≤ n) (hn_m : p.degree ≤ n - m) :
  divByMonic_n q hq n p hn = divByMonic_n q hq (n - m) p hn_m := by
  induction n, h using Nat.le_induction generalizing p with
  | base =>
    cases m with
    | zero => rfl
    | succ n =>
      simp_rw [Nat.sub_self (n + 1)]
      let n' := n + 1
      simp_rw [show n + 1 = n' from rfl] at hn hn_m ⊢
      apply divByMonic_n_0
  | succ n hmn ih =>
    simp_rw [Nat.succ_sub hmn] at hn_m ⊢
    unfold divByMonic_n
    split_ifs with h
    · let z := p - q * p.leadingCoeff • X ^ (p.natDegree - q.natDegree)
      have : p - q * p.leadingCoeff • X ^ (p.natDegree - q.natDegree) = z := rfl
      simp_rw [this]
      have : z.degree ≤ n - m := by
        unfold z
        simp only [toPolynomialSimp] at this h hq hn_m ⊢
        have := Trans.trans (Polynomial.div_wf_lemma h hq) hn_m
        rw [Polynomial.smul_eq_C_mul]
        apply WithBot.le_coe_iff.2
        intro a ha
        rw [ha] at this
        exact Nat.le_of_lt_succ (WithBot.coe_lt_coe.1 this)
      specialize ih z (this.trans <| WithBot.coe_le_coe.2 (Nat.sub_le n m)) this
      rw [ih]
    · rfl

def divByMonic {R : Type*} [DecidableEq R] [CommRing R] (p q : CPoly R) (hq : q.Monic) : CPoly R :=
  divByMonic_n q hq p.natDegree p <| by
    unfold natDegree
    cases p.degree
    · exact bot_le
    · rfl

def modByMonic {R : Type*} [DecidableEq R] [CommRing R] (p q : CPoly R) (hq : q.Monic) : CPoly R :=
  p - q * divByMonic p q hq

lemma zero_modByMonic {R : Type*} [DecidableEq R] [CommRing R] [Nontrivial R]
  (q : CPoly R) (hq : q.Monic) : modByMonic 0 q hq = 0 := by
  unfold modByMonic divByMonic
  simp only [zero_sub, neg_eq_zero]
  apply mul_eq_zero_of_right
  simp_rw [show natDegree (0 : CPoly R) = 0 from rfl]
  unfold divByMonic_n
  simp only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte]

lemma degree_modByMonic_lt {R : Type*} [DecidableEq R] [CommRing R] [Nontrivial R]
  (p q : CPoly R) (hq : q.Monic) : (modByMonic p q hq).degree < q.degree := by
  have : ¬(q.degree ≤ p.degree ∧ p ≠ 0) →  p.degree < q.degree := by
    intro h
    by_contra h'
    simp only [ne_eq, not_and, Decidable.not_not, not_lt] at h h'
    have : p.degree = ⊥ := by
      rw [h h']
      rfl
    have : q.degree = ⊥ := eq_bot_mono h' this
    unfold degree at this
    split at this
    · unfold Monic at hq
      have : ({coefs := [], condition := (by assumption)} : CPoly R).leadingCoeff = 0 := rfl
      rw [hq] at this
      exact one_ne_zero this
    · revert this
      simp only [WithBot.natCast_ne_bot, imp_self]
  unfold modByMonic divByMonic
  let n := p.natDegree
  have hn : p.natDegree = n := rfl
  clear_value n
  simp_rw [hn]
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
  cases n with
  | zero =>
    unfold divByMonic_n
    split_ifs with h
    · obtain ⟨h₁, h₂⟩ := h
      unfold natDegree at hn
      obtain h|h := WithBot.unbotD_eq_self_iff.1 hn
      · simp only [toPolynomialSimp] at h h₁ hq hn this ⊢
        rw [h] at h₁
        have : q.toPolynomial = 1 := by
          apply Polynomial.eq_one_of_monic_natDegree_zero hq
          exact Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 h₁
        rw [this]
        ring_nf
        apply (Polynomial.modByMonic_eq_self_iff Polynomial.monic_one).mp
        exact Polynomial.zero_modByMonic 1
      · exfalso
        simp only [toPolynomialSimp] at h h₂
        exact h₂ (Polynomial.degree_eq_bot.1 h)
    · ring_nf
      exact this h
  | succ n =>
    unfold divByMonic_n
    split_ifs with h
    · have hp : p.degree = n + 1 := by
        unfold natDegree at hn
        let k := p.degree
        rw [show p.degree = k from rfl] at hn ⊢
        revert hn
        induction k with
        | bot => exact fun hn ↦ ((Nat.succ_ne_zero n).symm hn).elim
        | coe a => exact congrArg WithBot.some
      letI z := p - q * p.leadingCoeff • X ^ (p.natDegree - q.natDegree)
      have hz_deg : z.natDegree < n + 1 := by
        subst z
        simp only [toPolynomialSimp] at h hn hp hq ⊢
        rw [Polynomial.smul_eq_C_mul]
        have := hp ▸ Polynomial.div_wf_lemma h hq
        rw [Nat.lt_succ_iff]
        apply Polynomial.natDegree_le_iff_degree_le.2
        rw [← Order.lt_succ_iff]
        exact this
      simp_rw [show p - q * p.leadingCoeff • X ^ (p.natDegree - q.natDegree) = z from rfl]
      specialize ih (p - q * p.leadingCoeff • X ^ (p.natDegree - q.natDegree)).natDegree
        hz_deg z
      have hzdef : p - q * p.leadingCoeff • X ^ (p.natDegree - q.natDegree) = z := rfl
      by_cases hz0 : z = 0
      · simp_rw [hz0]
        rw [zero_divByMonic_n]
        ring_nf
        simp only [toPolynomialSimp] at h hq hz0 hzdef ⊢
        rw [Polynomial.smul_eq_C_mul] at hzdef ⊢
        rw [hzdef, hz0, Polynomial.degree_zero]
        refine bot_lt_iff_ne_bot.2 (Polynomial.degree_ne_bot.2 ?_)
        intro hq0
        unfold Polynomial.Monic Polynomial.leadingCoeff at hq
        rw [hq0, Polynomial.coeff_zero] at hq
        exact one_ne_zero hq.symm
      · specialize ih (fun h₁ ↦ Decidable.byContradiction fun h₂ ↦ h₁ ⟨not_lt.1 h₂, hz0⟩) rfl
        simp_rw [hzdef] at ih
        have hz_deg : z.degree ≤ n := by
          simp only [toPolynomialSimp] at hz_deg ⊢
          exact Polynomial.degree_le_of_natDegree_le (Nat.le_of_lt_succ hz_deg)
        have : n - (n - z.natDegree) = z.natDegree := by
          apply Nat.sub_sub_self
          simp only [toPolynomialSimp] at hz_deg ⊢
          exact Polynomial.natDegree_le_of_degree_le hz_deg
        rw [divByMonic_n_m q hq n (n - z.natDegree) (Nat.sub_le _ _) z hz_deg] <;> simp_rw [this]
        · simp_rw [mul_add]
          rwa [← sub_sub, hzdef]
        · simp only [toPolynomialSimp, Polynomial.degree_le_natDegree]
    · ring_nf
      exact this h

lemma toPolynomial_div_modByMonic {R : Type*} [DecidableEq R] [CommRing R]
  (p q : CPoly R) (hq : q.Monic) : p.toPolynomial.divByMonic q.toPolynomial =
  (p.divByMonic q hq).toPolynomial ∧ p.toPolynomial.modByMonic q.toPolynomial =
  (p.modByMonic q hq).toPolynomial := by
  cases subsingleton_or_nontrivial R
  · constructor <;> apply Subsingleton.allEq
  · apply Polynomial.div_modByMonic_unique (p.divByMonic q hq).toPolynomial
      (p.modByMonic q hq).toPolynomial (toPolynomial_Monic q ▸ hq)
    constructor
    · unfold modByMonic
      simp only [toPolynomialSimp]
      ring
    · simp_rw [← toPolynomial_degree]
      exact degree_modByMonic_lt p q hq

@[toPolynomialSimp]
lemma toPolynomial_divByMonic {R : Type*} [DecidableEq R] [CommRing R]
  (p q : CPoly R) (hq : q.Monic) : toPolynomial (p.divByMonic q hq) =
  p.toPolynomial.divByMonic q.toPolynomial := (toPolynomial_div_modByMonic p q hq).1.symm

@[toPolynomialSimp]
lemma toPolynomial_modByMonic {R : Type*} [DecidableEq R] [CommRing R]
  (p q : CPoly R) (hq : q.Monic) : toPolynomial (p.modByMonic q hq) =
  p.toPolynomial.modByMonic q.toPolynomial := (toPolynomial_div_modByMonic p q hq).2.symm

def div {R : Type*} [DecidableEq R] [Field R] (p q : CPoly R) : CPoly R :=
  if h : q = 0 then 0 else
  haveI := by
    simp only [toPolynomialSimp] at h ⊢
    apply Polynomial.monic_mul_leadingCoeff_inv h
  const q.leadingCoeff⁻¹ * p.divByMonic (q * const q.leadingCoeff⁻¹) this

instance {R : Type*} [DecidableEq R] [Field R] : Div (CPoly R) := ⟨div⟩

@[toPolynomialSimp]
lemma toPolynomial_div {R : Type*} [DecidableEq R] [Field R] (p q : CPoly R) :
  toPolynomial (p / q) = p.toPolynomial / q.toPolynomial := by
  simp only [(· / ·), Div.div]
  unfold div Polynomial.div
  split_ifs
  · simp only [toPolynomial_zero, ‹q = 0›, Polynomial.leadingCoeff_zero, inv_zero, map_zero,
      MulZeroClass.mul_zero, Polynomial.divByMonic_zero]
  · simp only [toPolynomialSimp]

def mod {R : Type*} [DecidableEq R] [Field R] (p q : CPoly R) : CPoly R :=
  if h : q = 0 then p else
  haveI := by
    simp only [toPolynomialSimp] at h ⊢
    apply Polynomial.monic_mul_leadingCoeff_inv h
  p.modByMonic (q * const q.leadingCoeff⁻¹) this

instance {R : Type*} [DecidableEq R] [Field R] : Mod (CPoly R) := ⟨mod⟩

@[toPolynomialSimp]
lemma toPolynomial_mod {R : Type*} [DecidableEq R] [Field R] (p q : CPoly R) :
  toPolynomial (p % q) = p.toPolynomial % q.toPolynomial := by
  simp only [(· % ·), Mod.mod]
  unfold mod Polynomial.mod
  split_ifs
  · simp only [‹q = 0›, toPolynomial_zero, Polynomial.leadingCoeff_zero, inv_zero, map_zero,
    MulZeroClass.mul_zero, Polynomial.modByMonic_zero]
  · simp only [toPolynomialSimp]

instance {R : Type*} [DecidableEq R] [Field R] : Nontrivial (CPoly R) := by
  constructor
  use 1, 0
  simp only [toPolynomialSimp]
  exact one_ne_zero

instance {R : Type*} [DecidableEq R] [Field R] : EuclideanDomain (CPoly R) where
  quotient a b := a / b
  quotient_zero := by
    simp only [HDiv.hDiv, Div.div, div, ↓reduceDIte, implies_true]
  remainder a b := a % b
  quotient_mul_add_remainder_eq := by
    intro a b
    simp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod]
    unfold div mod modByMonic
    split_ifs <;> ring
  r p q := p.degree < q.degree
  r_wellFounded := by
    refine (Function.Surjective.wellFounded_iff toPolynomial_sur ?_).2 Polynomial.degree_lt_wf
    simp only [toPolynomialSimp, implies_true]
  remainder_lt := by
    intro a b h
    simp only [toPolynomialSimp] at h ⊢
    apply Polynomial.degree_mod_lt _ h
  mul_left_not_lt := by
    intro a b h
    apply not_lt_of_ge
    simp only [toPolynomialSimp] at h ⊢
    apply Polynomial.degree_le_mul_left _ h

example {R : Type*} [DecidableEq R] [Field R] (a : Polynomial R) :
  normalize a = a * Polynomial.C a.leadingCoeff⁻¹ := by
  by_cases h : a = 0
  · subst a
    simp only [map_zero, Polynomial.leadingCoeff_zero, inv_zero, MulZeroClass.mul_zero]
  · have := Polynomial.leadingCoeff_ne_zero.2 h
    apply Polynomial.eq_of_monic_of_associated (Polynomial.monic_normalize h)
    · unfold Polynomial.Monic
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, mul_inv_cancel₀ this]
    · apply associated_of_dvd_dvd
      · apply normalize_dvd_iff.2 <| dvd_mul_right a _
      · refine dvd_normalize_iff.2 ((Polynomial.dvd_mul_leadingCoeff_inv h).1 <| by rfl)

instance {R : Type*} [DecidableEq R] [Field R] : NormalizationMonoid (CPoly R) where
  normUnit p := {
    val := if p = 0 then 1 else const p.leadingCoeff⁻¹
    inv := if p = 0 then 1 else const p.leadingCoeff
    val_inv := by
      split_ifs with h
      · simp only [_root_.mul_one]
      · simp only [toPolynomialSimp] at h ⊢
        rw [← Polynomial.C_mul, inv_mul_cancel₀, map_one]
        exact Polynomial.leadingCoeff_ne_zero.2 h
    inv_val := by
      split_ifs with h
      · simp only [_root_.mul_one]
      · simp only [toPolynomialSimp] at h ⊢
        rw [← Polynomial.C_mul, mul_inv_cancel₀, map_one]
        exact Polynomial.leadingCoeff_ne_zero.2 h
  }
  normUnit_zero := rfl
  normUnit_mul := by
    intro a b ha0 hb0
    apply Units.ext
    simp only [mul_eq_zero, Units.val_mul, mul_ite, _root_.mul_one, ite_mul, _root_.one_mul]
    split_ifs with h
    · tauto
    · simp only [toPolynomial_leadingCoeff, toPolynomial_mul, Polynomial.leadingCoeff_mul,
      mul_inv_rev, toPolynomial_eq, toPolynomial_const, map_mul]
      ring
  normUnit_coe_units := by
    intro u
    apply Units.ext
    simp only [Units.ne_zero, ↓reduceIte]
    apply mul_left_cancel₀ (Units.ne_zero u)
    simp only [Units.mul_inv]
    let u' : Units (Polynomial R) := {
      val := u.val.toPolynomial
      inv := u.inv.toPolynomial
      val_inv := by
        have := u.val_inv
        simp only [toPolynomialSimp] at this
        assumption
      inv_val := by
        have := u.inv_val
        simp only [toPolynomialSimp] at this
        assumption
    }
    obtain ⟨u'c, h₁, h₂⟩ := Polynomial.isUnit_iff.1 u'.isUnit
    simp only [toPolynomialSimp]
    rw [show u.val.toPolynomial = u'.val from rfl, ← h₂, ← Polynomial.C_mul, ← Polynomial.C_1,
      Polynomial.C_inj.2]
    rw [Polynomial.leadingCoeff_C, mul_inv_cancel₀]
    exact IsUnit.ne_zero h₁

lemma Monic_normalize {R : Type*} [DecidableEq R] [Field R] (p : CPoly R) :
  p ≠ 0 → (normalize p).Monic := by
  intro h
  unfold normalize normUnit instNormalizationMonoid Monic
  simp only [mul_ite, _root_.mul_one, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, h, ↓reduceIte]
  simp only [toPolynomialSimp] at h ⊢
  simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.2 h)]

instance {R : Type*} [DecidableEq R] [Field R] : GCDMonoid (CPoly R) where
  gcd p q := normalize (EuclideanDomain.gcd p q)
  lcm p q := normalize (EuclideanDomain.lcm p q)
  gcd_dvd_left := fun a b ↦ normalize_dvd_iff.2 (EuclideanDomain.gcd_dvd_left a b)
  gcd_dvd_right := fun a b ↦ normalize_dvd_iff.2 (EuclideanDomain.gcd_dvd_right a b)
  dvd_gcd := fun hc hb ↦ dvd_normalize_iff.2 (EuclideanDomain.dvd_gcd hc hb)
  gcd_mul_lcm := by
    intro a b
    apply associated_of_dvd_dvd
    · rw [← map_mul normalize _ _]
      apply normalize_dvd_iff.2
      rw [EuclideanDomain.gcd_mul_lcm]
    · rw [← map_mul normalize _ _]
      apply dvd_normalize_iff.2
      rw [EuclideanDomain.gcd_mul_lcm]
  lcm_zero_left := fun a ↦ (EuclideanDomain.lcm_zero_left a).symm ▸ rfl
  lcm_zero_right := fun a ↦ (EuclideanDomain.lcm_zero_right a).symm ▸ rfl

instance {R : Type*} [DecidableEq R] [Field R] : NormalizedGCDMonoid (CPoly R) where
  normalize_gcd := fun _ _ ↦ normalize_idem _
  normalize_lcm := fun _ _ ↦ normalize_idem _

@[toPolynomialSimp]
lemma toPolynomial_dvd {R : Type*} [DecidableEq R] [CommSemiring R] (p q : CPoly R) :
  (p ∣ q) = (p.toPolynomial ∣ q.toPolynomial) :=
  haveI : MulEquivClass (CPoly R ≃+* Polynomial R) .. := ⟨RingEquiv.map_mul⟩
  propext (map_dvd_iff toPolynomial_ringEquiv).symm

@[toPolynomialSimp]
lemma toPolynomial_gcd {R : Type*} [DecidableEq R] [Field R] (p q : CPoly R) :
  toPolynomial (gcd p q) = gcd p.toPolynomial q.toPolynomial := by
  by_cases h : p = 0 ∧ q = 0
  · simp only [h.1, h.2, gcd_same, map_zero, toPolynomial_zero]
  · apply Polynomial.eq_of_monic_of_associated
    · rw [show gcd p q = normalize (EuclideanDomain.gcd p q) from rfl, ← toPolynomial_Monic]
      apply Monic_normalize
      exact EuclideanDomain.gcd_eq_zero_iff.not.2 h
    · simp only [toPolynomialSimp] at h
      rw [← normalize_gcd]
      apply Polynomial.monic_normalize
      exact (gcd_eq_zero_iff _ _).not.2 h
    · apply associated_of_dvd_dvd
      · apply dvd_gcd
        · rw [← toPolynomial_dvd]
          exact gcd_dvd_left p q
        · rw [← toPolynomial_dvd]
          exact gcd_dvd_right p q
      · letI fp := (toPolynomial_Equiv (R := R)).invFun
        have : ∀ a, a = (fp a).toPolynomial :=
          fun a ↦ ((toPolynomial_Equiv (R := R)).right_inv a).symm
        rw [this (gcd p.toPolynomial q.toPolynomial), this ((gcd p q).toPolynomial),
          ← toPolynomial_dvd, show fp (gcd p q).toPolynomial = gcd p q from (toPolynomial_Equiv
          (R := R)).left_inv (gcd p q)]
        apply dvd_gcd <;> rw [toPolynomial_dvd, ← this (gcd p.toPolynomial q.toPolynomial)]
        · exact gcd_dvd_left ..
        · exact gcd_dvd_right ..

@[toPolynomialSimp]
lemma toPolynomial_IsUnit {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) :
  IsUnit p = IsUnit p.toPolynomial := by
  unfold IsUnit
  refine propext ⟨?_, ?_⟩
  · intro ⟨u, hu⟩
    use {
      val := u.val.toPolynomial
      inv := u.inv.toPolynomial
      val_inv := by
        have := u.val_inv
        simp only [toPolynomialSimp] at this
        assumption
      inv_val := by
        have := u.inv_val
        simp only [toPolynomialSimp] at this
        assumption
    }
    exact congrArg toPolynomial hu
  · intro ⟨u, hu⟩
    use {
      val := toPolynomial_Equiv.invFun u.val
      inv := toPolynomial_Equiv.invFun u.inv
      val_inv := by
        simp only [toPolynomialSimp]
        rw [show toPolynomial = toPolynomial_Equiv.toFun from rfl,
          toPolynomial_Equiv.right_inv u.val, toPolynomial_Equiv.right_inv u.inv, u.val_inv]
      inv_val := by
        simp only [toPolynomialSimp]
        rw [show toPolynomial = toPolynomial_Equiv.toFun from rfl,
        toPolynomial_Equiv.right_inv u.val, toPolynomial_Equiv.right_inv u.inv, u.inv_val]
    }
    simp only [hu, show toPolynomial = toPolynomial_Equiv.toFun from rfl,
      toPolynomial_Equiv.left_inv p]

@[toPolynomialSimp]
lemma toPolynomial_Irreducible {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) :
  Irreducible p = Irreducible p.toPolynomial := by
  simp only [irreducible_iff, toPolynomial_IsUnit, toPolynomial_eq, toPolynomial_mul, eq_iff_iff,
    and_congr_right_iff]
  intro
  constructor <;> intro h a b
  · specialize @h (toPolynomial_Equiv.invFun a) (toPolynomial_Equiv.invFun b)
    simp only [show toPolynomial = toPolynomial_Equiv.toFun from rfl,
      toPolynomial_Equiv.right_inv a, toPolynomial_Equiv.right_inv b] at h
    exact h
  · apply h

instance {R : Type*} [DecidableEq R] [CommRing R] [IsDomain R] : IsDomain (CPoly R) where
  mul_left_cancel_of_ne_zero := by
    intro a ha x y h
    simp only [toPolynomialSimp] at *
    haveI : IsDomain (Polynomial R) := inferInstance
    apply this.mul_left_cancel_of_ne_zero ha h
  mul_right_cancel_of_ne_zero := by
    intro a ha x y h
    simp only [toPolynomialSimp] at *
    haveI : IsDomain (Polynomial R) := inferInstance
    apply this.mul_right_cancel_of_ne_zero ha h
  exists_pair_ne := by
    use 1, 0
    simp only [toPolynomialSimp] at *
    exact one_ne_zero

instance {R : Type*} [DecidableEq R] [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
  UniqueFactorizationMonoid (CPoly R) := by
  haveI : UniqueFactorizationMonoid (Polynomial R) := inferInstance
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro a ha
  obtain ⟨f, hf₁, hf₂⟩ := this.exists_prime_factors a.toPolynomial <| cast toPolynomial_ne ha
  use (f.map toPolynomial_ringEquiv.symm)
  constructor
  · intro b hb
    rw [Multiset.mem_map] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have := toPolynomial_ringEquiv.eq_symm_apply.1 hbb'.symm
    rw [show toPolynomial_ringEquiv b = toPolynomial b from rfl] at this
    unfold Prime
    simp only [toPolynomialSimp]
    specialize hf₁ b.toPolynomial (this ▸ hb')
    use hf₁.1, hf₁.2.1, fun a c ↦ hf₁.2.2 a.toPolynomial c.toPolynomial
  · obtain ⟨u, hu⟩ := hf₂
    use {
      val := toPolynomial_ringEquiv.invFun u.val
      inv := toPolynomial_ringEquiv.invFun u.inv
      val_inv := by
        simp only [toPolynomialSimp]
        rw [show toPolynomial = toPolynomial_ringEquiv.toFun from rfl,
          toPolynomial_ringEquiv.right_inv u.val, toPolynomial_ringEquiv.right_inv u.inv, u.val_inv]
      inv_val := by
        simp only [toPolynomialSimp]
        rw [show toPolynomial = toPolynomial_ringEquiv.toFun from rfl,
        toPolynomial_ringEquiv.right_inv u.val, toPolynomial_ringEquiv.right_inv u.inv, u.inv_val]
    }
    simp only [Equiv.invFun_as_coe, toPolynomialSimp, ← hu]
    congr
    · rw [← Multiset.prod_map_toList, ← Multiset.prod_toList,
        List.prod_hom f.toList toPolynomial_ringEquiv.symm]
      apply toPolynomial_ringEquiv.right_inv
    · apply toPolynomial_ringEquiv.right_inv

@[toPolynomialSimp]
lemma toPolynomial_Squarefree {R : Type*} [DecidableEq R] [CommSemiring R] (p : CPoly R) :
  Squarefree p = Squarefree p.toPolynomial := by
  refine propext ⟨?_, ?_⟩ <;> unfold Squarefree <;> simp only [toPolynomialSimp] <;> intro h x hx
  · specialize h (toPolynomial_Equiv.invFun x)
    have : (toPolynomial_Equiv.invFun x).toPolynomial = x := by
      apply toPolynomial_Equiv.right_inv
    rw [this] at h
    exact h hx
  · exact h x.toPolynomial hx

lemma squarefree_div_gcd_deriv {R : Type*} [DecidableEq R] [Field R] (f : CPoly R) :
  f ≠ 0 → Squarefree (f / gcd f f.deriv) := by
  simp only [toPolynomialSimp]
  intro hf
  apply (squarefree_iff_emultiplicity_le_one _).2
  intro x
  by_cases IsUnit x
  · exact Or.inr ‹IsUnit x›
  · left
    let d := gcd f.toPolynomial f.toPolynomial.derivative
    rw [show gcd f.toPolynomial f.toPolynomial.derivative = d from rfl]
    let r := f.toPolynomial / d
    rw [show f.toPolynomial / d = r from rfl]
    have hfdr := (EuclideanDomain.div_eq_iff_eq_mul_of_dvd
      f.toPolynomial d r (gcd_ne_zero_of_left hf)
      (gcd_dvd_left ..)).1 rfl
    let k := emultiplicity x f.toPolynomial
    have hk : k = emultiplicity x f.toPolynomial := rfl
    revert hk
    cases k with
    | top =>
      intro h
      have := emultiplicity_eq_top.1 h.symm
      have := FiniteMultiplicity.of_not_isUnit ‹¬IsUnit x› hf
      contradiction
    | coe a =>
    intro hm
    have : emultiplicity x r ≤ a := hm ▸ emultiplicity_le_emultiplicity_of_dvd_right (a := x)
      (EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left f.toPolynomial f.toPolynomial.derivative))
    cases a with
    | zero =>
      apply this.trans
      exact right_eq_inf.1 rfl
    | succ n =>
      have := Nat.add_sub_self_right n 1 ▸ Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd
        (pow_dvd_of_le_emultiplicity (le_of_eq hm))
      have : x ^ n ∣ d := by
        apply dvd_gcd
        · apply pow_dvd_of_le_emultiplicity
          rw [← hm]
          apply ENat.coe_le_coe.2 (Nat.le_succ n)
        · assumption
      have ⟨h1, h2⟩ := emultiplicity_eq_coe.1 hm.symm
      apply Order.le_of_lt_succ
      by_contra h
      simp only [not_lt] at h
      have := mul_dvd_mul this (pow_dvd_of_le_emultiplicity h)
      simp only [Nat.succ_eq_succ, Nat.succ_eq_add_one, Nat.reduceAdd, ← hfdr] at this
      apply h2
      ring_nf at *
      assumption

end CPoly
