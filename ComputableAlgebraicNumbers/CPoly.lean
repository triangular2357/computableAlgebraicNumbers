import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace CPoly

@[simp]
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

@[simp]
private lemma _removeLeadingZeros_nil {R : Type*} [DecidableEq R] [CommSemiring R]
  : _removeLeadingZeros (R := R) [] = [] := rfl

@[simp]
private lemma _removeLeadingZeros_cons {R : Type*} [DecidableEq R] [CommSemiring R]
  {x : R} {xs : List R}
  : _removeLeadingZeros (x :: xs) = if x = 0 then _removeLeadingZeros xs else x :: xs := rfl

@[simp]
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

@[simp]
lemma noTailingZero_removeTailingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
    {l : List R} : noTailingZero (removeTailingZeros l) := by
  unfold noTailingZero removeTailingZeros
  rw [List.reverse_reverse]
  apply _noLeadingZero_removeLeadingZeros

@[simp]
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

@[simp]
lemma coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : CPoly R}
  : removeTailingZeros a.coefs = a.coefs := (noTailingZero_iff'.1 a.condition).symm

@[simp]
lemma removeTailingZeros_removeTailingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
  {l : List R} : removeTailingZeros (removeTailingZeros l) = removeTailingZeros l :=
  (noTailingZero_iff.1 noTailingZero_removeTailingZeros).symm

@[simp]
private lemma _removeLeadingZeros_removeLeadingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
  (l : List R) : _removeLeadingZeros (_removeLeadingZeros l) = _removeLeadingZeros l := by
  rw [←l.reverse_reverse]
  refine List.reverse_inj.1 (Eq.trans ?_ removeTailingZeros_removeTailingZeros)
  simp only [List.reverse_reverse, removeTailingZeros]

@[simp]
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

@[simp]
lemma removeTailingZeros_zero_cons_of_removeTailingZeros
  {R : Type*} [DecidableEq R] [CommSemiring R]
  {as : List R} (h : removeTailingZeros as = []) : removeTailingZeros (0 :: as) = [] := by
  rw [removeTailingZeros_zero_cons_ite, if_pos h]

@[simp]
lemma cons_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {as : List R}
  : removeTailingZeros (a :: removeTailingZeros as) = removeTailingZeros (a :: as) := by
  by_cases h : a = 0
  · simp only [h, removeTailingZeros_zero_cons_ite, removeTailingZeros_removeTailingZeros]
  · simp only [removeTailingZeros_cons_of_ne_zero h, removeTailingZeros_removeTailingZeros]

@[simp]
lemma cons_coh' {R : Type*} [DecidableEq R] [CommSemiring R]
  {a b : R} {as bs : List R} (h : a = b) (hs : removeTailingZeros as = removeTailingZeros bs)
  : removeTailingZeros (a :: as) = removeTailingZeros (b :: bs) := by
  rw [h, ←cons_coh, hs, cons_coh]

def list_add (R : Type*) [CommSemiring R] : List R → List R → List R
  | []     , bs      => bs
  | as     , []      => as
  | a :: as, b :: bs => (a + b) :: (list_add R as bs)

@[simp]
lemma nil_list_add {R : Type*} [CommSemiring R] {a : List R} : list_add R [] a = a := rfl

@[simp]
lemma list_add_nil {R : Type*} [CommSemiring R] {a : List R} : list_add R a [] = a :=
  a.rec rfl (fun _ _ _ ↦ rfl)

@[simp]
lemma cons_list_add_cons {R : Type*} [CommSemiring R] {a b : R} {as bs : List R}
  : list_add R (a :: as) (b :: bs) = (a + b) :: (list_add R as bs) := rfl

@[simp]
lemma list_add_comm {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : list_add R a b = list_add R b a := by
  induction a generalizing b with
  | nil => simp only [nil_list_add, list_add_nil]
  | cons a0 a' ih =>
  induction b with
  | nil => simp only [list_add_nil, nil_list_add]
  | cons b0 b' _ =>
  simp only [cons_list_add_cons, List.cons.injEq]
  use add_comm a0 b0
  apply ih

@[simp]
lemma list_add_coh_left {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : removeTailingZeros (list_add R (removeTailingZeros a) b)
  = removeTailingZeros (list_add R a b) := by
  induction a generalizing b with
  | nil => simp only [removeTailingZeros_nil, nil_list_add]
  | cons a0 as ih =>
  induction b with
  | nil => rw [list_add_nil, list_add_nil, removeTailingZeros_removeTailingZeros]
  | cons b0 bs _ =>
  rw [cons_list_add_cons]
  by_cases ha : a0 = 0
  · rw [ha, zero_add, removeTailingZeros_zero_cons_ite]
    by_cases h : removeTailingZeros as = []
    · rw [if_pos h, nil_list_add]
      apply cons_coh' rfl
      rw [←ih, h, nil_list_add]
    · rw [if_neg h, cons_list_add_cons]
      exact cons_coh' (zero_add b0) ih
  · rw [removeTailingZeros_cons_of_ne_zero ha, cons_list_add_cons]
    exact cons_coh' rfl ih

@[simp]
lemma list_add_coh_right {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : removeTailingZeros (list_add R a (removeTailingZeros b))
  = removeTailingZeros (list_add R a b) := by
  rw [list_add_comm, list_add_coh_left, list_add_comm]

@[simp]
lemma list_add_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : removeTailingZeros (list_add R (removeTailingZeros a) (removeTailingZeros b))
  = removeTailingZeros (list_add R a b) := by
  rw [list_add_coh_left, list_add_coh_right]

@[simp]
lemma list_add_assoc {R : Type*} [DecidableEq R] [CommSemiring R] {a b c : List R}
  : list_add R (list_add R a b) c = list_add R a (list_add R b c) := by
  induction a generalizing b c with
  | nil => simp only [nil_list_add]
  | cons a0 a' ih =>
  induction b generalizing c with
  | nil => simp only [list_add_nil, nil_list_add]
  | cons b0 b' _ =>
  induction c with
  | nil => simp only [cons_list_add_cons, list_add_nil]
  | cons c0 c' _ =>
  simp only [cons_list_add_cons, List.cons.injEq]
  use add_assoc a0 b0 c0
  rw [ih]

def list_smul (R : Type*) [CommSemiring R] : R → List R → List R
  | _,      [] => []
  | r, a :: as => (r*a) :: (list_smul R r as)

@[simp]
lemma list_smul_nil {R : Type*} [CommSemiring R] {a : R}
  : list_smul R a [] = [] := rfl

@[simp]
lemma list_smul_cons {R : Type*} [CommSemiring R] {a b : R} {bs : List R}
  : list_smul R a (b :: bs) = a * b :: list_smul R a bs := rfl

@[simp]
lemma add_list_smul {R : Type*} [CommSemiring R] {a b : R} {c : List R}
  : list_smul R (a + b) c = list_add R (list_smul R a c) (list_smul R b c) := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    rw [list_smul_cons, list_smul_cons, list_smul_cons, cons_list_add_cons, ←ih]
    ring_nf

/-
lemma removeTailingZeros_list_smul_eq_nil_of_removeTailingZeros_eq_nil {R : Type*}
  [DecidableEq R] [CommSemiring R] {a : R} {as : List R} (h : removeTailingZeros as = [])
  : removeTailingZeros (list_smul R a as) = [] := by
  induction as with
  | nil => rfl
  | cons head tail ih =>
    by_cases h' : head = 0
    · rw [h', removeTailingZeros_zero_cons_ite] at h
      rw [list_smul_cons, mul_eq_zero_of_right _ h',
        removeTailingZeros_zero_cons_ite, if_pos (ih ?_)]
      rwa [Ne.ite_eq_left_iff (List.cons_ne_nil _ _).symm] at h
    · rw [removeTailingZeros_cons_of_ne_zero h'] at h
      exfalso
      exact List.cons_ne_nil _ _ h
-/

@[simp]
lemma list_smul_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {as : List R}
  : removeTailingZeros (list_smul R a (removeTailingZeros as))
  = removeTailingZeros (list_smul R a as) := by
  induction as with
  | nil => rw [removeTailingZeros_nil]
  | cons head tail ih =>
    by_cases h : head = 0
    · rw [h, removeTailingZeros_zero_cons_ite]
      by_cases h' : removeTailingZeros tail = []
      · rw [if_pos h', list_smul_cons, mul_zero, removeTailingZeros_zero_cons_ite,
          ←ih, h']
        rfl
      · rw [if_neg h', list_smul_cons, mul_zero, list_smul_cons, mul_zero, cons_coh' rfl ih]
    · rw [removeTailingZeros_cons_of_ne_zero h, list_smul_cons, list_smul_cons, cons_coh' rfl ih]

@[simp]
lemma one_list_smul {R : Type*} [DecidableEq R] [CommSemiring R] {a : List R}
  : list_smul R 1 a = a := by
  induction a with
  | nil => rfl
  | cons head tail ih => rw [list_smul_cons, one_mul, ih]

@[simp]
lemma zero_list_smul_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : List R}
  : removeTailingZeros (list_smul R 0 a) = [] := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [list_smul_cons, ←cons_coh, ih, zero_mul, removeTailingZeros_zero_cons_ite]
    rfl

@[simp]
lemma mul_list_smul {R : Type*} [DecidableEq R] [CommSemiring R] {a b : R} {c : List R}
  : list_smul R (a * b) c = list_smul R a (list_smul R b c) := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    rw [list_smul_cons, list_smul_cons, list_smul_cons, ih, mul_assoc]

@[simp]
lemma list_smul_list_add {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {b c : List R}
  : list_smul R a (list_add R b c) = list_add R (list_smul R a b) (list_smul R a c) := by
  induction b generalizing c with
  | nil => rfl
  | cons b₀ b' ih =>
  induction c with
  | nil => rfl
  | cons c₀ c' _ =>
    rw [cons_list_add_cons, list_smul_cons, list_smul_cons, list_smul_cons, ih, cons_list_add_cons,
      mul_add]

def smul {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) (b : CPoly R) : CPoly R :=
  toCPoly (list_smul R a b.coefs)

def list_mul (R : Type*) [CommSemiring R] : List R → List R → List R
  | []     , _  => []
  | a :: as, bs => list_add R (list_smul R a bs) (0 :: list_mul R as bs)

@[simp]
lemma nil_list_mul {R : Type*} [CommSemiring R] {a : List R} : list_mul R [] a = [] := rfl

@[simp]
lemma cons_list_mul {R : Type*} [CommSemiring R] {a : R} {as bs : List R}
  : list_mul R (a :: as) bs = list_add R (list_smul R a bs) (0 :: list_mul R as bs) := rfl

@[simp]
lemma list_mul_nil_coh {R : Type*} [CommSemiring R] [DecidableEq R] {a : List R}
  : removeTailingZeros (list_mul R a []) = [] := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [cons_list_mul, list_smul_nil, nil_list_add, removeTailingZeros_zero_cons_ite, if_pos ih]

@[simp]
lemma list_mul_cons_coh {R : Type*} [CommSemiring R] [DecidableEq R] {b : R} {as bs : List R}
  : removeTailingZeros (list_mul R as (b :: bs))
  = removeTailingZeros (list_add R (0 :: list_mul R as bs) (list_smul R b as)) := by
  induction as with
  | nil =>
    rw [nil_list_mul, nil_list_mul, list_smul_nil, list_add_nil,
      removeTailingZeros_zero_cons_ite, if_pos] <;> rfl
  | cons head tail ih =>
    rw [cons_list_mul, list_smul_cons, cons_list_add_cons, list_smul_cons, cons_list_mul,
      cons_list_add_cons, list_add_assoc]
    apply cons_coh' (by ring)
    rw [←list_add_coh_right, ih, list_add_coh_right]

@[simp]
lemma list_mul_comm_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : removeTailingZeros (list_mul R a b) = removeTailingZeros (list_mul R b a) := by
  induction a with
  | nil => rw [nil_list_mul, list_mul_nil_coh, removeTailingZeros_nil]
  | cons head tail ih =>
    rw [cons_list_mul, list_mul_cons_coh, list_add_comm, ←list_add_coh_left, ←cons_coh,
      ih, cons_coh, list_add_coh_left]

@[simp]
lemma list_mul_coh_right {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : removeTailingZeros (list_mul R a (removeTailingZeros b))
  = removeTailingZeros (list_mul R a b) := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [cons_list_mul, ←list_add_coh, list_smul_coh, cons_list_mul]
    nth_rw 2 [←list_add_coh]
    rw [cons_coh' rfl ih]

@[simp]
lemma list_mul_coh_left {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : removeTailingZeros (list_mul R (removeTailingZeros a) b)
  = removeTailingZeros (list_mul R a b) := by
  rw [list_mul_comm_coh, list_mul_coh_right, list_mul_comm_coh]

@[simp]
lemma list_mul_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a b : List R}
  : removeTailingZeros (list_mul R (removeTailingZeros a) (removeTailingZeros b))
  = removeTailingZeros (list_mul R a b) := by
  rw [list_mul_coh_left, list_mul_coh_right]

@[simp]
lemma list_mul_list_add {R : Type*} [DecidableEq R] [CommSemiring R] {a b c : List R}
  : list_mul R a (list_add R b c) = list_add R (list_mul R a b) (list_mul R a c) := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [cons_list_mul, ih, ←add_zero 0, ←cons_list_add_cons, list_smul_list_add, list_add_assoc,
      ←list_add_assoc (a := list_smul R head c), list_add_comm (a := list_smul R head c),
      list_add_assoc, ←list_add_assoc, ←cons_list_mul, ←cons_list_mul]

@[simp]
lemma list_add_list_mul {R : Type*} [DecidableEq R] [CommSemiring R] {a b c : List R}
  : list_mul R (list_add R a b) c = list_add R (list_mul R a c) (list_mul R b c) := by
  induction a generalizing b with
  | nil => rw [nil_list_add, nil_list_mul, nil_list_add]
  | cons a₀ a' ih =>
  induction b with
  | nil => rw [list_add_nil, nil_list_mul, list_add_nil]
  | cons b₀ b' _ =>
  rw [cons_list_add_cons, cons_list_mul, cons_list_mul, cons_list_mul, add_list_smul,
    list_add_assoc, list_add_assoc]
  nth_rw 5 [list_add_comm]
  rw [list_add_assoc, cons_list_add_cons, zero_add, ih]
  simp only [list_add_comm]

@[simp]
lemma list_smul_list_mul {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {b c : List R}
  : list_mul R (list_smul R a b) c = list_smul R a (list_mul R b c) := by
  induction b generalizing a with
  | nil => rfl
  | cons head tail ih =>
    rw [list_smul_cons, cons_list_mul, ih, mul_list_smul, cons_list_mul,
      list_smul_list_add, list_smul_cons, mul_zero]

@[simp]
lemma list_mul_assoc_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a b c : List R}
  : removeTailingZeros (list_mul R (list_mul R a b) c)
  = removeTailingZeros (list_mul R a (list_mul R b c)) := by
  induction a with
  | nil => simp only [nil_list_mul]
  | cons a₀ a' ih =>
    nth_rw 2 [cons_list_mul]
    rw [←list_add_coh_right, ←cons_coh, ←ih, cons_list_mul, list_add_list_mul, list_smul_list_mul,
      ←list_add_coh_right, ←list_mul_coh_left, ←cons_coh, list_mul_coh_left]
    congr 2
    rw [cons_list_mul, ←list_add_coh_left, zero_list_smul_coh, nil_list_add,
      ←cons_coh, list_mul_coh_left]

@[simp]
lemma singleton_list_mul_coh {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {as : List R}
  : removeTailingZeros (list_mul R [a] as) = removeTailingZeros (list_smul R a as) := by
  rw [cons_list_mul, ←list_add_coh_right, ←cons_coh,
    removeTailingZeros_zero_cons_of_removeTailingZeros rfl, list_add_nil]

@[simp]
lemma list_mul_singleton {R : Type*} [DecidableEq R] [CommSemiring R] {a : R} {as : List R}
  : list_mul R as [a] = list_smul R a as := by
  induction as with
  | nil => rfl
  | cons head tail ih =>
    rw [cons_list_mul, ih, list_smul_cons, cons_list_add_cons, list_smul_nil, nil_list_add,
    list_smul_cons, add_zero, mul_comm]

def list_neg (R : Type*) [CommRing R] : List R → List R
  | []      => []
  | a :: as => -a :: list_neg R as

@[simp]
lemma list_neg_nil {R : Type*} [CommRing R] : list_neg R [] = [] := rfl

@[simp]
lemma list_neg_cons {R : Type*} [CommRing R] {a : R} {as : List R}
  : list_neg R (a :: as) = -a :: list_neg R as := rfl

@[simp]
lemma list_neg_eq_list_smul_neg_one {R : Type*} [CommRing R] {a : List R}
  : list_neg R a = list_smul R (-1) a := by
  induction a with
  | nil => rfl
  | cons head tail ih => exact congr_arg₂ _ (neg_eq_neg_one_mul head) ih

@[simp]
lemma list_neg_coh {R : Type*} [DecidableEq R] [CommRing R] {a : List R}
  : removeTailingZeros (list_neg R (removeTailingZeros a)) = removeTailingZeros (list_neg R a) := by
  simp only [list_neg_eq_list_smul_neg_one, list_smul_coh]

def list_sub (R : Type*) [CommRing R] : List R → List R → List R
  | []     , bs      => list_neg R bs
  | as     , []      => as
  | a :: as, b :: bs => (a - b) :: (list_sub R as bs)

@[simp]
lemma nil_list_sub {R : Type*} [CommRing R] {a : List R} : list_sub R [] a = list_neg R a := rfl

@[simp]
lemma list_sub_nil {R : Type*} [CommRing R] {a : List R} : list_sub R a [] = a :=
  a.rec rfl (fun _ _ _ ↦ rfl)

@[simp]
lemma cons_list_sub_cons {R : Type*} [CommRing R] {a b : R} {as bs : List R}
  : list_sub R (a :: as) (b :: bs) = (a - b) :: (list_sub R as bs) := rfl

@[simp]
lemma list_sub_eq_list_add_list_neg {R : Type*} [CommRing R] {a b : List R}
  : list_sub R a b = list_add R a (list_neg R b) := by
  induction a generalizing b with
  | nil => exact nil_list_sub
  | cons a₀ a' ih =>
  induction b with
  | nil => exact list_sub_nil
  | cons b₀ b' _ =>
  rw [cons_list_sub_cons, list_neg_cons, cons_list_add_cons, ih, sub_eq_add_neg]

@[simp]
lemma list_sub_coh_left {R : Type*} [DecidableEq R] [CommRing R] {a b : List R}
  : removeTailingZeros (list_sub R (removeTailingZeros a) b)
  = removeTailingZeros (list_sub R a b) := by
  simp only [list_sub_eq_list_add_list_neg, list_add_coh_left]

@[simp]
lemma list_sub_coh_right {R : Type*} [DecidableEq R] [CommRing R] {a b : List R}
  : removeTailingZeros (list_sub R a (removeTailingZeros b))
  = removeTailingZeros (list_sub R a b) := by
  rw [list_sub_eq_list_add_list_neg, ←list_add_coh_right, list_neg_coh,
    list_sub_eq_list_add_list_neg, list_add_coh_right]

@[simp]
lemma list_sub_coh {R : Type*} [DecidableEq R] [CommRing R] {a b : List R}
  : removeTailingZeros (list_sub R (removeTailingZeros a) (removeTailingZeros b))
  = removeTailingZeros (list_sub R a b) := by
  rw [list_sub_coh_left, list_sub_coh_right]

@[simp]
lemma list_neg_list_add_cancel_coh {R : Type*} [DecidableEq R] [CommRing R] {a : List R}
  : removeTailingZeros (list_add R (list_neg R a) a) = [] := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [list_neg_cons, cons_list_add_cons, neg_add_cancel,
      removeTailingZeros_zero_cons_of_removeTailingZeros ih]

 --semiring so Polys in ℕ work idk if this is useful
def list_eval (R : Type*) [CommSemiring R] : List R → R → R
  | [] => 0
  | a :: as => fun r ↦ a + r * list_eval R as r

def eval {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) (b : R) : R :=
  list_eval R a.coefs b

@[simp]
def add {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_add R a.coefs b.coefs)

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Add (CPoly R) := ⟨add⟩

@[simp]
lemma add_def {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : a + b = add a b := rfl

lemma add_coh {R : Type*} [DecidableEq R] [CommSemiring R] (a b : List R)
  : toCPoly a + toCPoly b = toCPoly (list_add R a b) := by
  simp only [add_def, add, toCPoly, list_add_coh]

lemma add_assoc {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a + b + c = a + (b + c) := by
  simp only [add_def, add, toCPoly, list_add_coh_left, list_add_coh_right, list_add_assoc]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddSemigroup (CPoly R) := ⟨add_assoc⟩

@[simp]
def zero {R : Type*} [DecidableEq R] [CommSemiring R] : CPoly R := ⟨[], trivial⟩

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Zero (CPoly R) := ⟨zero⟩

@[simp]
lemma zero_def {R : Type*} [DecidableEq R] [CommSemiring R] : (0 : CPoly R) = zero := rfl

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZero (CPoly R) := ⟨⟩

lemma zero_add {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 0 + a = a := by
  ext1
  simp
  -- simp only [zero_def, zero, add_def, add, toCPoly, nil_list_add, coh]


lemma add_zero {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a + 0 = a := by
  ext1
  simp
  -- simp only [zero_def, zero, add_def, add, toCPoly, list_add_nil, coh]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZeroClass (CPoly R)
  := ⟨zero_add, add_zero⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddMonoid (CPoly R) where
  nsmul := nsmulRec

lemma add_comm {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R)
  : a + b = b + a := by simp
  -- simp only [add_def, add, toCPoly, list_add_comm]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMagma (CPoly R) := ⟨add_comm⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommSemigroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMonoid (CPoly R) where

@[simp]
def mul {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_mul R a.coefs b.coefs)

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Mul (CPoly R) := ⟨mul⟩

@[simp]
lemma mul_def {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : a * b = mul a b := rfl

lemma mul_coh {R : Type*} [DecidableEq R] [CommSemiring R] (a b : List R)
  : toCPoly a * toCPoly b = toCPoly (list_mul R a b) := by
  simp only [mul_def, mul, toCPoly, list_mul_coh]

lemma zero_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 0 * a = 0 := by
  ext1
  simp
  -- simp only [zero_def, zero, mul_def, mul, toCPoly, nil_list_mul, removeTailingZeros_nil]

lemma mul_zero {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a * 0 = 0 := by
  ext1
  simp
  -- simp only [zero_def, zero, mul_def, mul, toCPoly, list_mul_nil_coh]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroClass (CPoly R)
  := ⟨zero_mul, mul_zero⟩

lemma mul_assoc {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a * b * c = a * (b * c) := by
  simp only [mul_def, mul, toCPoly, list_mul_coh_left, list_mul_coh_right, list_mul_assoc_coh]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semigroup (CPoly R) := ⟨mul_assoc⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : SemigroupWithZero (CPoly R) where

@[simp]
def one {R : Type*} [DecidableEq R] [CommSemiring R] : CPoly R := toCPoly [1]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : One (CPoly R) := ⟨one⟩

@[simp]
lemma one_def {R : Type*} [DecidableEq R] [CommSemiring R] : (1 : CPoly R) = one := rfl

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOne (CPoly R) := ⟨⟩

lemma one_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : 1 * a = a := by
  ext1
  simp
  -- simp only [one_def, one, mul_def, mul, toCPoly, list_mul_coh_left, singleton_list_mul_coh,
  --   one_list_smul, coh]
lemma mul_one {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) : a * 1 = a := by
  ext1
  simp
  -- simp only [one_def, one, mul_def, mul, toCPoly, list_mul_coh_right, list_mul_singleton,
  --   one_list_smul, coh]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOneClass (CPoly R) := ⟨one_mul, mul_one⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroOneClass (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Monoid (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MonoidWithZero (CPoly R) where

lemma mul_comm {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R)
  : a * b = b * a := by simp
  -- simp only [mul_def, mul, toCPoly, list_mul_comm_coh]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommMagma (CPoly R) := ⟨mul_comm⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommSemigroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommMonoid (CPoly R) where

lemma mul_add {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : a * (b + c) = a * b + a * c := by simp
  -- simp only [mul_def, add_def, mul, add, toCPoly,
  --   list_mul_coh_right, list_add_coh,list_mul_list_add]

lemma add_mul {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R)
  : (a + b) * c = a * c + b * c := by simp only [mul_def, add_def, mul, add, toCPoly,
    list_mul_coh_left, list_add_coh, list_add_list_mul]

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Distrib (CPoly R) := ⟨mul_add, add_mul⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalNonAssocSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonAssocSemiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semiring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommSemiring R] : CommSemiring (CPoly R) where

@[simp]
def neg {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) : CPoly R :=
  toCPoly (list_neg R a.coefs)

instance {R : Type*} [DecidableEq R] [CommRing R] : Neg (CPoly R) := ⟨neg⟩

@[simp]
lemma neg_def {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) : -a = neg a := rfl

lemma neg_coh {R : Type*} [DecidableEq R] [CommRing R] (a : List R)
  : -toCPoly a = toCPoly (list_neg R a) := by
  simp only [neg_def, neg, toCPoly, list_neg_coh]

@[simp]
def sub {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_sub R a.coefs b.coefs)

instance {R : Type*} [DecidableEq R] [CommRing R] : Sub (CPoly R) := ⟨sub⟩

@[simp]
lemma sub_def {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R) : a - b = sub a b := rfl

lemma sub_coh {R : Type*} [DecidableEq R] [CommRing R] (a b : List R)
  : toCPoly a - toCPoly b = toCPoly (list_sub R a b) := by
  simp only [sub_def, sub, toCPoly, list_sub_coh]

lemma sub_eq_add_neg {R : Type*} [DecidableEq R] [CommRing R] (a b : CPoly R)
  : a - b = a + -b := by
  simp only [sub_def, sub, toCPoly, list_sub_eq_list_add_list_neg,
    neg_def, neg, add_def, add, list_add_coh_right]

instance {R : Type*} [DecidableEq R] [CommRing R] : SubNegMonoid (CPoly R) where
  sub_eq_add_neg := sub_eq_add_neg
  zsmul := zsmulRec

lemma neg_add_cancel {R : Type*} [DecidableEq R] [CommRing R] (a : CPoly R) : -a + a = 0 := by
  simp only [neg_def, neg, toCPoly, add_def, add,
    list_add_coh_left, list_neg_list_add_cancel_coh, zero_def, zero]

instance {R : Type*} [DecidableEq R] [CommRing R] : AddGroup (CPoly R) := ⟨neg_add_cancel⟩
instance {R : Type*} [DecidableEq R] [CommRing R] : AddCommGroup (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommRing R] : Ring (CPoly R) where
instance {R : Type*} [DecidableEq R] [CommRing R] : CommRing (CPoly R) where

def ℤdiv : ℤ  → List ℤ → List ℤ
  | _,      [] => []
  | r, a :: as => (a/r) :: (ℤdiv r as)

def ℚdiv : ℚ  → List ℚ → List ℚ
  | _,      [] => []
  | r, a :: as => (a / r) :: (ℚdiv r as)

def ℤgcd : List ℤ → ℕ
  | [] => 0
  | r::[]=> r.natAbs
  | r::rs=> r.gcd (ℤgcd rs)

def ℚlcd : List ℚ → ℕ --least common denominator
  | [] => 1
  | r::[]=> r.den
  | r::rs=> r.den.lcm (ℚlcd rs)

def ℤnormalize (i : List ℤ):List ℤ :=
  let i' := removeTailingZeros i
  --last element must not be zero otherwise it breaks because then getLastD returns 0
  ℤdiv ((i'.getLastD 1).sign * ℤgcd i') i'

def toNormℤPoly (i : List ℤ):CPoly ℤ:=
  toCPoly (ℤnormalize i)

def ℚnormalize (i : List ℚ):List ℚ :=
    let i' := removeTailingZeros i
  --last element must not be zero otherwise it breaks because then getLastD returns 0
  ℚdiv (i'.getLastD 1) i'

private def _ℚrevNorm (i : List ℚ):List ℚ :=
  if (i.getD 0 0) = 0 then i else
  ℚdiv (i.getD 0 1) i

def toNormℚPoly (i : List ℚ):CPoly ℚ:=
  toCPoly (ℚnormalize i)

def ℤℚconvert : List ℤ → List ℚ
  | [] => []
  | z::zs=> z :: ℤℚconvert zs

def ℚℤconvert (i : List ℚ) : List ℤ :=
  let rec _ℚℤmulConvert : ℤ → List ℚ → List ℤ
    | _, [] => []
    | x,z::zs=> (z*x).num / (z*x).den  :: _ℚℤmulConvert x zs
  _ℚℤmulConvert (ℚlcd i) i



-- TODO replace this with the rewrite below using arrays
-- (to make it faster and enable easier provable correctness)
-- unsafe because I still need to show termination
-- maximum of M.map (fun l ↦ l.length) could work
-- does gaussian elimination
private unsafe def _OLDreducedRowEchelonForm (M : List (List ℚ)) :List (List ℚ) :=
  let normedM := M.map (_ℚrevNorm)
  let i := normedM.findFinIdx? (fun l ↦ ¬( l.getD 0 0 = 0))
  if h : i.isSome then
    let i := i.get h
    --make sure the only non zero in the first column is a one in row i
    --we move row i up at the end maybe we can already do this here
    --(if we use arrays there is array.swap)
    let M'' := normedM.mapIdx (fun idx l ↦
      if idx = i then l else
      if l.getD 0 0 = 0 then l else
      list_sub ℚ l normedM[i]!
    )
    let stay := M''.find? (fun l ↦ ¬( l.getD 0 0 = 0)) --should only contain the i's row
    let smaller := (M''.filter (fun l ↦ l.getD 0 0 = 0)).map ( --should contain everything else
      fun l => match l with | [] => [] | _ :: qs => qs) -- removes the first column
    let processedSmaller := _OLDreducedRowEchelonForm smaller
    let processedSmallerWithLeadingZeros :=
      processedSmaller.map (fun l ↦ 0::l)
    if h' : stay.isSome then
      let first := processedSmallerWithLeadingZeros.find? ⊤
      if h'' : first.isSome then
        let q:ℚ := (stay.get h').getD 1 0 -- get second index to make it zero
        list_sub ℚ (stay.get h') (list_smul ℚ q (first.get h'')) :: processedSmallerWithLeadingZeros
      else
        stay.get h' :: processedSmallerWithLeadingZeros
    else
      processedSmallerWithLeadingZeros
  else
    normedM


structure Array2d (R : Type*) where
  data : Array R -- make sure that there is only one reference to this at a time
  row_count : ℕ  -- then the compiler optimizes it to modify it in place
  column_count : ℕ
  condition : data.size = row_count * column_count

def _at (R : Type*) (M : Array2d R) (row : ℕ) (column : ℕ)
  (h : row < M.row_count) (h' : column < M.column_count) : R :=
  have : M.data.size > row*M.column_count+column := by
    rw [M.condition]
    simp only [gt_iff_lt]
    grw [← Order.add_one_le_iff] at h h' ⊢
    rw [_root_.add_assoc (row * M.column_count) column 1]
    grw [h']
    rw [← Nat.add_one_mul row M.column_count]
    grw [h]
  M.data[row*M.column_count+column]

private unsafe def _matrixToReducedRowEchelonForm (M : List (List ℚ)) :List (List ℚ) :=
  --TODO just take the Array2d as input and let another fuction handle the conversion (maybe solve)
  let length_lists' := M.map List.length
  let length_lists := length_lists'.toSSet.toList
  if length_unique:length_lists.length > 1 then [] else
  if length_non_zero: length_lists.length = 0 then [] else
  let length := length_lists[0]
  let flatArrry := M.flatten.toArray
  have :flatArrry.size = length*M.length := by
    rw [List.size_toArray]
    rw [List.length_flatten]

    have h:(List.map List.length M).sum = length_lists'.sum := by rfl
    rw [h]
    have :length_lists'.sum = length_lists[0] *length_lists'.length := by
      sorry
    sorry
  let Matrix := Array2d.mk flatArrry length M.length
  let M := M.map (_ℚrevNorm)
  let i := M.findFinIdx? (fun (l:List ℚ) ↦ ¬( l.getD 0 0 = 0))
  if h : i.isSome then
    let i := i.get h
    --make sure the only non zero in the first column is a one in row i
    --we move row i up at the end maybe we can already do this here
    --(if we use arrays there is array.swap)
    let M'' := M.mapIdx (fun idx (l:List ℚ) ↦
      if idx = i then l else
      if l.getD 0 0 = 0 then l else
      list_sub ℚ l M[i]!
    )
    let stay := M''.find? (fun (l:List ℚ) ↦ ¬( l.getD 0 0 = 0)) --should only contain the i's row
    let smaller :=                                               --should contain everything else
      (M''.filter (fun (l:List ℚ) ↦ l.getD 0 0 = 0)).map (
      fun l => match l with | [] => [] | _ :: qs => qs) -- removes the first column
    let processedSmaller := _OLDreducedRowEchelonForm smaller
    let processedSmallerWithLeadingZeros :=
      processedSmaller.map (fun l ↦ 0::l)
    if h' : stay.isSome then
      let first := processedSmallerWithLeadingZeros.find? ⊤
      if h'' : first.isSome then
        let q:ℚ := (stay.get h').getD 1 0 -- get second index to make it zero
        list_sub ℚ (stay.get h') (list_smul ℚ q (first.get h'')) :: processedSmallerWithLeadingZeros
      else
        stay.get h' :: processedSmallerWithLeadingZeros
    else
      processedSmallerWithLeadingZeros
  else
    M

unsafe def solve (M : List (List ℚ)) :List ℚ :=
  let solvedM := _OLDreducedRowEchelonForm M
  let max_length := (solvedM.map (fun l ↦ l.length)).max?
  if h : max_length.isSome then
    ((Array.range ((max_length.get h)-1)).map (fun i ↦ -- there is probably a nicer way to do this
      let e := solvedM.find? (fun l ↦ (¬ ((l.getD i 0)=0)))
      if h : e.isSome then
        (e.get h).getLastD 0
      else
        0
    )).toList
  else
    []

/-
#eval list_mul ℤ [1]           [3]
#eval list_mul ℤ [1,4]         [3]
#eval list_mul ℤ [1,4]       [3,4]
#eval list_mul ℤ [1,2,3,4]   [5,7]
#eval list_add ℤ [1,4]         [3]
#eval list_smul ℤ 2          [1,4]
#eval list_eval ℤ [4,2] 2
#eval list_eval ℤ [2,3,-1] (-1)
#eval list_eval ℤ [0,6] 2
#eval list_eval ℤ [0,0,0,0,1] 2

#eval _reducedRowEchelonForm [[1,1]]
#eval _reducedRowEchelonForm [[2,1]]
#eval _reducedRowEchelonForm [[0,1]]
#eval _reducedRowEchelonForm [[2,1,3],[1,2,3]]
#eval _reducedRowEchelonForm [[2,1,3],[2,4,6]]
#eval _reducedRowEchelonForm [[2,4,6],[2,1,3]]
#eval _reducedRowEchelonForm [[2,4,12],[2,1,6]]
#eval _reducedRowEchelonForm [[0,1,3],[1,2,4]]
#eval _reducedRowEchelonForm [[0,1,3],[123,-2,5]]
#eval solve [[2,4,6],[2,1,3]]
#eval solve [[2,4,12],[2,1,6]]
#eval solve [[0,1,3],[1,2,4]]
#eval _reducedRowEchelonForm [[1,2,3],[1,2,4]]
#eval solve [[1,2,3],[1,2,4]]
#eval solve [[1,0,3],[1,0,4]]
#eval solve []
#eval ℤdiv   2 [4,2,0,-1,1,4]
#eval ℤnormalize   [4,2,0,4]
#eval ℤnormalize   [4,2,0]
#eval ℤnormalize   [-6]
#eval ℚdiv   2 [4,2,0,-1,1,4]
#eval ℚnormalize [4,2,0,-1,1,4]
#eval ℚℤconvert (ℚnormalize [4,2,0,-1,1,4])
#eval ℤℚconvert [4,2,0,-1,1,4]
-/
end CPoly
