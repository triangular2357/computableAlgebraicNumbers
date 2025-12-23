import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace CPoly

private def _noLeadingZero {R : Type*} [CommSemiring R] : List R → Prop
  | []     => True
  | x :: _ => x ≠ 0

def noTailingZero {R : Type*} [CommSemiring R] (l : List R) : Prop :=
  _noLeadingZero l.reverse

end CPoly

@[ext] structure CPoly (R : Type*) [CommSemiring R] where
  coefs : List R -- `[c₀,c₁,c₂,...,cₙ]` and then `∑ Xⁱcᵢ`
  condition : CPoly.noTailingZero coefs

namespace CPoly

private def _removeLeadingZeros {R : Type*} [DecidableEq R] [CommSemiring R] : List R → List R
  | []      => []
  | x :: xs => if x = 0 then _removeLeadingZeros xs else x :: xs

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

lemma removeTailingZeros_removeTailingZeros {R : Type*} [DecidableEq R] [CommSemiring R]
  {l : List R} :
  removeTailingZeros (removeTailingZeros l) = removeTailingZeros l :=
  (noTailingZero_iff.1 noTailingZero_removeTailingZeros).symm

def list_add (R : Type*) [CommSemiring R] : List R → List R → List R
  | []     , bs      => bs
  | as     , []      => as
  | a :: as, b :: bs => (a+b) :: (list_add R as bs)

def add {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_add R a.coefs b.coefs)

lemma add_coh {R : Type*} [DecidableEq R] [CommSemiring R] (a b : List R)
  : add (toCPoly a) (toCPoly b) = toCPoly (list_add R a b) := by
  sorry

def list_smul (R : Type*) [CommSemiring R] : R → List R → List R
  | _,      [] => []
  | r, a :: as => (r*a) :: (list_smul R r as)

def smul {R : Type*} [DecidableEq R] [CommSemiring R] (a : R) (b : CPoly R) : CPoly R :=
  toCPoly (list_smul R a b.coefs)

def list_mul (R : Type*) [CommSemiring R] : List R → List R → List R
  | []     , _  => []
  | a :: as, bs => list_add R (list_smul R a bs) (0 :: list_mul R as bs)

def list_sub (R : Type*) [CommRing R] : List R → List R → List R
  | []     , bs      => list_smul R (-1) bs
  | as     , []      => as
  | a :: as, b :: bs => (a-b) :: (list_sub R as bs)

def mul {R : Type*} [DecidableEq R] [CommSemiring R] (a b : CPoly R) : CPoly R :=
  toCPoly (list_mul R a.coefs b.coefs)

 --semiring so Polys in ℕ work idk if this is useful
def list_eval (R : Type*) [CommSemiring R] : List R → R → R
  | [] => 0
  | a :: as => fun r ↦ a + r * list_eval R as r

def eval {R : Type*} [DecidableEq R] [CommSemiring R] (a : CPoly R) (b : R) : R :=
  list_eval R a.coefs b

instance {R : Type*} [DecidableEq R] [CommSemiring R] : Add (CPoly R) := ⟨add⟩

lemma add_assoc {R : Type*} [DecidableEq R] [CommSemiring R] (a b c : CPoly R) : a + b + c = a + (b + c) := by
  ext1
  simp [· + ·, show Add.add (α := CPoly R) = add by rfl, add]
  repeat rw [←add_coh]
  sorry

instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddSemigroup (CPoly R) := ⟨add_assoc⟩
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Zero (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZero (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddZeroClass (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddMonoid (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMagma (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommSemigroup (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : AddCommMonoid (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Mul (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Distrib (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroClass (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalNonAssocSemiring (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semigroup (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : SemigroupWithZero (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonUnitalSemiring (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : One (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOne (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulOneClass (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MulZeroOneClass (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : NonAssocSemiring (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Monoid (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : SemigroupWithZero (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : MonoidWithZero (CPoly R) := sorry
instance {R : Type*} [DecidableEq R] [CommSemiring R] : Semiring (CPoly R) := sorry


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
  let i' := (toCPoly i).coefs --maybe make a new function only on lists?
  --last element must not be zero otherwise it breaks because then getLastD returns 0
  ℤdiv ((i'.getLastD 1).sign * ℤgcd i') i'

def toNormℤPoly (i : List ℤ):CPoly ℤ:=
  toCPoly (ℤnormalize i)

def ℚnormalize (i : List ℚ):List ℚ :=
    let i' := (toCPoly i).coefs --maybe make a new function only on lists?
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


-- unsafe because I still need to show termination
-- maximum of M.map (fun l ↦ l.length) should work
-- TODO clean up or remove the option unwraping
-- Maybe rewrite with arrays for performance (its really slow for some reason)
-- does gaussian elimination
private unsafe def _reducedRowEchelonForm (M : List (List ℚ)) :List (List ℚ) :=
  let M := M.map (_ℚrevNorm)
  let i := M.findFinIdx? (fun l ↦ ¬( l.getD 0 0 = 0))
  if h : i.isSome then
    let i := i.get h
    --make sure the only non zero in the first column is a one in row i
    --we move row i up at the end maybe we can already do this here
    --(if we use arrays there is array.swap)
    let M'' := M.mapIdx (fun idx l ↦
      if idx = i then l else
      if l.getD 0 0 = 0 then l else
      list_sub ℚ l M[i]!
    )
    let stay := M''.find? (fun l ↦ ¬( l.getD 0 0 = 0)) --should only contain the i's row
    let smaller := (M''.filter (fun l ↦ l.getD 0 0 = 0)).map ( --should contain everything else
      fun l => match l with | [] => [] | _ :: qs => qs) -- removes the first column
    let processedSmaller := _reducedRowEchelonForm smaller
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
  let solvedM := _reducedRowEchelonForm M
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

end CPoly
