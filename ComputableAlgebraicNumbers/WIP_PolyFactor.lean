import ComputableAlgebraicNumbers.CPoly
--import Mathlib

def CPoly.IsDevisorOf (q : CPoly ℕ) (p : CPoly ℕ) := ∃ (s:CPoly ℕ) , s*q=p

def CPoly.Devide (p : CPoly ℕ) (q : CPoly ℕ) (h : q.IsDevisorOf p) : CPoly ℕ := sorry

lemma sagdf (p : CPoly ℕ) (q : CPoly ℕ) (h : q.IsDevisorOf p) :
  (p.Devide q h)*q = p := by
    unfold CPoly.Devide
    sorry


--split_ifs is a very good taktic

private def Nat._getPrimes' (n : Nat) (l : List Nat) : List Nat :=
  if n≤1 then l else
  n.minFac :: (n/n.minFac)._getPrimes' l
termination_by n
decreasing_by
  expose_names --to remove unused variable warning TODO test with newest version and create issue
  simp only [not_le] at h
  have := Nat.minFac_prime (n:=n) (Ne.symm (ne_of_lt h))
  have : n.minFac>1:=by
    exact Prime.one_lt this
  refine div_lt_self ?_ this
  exact zero_lt_of_lt h


--def Nat.getPrimes (n : Nat) : Multiset Nat := Quot.mk _ ((n)._getPrimes [])
private def Nat._getPrimes (n : Nat) : List Int := ((n)._getPrimes' [])

def Int.getPrimes (z : Int) : List Int :=
  (if sign z=-1 then [-(1:ℤ)] else [])
  ++(Nat._getPrimes z.natAbs)
#eval (100)._getPrimes
#eval (-100).getPrimes

private def CPoly._eval_at_range_degree (p : CPoly ℤ) : List ℤ:=
  (List.range (p.coefs.length)).map (p.eval ·)

def list_contains_zero {R : Type*} [CommSemiring R] : List R → Prop
  | []     => False
  | x :: xs => x = 0 ∨ list_contains_zero xs

--def list_contains_zero (l : List ℕ):=
--  (l.map (· = 0)).foldl (· ∨ ·) False


instance (l : List ℕ) :  Decidable (list_contains_zero l) := by
  unfold list_contains_zero
  induction l with
  | nil => simp only; exact instDecidableFalse
  | cons head tail ih => simp only ; unfold list_contains_zero ; exact instDecidableOr

#eval -2 % 3
#eval -9 % 3
#eval list_contains_zero [5,1]
#eval [4,0,3,4].findFinIdx? (· = 0)
#eval mkRat 1 0

def ℤgcd : List ℤ → ℕ
  | [] => 0
  | r::[]=> r.natAbs
  | r::rs=> r.gcd (ℤgcd rs)

def ℤdiv : ℤ  → List ℤ → List ℤ
  | _,      [] => []
  | r, a :: as => (a/r) :: (ℤdiv r as)

def ℤnormalize (p : CPoly ℤ):CPoly ℤ × ℤ:=
  let z := (p.coefs.getLastD 1).sign * ℤgcd p.coefs;
  ⟨CPoly.toCPoly (ℤdiv z p.coefs),z⟩

private def _SubSetList : (l : List ℤ) → (p:List (List ℤ)) → List (List ℤ)
  | [],p => p
  | l::ls, p => _SubSetList ls (p.flatMap (fun e ↦ [(l :: e), (e)]))


def SubSetList (l : List ℤ) : List (List ℤ)  :=
  (_SubSetList l [[]]).dedup --TODO sort by abs(product)

#eval _SubSetList [1,2,3] [[]]


def factor (p : CPoly ℤ) : CPoly ℤ:=
  let ⟨p',z⟩  := ℤnormalize p;
  if z ≠ 1 then
    CPoly.toCPoly [z]
  else
  let evaled := p'._eval_at_range_degree
  match (evaled.findFinIdx? (· = 0)) with
  | some val => CPoly.toCPoly [-(val:ℤ),1]
  | none =>
  let evaledFactorized := evaled.map (·.getPrimes)
  p

def divide (p : CPoly ℚ) (q : CPoly ℚ) : CPoly ℚ × CPoly ℚ :=
  sorry

lemma divide_lowers_degree (p : CPoly ℚ) (q : CPoly ℚ) : q.degree > ((divide p q).2).degree := by
  sorry

lemma _divide_lowers_degree (p : CPoly ℚ) (q : CPoly ℚ) : q.degree ≥ ((divide p q).2).degree := by
  grind only [!divide_lowers_degree]


partial def _gcd (p : CPoly ℚ) (q : CPoly ℚ) (h : p.degree ≥ q.degree):CPoly ℚ:=
  _gcd q (divide p q).2 (_divide_lowers_degree p q)
  -- divide p/q and recursively call it self with q and the remainder
  -- until the remainder vanishes (is that the right word I mean that it gets zero)

def gcd (p : CPoly ℚ) (q : CPoly ℚ) :CPoly ℚ:=
  if h: p.degree ≥ q.degree then
    _gcd p q h
  else
    have h': q.degree ≥ p.degree := by
      grind only
    _gcd q p h'

--def removesqaures (p : CPoly ℚ) :CPoly ℚ :=
--  (divide p (gcd p p.deriv)).1

#print Multiset
#eval! factor (CPoly.toCPoly [(-2:ℤ),2])
#eval! factor (CPoly.toCPoly [(-2:ℤ),2,3,4,7])
#min_imports
#eval (CPoly.toCPoly [(-2:ℤ),2,4]).deriv


--def eq_rel (a : PreRealAlgebraicNumber) (b : PreRealAlgebraicNumber):=
--  a.lower ≤ b.upper ∧ b.lower ≤ a.upper ∧ ⊤
-- gcd contains the root so it has a root
-- between max a.lower b.lower and min a.upper b.upper
/-instance PreRealAlgebraicNumberSetoid : Setoid PreRealAlgebraicNumber := ⟨eq_rel, by
  constructor
  · intro x
    unfold eq_rel
    constructor
    · exact x.lower_le_upper
    · constructor
      · exact x.lower_le_upper
      · trivial
  · unfold eq_rel
    grind
  · intro x y z
    unfold eq_rel
    intro ⟨hxy,hxy',_⟩ ⟨hyz,hyz',_⟩
    sorry -- this is actually wrong we need the root
⟩
def RealAlgebraicNumber := Quotient PreRealAlgebraicNumberSetoid
-/
structure TestPreNumber where
  z : ℤ

def testeq_rel (a : TestPreNumber) (b : TestPreNumber) :=
  a.z ≡ b.z [ZMOD 5]


instance : Repr TestPreNumber where
   reprPrec n := reprPrec n.z

instance TestPreNumberSetoid : Setoid TestPreNumber := ⟨
  testeq_rel,by
    constructor <;> unfold testeq_rel;
    · intro x
      rfl
    · intro x y
      exact fun a ↦ id (Int.ModEq.symm a)
    · intro x y z h h'
      grw [h'] at h
      assumption
⟩
def TestNumber := Quotient TestPreNumberSetoid



instance : Repr (Quotient TestPreNumberSetoid) where
   reprPrec _ := fun _ ↦ Std.Format.text "test"

#eval (Quotient.mk' (⟨5⟩:TestPreNumber) :TestNumber)
