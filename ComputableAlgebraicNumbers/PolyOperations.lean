import Mathlib
import ComputableAlgebraicNumbers.CPoly

inductive Vec.{u} (α : Sort u) : ℕ → Type u where
| nil : Vec α 0
| cons : {n : ℕ} → α → Vec α n → Vec α (n + 1)

namespace Vec

def map {α β : Type*} {n : ℕ} : Vec α n → (α → β) → Vec β n
| nil, f => nil
| cons a v, f => cons (f a) (v.map f)

def toList {α : Type*} {n : ℕ} : Vec α n → List α
| nil => []
| cons a v => a :: v.toList

lemma toList_length {α : Type*} {n : ℕ} : (v : Vec α n) → v.toList.length = n
| nil => rfl
| cons a vs => by
  have := toList_length vs
  unfold toList
  rw [List.length_cons, toList_length vs]

def ofList {α : Type*} : (l : List α) → Vec α (l.length)
| [] => nil
| a :: as => cons a (ofList as)

def toVector {α : Type*} {n : ℕ} (v : Vec α n) : Vector α n :=
  Vector.mk v.toList.toArray <| by
  rw [List.size_toArray, toList_length]

def ofVector {α : Type*} : {n : ℕ} → Vector α n → Vec α n
| 0, _ => nil
| _ + 1, v => cons v.head (Vec.ofVector v.tail)

def find {α : Type*} [Zero α] [DecidableEq α] {n : ℕ} : Vec α n → Option (Fin n)
| nil => none
| cons a v => if a ≠ 0 then some 0 else
  match find v with
  | none => none
  | some k => k.succ

def get {α : Type*} {n : ℕ} (k : Fin n) : Vec α n → α
| nil => by apply k.rec0
| cons a v => if h : k = 0 then a else v.get (k.pred h)

def set {α : Type*} {n : ℕ} (k : Fin n) : Vec α n → α → Vec α n
| nil, _ => by apply k.rec0
| cons a v, a' => if h : k = 0 then cons a' v else cons a (v.set (k.pred h) a')

def swap {α : Type*} {n : ℕ} (k : Fin n) : Vec α n → Vec α n
| nil => nil
| cons a v => if h : k = 0 then cons a v else cons (v.get (k.pred h)) (v.set (k.pred h) a)

def zero {α : Type*} [Zero α] : {n : ℕ} → Vec α n
| 0 => nil
| _ + 1 => cons 0 zero

def add {α : Type*} [Add α] {n : ℕ} : Vec α n → Vec α n → Vec α n
| nil, nil => nil
| cons a v, cons a' v' => cons (a + a') (v.add v')

def smul {α : Type*} [Mul α] {n : ℕ} (a : α) : Vec α n → Vec α n
| nil => nil
| cons a' v' => cons (a * a') (v'.smul a)

def head {α : Type*} {n : ℕ} : Vec α (n + 1) → α
| cons a _ => a

def tail {α : Type*} {n : ℕ} : Vec α (n + 1) → Vec α n
| cons _ v => v

def sum {α : Type*} [Zero α] [Add α] {n : ℕ} : Vec α n → α
| nil => 0
| cons a v => a + v.sum

def zipWith {α β γ : Type*} {n : ℕ} (f : α → β → γ) : Vec α n → Vec β n → Vec γ n
| nil, nil => nil
| cons a va, cons b vb => cons (f a b) (zipWith f va vb)

def find_eliminator' {n : ℕ} : Vec (Vec ℚ n) (n + 1) → Vec ℚ (n + 1)
| .cons v vs =>
  match v.find with
  | none => cons 1 zero
  | some i =>
  match n with
  | 0 => cons 1 nil
  | _ + 1 =>
  letI v' := v.swap i
  letI vs' := vs.map fun v ↦ v.swap i
  letI vs'' := vs'.map fun v ↦ v.add (cons 0 (v'.tail.smul (-v.head / v'.head)))
  letI tail := (vs''.map fun v ↦ v.tail).find_eliminator'
  letI head := -(zipWith (· * ·) tail (vs''.map fun v ↦ v.head)).sum / v'.head
  cons head tail

end Vec

def find_eliminator {n : ℕ} (v : Vector (Vector ℚ n) (n + 1)) : Vector ℚ (n + 1) :=
  ((Vec.ofVector v).map Vec.ofVector).find_eliminator'.toVector

def reduce_mod_Monic (f : CPoly (CPoly ℚ)) (p q : CPoly ℚ) (hp : p.Monic) (hq : q.Monic) :
  CPoly (CPoly ℚ) :=
  (f.modByMonic (p.liftTo (CPoly ℚ)) (CPoly.Monic_liftTo hp)).map'
    fun g : CPoly ℚ ↦ g.modByMonic q hq

def reduce_mod (f : CPoly (CPoly ℚ)) (p q : CPoly ℚ) : CPoly (CPoly ℚ) :=
  if hp : p = 0 then 0 else if hq : q = 0 then 0 else reduce_mod_Monic f
  (normalize p) (normalize q) (CPoly.Monic_normalize p hp) (CPoly.Monic_normalize q hq)

def poly_to_coefs {n m : ℕ} (f : CPoly (CPoly ℚ)) : Vector ℚ (n * m) :=
  Vector.ofFn ((fun (⟨i, _⟩, ⟨j, _⟩) ↦ (f.toPolynomial.coeff i).toPolynomial.coeff j) ∘
  finProdFinEquiv.invFun)

def coefs_to_poly {n : ℕ} (v : Vector ℚ n) : CPoly ℚ :=
  CPoly.toCPoly v.toList

def poly_add (p q : CPoly ℚ) :=
  coefs_to_poly (find_eliminator (Vector.ofFn fun k : Fin (p.natDegree * q.natDegree + 1) ↦
  poly_to_coefs <| reduce_mod ((CPoly.X + CPoly.const CPoly.X) ^ k.val) p q))

def poly_mul (p q : CPoly ℚ) :=
  coefs_to_poly (find_eliminator (Vector.ofFn fun k : Fin (p.natDegree * q.natDegree + 1) ↦
  poly_to_coefs <| reduce_mod ((CPoly.X * CPoly.const CPoly.X) ^ k.val) p q))
