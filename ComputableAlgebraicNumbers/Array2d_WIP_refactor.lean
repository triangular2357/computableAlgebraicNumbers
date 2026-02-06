import Mathlib.Data.List.Range
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic


structure Array2d (α : Type*) (row_count : ℕ) (column_count : ℕ) where
  data : Array α -- make sure that there is only one reference to this at a time
                 -- then the compiler optimizes it to modify it in place
  condition : data.size = row_count * column_count

#print Vector
namespace Array2d

def empty (α : Type*) : Array2d α 0 0:=⟨Array.empty,by rfl ⟩

abbrev NeEmpty {α : Type*} (M : Array2d α r c) : Prop := ¬M.data.size = 0

instance {α : Type*} (M : Array2d α r c) : Decidable M.NeEmpty := by
  unfold NeEmpty
  infer_instance

lemma NeEmpty_imp_NeZero_row_count {α : Type*} (M : Array2d α r c) :
  NeEmpty M → NeZero r := by
  unfold NeEmpty
  rw [condition, neZero_iff, Nat.mul_eq_zero, not_or, ne_eq]
  intro ⟨h,h'⟩
  assumption

lemma NeEmpty_NeZero_row_count {α : Type*} (M : Array2d α r c) (h : NeEmpty M)
  :NeZero r := by
  apply NeEmpty_imp_NeZero_row_count;assumption

lemma NeEmpty_imp_NeZero_column_count {α : Type*} (M : Array2d α r c) :
  NeEmpty M → NeZero c := by
  unfold NeEmpty
  rw [condition, neZero_iff, Nat.mul_eq_zero, not_or, ne_eq]
  intro ⟨h,h'⟩
  assumption

lemma NeEmpty_NeZero_column_count {α : Type*} (M : Array2d α r c) (h : NeEmpty M)
  :NeZero c := by
  apply NeEmpty_imp_NeZero_column_count;assumption

lemma NeZero_row_column_count_imp_NeEmpty {α : Type*} (M : Array2d α r c) :
  NeZero r → NeZero c → NeEmpty M := by
  unfold NeEmpty
  rw [condition, neZero_iff, neZero_iff, Nat.mul_eq_zero, not_or, ne_eq, ne_eq]
  intro h h'
  constructor <;> assumption

def _at {α : Type*} (M : Array2d α r c) (row : ℕ) (column : ℕ)
  (h : row < r) (h' : column < c) : α :=
  have : M.data.size > row*c+column := by
    rw [M.condition]
    simp only [gt_iff_lt]
    grw [← Order.add_one_le_iff] at h h' ⊢
    rw [_root_.add_assoc (row * c) column 1]
    grw [h']
    rw [← Nat.add_one_mul row c]
    grw [h]
  M.data[row*c+column]

def atD {α : Type*} (M : Array2d α r c) (row : ℕ) (column : ℕ) (default : α) : α :=
  if h : row < r then
  if h' : column < c then
  M._at row column h h'
  else default else default

def get_row {α : Type*} (M : Array2d α r c) (row : ℕ) : Subarray α :=
  M.data.toSubarray (row*c) ((row+1)*c)

def get_column {α : Type*} [DecidableEq α] (M : Array2d α r c) (column : ℕ)
 (h : NeZero c) : Array α := -- impl like getEvenElems in Mathlib
  (·.2) <| M.data.foldl (init := ((0:Fin c), Array.empty)) fun (c, acc) a =>
    if c=column then
      (c+1, acc.push a)
    else
      (c+1, acc)

def map {α : Type*} [DecidableEq α] (M : Array2d α r c) (f : α → α) : Array2d α r c:=
  ⟨
    M.data.map f,
    by
      rw [← M.condition]
      exact Array.size_map
  ⟩

def mapIdx {α : Type*} [DecidableEq α] (M : Array2d α r c) (f : ℕ → α → α) : Array2d α r c:=
  ⟨
    M.data.mapIdx f,
    by
      rw [← M.condition]
      exact Array.size_mapIdx
  ⟩

def mapIdxRC {α : Type*} [DecidableEq α] (M : Array2d α r c) (f : ℕ → ℕ → α → α) : Array2d α r c:=
  ⟨
    M.data.mapIdx (fun i a ↦ (f (i / c) (i % c) a)),
    by
      rw [← M.condition]
      exact Array.size_mapIdx
  ⟩

@[simp]
lemma mapIdxRCKeepsSize {α : Type*} [DecidableEq α] (M : Array2d α r c) (f : ℕ → ℕ → α → α)
:M.data.size = (M.mapIdxRC f).data.size:=by
  unfold mapIdxRC
  simp only [Array.size_mapIdx]

@[simp]
lemma mapIdxRCKeepsNeEmpty {α : Type*} [DecidableEq α] (M : Array2d α r c) (f : ℕ → ℕ → α → α)
(h : M.NeEmpty) :(M.mapIdxRC f).NeEmpty:=by
  unfold NeEmpty at ⊢ h
  grind only [mapIdxRCKeepsSize]

private def _ℚrevNormMatrix' (M : Array2d ℚ r c) (column_index : Fin c) : Array2d ℚ r c :=
  have h: NeZero c := by
    by_contra h
    rw [not_neZero] at h
    rw [h] at column_index
    apply Fin.elim0 column_index
  let row_coeficients: Array ℚ := (M.get_column column_index h).map (fun q ↦ if q=0 then 1 else q)
  M.mapIdxRC (fun r _ q ↦ q/(row_coeficients[r]?.getD 1))
  -- TODO maybe prove that index is valid so we dont need the option
  -- to do that we would need a new map method on Array2d
  -- which takes a function of Fin column_count and Fin row_count


@[simp]
lemma _ℚrevNormMatrix'KeepsSize (M : Array2d ℚ r c) (column_index : Fin c)
  :(M._ℚrevNormMatrix' column_index).data.size = M.data.size :=by
  unfold _ℚrevNormMatrix'
  unfold mapIdxRC
  simp only [Array.getElem?_map, Array.size_mapIdx]


private def _ℚrevNormMatrix (M : Array2d ℚ r c) (h : M.NeEmpty) : (Array2d ℚ r c) × ℕ:=
  have : NeZero r := NeEmpty_NeZero_row_count M h
  have : NeZero c := NeEmpty_NeZero_column_count M h
  let column := (·.2) <|
  M.data.foldl (init := (((0:Fin c),(0:Fin r)),
  c)) fun ((c, r), smallestC) q =>
    (if c+1=0 then ((c+1,r+1), ·) else ((c+1,r),·)) <|
      if q=0 then smallestC else min smallestC c
  --if (column ≥ M.column_count) then (M, column) else
  (M._ℚrevNormMatrix' (Fin.ofNat c column), column)
  -- if everything is zero ℚrevNormMatrix' doesn't do anything
  -- so we probably don't need the if line above

@[simp]
lemma _ℚrevNormMatrixKeepsSize (M : Array2d ℚ r c) (h : M.NeEmpty)
  :(M._ℚrevNormMatrix h).1.data.size = M.data.size:=by
  unfold _ℚrevNormMatrix
  apply _ℚrevNormMatrix'KeepsSize

@[simp]
lemma _ℚrevNormMatrixKeepsNeEmpty (M : Array2d ℚ r c) (h : M.NeEmpty)
  :(M._ℚrevNormMatrix h).1.NeEmpty:=by
  unfold NeEmpty at ⊢ h
  have : M.data.size=(M._ℚrevNormMatrix h).1.data.size := by symm;apply _ℚrevNormMatrixKeepsSize
  grind only

private def _matrixToReducedRowEchelonForm (M : Array2d ℚ r c) : Array2d ℚ r c :=
  if h:M.NeEmpty then

  let M'c := M._ℚrevNormMatrix h
  let M' := M'c.1
  let column := M'c.2
  have hc: NeZero c := by
    sorry
    --simp []

  let relevant_column' := M'.get_column column hc -- returns empty on c=M.column_count
  let first_non_zero := (relevant_column'.toList.findIdx? (fun l ↦ ¬( l= 0))).getD 0
  let M'' := M'.mapIdxRC (fun r c q ↦ -- switches rows 0 and first_non_zero
    if r=0 then M'.atD first_non_zero c 0 else
    if r=first_non_zero then M'.atD 0 c 0 else q)

  let relevant_column'' := M''.get_column column hc -- returns empty on c=M.column_count
  let step := M''.mapIdxRC (fun r c q ↦
    if r = 0 ∨ relevant_column''.getD r 0 = 0 then q else
    q - M''.atD 0 c 0 -- subtract first row
  )

  have hrc:r = r := by rfl
  have :step.NeEmpty := by
    unfold step
    apply mapIdxRCKeepsNeEmpty _ _
    unfold M''
    apply mapIdxRCKeepsNeEmpty _ _
    unfold M' M'c
    apply _ℚrevNormMatrixKeepsNeEmpty M h

  let smaller : Array2d ℚ (r-1) c := ⟨
    step.data.extract c,
    by
      rw [Array.size_extract_of_le ?_]
      · rw [step.condition, Nat.sub_one_mul r c]
      · linarith
  ⟩

  have :r - 1 < r := by
    rw [hrc]; simp; rw [Nat.pos_iff_ne_zero];rw [← neZero_iff]; apply NeEmpty_NeZero_row_count M h
  let smaller_step := _matrixToReducedRowEchelonForm smaller
  let result : Array2d ℚ r c := ⟨
    (step.data.extract 0 c) ++ smaller_step.data,
    by
      rw [Array.size_append, Array.size_extract_of_le ?_]
      · sorry
        --rw [smaller.condition, tsub_zero, add_comm, Nat.add_one_mul]
      · rw [step.condition]
        have h': 1 ≤ r := by
          rw [Nat.one_le_iff_ne_zero]
          have h':step.NeEmpty := by
            clear smaller_step
            grind only
          rw [ ← neZero_iff]
          apply NeEmpty_NeZero_row_count step h'
        grw [← h']
        simp only [one_mul, le_refl]
  ⟩
  result
  else M
termination_by r


lemma _matrixToReducedRowEchelonFormKeepsSize (M : Array2d ℚ r c)
  :(M._matrixToReducedRowEchelonForm).data.size = M.data.size :=by
  unfold _matrixToReducedRowEchelonForm
  sorry
  --simp_rw [apply_ite Array2d.data]
  --apply _ℚrevNormMatrixKeepsSize

def find_eliminator {n : ℕ} (V : Vector (Vector ℚ n) (n + 1)) : IO (Vector ℚ (n + 1)) := do
  let Range : Array2d ℚ n (n+2) := ⟨(Array.range (n*(n+2))).map (Rat.instNatCast.natCast ·),
                            by grind⟩
  let M := Range.mapIdxRC (fun r c q ↦
    if h: c > n then 0 else
    let column := V.getD c (Vector.ofFn (fun _:Fin n ↦ (0:ℚ)))
    column.getD r (0:ℚ)
  )
  let M' := M._matrixToReducedRowEchelonForm
  let M'rows := (Array.range n).map (fun (r:ℕ) ↦ (M'.get_row r).toArray)
  let ones := M'rows.map (fun row ↦ row.findIdx (· = 1))
  -- TODO use something with Nat and find directly
  let coloum:ℕ := (Array.range (n+2)).findIdx
    (fun c ↦ ((ones.findIdx (fun q ↦ q=c)) = n))
  let M'' : Array2d ℚ (n+1) (n+2) := ⟨M'.data ++ ((Array.range (n+2)).map (
    fun c ↦ if c = coloum ∨ c = n+1 then 1 else 0
  )), by
    rw [Array.size_append]
    rw [Array.size_map]
    have :M'.data.size = n*(n+2) := by
      unfold M'
      rw [_matrixToReducedRowEchelonFormKeepsSize]
      unfold M
      sorry
    grind
  ⟩
  let M''' := M''._matrixToReducedRowEchelonForm
  if h:n=0 then
    return cast (congrArg _ (show 1 = n + 1 by grind only)) #v[(1:ℚ)]
  else
  have h' : NeZero (n+2) := by sorry

  let M'''rows := (Array.range (n+1)).map (fun (r:ℕ) ↦ (M'''.get_row r).toArray)
  let ones := M'''rows.map (fun row ↦ row.findIdx (· = 1))

  IO.println s!"M'' {M''.data}"
  IO.println s!"M''' {M'''.data}"

  return ((Vector.range (n+1)).map (fun (c:ℕ) ↦
    M'''.atD (ones.findIdx (fun q ↦ q=c)) (c-1) 0
    ))
  --let coloum:ℕ := (Array.range (n+2)).findIdx
  --    (fun c ↦ ((ones.findIdx (fun q ↦ q=c)) = M.row_count))

  --((Vector.range (n+1)).map (fun (n:ℕ) ↦
  --  (((M'''.get_column n h').findIdx? (· = 1)).getD (n+2))
  --)).map (M'''.atD · (n+1) 0)

/-
def M := (Array2d.mk #[1,2,(Rat.mk' 1 2)] 1 3 (by decide))
def M' := (Array2d.mk #[1,2,(Rat.mk' 1 2),1,1,1] 2 3 (by decide))
def M2' := (Array2d.mk #[2,2,(Rat.mk' 1 2)] 1 3 (by decide))
def M2 := (Array2d.mk #[2,2,(Rat.mk' 1 2)] 3 1 (by decide))
def M3 := (Array2d.mk #[2,-2,(Rat.mk' 1 2)] 3 1 (by decide))
def M4 := (Array2d.mk #[1,-2,(Rat.mk' 1 2)] 3 1 (by decide))
def M5 := (Array2d.mk #[1,1,1,1,1,(Rat.mk' 2 1)] 3 2 (by decide))
def M6' := (Array2d.mk #[1,0,(Rat.mk' 1 3),0,0,1,(Rat.mk' 10 3),0,0,0,1,1] 3 4 (by decide))

#eval! M6'._matrixToReducedRowEchelonForm

def M6 := (Array2d.mk #[3,0,1,2,(Rat.mk' 1 1),4] 2 3 (by decide))

#eval! M6._matrixToReducedRowEchelonForm

#eval! find_eliminator (#v[#v[3,2],#v[0,1],#v[1,4]])

#eval M5._matrixToReducedRowEchelonForm |> data
def M5' := (Array2d.mk #[1,1,1,1,1,(Rat.mk' 2 1)] 2 3 (by decide))
#eval M5._matrixToReducedRowEchelonForm |> data

#eval (M._ℚrevNormMatrix (by decide)).1 |> data
#eval (M._ℚrevNormMatrix (by decide)).2

instance : NeZero M2'.column_count := NeEmpty_NeZero_column_count M2' (by decide)

#eval M2'.get_column 0 (NeEmpty_NeZero_column_count M2' (by decide))
#eval M2'._ℚrevNormMatrix' 0 |> data
#eval (M2'._ℚrevNormMatrix (by decide)).1.data
#eval (M2'._ℚrevNormMatrix (by decide)).2

#eval! M2._matrixToReducedRowEchelonForm |> data
#eval! M3._matrixToReducedRowEchelonForm |> data
#eval! M4._matrixToReducedRowEchelonForm |> data
#eval M.mapIdxRC (fun r c _ ↦ 10*r+c) |> data
#eval M'.mapIdxRC (fun r c _ ↦ 10*r+c) |> data
#eval M.mapIdx (fun i _ ↦ i) |> data
#eval! M'._matrixToReducedRowEchelonForm |> data
-/
end Array2d
