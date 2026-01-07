import Mathlib.Data.List.Range
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

structure Array2d (α : Type*) where
  data : Array α -- make sure that there is only one reference to this at a time
  row_count : ℕ  -- then the compiler optimizes it to modify it in place
  column_count : ℕ
  condition : data.size = row_count * column_count

#print Vector
namespace Array2d

def empty (α : Type*) : Array2d α:=⟨Array.empty,0,0,by rfl ⟩

abbrev NeEmpty {α : Type*} (M : Array2d α) : Prop := ¬M.data.size = 0

instance {α : Type*} (M : Array2d α) : Decidable M.NeEmpty := by
  unfold NeEmpty
  infer_instance

lemma NeEmpty_imp_NeZero_row_count {α : Type*} (M : Array2d α) :
  NeEmpty M → NeZero M.row_count := by
  unfold NeEmpty
  rw [condition, neZero_iff, Nat.mul_eq_zero, not_or, ne_eq]
  intro ⟨h,h'⟩
  assumption

lemma NeEmpty_NeZero_row_count {α : Type*} (M : Array2d α) (h : NeEmpty M)
  :NeZero M.row_count := by
  apply NeEmpty_imp_NeZero_row_count;assumption

lemma NeEmpty_imp_NeZero_column_count {α : Type*} (M : Array2d α) :
  NeEmpty M → NeZero M.column_count := by
  unfold NeEmpty
  rw [condition, neZero_iff, Nat.mul_eq_zero, not_or, ne_eq]
  intro ⟨h,h'⟩
  assumption

lemma NeEmpty_NeZero_column_count {α : Type*} (M : Array2d α) (h : NeEmpty M)
  :NeZero M.column_count := by
  apply NeEmpty_imp_NeZero_column_count;assumption

lemma NeZero_row_column_count_imp_NeEmpty {α : Type*} (M : Array2d α) :
  NeZero M.row_count → NeZero M.column_count → NeEmpty M := by
  unfold NeEmpty
  rw [condition, neZero_iff, neZero_iff, Nat.mul_eq_zero, not_or, ne_eq, ne_eq]
  intro h h'
  constructor <;> assumption

def _at {α : Type*} (M : Array2d α) (row : ℕ) (column : ℕ)
  (h : row < M.row_count) (h' : column < M.column_count) : α :=
  have : M.data.size > row*M.column_count+column := by
    rw [M.condition]
    simp only [gt_iff_lt]
    grw [← Order.add_one_le_iff] at h h' ⊢
    rw [_root_.add_assoc (row * M.column_count) column 1]
    grw [h']
    rw [← Nat.add_one_mul row M.column_count]
    grw [h]
  M.data[row*M.column_count+column]

def atD {α : Type*} (M : Array2d α) (row : ℕ) (column : ℕ) (default : α) : α :=
  if h : row < M.row_count then
  if h' : column < M.column_count then
  M._at row column h h'
  else default else default

def get_row (α : Type*) (M : Array2d α) (row : ℕ) : Subarray α :=
  M.data.toSubarray (row*M.column_count) ((row+1)*M.column_count)

def get_column {α : Type*} [DecidableEq α] (M : Array2d α) (column : ℕ)
 (h : NeZero M.column_count) : Array α := -- impl like getEvenElems in math lib
  (·.2) <| M.data.foldl (init := ((0:Fin M.column_count), Array.empty)) fun (c, acc) a =>
    if c=column then
      (c+1, acc.push a)
    else
      (c+1, acc)

def map {α : Type*} [DecidableEq α] (M : Array2d α) (f : α → α) : Array2d α:=
  ⟨
    M.data.map f,
    M.row_count,
    M.column_count,
    by
      rw [← M.condition]
      exact Array.size_map
  ⟩

def mapIdx {α : Type*} [DecidableEq α] (M : Array2d α) (f : ℕ → α → α) : Array2d α:=
  ⟨
    M.data.mapIdx f,
    M.row_count,
    M.column_count,
    by
      rw [← M.condition]
      exact Array.size_mapIdx
  ⟩

def mapIdxRC {α : Type*} [DecidableEq α] (M : Array2d α) (f : ℕ → ℕ → α → α) : Array2d α:=
  ⟨
    M.data.mapIdx (fun i a ↦ (f (i / M.column_count) (i % M.column_count) a)),
    M.row_count,
    M.column_count,
    by
      rw [← M.condition]
      exact Array.size_mapIdx
  ⟩

@[simp]
lemma mapIdxRCKeepsSize {α : Type*} [DecidableEq α] (M : Array2d α) (f : ℕ → ℕ → α → α)
:M.data.size = (M.mapIdxRC f).data.size:=by
  unfold mapIdxRC
  simp only [Array.size_mapIdx]

@[simp]
lemma mapIdxRCKeepsNeEmpty {α : Type*} [DecidableEq α] (M : Array2d α) (f : ℕ → ℕ → α → α)
(h : M.NeEmpty) :(M.mapIdxRC f).NeEmpty:=by
  unfold NeEmpty at ⊢ h
  grind only [mapIdxRCKeepsSize]

private def _ℚrevNormMatrix' (M : Array2d ℚ) (column_index : Fin M.column_count) : Array2d ℚ :=
  have h: NeZero M.column_count := by
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
lemma _ℚrevNormMatrix'KeepsSize (M : Array2d ℚ) (column_index : Fin M.column_count)
  :M.data.size = (M._ℚrevNormMatrix' column_index).data.size:=by
  unfold _ℚrevNormMatrix'
  unfold mapIdxRC
  simp only [Array.getElem?_map, Array.size_mapIdx]

@[simp]
lemma _ℚrevNormMatrix'KeepsRowCount (M : Array2d ℚ) (column_index : Fin M.column_count)
  :M.row_count = (M._ℚrevNormMatrix' column_index).row_count:= by
  unfold _ℚrevNormMatrix'
  unfold mapIdxRC
  simp only


private def _ℚrevNormMatrix (M : Array2d ℚ) (h : M.NeEmpty) : (Array2d ℚ) × ℕ:=
  have : NeZero M.row_count := NeEmpty_NeZero_row_count M h
  have : NeZero M.column_count := NeEmpty_NeZero_column_count M h
  let column := (·.2) <|
  M.data.foldl (init := (((0:Fin M.column_count),(0:Fin M.row_count)),
  M.column_count)) fun ((c, r), smallestC) q =>
    (if c+1=0 then ((c+1,r+1), ·) else ((c+1,r),·)) <|
      if q=0 then smallestC else min smallestC c
  --if (column ≥ M.column_count) then (M, column) else
  (M._ℚrevNormMatrix' (Fin.ofNat M.column_count column), column)
  -- if everything is zero ℚrevNormMatrix' doesn't do anything
  -- so we probably don't need the if line above

@[simp]
lemma _ℚrevNormMatrixKeepsSize (M : Array2d ℚ) (h : M.NeEmpty)
  :M.data.size = (M._ℚrevNormMatrix h).1.data.size:=by
  unfold _ℚrevNormMatrix
  apply _ℚrevNormMatrix'KeepsSize

@[simp]
lemma _ℚrevNormMatrixKeepsRowCount (M : Array2d ℚ) (h : M.NeEmpty)
  :M.row_count = (M._ℚrevNormMatrix h).1.row_count:=by
  unfold _ℚrevNormMatrix
  simp
  apply _ℚrevNormMatrix'KeepsRowCount

@[simp]
lemma _ℚrevNormMatrixKeepsNeEmpty (M : Array2d ℚ) (h : M.NeEmpty)
  :(M._ℚrevNormMatrix h).1.NeEmpty:=by
  unfold NeEmpty at ⊢ h
  have : M.data.size=(M._ℚrevNormMatrix h).1.data.size := by apply _ℚrevNormMatrixKeepsSize
  grind only

/-
private def _matrixToReducedRowEchelonFormStep (M : Array2d ℚ) (h : M.NeEmpty) : Array2d ℚ :=
  have hr: NeZero M.row_count := NeEmpty_NeZero_row_count M h
  have hc: NeZero M.column_count := NeEmpty_NeZero_column_count M h
  --let ⟨M',c⟩ := M._ℚrevNormMatrix h
  -- using the definition in proves somehow doesn't work with pattern matching
  let M'c := M._ℚrevNormMatrix h
  let M' := M'c.1
  let c := M'c.2
  have hc: NeZero M'.column_count := by
    unfold M' M'c
    apply NeEmpty_imp_NeZero_column_count
    apply _ℚrevNormMatrixKeepsNeEmpty
  --if (c ≥ M.column_count) then M else
  let relevant_column := M'.get_column c hc -- returns empty on c=M.column_count
  let first_non_zero := (relevant_column.toList.findIdx? (fun l ↦ ¬( l= 0))).getD 0
  let M'' := M'.mapIdxRC (fun r c q ↦ -- switches rows 0 and first_non_zero
    if r=0 then M'.atD first_non_zero c 0 else
    if r=first_non_zero then M'.atD 0 c 0 else q)
  let relevant_column := M''.get_column c hc -- returns empty on c=M.column_count
  let isZeroRowOrZero (r : ℕ) : Prop := r = 0 ∨ relevant_column.getD r 0 = 0
  M''.mapIdxRC (fun r c q ↦
    if isZeroRowOrZero r then q else
    q - M''.atD 0 c 0 -- subtract first row
  )

private def _matrixToReducedRowEchelonFormStep'
  (M' : Array2d ℚ) (c : ℕ) (hc : NeZero M'.column_count) : Array2d ℚ :=
  let first_non_zero := ((M'.get_column c hc).toList.findIdx? (fun l ↦ ¬( l= 0))).getD 0
  let M'' := M'.mapIdxRC (fun r c q ↦ -- switches rows 0 and first_non_zero
    if r=0 then M'.atD first_non_zero c 0 else
    if r=first_non_zero then M'.atD 0 c 0 else q)
  M''.mapIdxRC (fun r c q ↦
    if r = 0 ∨ (M''.get_column c hc).getD r 0 = 0 then q else
    q - M''.atD 0 c 0 -- subtract first row
  )
-/


/-
example (M : Array2d ℚ) (h : M.NeEmpty):
  M.data.size = (M._matrixToReducedRowEchelonFormStep' h).data.size:= by
  unfold _matrixToReducedRowEchelonFormStep'
  simp [mapIdxRCKeepsSize,_ℚrevNormMatrixKeepsSize]
  sorry


lemma _matrixToReducedRowEchelonFormStepKeepsRowCount (M : Array2d ℚ) (h : M.NeEmpty)
  :M.row_count = (M._matrixToReducedRowEchelonFormStep h).row_count := by
  --unfold _matrixToReducedRowEchelonFormStep
  sorry


lemma _matrixToReducedRowEchelonFormStepKeepsSize (M : Array2d ℚ) (h : M.NeEmpty)
  :M.data.size = (M._matrixToReducedRowEchelonFormStep h).data.size:=by
  --unfold _matrixToReducedRowEchelonFormStep
  sorry

lemma _matrixToReducedRowEchelonFormStepKeepsNeEmpty (M : Array2d ℚ) (h : M.NeEmpty)
  :(M._matrixToReducedRowEchelonFormStep h).NeEmpty:=by
  unfold NeEmpty at ⊢ h
  have : M.data.size=(M._matrixToReducedRowEchelonFormStep h).data.size := by
    apply _matrixToReducedRowEchelonFormStepKeepsSize
  grind only
-/

private def _matrixToReducedRowEchelonForm (M : Array2d ℚ) : Array2d ℚ :=
  if h:M.NeEmpty then

  let M'c := M._ℚrevNormMatrix h
  let M' := M'c.1
  let c := M'c.2
  have hc: NeZero M'.column_count := by
    unfold M' M'c
    apply NeEmpty_imp_NeZero_column_count
    apply _ℚrevNormMatrixKeepsNeEmpty

  let relevant_column' := M'.get_column c hc -- returns empty on c=M.column_count
  let first_non_zero := (relevant_column'.toList.findIdx? (fun l ↦ ¬( l= 0))).getD 0
  let M'' := M'.mapIdxRC (fun r c q ↦ -- switches rows 0 and first_non_zero
    if r=0 then M'.atD first_non_zero c 0 else
    if r=first_non_zero then M'.atD 0 c 0 else q)

  let relevant_column'' := M''.get_column c hc -- returns empty on c=M.column_count
  let step := M''.mapIdxRC (fun r c q ↦
    if r = 0 ∨ relevant_column''.getD r 0 = 0 then q else
    q - M''.atD 0 c 0 -- subtract first row
  )

  have hrc:step.row_count = M.row_count := by
    have hrc':M'.row_count = M.row_count := by
      apply _ℚrevNormMatrixKeepsRowCount M h
    apply hrc'
  have :step.NeEmpty := by
    unfold step
    apply mapIdxRCKeepsNeEmpty _ _
    unfold M''
    apply mapIdxRCKeepsNeEmpty _ _
    unfold M' M'c
    apply _ℚrevNormMatrixKeepsNeEmpty M h

  --let step := _matrixToReducedRowEchelonFormStep M h
  let smaller : Array2d ℚ := ⟨
    step.data.extract step.column_count,
    step.row_count-1,
    step.column_count,
    by
      rw [Array.size_extract_of_le ?_]
      · rw [step.condition, Nat.sub_one_mul step.row_count step.column_count]
      · linarith
  ⟩
  --have :Decidable smaller.NeEmpty := sorry
  -- this is probably just wrong in all generality is it possible to make row_count "decidable"?

  have :step.row_count - 1 < M.row_count := by
    rw [hrc]; simp; rw [Nat.pos_iff_ne_zero];rw [← neZero_iff]; apply NeEmpty_NeZero_row_count M h
  let smaller_step := _matrixToReducedRowEchelonForm smaller
  let result : Array2d ℚ := ⟨
    (step.data.extract 0 step.column_count) ++ smaller.data,
    smaller.row_count + 1,
    smaller.column_count,
    by
      rw [Array.size_append, Array.size_extract_of_le ?_]
      · rw [smaller.condition, tsub_zero, add_comm, Nat.add_one_mul]
      · rw [step.condition]
        have h': 1 ≤ step.row_count := by
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
termination_by M.row_count

def M := (Array2d.mk #[1,2,(Rat.mk' 1 2)] 1 3 (by decide))
def M' := (Array2d.mk #[1,2,(Rat.mk' 1 2),1,1,1] 2 3 (by decide))
def M2' := (Array2d.mk #[2,2,(Rat.mk' 1 2)] 1 3 (by decide))
def M2 := (Array2d.mk #[2,2,(Rat.mk' 1 2)] 3 1 (by decide))
def M3 := (Array2d.mk #[2,-2,(Rat.mk' 1 2)] 3 1 (by decide))
def M4 := (Array2d.mk #[1,-2,(Rat.mk' 1 2)] 3 1 (by decide))

#eval (M._ℚrevNormMatrix (by decide)).1 |> data
#eval (M._ℚrevNormMatrix (by decide)).2

instance : NeZero M2'.column_count := NeEmpty_NeZero_column_count M2' (by decide)

#eval M2'.get_column 0 (NeEmpty_NeZero_column_count M2' (by decide))
--#eval M2'._testℚrevNormMatrix' 1
#eval M2'._ℚrevNormMatrix' 0 |> data
#eval (M2'._ℚrevNormMatrix (by decide)).1.data
#eval (M2'._ℚrevNormMatrix (by decide)).2

#eval! M2._matrixToReducedRowEchelonForm |> data
#eval! M3._matrixToReducedRowEchelonForm |> data
#eval! M4._matrixToReducedRowEchelonForm |> data
--#eval M'._matrixToReducedRowEchelonFormStep (by unfold M';simp) |> data
#eval M.mapIdxRC (fun r c _ ↦ 10*r+c) |> data
#eval M'.mapIdxRC (fun r c _ ↦ 10*r+c) |> data
#eval M.mapIdx (fun i _ ↦ i) |> data
#eval! M'._matrixToReducedRowEchelonForm |> data

  --if h:M.column_count=0 then empty ℚ else
  --have neZero_column_count:NeZero M.column_count := by rw [neZero_iff];assumption
  --let column_non_zero (column : Fin M.column_count):Prop:=
  --((M.get_column column neZero_column_count).map (·=0)).foldl (· ∧ ·) true
  --let ℕcolumn_non_zero (column : ℕ):Prop:=
  --if column ≥ M.column_count then False else column_non_zero (Fin.ofNat M.column_count column)
  --have: Decidable (∃ (n:Fin M.column_count), column_non_zero n) := by fin_cases _;done
  --have: Decidable (∃ (n:ℕ), ℕcolumn_non_zero n) := by sorry
  --have (column : Fin M.column_count) : DecidablePred (column_non_zero column):= by


  --if column_exists:(∃ (n:ℕ), ℕcolumn_non_zero n) then
  --(_ℚrevNormMatrix M (Nat.find column_exists))
  --else (empty ℚ)

end Array2d
