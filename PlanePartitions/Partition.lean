import Mathlib.Tactic.ApplyAt
import Mathlib.Data.List.Defs

structure PlanePartition (n : Nat) where
  data : Vector (Vector Nat n) n
  -- Make sure cols are weakly decreasing
  invariant_col : ∀ (i : Fin (n - 1)) (j : Fin n),
    data[i][j] ≥ data[i + (1 : Nat)][j]
  -- Make sure rows are weakly decreasing
  invariant_row : ∀ (i : Fin n) (j : Fin (n - 1)),
    data[i][j] ≥ data[i][j + (1 : Nat)]
  invariant_height : ∀ (i : Fin n) (j : Fin n),
    -- why not just make this a vec of `Fin`s instead?
    data[i][j] ≤ n
deriving DecidableEq, Repr

-- Computable validation function
def validPlanePartition {n : Nat} (arr : Vector (Vector Nat n) n) : Bool :=
  arr.size > 1 &&
  (List.finRange (n - 1)).all (fun i =>
    (List.finRange n).all (fun j =>
      arr[i][j] ≥ arr[i + (1 : Nat)][j]
    )
  ) &&
  (List.finRange n).all (fun i =>
    (List.finRange (n - 1)).all (fun j =>
      arr[i][j] ≥ arr[i][j + (1 : Nat)]
    )
  )

-- you could also use dif-then-else instead
def guardP {f} [Alternative f] (p : Prop) [Decidable p] :
    f (PLift p) := if h : p then pure (.up h) else failure

def mkPlanePartition {n : Nat} (arr : Vector (Vector Nat n) n) : Option (PlanePartition n) := do
  -- Make sure it's weakly decreasing along the rows
  -- let rowElementsValid := arr.all (fun row =>
  --   (List.finRange (n - 1)).all (fun j =>
  --     row[j] ≥ row[j + (1 : Nat)]
  --   )
  -- )
  let rowElementsValid := (List.finRange n).all (fun i =>
    (List.finRange (n - 1)).all (fun j =>
      arr[i][j] ≥ arr[i][j + (1 : Nat)]
    )
  )
  let rowValid ← guardP rowElementsValid

  -- Make sure it's weakly decreasing along the columns
  let colElementsValid := (List.finRange (n - 1)).all (fun i =>
    (List.finRange n).all (fun j =>
      arr[i][j] ≥ arr[i + (1 : Nat)][j]
    )
  )
  let colValid ← guardP colElementsValid

  let elemHeightValid := (List.finRange n).all (fun i =>
    (List.finRange n).all (fun j =>
      arr[i][j] ≤ n
    )
  )
  let heightValid ← guardP elemHeightValid

  return {
    data := arr
    invariant_col := by
      intro i j
      apply PLift.down at colValid
      simp only [Fin.getElem_fin, List.all_eq_true, colElementsValid] at colValid
      apply of_decide_eq_true
      apply colValid
      · apply List.mem_iff_get.mpr
        exact ⟨i.cast (List.length_finRange (n - 1)).symm, by simp⟩
      · apply List.mem_iff_get.mpr
        exact ⟨j.cast (List.length_finRange n).symm, by simp⟩
    invariant_row := by
      intro i j
      apply PLift.down at rowValid
      simp only [Fin.getElem_fin, List.all_eq_true, rowElementsValid] at rowValid
      apply of_decide_eq_true
      apply rowValid
      · apply List.mem_iff_get.mpr
        exact ⟨i.cast (List.length_finRange n).symm, by simp⟩
      · apply List.mem_iff_get.mpr
        exact ⟨j.cast (List.length_finRange (n - 1)).symm, by simp⟩
    invariant_height := by
      intro i j
      apply PLift.down at heightValid
      simp only [Fin.getElem_fin, List.all_eq_true, elemHeightValid,] at heightValid
      apply of_decide_eq_true
      apply heightValid
      · apply List.mem_iff_get.mpr
        exact ⟨i.cast (List.length_finRange n).symm, by simp⟩
      · apply List.mem_iff_get.mpr
        exact ⟨j.cast (List.length_finRange n).symm, by simp⟩
  }


def pp2 : Option (PlanePartition 2) := mkPlanePartition #v[#v[1, 0], #v[0, 0]]

#eval pp2
