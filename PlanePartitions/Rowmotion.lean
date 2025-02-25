import PlanePartitions.Partition
import Init.Data.Vector.Basic

open PlanePartition

def rowmotion (p : PlanePartition n) : PlanePartition n  :=
  let minimal : Vector (Vector (Bool) n) n := ⟨p.data.mapFinIdx (fun i a =>
    ⟨a.mapFinIdx (fun j k =>
      -- if i is zero, only check j
      -- if j is zero, only check i
      -- if both are zero, it is automatically true, unless it goes above Fin (n+1)
      -- if neither are zero, check both
      -- else false
      -- if n < p.data[i - (1 : Nat)][j] ∧ n < p.data[i][j - 1] then
      --   true
      -- else
      --   false
      if i == (0 : Nat) && j == (0 : Nat) then
        true && (p.data[i][j] < n+1)
      else if i == (0 : Nat) then
        true && (p.data[i][j - (1 : Nat)]! > k)
      else if j == (0 : Nat) then
        true && (p.data[i - (1 : Nat)]![j] > k)
      else
        true && (p.data[i - (1 : Nat)]![j] > k)
        && (p.data[i][j - (1 : Nat)]! > k)
    ), by simp⟩
  ), by simp⟩

  let just_min : Vector (Vector (Fin (n+1)) n) n := ⟨p.data.mapFinIdx (fun i a =>
    ⟨a.mapFinIdx (fun j k => 
      if minimal[i][j] then
        k + 1
      else 
        0
    ), by simp⟩
  ), by simp⟩


 -- need to fill with minimum
  {
    data := just_min
    invariant_col :=
      sorry
    invariant_row :=
      sorry
  }
