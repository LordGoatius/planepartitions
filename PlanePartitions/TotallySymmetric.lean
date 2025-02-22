import PlanePartitions.Partition
import Init.Data.Nat.Basic
import Mathlib.Order.Nat

structure TotallySymmetricPlanePartition (n : Nat) where
  data : PlanePartition n
  invariant_transpose: ∀ (i j : Fin n),
    let value := data.data[i][j] -- Note: we need .val since data now contains Fin (n+1)
    -- First transpose - only applies when value < n
    value < n →
    data.data[j][i] = value

  invariant_s3: ∀ (i j : Fin n),
    let value := data.data[i][j].val
    (if h : value < n then
      -- We only need these equalities when value < n
      -- When value < n, we can safely create a Fin n from it
      let value_fin : Fin n := ⟨value, h⟩
      data.data[j][value_fin] = i.val ∧ 
      data.data[i][value_fin] = j.val
    else
      -- If value = n, no additional conditions needed
      True)
deriving DecidableEq, Repr
