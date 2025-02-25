import PlanePartitions.Partition
import Init.Data.Nat.Basic
import Mathlib.Order.Nat

structure TotallySymmetricPlanePartition (n : Nat) extends PlanePartition n where
  invariant_transpose: ∀ (i j : Fin n),
    data[i][j] = data[j][i]
    -- First transpose - only applies when value < n
  invariant_s3: ∀ (i j : Fin n),
    let value := data[i][j].val
    (if h : value < n then
      -- We only need these equalities when value < n
      let value_fin : Fin n := ⟨value, h⟩
      data[j][value_fin] = i.val ∧ 
      data[i][value_fin] = j.val
    else
      -- If value = n, no additional conditions needed
      True)
deriving DecidableEq, Repr
