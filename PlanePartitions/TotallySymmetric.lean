import PlanePartitions.Partition

structure TotallySymmetricPlanePartition (n : Nat) where
  data : PlanePartition n
  invariant_transpose: ∀ (i j : Fin n),
    let value := data.data[i][j]
    -- Only need to check when the value is within bounds (is a valid index)
    value < n →
    -- First cycle: (i,j,value) → (value,j,i) → (i,value,j)
    data.data[j][i] = value
  
  invariant_ts_2 : ∀ (i j : Fin n),
    let value := data.data[i][j]
    value < n →
    -- Second cycle: (i,j,value) → (j,i,value) → (j,value,i)
    data.data[j][i] = value ∧
    data.data[j][value]! = i
  -- invariant_ts: ∀ (i : Fin (n - 1)) (j : Fin n),
deriving DecidableEq, Repr
