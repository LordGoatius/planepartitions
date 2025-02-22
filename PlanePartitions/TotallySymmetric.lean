import PlanePartitions.Partition

structure TotallySymmetricPlanePartition (n : Nat) where
  data : PlanePartition n
  invariant_transpose: ∀ (i j : Fin n),
    let value := data.data[i][j]
    -- Only need to check when the value is within bounds (is a valid index)
    value < n →
    -- First transpose
    data.data[j][i] = value
  
  invariant_s3: ∀ (i j : Fin n),
    let value := data.data[i][j]
    value < n →
    -- Second cycle: (i,j,value) → (j,i,value) → (j,value,i)
    data.data[j][value] = i ∧ 
    data.data[i][value] = j

  -- invariant_ts: ∀ (i : Fin (n - 1)) (j : Fin n),
deriving DecidableEq, Repr

def mkTotallySymmPlanePartition {n : Nat} (part : PlanePartition n) : Option (TotallySymmetricPlanePartition n) := do
  sorry

