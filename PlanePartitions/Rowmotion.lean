import PlanePartitions.Partition

open PlanePartition
def rowmotion (p : PlanePartition n) : PlanePartition n :=
  -- arr.size > 1 &&
  -- (List.finRange (n - 1)).all (fun i =>
  --   (List.finRange n).all (fun j =>
  --     arr[i][j] ≥ arr[i + (1 : Nat)][j]
  --   )
  -- ) &&
  -- (List.finRange n).all (fun i =>
  --   (List.finRange (n - 1)).all (fun j =>
  --     arr[i][j] ≥ arr[i][j + (1 : Nat)]
  --   )
  -- )

  -- NOTE: Minimal elements not in
  -- Generate partition from there
