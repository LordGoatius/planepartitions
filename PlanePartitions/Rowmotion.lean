import PlanePartitions.Partition

open PlanePartition
def rowmotion (p : PlanePartition n) : PlanePartition n :=
  let minimalElements := 
      (List.range n).filter (λ i =>
        (List.range n).filter (λ j =>
          p.data[i][j] = 0 ∧ 
          (i = 0 ∨ p.data[i - 1][j] > 0) ∧ 
          (j = 0 ∨ p.data[i][j - 1] > 0)
        )
      )

  let newData := 
    p.data.map (λ row =>
      row.map (λ x =>
        if minimalElements.contains x then x + 1 else x
      )
    )

  ⟨newData, 
    λ i j => by simp; exact p.invariant_col i j, 
    λ i j => by simp; exact p.invariant_row i j⟩


