import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22440 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881903 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 21] }], output := 22 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
