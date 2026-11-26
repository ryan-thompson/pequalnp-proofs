import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22509 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898233 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 21] }], output := 22 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
