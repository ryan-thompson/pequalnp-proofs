import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22260 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (818814 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 21] }], output := 22 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
