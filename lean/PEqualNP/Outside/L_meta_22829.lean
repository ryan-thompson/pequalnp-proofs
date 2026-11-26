import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22829 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841718 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 23] }], output := 24 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
