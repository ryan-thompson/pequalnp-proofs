import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22082 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837099 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 20] }], output := 21 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
