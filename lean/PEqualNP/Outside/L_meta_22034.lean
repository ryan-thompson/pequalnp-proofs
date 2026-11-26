import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22034 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816124 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 20] }], output := 21 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
