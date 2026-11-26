import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21300 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47607 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 18] }], output := 19 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
