import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22516 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899773 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }], output := 22 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
