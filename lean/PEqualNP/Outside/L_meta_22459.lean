import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22459 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17072 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 18] }], output := 20 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
