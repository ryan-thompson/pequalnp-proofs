import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24083 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283353 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [12] }], output := 13 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
