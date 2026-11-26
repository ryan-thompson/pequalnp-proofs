import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23927 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4168 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 6] }], output := 11 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
