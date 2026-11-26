import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19426_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [12, 14]⟩, ⟨.not, [7]⟩, ⟨.and, [16, 0]⟩, ⟨.or, [15, 17]⟩, ⟨.not, [18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19426_aux

theorem PEqualNP.Outside.L_meta_19426 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24882532 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19426_aux.circuit, PEqualNP.Outside.L_meta_19426_aux.fan, by decide, by decide +kernel⟩
