import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19243_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 1]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19243_aux

theorem PEqualNP.Outside.L_meta_19243 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (495 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19243_aux.circuit, PEqualNP.Outside.L_meta_19243_aux.fan, by decide, by decide +kernel⟩
