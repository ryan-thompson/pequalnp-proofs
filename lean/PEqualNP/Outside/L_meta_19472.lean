import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19472_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [0, 16]⟩, ⟨.and, [12, 17]⟩, ⟨.or, [15, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19472_aux

theorem PEqualNP.Outside.L_meta_19472 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (11911415 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19472_aux.circuit, PEqualNP.Outside.L_meta_19472_aux.fan, by decide, by decide +kernel⟩
