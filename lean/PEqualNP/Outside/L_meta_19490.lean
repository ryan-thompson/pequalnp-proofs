import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19490_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.not, [10]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [14, 6]⟩, ⟨.not, [15]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [17, 6]⟩, ⟨.or, [16, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19490_aux

theorem PEqualNP.Outside.L_meta_19490 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3585117 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19490_aux.circuit, PEqualNP.Outside.L_meta_19490_aux.fan, by decide, by decide +kernel⟩
