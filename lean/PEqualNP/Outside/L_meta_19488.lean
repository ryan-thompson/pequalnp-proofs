import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19488_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [7, 9]⟩, ⟨.and, [10, 4]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19488_aux

theorem PEqualNP.Outside.L_meta_19488 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3384055 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19488_aux.circuit, PEqualNP.Outside.L_meta_19488_aux.fan, by decide, by decide +kernel⟩
