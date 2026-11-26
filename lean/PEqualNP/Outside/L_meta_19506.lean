import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19506_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19506_aux

theorem PEqualNP.Outside.L_meta_19506 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16221265 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19506_aux.circuit, PEqualNP.Outside.L_meta_19506_aux.fan, by decide, by decide +kernel⟩
