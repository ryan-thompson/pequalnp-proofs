import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19424_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [13, 8]⟩, ⟨.not, [14]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [16, 0]⟩, ⟨.or, [15, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19424_aux

theorem PEqualNP.Outside.L_meta_19424 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19424_aux.circuit, PEqualNP.Outside.L_meta_19424_aux.fan, by decide, by decide +kernel⟩
