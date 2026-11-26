import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19469_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.and, [10, 4]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [14, 7]⟩, ⟨.not, [15]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [17, 7]⟩, ⟨.or, [16, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19469_aux

theorem PEqualNP.Outside.L_meta_19469 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7705467 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19469_aux.circuit, PEqualNP.Outside.L_meta_19469_aux.fan, by decide, by decide +kernel⟩
