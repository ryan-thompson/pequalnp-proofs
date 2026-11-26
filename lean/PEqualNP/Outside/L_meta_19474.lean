import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19474_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [14, 4]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [16, 17]⟩, ⟨.not, [18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19474_aux

theorem PEqualNP.Outside.L_meta_19474 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12066551 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19474_aux.circuit, PEqualNP.Outside.L_meta_19474_aux.fan, by decide, by decide +kernel⟩
