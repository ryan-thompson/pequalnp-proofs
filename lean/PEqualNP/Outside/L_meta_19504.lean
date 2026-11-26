import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19504_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19504_aux

theorem PEqualNP.Outside.L_meta_19504 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7881278 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19504_aux.circuit, PEqualNP.Outside.L_meta_19504_aux.fan, by decide, by decide +kernel⟩
