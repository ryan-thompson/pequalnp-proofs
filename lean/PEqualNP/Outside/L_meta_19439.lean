import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19439_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.not, [10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [15, 4]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19439_aux

theorem PEqualNP.Outside.L_meta_19439 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3957566 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19439_aux.circuit, PEqualNP.Outside.L_meta_19439_aux.fan, by decide, by decide +kernel⟩
