import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19501_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [5, 0]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19501_aux

theorem PEqualNP.Outside.L_meta_19501 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594073 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19501_aux.circuit, PEqualNP.Outside.L_meta_19501_aux.fan, by decide, by decide +kernel⟩
