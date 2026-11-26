import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19477_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [2, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.not, [17]⟩, ⟨.and, [14, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19477_aux

theorem PEqualNP.Outside.L_meta_19477 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223860 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19477_aux.circuit, PEqualNP.Outside.L_meta_19477_aux.fan, by decide, by decide +kernel⟩
