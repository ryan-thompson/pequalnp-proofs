import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19487_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [8, 13]⟩, ⟨.not, [15]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19487_aux

theorem PEqualNP.Outside.L_meta_19487 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3383575 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19487_aux.circuit, PEqualNP.Outside.L_meta_19487_aux.fan, by decide, by decide +kernel⟩
