import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19796

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The posted sketch gives the gate list in wire order.
def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 8, 13), (true, 11, 14), (true, 10, 12), (true, 18, 13), (false, 0, 19), (true, 9, 10), (true, 21, 15), (false, 1, 22), (true, 9, 16), (false, 2, 24), (true, 10, 17), (false, 3, 26), (true, 9, 12), (true, 28, 14), (false, 4, 29), (true, 12, 16), (false, 5, 31), (true, 15, 17), (false, 6, 33), (true, 8, 11), (true, 35, 15), (false, 7, 36), (true, 20, 23), (true, 38, 25), (true, 39, 27), (true, 40, 30), (true, 41, 32), (true, 42, 34), (true, 43, 37)]
def circuit : Circuit := ⟨codes.map asGate, 44⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_19796

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_19796 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9928239608072734260 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  exact ⟨PEqualNP.Outside.L_meta_19796.circuit, PEqualNP.Outside.L_meta_19796.mono, by decide, by decide +kernel⟩
