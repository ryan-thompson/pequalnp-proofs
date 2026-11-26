import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20072

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate list obtained by factoring a cover of the matrix by rectangles.
def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 2, 6), (true, 0, 7), (true, 3, 5), (true, 1, 17), (true, 1, 16), (true, 20, 5), (true, 4, 19), (true, 20, 4), (true, 0, 16), (true, 24, 3), (true, 2, 18), (true, 26, 7), (true, 17, 5), (true, 28, 4), (true, 3, 19), (true, 6, 18), (true, 31, 4), (false, 21, 8), (false, 22, 9), (false, 23, 10), (false, 25, 11), (false, 27, 12), (false, 29, 13), (false, 30, 14), (false, 32, 15), (true, 33, 34), (true, 41, 35), (true, 42, 36), (true, 43, 37), (true, 44, 38), (true, 45, 39), (true, 46, 40)]
def circuit : Circuit := ⟨codes.map asGate, 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20072

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_20072 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8254449022188472170 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_20072.circuit, PEqualNP.Outside.L_meta_20072.mono, by decide, by decide +kernel⟩
