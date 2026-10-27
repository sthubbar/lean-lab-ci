/-
P0017 p. 1747 Section 4, fixed shifts and word offsets.
An odd prime p adds a bit shift of (p - 1) / 2.
The implementation splits this into a word offset and a residue below 32.
These are arithmetic correctness obligations, not a certificate for the full computation.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Richstein2001

/-- LEAF. P0017 p. 1747 Section 4: the stored bit remainder is below 32,
and the word offset accounts for the rest of the shift. -/
theorem shift_split116 (p : ℕ) :
    (p - 1) / 2 = 32 * ((p - 1) / 64) + (p - 1) / 2 % 32 ∧
      (p - 1) / 2 % 32 < 32 := by
  constructor
  · have h := Nat.div_add_mod ((p - 1) / 2) 32
    simpa [Nat.div_div_eq_div_mul] using h.symm
  · exact Nat.mod_lt _ (by decide)

/-- LEAF. P0017 p. 1747 Section 4: adding odd p to an odd represented number
agrees with the stored word offset and bit remainder, including the carry. -/
theorem shifted_value116 (p m j : ℕ) (hp : Odd p) :
    64 * m + 2 * j + 1 + p =
      64 * (m + (p - 1) / 64 + (j + (p - 1) / 2 % 32) / 32) +
        2 * ((j + (p - 1) / 2 % 32) % 32) + 2 := by
  obtain ⟨k, hk⟩ := hp
  omega

/-- LEAF. P0017 p. 1747 Section 4: a valid source bit and stored remainder
produce at most one carry, and the resulting bit is valid. -/
theorem shift_carry116 (p j : ℕ) (hj : j < 32) :
    (j + (p - 1) / 2 % 32) / 32 ≤ 1 ∧
      (j + (p - 1) / 2 % 32) % 32 < 32 := by
  have h := Nat.mod_lt ((p - 1) / 2) (by decide : 0 < 32)
  constructor
  · omega
  · exact Nat.mod_lt _ (by decide)

/-- P0017 p. 1747 Section 4: the fixed-shift representation preserves the value
of q plus p and produces a valid destination bit. -/
theorem fixed_shift_correct116 (p m j : ℕ) (hp : Odd p) (hj : j < 32) :
    (p - 1) / 2 % 32 < 32 ∧
    (j + (p - 1) / 2 % 32) / 32 ≤ 1 ∧
    (j + (p - 1) / 2 % 32) % 32 < 32 ∧
    64 * m + 2 * j + 1 + p =
      64 * (m + (p - 1) / 64 + (j + (p - 1) / 2 % 32) / 32) +
        2 * ((j + (p - 1) / 2 % 32) % 32) + 2 := by
  exact ⟨(shift_split116 p).2, (shift_carry116 p j hj).1,
    (shift_carry116 p j hj).2, shifted_value116 p m j hp⟩

end LeanLab.Richstein2001
