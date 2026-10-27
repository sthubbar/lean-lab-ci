/-
AI wrote this Lean code for CODEX task121.
P0037 Section 4.2, printed page 210.
Arithmetic soundness of the SGI word and bit addresses.
The seed and index assumptions prevent truncated natural subtraction.
These lemmas do not assert the cited computational coverage.
Binary Goldbach is open.
-/
import LeanLab.Common.Goldbach

namespace LeanLab.DtRS1998.Algorithms121

open LeanLab

/-- P0037 Section 4.2, page 210. The two searched integers add to the addressed
sieve entry when k is an earlier word and the even seed is at least 4. -/
theorem sgi_split_identity {i k j seed : ℕ} (hki : k ≤ i) (hseed : 4 ≤ seed) :
    (128 * (i - k) + seed - 3) + (128 * k + 2 * j + 3) =
      128 * i + 2 * j + seed := by
  have hmul : 128 * k ≤ 128 * i := Nat.mul_le_mul_left 128 hki
  rw [Nat.mul_sub_left_distrib]
  omega

/-- P0037 Section 4.2, page 210. A successful prime search certifies the
addressed even integer as a sum of two primes. -/
theorem sgi_split_sound {i k j seed : ℕ} (hki : k ≤ i) (hseed : 4 ≤ seed)
    (hq : (128 * (i - k) + seed - 3).Prime)
    (hp : (128 * k + 2 * j + 3).Prime) :
    IsGoldbachSum (128 * i + 2 * j + seed) := by
  exact ⟨_, _, hq, hp, sgi_split_identity hki hseed⟩

/-- P0037 Section 4.2, page 210. The smallest nontrivial prime pair is a
concrete instance of the word and bit address lemma. -/
theorem sgi_split_instance : IsGoldbachSum (128 * 0 + 2 * 0 + 6) := by
  apply sgi_split_sound (i := 0) (k := 0) (j := 0) (seed := 6)
  · exact le_rfl
  · decide
  · exact Nat.prime_three
  · exact Nat.prime_three

#print axioms sgi_split_identity
#print axioms sgi_split_sound
#print axioms sgi_split_instance

end LeanLab.DtRS1998.Algorithms121
