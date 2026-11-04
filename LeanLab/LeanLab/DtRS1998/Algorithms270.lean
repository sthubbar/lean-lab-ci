/-
AI wrote this Lean code for CODEX task270.
P0037 Section 4.2 page 210, the displayed word and bit addresses.
Natural subtraction is taken after adding the seed.
This permits k to exceed i when the searched integer stays nonnegative.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper

namespace LeanLab.DtRS1998.Algorithms270

open LeanLab

/-- P0037 Section 4.2 page 210, the two searched integers.
With the seed included before subtraction, no comparison of k with i is needed. -/
theorem sgi_split_identity {i k j seed : ℕ}
    (hsub : 128 * k + 3 ≤ 128 * i + seed) :
    (128 * i + seed - (128 * k + 3)) + (128 * k + 2 * j + 3) =
      128 * i + 2 * j + seed := by
  have h := Nat.sub_add_cancel hsub
  omega

/-- P0037 Section 4.2 page 210, successful searches certify the addressed entry.
This is CONDITIONAL ON the supplied primality proofs. -/
theorem sgi_split_sound {i k j seed : ℕ}
    (hsub : 128 * k + 3 ≤ 128 * i + seed)
    (hq : (128 * i + seed - (128 * k + 3)).Prime)
    (hp : (128 * k + 2 * j + 3).Prime) :
    IsGoldbachSum (128 * i + 2 * j + seed) :=
  ⟨_, _, hq, hp, sgi_split_identity hsub⟩

/-- P0037 Section 4.2 page 210, a nonvacuous address instance with k greater than i.
At i = j = 0, k = 1 and seed = 134, the prime pair is 3 and 131. -/
theorem sgi_split_instance : IsGoldbachSum 134 :=
  sgi_split_sound (i := 0) (k := 1) (j := 0) (seed := 134)
    (by decide) (by decide +kernel) (by decide +kernel)

#print axioms sgi_split_identity
#print axioms sgi_split_sound
#print axioms sgi_split_instance

end LeanLab.DtRS1998.Algorithms270
