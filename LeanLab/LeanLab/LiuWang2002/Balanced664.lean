import LeanLab.LiuWang2002.Counting109

/-!
Retain every prime size restriction in Liu and Wang display 3.9, page 145.
The existing positive count bridge records only the ternary representation.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task664
open Reduction Counting109

/-- Positivity of display 3.9 supplies primes with all its size bounds retained. -/
theorem balanced_three_primes_of_Icount_pos (N : ℕ) (hI : 0 < Icount N) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N ∧
      (0.001 : ℝ) * N ≤ p ∧ p ≤ N ∧
      (0.001 : ℝ) * N ≤ q ∧ q ≤ N ∧
      (0.001 : ℝ) * N ≤ r ∧ r ≤ N := by
  obtain ⟨p, q, h⟩ := (Icount_pos_iff N).mp hI
  rcases h with ⟨hs, hp, hq, hr, hlp, hlq, hlr⟩
  exact ⟨p, q, N - p - q, hp, hq, hr, by omega,
    hlp, by omega, hlq, by omega, hlr, by omega⟩

end LeanLab.LiuWang2002.Task664
#print axioms LeanLab.LiuWang2002.Task664.balanced_three_primes_of_Icount_pos
