/-
P0006, page 2, Sections 2 and 3, one certified successful ladder step.
This connects the bounded test with the coefficient window. It does not provide
the missing ladder data. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.Algorithm98
import LeanLab.HelfgottPlatt.Window98

namespace LeanLab.HelfgottPlatt.Task98

/-- Page 2, Section 2, steps 5 and 6, and Section 3, steps 2 to 4.
An accepted Proth candidate in the window gives the sharp ladder step when
it differs from the current prime and the spacing is even. -/
theorem certified_window_step {N Δ k m B : ℕ} (hpN : N.Prime) (hN : 3 ≤ N)
    (hwin : k ∈ windowIndices N Δ (m + 1)) (hk0 : 0 < k) (hk : k < 2 ^ (m + 1))
    (htest : boundedTest k m B = true) (hne : N ≠ k * 2 ^ (m + 1) + 1)
    (hΔ : Even Δ) :
    (k * 2 ^ (m + 1) + 1).Prime ∧ U6816.Step2 Δ N (k * 2 ^ (m + 1) + 1) := by
  have hp := boundedTest_sound hk0 hk htest
  exact ⟨hp, window_prime_gap hpN hN hwin hp hne hΔ⟩

/-- Page 2, a successful step at N = 5, delta = 10, n = 2, k = 3 and B = 2. -/
theorem certified_step_instance : (13 : ℕ).Prime ∧ U6816.Step2 10 5 13 := by
  simpa using certified_window_step (N := 5) (Δ := 10) (k := 3) (m := 1) (B := 2)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel) (by decide) (by decide)

end LeanLab.HelfgottPlatt.Task98
