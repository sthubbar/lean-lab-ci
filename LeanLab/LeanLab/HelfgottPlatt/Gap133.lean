/-
P0006 page 2, Section 3, fallback advancement and elementary prime gap
bounds. Bertrand supplies a sufficient width exceeding the current
rung. This does not certify the paper's fixed width ladder to T.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.Fallback133
import Mathlib.NumberTheory.Bertrand

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 2, a standard sufficient condition for fallback progress.
Bertrand supplies a new prime when delta exceeds the current prime. -/
theorem fallbackPrime_bertrand {N Δ : ℕ} (hp : N.Prime) (hN : 3 ≤ N)
    (hΔ : Even Δ) (hwide : N < Δ) :
    (fallbackPrime (N + Δ)).Prime ∧ U6816.Step2 Δ N (fallbackPrime (N + Δ)) := by
  obtain ⟨q, hqp, hNq, hqle⟩ := Nat.exists_prime_lt_and_le_two_mul N hp.ne_zero
  exact fallbackPrime_step hp hN hΔ ⟨q, hqp, hNq, by omega⟩

/-- Page 2, a standard limitation of global fixed width replacements.
Every integer from D factorial plus two through D factorial plus D is
composite. This is not a statement about the paper's finite ladder. -/
theorem factorial_gap {D q : ℕ} (hlo : D.factorial + 2 ≤ q) (hhi : q ≤ D.factorial + D) :
    ¬ q.Prime := by
  let d := q - D.factorial
  have hd2 : 2 ≤ d := by dsimp [d]; omega
  have hdD : d ≤ D := by dsimp [d]; omega
  have he : q = D.factorial + d := by dsimp [d]; omega
  have hdF : d ∣ D.factorial := Nat.dvd_factorial (by omega) hdD
  have hdq : d ∣ q := by rw [he]; exact dvd_add hdF (dvd_refl d)
  have hF : 0 < D.factorial := Nat.factorial_pos D
  exact Nat.not_prime_of_dvd_of_lt hdq hd2 (by omega)

/-- Page 2, limitation of a uniform replacement for the finite ladder.
For every positive fixed width there is an odd prime at which the fallback
stagnates. The paper only claims its finite computed ladder. -/
theorem no_uniform_fallback_progress {Δ : ℕ} (hΔ : 0 < Δ) :
    ∃ N : ℕ, N.Prime ∧ 3 ≤ N ∧ fallbackPrime (N + Δ) = N := by
  let D := max Δ 3
  have hD : 3 ≤ D := Nat.le_max_right Δ 3
  have hΔD : Δ ≤ D := Nat.le_max_left Δ 3
  have hF : 3 ≤ D.factorial := le_trans hD (Nat.self_le_factorial D)
  let N := fallbackPrime (D.factorial + 2)
  obtain ⟨hp, hNM, hmax⟩ := fallbackPrime_spec (by omega : 2 < D.factorial + 2)
  have h3 : 3 ≤ N := hmax 3 Nat.prime_three (by omega)
  refine ⟨N, hp, h3, (fallbackPrime_stagnates_iff hp hΔ).mpr ?_⟩
  rintro ⟨q, hq, hNq, hqM⟩
  by_cases hbefore : q < D.factorial + 2
  · exact (not_lt_of_ge (hmax q hq hbefore)) hNq
  · exact factorial_gap (D := D) (by omega) (by omega) hq

end LeanLab.HelfgottPlatt.Task133
