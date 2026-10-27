/-
P0006, page 2, Section 3, the prime ladder coefficient window.
The interval contains candidate coefficients, not certified primes. Advancement
of the ladder requires a distinct prime to be chosen. AI wrote the Lean code.
Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.HelfgottPlattU6816Sharp

namespace LeanLab.HelfgottPlatt.Task98

/-- Page 2, Section 3, step 2. For N at least 2, the greatest natural coefficient
whose progression term is strictly below N. -/
def indexBelow (N n : ℕ) : ℕ := (N - 2) / 2 ^ n

/-- Page 2, Section 3, step 2. The strict cutoff is characterized by indexBelow. -/
theorem indexBelow_spec {N n k : ℕ} (hN : 2 ≤ N) :
    k * 2 ^ n + 1 < N ↔ k ≤ indexBelow N n := by
  unfold indexBelow
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ n)]
  omega

/-- Page 2, Section 3, steps 2 and 3. The scanned coefficients are strictly
above k0 and at most k1. -/
def windowIndices (N Δ n : ℕ) : Finset ℕ :=
  Finset.Ioc (indexBelow N n) (indexBelow (N + Δ) n)

/-- Page 2, Section 3. The coefficient window is exactly the progression
terms at least N and strictly below N plus delta. -/
theorem mem_windowIndices {N Δ n k : ℕ} (hN : 2 ≤ N) :
    k ∈ windowIndices N Δ n ↔ N ≤ k * 2 ^ n + 1 ∧ k * 2 ^ n + 1 < N + Δ := by
  simp only [windowIndices, Finset.mem_Ioc]
  have hN' : 2 ≤ N + Δ := by omega
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, (indexBelow_spec hN').mpr hhi⟩
    by_contra h
    have hk := (indexBelow_spec hN).mp (by omega : k * 2 ^ n + 1 < N)
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, (indexBelow_spec hN').mp hhi⟩
    by_contra h
    have hk := (indexBelow_spec hN).mpr (by omega : k ≤ indexBelow N n)
    omega

/-- Page 2, Section 3, step 1. Spacing larger than 2 to the power n guarantees
a nonempty coefficient window, without asserting that it contains a new prime. -/
theorem windowIndices_nonempty {N Δ n : ℕ} (hN : 2 ≤ N) (hΔ : 2 ^ n < Δ) :
    (windowIndices N Δ n).Nonempty := by
  have hprod := Nat.div_mul_le_self (N - 2) (2 ^ n)
  have hsub : N - 2 + 2 = N := Nat.sub_add_cancel hN
  have hnext : (indexBelow N n + 1) * 2 ^ n + 1 < N + Δ := by
    unfold indexBelow
    nlinarith
  have hupper : indexBelow N n + 1 ≤ indexBelow (N + Δ) n :=
    (indexBelow_spec (by omega : 2 ≤ N + Δ)).mp hnext
  refine ⟨indexBelow N n + 1, ?_⟩
  simp only [windowIndices, Finset.mem_Ioc]
  omega

/-- Page 3, interval candidate counting. Shifting the endpoint by c whole
periods shifts the strict coefficient index by c. -/
theorem indexBelow_shift {N n : ℕ} (hN : 2 ≤ N) (c : ℕ) :
    indexBelow (N + c * 2 ^ n) n = indexBelow N n + c := by
  unfold indexBelow
  rw [Nat.sub_add_comm hN, Nat.add_mul_div_right _ _ (by positivity)]

/-- Page 3, candidate count. A window of c periods contains exactly c
progression coefficients, independent of its starting point N at least 2. -/
theorem window_card_mul {N n : ℕ} (hN : 2 ≤ N) (c : ℕ) :
    (windowIndices N (c * 2 ^ n) n).card = c := by
  rw [windowIndices, Nat.card_Ioc, indexBelow_shift hN]
  omega

/-- Page 3, Section 4. At n = 52 the printed interval width contains exactly
four billion progression coefficients before Proth size and primality checks. -/
theorem window_card_paper {N : ℕ} (hN : 2 ≤ N) :
    (windowIndices N (2 ^ 54 * 10 ^ 9) 52).card = 4 * 10 ^ 9 := by
  have hwidth : (2 : ℕ) ^ 54 * 10 ^ 9 = (4 * 10 ^ 9) * 2 ^ 52 := by norm_num
  rw [hwidth]
  exact window_card_mul hN (4 * 10 ^ 9)

/-- Page 2, Section 3, successful selection. A distinct prime in the coefficient
window gives the sharp gap when the current rung is an odd prime and delta is even. -/
theorem window_prime_gap {N Δ n k : ℕ} (hpN : N.Prime) (hN : 3 ≤ N)
    (hk : k ∈ windowIndices N Δ n) (hp : (k * 2 ^ n + 1).Prime)
    (hne : N ≠ k * 2 ^ n + 1) (hΔ : Even Δ) :
    U6816.Step2 Δ N (k * 2 ^ n + 1) := by
  obtain ⟨hlo, hhi⟩ := (mem_windowIndices (by omega : 2 ≤ N)).mp hk
  exact U6816.algorithm_step hpN hp hN (by omega) hhi hΔ

/-- Pages 2 and 3, small instances of the endpoints, period count and sharp gap. -/
theorem window_instances :
    indexBelow 5 2 = 0 ∧ indexBelow 15 2 = 3 ∧
    windowIndices 5 10 2 = {1, 2, 3} ∧ 3 ∉ windowIndices 5 8 2 ∧
    (windowIndices 5 (2 * 2 ^ 2) 2).card = 2 ∧ U6816.Step2 10 5 13 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, window_card_mul (by decide) 2, ?_⟩
  simpa using window_prime_gap (N := 5) (Δ := 10) (n := 2) (k := 3)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide) (by decide)

end LeanLab.HelfgottPlatt.Task98
