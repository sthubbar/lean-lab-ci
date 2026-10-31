/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Euler's finite product in the odd prime form requested by U1436.
-/
import Mathlib

namespace LeanLab.Routes.Task59

open Finset

/-- At an even positive integer the factor from the prime 2 is exactly 2. -/
theorem totient_ratio_even_eq_two_prod {N : ℕ} (hN : 2 ≤ N) (hev : 2 ∣ N) :
    (N : ℝ) / N.totient =
      2 * ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have ht := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors N)
  push_cast at ht
  have hp : 0 < ∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹) := by
    apply prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hi := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hall : (N : ℝ) / N.totient =
      ∏ p ∈ N.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    calc _ = (∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
          rw [ht]
          field_simp [hN0, hp.ne']
      _ = ∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := (prod_inv_distrib _).symm
      _ = _ := by
          apply prod_congr rfl
          intro p hp
          have hp0 : (0 : ℝ) < p := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          have hf : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by
            field_simp [hp0.ne']
          rw [hf, inv_div]
  have h2 : 2 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hev, by omega⟩
  have he : N.primeFactors.erase 2 = N.primeFactors.filter (fun p => 2 < p) := by
    ext p
    simp only [mem_erase, mem_filter]
    constructor
    · rintro ⟨hp2, hp⟩
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, h2p⟩
      exact ⟨by omega, hp⟩
  rw [hall, ← mul_prod_erase N.primeFactors (fun p : ℕ => (p : ℝ) / ((p : ℝ) - 1)) h2, he]
  norm_num

example : (30 : ℝ) / (30 : ℕ).totient =
    2 * ∏ p ∈ (30 : ℕ).primeFactors.filter (fun p => 2 < p), (p : ℝ) / ((p : ℝ) - 1) :=
  totient_ratio_even_eq_two_prod (by norm_num) (by norm_num)

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.totient_ratio_even_eq_two_prod
