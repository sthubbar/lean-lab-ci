/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Explicit constants for the singular series comparison on MM printed page 1.
This comparison does not estimate the actual Goldbach count.
-/
import LeanLab.Routes.Task59FiniteTwin
import LeanLab.Routes.Task59TotientProduct
import LeanLab.Routes.Task59SingularSeries

namespace LeanLab.Routes.Task59

open Finset LeanLab.Routes.U1451

/-- The singular series comparison with explicit constants twinProd and 1. -/
theorem singSeries_totient_bounds (h : ℕ) (hh : 1 ≤ h) :
    twinProd * (if 2 ∣ h then (h : ℝ) / h.totient else 0) ≤ singSeries h ∧
      singSeries h ≤ (if 2 ∣ h then (h : ℝ) / h.totient else 0) := by
  classical
  by_cases hev : 2 ∣ h
  · simp only [if_pos hev]
    have h2 : 2 ≤ h := Nat.le_of_dvd (by omega) hev
    let s := h.primeFactors.filter (fun p => 2 < p)
    let f : ℕ → ℝ := fun p => (p : ℝ) / ((p : ℝ) - 1)
    let g : ℕ → ℝ := fun p => ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))
    have hp : ∀ p ∈ s, p.Prime ∧ 2 < p := by
      intro p hp
      exact ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
    have hb := finite_inverse_twin_bounds s hp
    change 1 ≤ (∏ p ∈ s, g p) ∧ (∏ p ∈ s, g p) ≤ twinProd⁻¹ at hb
    have hprod : (∏ p ∈ s, (1 + 1 / ((p : ℝ) - 2))) =
        (∏ p ∈ s, f p) * (∏ p ∈ s, g p) := by
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro p hp'
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (hp p hp').2
      have h0 : (p : ℝ) ≠ 0 := by linarith
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2' : (p : ℝ) - 2 ≠ 0 := by linarith
      dsimp [f, g]
      field_simp [h0, h1, h2'] <;> ring
    have heq : singSeries h = twinProd * ((h : ℝ) / h.totient) * (∏ p ∈ s, g p) := by
      rw [singSeries, if_pos hev, totient_ratio_even_eq_two_prod h2 hev]
      change 2 * twinProd * (∏ p ∈ s, (1 + 1 / ((p : ℝ) - 2))) =
        twinProd * (2 * ∏ p ∈ s, f p) * ∏ p ∈ s, g p
      rw [hprod]
      ring
    have hc : 0 ≤ twinProd * ((h : ℝ) / h.totient) :=
      mul_nonneg twinProd_pos.le (by positivity)
    rw [heq]
    constructor
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.1 hc
    · calc _ ≤ (twinProd * ((h : ℝ) / h.totient)) * twinProd⁻¹ :=
          mul_le_mul_of_nonneg_left hb.2 hc
        _ = ((h : ℝ) / h.totient) * (twinProd * twinProd⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ twinProd_pos.ne', mul_one]
  · simp [singSeries, hev]

example : twinProd * ((2 : ℝ) / (2 : ℕ).totient) ≤ singSeries 2 ∧
    singSeries 2 ≤ (2 : ℝ) / (2 : ℕ).totient := by
  simpa using singSeries_totient_bounds 2 (by norm_num)

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.singSeries_totient_bounds
