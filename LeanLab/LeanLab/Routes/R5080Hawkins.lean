/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5700, route R-5080.

# Hawkins' random sieve and the Goldbach count

Hawkins 1957: start from `{2, 3, ...}`, take `P₁ = 2`, remove each later element independently
with probability `1/P₁`, let `P₂` be the least survivor above `P₁`, and so on. Sequentially,
given the Hawkins primes below `n`, the number `n` survives with probability
`q(n) = ∏_{P < n} (1 - 1/P)`, from coins independent of everything below `n`.

The route needs two probabilistic steps, both proved here in their abstract form:

* `prod_one_sub_le_exp_neg_sum`: `∏ (1 - x_i) ≤ exp(-Σ x_i)` for `x_i ≤ 1`. With independent
  pair events of probability `x_a`, this bounds the chance that `n` has no representation by
  `exp(-Σ_a x_a)`; for Hawkins primes `x_a ≈ q(a) q(n - a) ≈ 1/(log a log(n - a))`.
* `ae_eventually_represented`: Borel-Cantelli. If the failure events `E n` have summable
  probabilities, then almost surely only finitely many `n` fail.
* `summable_exp_neg_div_log_sq`: the bound `exp(-c n / log² n)` is summable for every `c > 0`,
  so the scheme closes whenever the failure probability has that size.

The pair events of Hawkins' sieve are not independent, so the first step does not apply to the
model as it stands; that dependence is the open point of the model question, and the model
question is not Goldbach. KNOWN mathematics in substance. Not progress on Goldbach, which is OPEN.
-/
import Mathlib

open Finset MeasureTheory Filter Real
open scoped ENNReal

noncomputable section
namespace LeanLab.Routes.R5080

/-- `∏ (1 - x_i) ≤ exp (-Σ x_i)` for `x_i ≤ 1`, from `1 - x ≤ exp(-x)`; probabilities qualify. -/
theorem prod_one_sub_le_exp_neg_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h1 : ∀ i ∈ s, x i ≤ 1) :
    ∏ i ∈ s, (1 - x i) ≤ exp (-∑ i ∈ s, x i) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i hi => by linarith [h1 i hi]) (fun i _ => ?_)
  have := Real.add_one_le_exp (-x i)
  linarith

/-- Borel-Cantelli in the form the route uses: summable failure probabilities give, almost
surely, a representation for every large `n`. -/
theorem ae_eventually_represented {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ℕ → Set Ω) (b : ℕ → ℝ≥0∞) (hb : ∑' n, b n ≠ ∞) (hE : ∀ n, μ (E n) ≤ b n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ E n :=
  ae_eventually_notMem (ne_top_of_le_ne_top hb (ENNReal.tsum_le_tsum hE))

/-- The failure bound `exp(-c n / log² n)` is summable over `n` for every `c > 0`. -/
theorem summable_exp_neg_div_log_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => exp (-(c * n / (log n) ^ 2))) := by
  have hlo := (isLittleO_pow_log_id_atTop (n := 3)).bound (half_pos hc)
  have hN : ∀ᶠ n : ℕ in atTop, ‖log (n : ℝ) ^ 3‖ ≤ c / 2 * ‖((n : ℝ))‖ :=
    tendsto_natCast_atTop_atTop.eventually hlo
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (summable_one_div_nat_pow.mpr (by norm_num)) ?_
  filter_upwards [hN, eventually_ge_atTop 3] with n hn h3
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnpos : (0 : ℝ) < n := by linarith
  have hl : 0 < log (n : ℝ) := log_pos hn1
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  rw [Real.norm_eq_abs, abs_of_pos (pow_pos hl 3), Real.norm_eq_abs, abs_of_pos hnpos] at hn
  have key : 2 * log (n : ℝ) ≤ c * n / (log n) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hl 2)]
    nlinarith
  calc exp (-(c * n / (log n) ^ 2)) ≤ exp (-(2 * log (n : ℝ))) := exp_le_exp.mpr (by linarith)
    _ = 1 / (n : ℝ) ^ 2 := by
      rw [show -(2 * log (n : ℝ)) = -log ((n : ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
        exp_neg, exp_log (pow_pos hnpos 2), one_div]

end LeanLab.Routes.R5080
