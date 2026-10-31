/-
P0096 Heath-Brown 1985, the prime-count window of Corollary 2 without Siegel-Walfisz.
The proof of Corollary 2 in Vinogradov.lean uses its Siegel-Walfisz hypothesis twice: at modulus
k = 1 for the primes in (n/7 + 1, 3n/7 - 1], and through Theorem 1. The k = 1 use is the prime
number theorem with error term, now PROVED in the lab from the PrimeNumberTheoremAnd port,
LeanLab.PNTPort.psi_explicit_strong. So:
* `theta_window_ge_of_psi`: theta_window_ge on the k = 1 hypothesis only, same proof.
* `primeWindow_eventually`: unconditional, for all large t, θ(3t/7 - 1) - θ(t/7 + 1) ≥ t/7.
* `corollary2_of_theorem1`: Vinogradov's three primes theorem from Theorem 1 at C = 2 alone,
  CONDITIONAL ON Theorem 1, which the lab derives from Siegel-Walfisz. KNOWN mathematics.
AI-written Lean code, Claude, run 20261018T0002Z-3485, unit U-0911. Proof text adapted from
Vinogradov.lean of run 20261017T0603Z-10326. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HeathBrown1985.Vinogradov
import LeanLab.PNTPort.StrongPNT.Bridge

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Filter Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

theorem theta_window_ge_of_psi {c K ε : ℝ} (hε : 0 ≤ ε) (hKε : |K| * ε ≤ 1 / 28)
    (hK : ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (t : ℝ) (ht : 56 ≤ t) (hl1 : 1 ≤ Real.log (t / 7 + 1))
    (hE1 : Real.exp (-c * Real.sqrt (Real.log (t / 7 + 1))) ≤ ε)
    (hE2 : Real.exp (-c * Real.sqrt (Real.log (3 * t / 7 - 1))) ≤ ε)
    (hsq : 2 * Real.sqrt (3 * t / 7 - 1) * Real.log (3 * t / 7 - 1) ≤ t / 28) :
    t / 7 ≤ ∑ p ∈ (Ioc ⌊t / 7 + 1⌋₊ ⌊3 * t / 7 - 1⌋₊).filter Nat.Prime, Real.log p := by
  set y₁ := t / 7 + 1
  set y₂ := 3 * t / 7 - 1
  have hy12 : y₁ ≤ y₂ := by simp only [y₁, y₂]; linarith
  have hy1 : 2 ≤ y₁ := by simp only [y₁]; linarith
  have hl2 : 1 ≤ Real.log y₂ := hl1.trans (Real.log_le_log (by linarith) hy12)
  rw [← theta_sub_eq y₁ y₂ (Nat.floor_le_floor hy12)]
  have h1 := hK y₁ hy1
  have h2 := hK y₂ (by linarith)
  have h3 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show 1 ≤ y₂ by linarith)
  have h4 := Chebyshev.theta_le_psi y₁
  have e1 : K * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁)) ≤ y₁ / 28 := by
    calc K * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁))
        ≤ |K| * y₁ * ε := by
          have : 0 ≤ y₁ := by linarith
          have h0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log y₁)) := (Real.exp_pos _).le
          calc K * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁))
              ≤ |K| * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁)) := by
                apply mul_le_mul_of_nonneg_right _ h0
                exact mul_le_mul_of_nonneg_right (le_abs_self K) this
            _ ≤ |K| * y₁ * ε := mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ = (|K| * ε) * y₁ := by ring
      _ ≤ (1 / 28) * y₁ := mul_le_mul_of_nonneg_right hKε (by linarith)
      _ = y₁ / 28 := by ring
  have e2 : K * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂)) ≤ y₂ / 28 := by
    calc K * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂))
        ≤ |K| * y₂ * ε := by
          have : 0 ≤ y₂ := by linarith
          have h0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log y₂)) := (Real.exp_pos _).le
          calc K * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂))
              ≤ |K| * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂)) := by
                apply mul_le_mul_of_nonneg_right _ h0
                exact mul_le_mul_of_nonneg_right (le_abs_self K) this
            _ ≤ |K| * y₂ * ε := mul_le_mul_of_nonneg_left hE2 (by positivity)
      _ = (|K| * ε) * y₂ := by ring
      _ ≤ (1 / 28) * y₂ := mul_le_mul_of_nonneg_right hKε (by linarith)
      _ = y₂ / 28 := by ring
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  have a3 := (abs_le.mp h3).2
  simp only [y₁, y₂] at *
  linarith


/-! ### Corollary 2 from Siegel-Walfisz -/


/-- Unconditional: for all large `t`, the primes in `(t/7 + 1, 3t/7 - 1]` have
`Σ log p ≥ t/7`. From the ported prime number theorem with error term. -/
theorem primeWindow_eventually : ∀ᶠ t : ℝ in atTop,
    t / 7 ≤ ∑ p ∈ (Ioc ⌊t / 7 + 1⌋₊ ⌊3 * t / 7 - 1⌋₊).filter Nat.Prime, Real.log p := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  set ε : ℝ := 1 / (28 * (|K| + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hKε : |K| * ε ≤ 1 / 28 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg K]
  have G1 : ∀ᶠ y in atTop, Real.exp (-c * Real.sqrt (Real.log y)) ≤ ε := by
    have h : Tendsto (fun y => Real.exp (-(c * Real.sqrt (Real.log y)))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hc)
    filter_upwards [h.eventually (Iic_mem_nhds hε)] with y hy
    simpa [neg_mul] using hy
  have G2 : ∀ᶠ y in atTop, 2 * Real.sqrt y * Real.log y ≤ y / 14 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 28 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hy
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith
  have G3 : ∀ᶠ y in atTop, 1 ≤ Real.log y := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hf1 : Tendsto (fun t : ℝ => t / 7 + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_id.atTop_div_const (by norm_num))
  have hf2 : Tendsto (fun t : ℝ => 3 * t / 7 - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-1)
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num)).atTop_div_const
        (show (0 : ℝ) < 7 by norm_num))
    refine this.congr (fun t => ?_)
    simp only [id]; ring
  filter_upwards [eventually_ge_atTop (56 : ℝ), hf1.eventually G3, hf1.eventually G1,
    hf2.eventually G1, hf2.eventually G2] with t h1 h2 h3 h4 h5
  have : (3 * t / 7 - 1) / 14 ≤ t / 28 := by linarith
  exact theta_window_ge_of_psi hε.le hKε hK t h1 h2 h3 h4 (h5.trans this)

/-- Heath-Brown 1985, Corollary 2, from Theorem 1 at `C = 2` and the ported PNT. CONDITIONAL ON
Theorem 1. -/
theorem corollary2_of_theorem1 (hT1 : Theorem1) : Corollary2 := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  obtain ⟨K1, hK1⟩ := hT1 2 two_pos
  set ε : ℝ := 1 / (28 * (|K| + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hKε : |K| * ε ≤ 1 / 28 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg K]
  have G1 : ∀ᶠ y in atTop, Real.exp (-c * Real.sqrt (Real.log y)) ≤ ε := by
    have h : Tendsto (fun y => Real.exp (-(c * Real.sqrt (Real.log y)))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hc)
    filter_upwards [h.eventually (Iic_mem_nhds hε)] with y hy
    simpa [neg_mul] using hy
  have G2 : ∀ᶠ y in atTop, 2 * Real.sqrt y * Real.log y ≤ y / 14 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 28 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hy
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith
  have G3 : ∀ᶠ y in atTop, 1 ≤ Real.log y := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hf1 : Tendsto (fun t : ℝ => t / 7 + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_id.atTop_div_const (by norm_num))
  have hf2 : Tendsto (fun t : ℝ => 3 * t / 7 - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-1)
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num)).atTop_div_const
        (show (0 : ℝ) < 7 by norm_num))
    refine this.congr (fun t => ?_)
    simp only [id]; ring
  have hf3 : Tendsto (fun t : ℝ => 2 * t / 7) atTop atTop :=
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).atTop_div_const
      (show (0 : ℝ) < 7 by norm_num)
  have G4 : ∀ᶠ t in atTop, 2 * |K1| * Real.exp 6 + 1 ≤ Real.log (2 * t / 7) :=
    (Real.tendsto_log_atTop.comp hf3).eventually_ge_atTop _
  have hev : ∀ᶠ t : ℝ in atTop, 56 ≤ t ∧ 1 ≤ Real.log (t / 7 + 1) ∧
      Real.exp (-c * Real.sqrt (Real.log (t / 7 + 1))) ≤ ε ∧
      Real.exp (-c * Real.sqrt (Real.log (3 * t / 7 - 1))) ≤ ε ∧
      2 * Real.sqrt (3 * t / 7 - 1) * Real.log (3 * t / 7 - 1) ≤ t / 28 ∧
      2 * |K1| * Real.exp 6 + 1 ≤ Real.log (2 * t / 7) := by
    filter_upwards [eventually_ge_atTop (56 : ℝ), hf1.eventually G3, hf1.eventually G1,
      hf2.eventually G1, hf2.eventually G2, G4] with t h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, h4, ?_, h6⟩
    have : (3 * t / 7 - 1) / 14 ≤ t / 28 := by linarith
    exact h5.trans this
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨N0, fun n hodd hn => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN0 n hn
  exact ternary_of_bounds n hodd K1 h1 (theta_window_ge_of_psi hε.le hKε hK (n : ℝ) h1 h2 h3 h4 h5)
    (hK1 (2 * (n : ℝ) / 7) (by linarith)) (win_of_large K1 n h1 h6)


/-- The lab's cited P0003 statement from Theorem 1 at `C = 2` alone. CONDITIONAL ON Theorem 1. -/
theorem vinogradov_of_theorem1 (hT1 : Theorem1) : ∃ C : ℝ, Ternary.TernaryAbove C := by
  obtain ⟨N, hN⟩ := corollary2_of_theorem1 hT1
  exact ⟨N, fun n hodd hn => hN n hodd (by exact_mod_cast hn)⟩

/-- Consistency check: the old route factors through the new one. -/
theorem corollary2_of_siegelWalfisz' (hSW : SiegelWalfisz) : Corollary2 :=
  corollary2_of_theorem1 (theorem1_of_siegelWalfisz hSW)

end LeanLab.HeathBrown1985
