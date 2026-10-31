/-
P0096 Heath-Brown 1985, Corollary 3 from Theorem 1 alone. Corollary3.lean uses 1.1 at k = 1 for
the primes in (t + 1, 3t/2 - 1]; that is the prime number theorem with error term, now PROVED in
the lab from the PrimeNumberTheoremAnd port, LeanLab.PNTPort.psi_explicit_strong.
* `theta_window_ge'_of_psi`: the window step on the k = 1 hypothesis only, same proof.
* `primeWindow3_eventually`: unconditional, for all large t, the primes in (t + 1, 3t/2 - 1]
  have Σ log p ≥ t/4.
* `corollary3_of_theorem1`: CONDITIONAL ON Theorem 1. KNOWN mathematics.
AI-written Lean code, Claude, run 20261018T0002Z-3485, unit U-0912. Proof text adapted from
Corollary3.lean of run 20261017T0903Z-2557.
-/
import Mathlib
import LeanLab.HeathBrown1985.Corollary3
import LeanLab.PNTPort.StrongPNT.Bridge

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Filter Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

theorem theta_window_ge'_of_psi {c K ε : ℝ} (hε : 0 ≤ ε) (hKε : |K| * ε ≤ 1 / 28)
    (hK : ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (t : ℝ) (ht : 16 ≤ t) (hl1 : 1 ≤ Real.log (t + 1))
    (hE1 : Real.exp (-c * Real.sqrt (Real.log (t + 1))) ≤ ε)
    (hE2 : Real.exp (-c * Real.sqrt (Real.log (3 * t / 2 - 1))) ≤ ε)
    (hsq : 2 * Real.sqrt (3 * t / 2 - 1) * Real.log (3 * t / 2 - 1) ≤ t / 28) :
    t / 4 ≤ ∑ p ∈ (Ioc ⌊t + 1⌋₊ ⌊3 * t / 2 - 1⌋₊).filter Nat.Prime, Real.log p := by
  set y₁ := t + 1
  set y₂ := 3 * t / 2 - 1
  have hy12 : y₁ ≤ y₂ := by simp only [y₁, y₂]; linarith
  have hy1 : 2 ≤ y₁ := by simp only [y₁]; linarith
  have hl2 : 1 ≤ Real.log y₂ := hl1.trans (Real.log_le_log (by linarith) hy12)
  rw [← theta_sub_eq y₁ y₂ (Nat.floor_le_floor hy12)]
  have h1 := hK y₁ hy1
  have h2 := hK y₂ (by linarith)
  have h3 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show 1 ≤ y₂ by linarith)
  have h4 := Chebyshev.theta_le_psi y₁
  have e : ∀ y : ℝ, 0 ≤ y → Real.exp (-c * Real.sqrt (Real.log y)) ≤ ε →
      K * y * Real.exp (-c * Real.sqrt (Real.log y)) ≤ y / 28 := by
    intro y hy hE
    have h0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log y)) := (Real.exp_pos _).le
    calc K * y * Real.exp (-c * Real.sqrt (Real.log y))
        ≤ |K| * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
          apply mul_le_mul_of_nonneg_right _ h0
          exact mul_le_mul_of_nonneg_right (le_abs_self K) hy
      _ ≤ |K| * y * ε := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (|K| * ε) * y := by ring
      _ ≤ (1 / 28) * y := mul_le_mul_of_nonneg_right hKε hy
      _ = y / 28 := by ring
  have e1 := e y₁ (by linarith) hE1
  have e2 := e y₂ (by linarith) hE2
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  have a3 := (abs_le.mp h3).2
  simp only [y₁, y₂] at *
  linarith

/-- Unconditional: for all large `t`, the primes in `(t + 1, 3t/2 - 1]` have `Σ log p ≥ t/4`.
From the ported prime number theorem with error term. -/
theorem primeWindow3_eventually : ∀ᶠ t : ℝ in atTop,
    t / 4 ≤ ∑ p ∈ (Ioc ⌊t + 1⌋₊ ⌊3 * t / 2 - 1⌋₊).filter Nat.Prime, Real.log p := by
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
  have G2 : ∀ᶠ y in atTop, 2 * Real.sqrt y * Real.log y ≤ y / 42 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 84 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hy
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith
  have G3 : ∀ᶠ y in atTop, 1 ≤ Real.log y := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hf1 : Tendsto (fun t : ℝ => t + 1) atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_id
  have hf2 : Tendsto (fun t : ℝ => 3 * t / 2 - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-1)
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num)).atTop_div_const
        (show (0 : ℝ) < 2 by norm_num))
    refine this.congr (fun t => ?_)
    simp only [id]; ring
  filter_upwards [eventually_ge_atTop (16 : ℝ), hf1.eventually G3, hf1.eventually G1,
    hf2.eventually G1, hf2.eventually G2] with t h1 h2 h3 h4 h5
  have : (3 * t / 2 - 1) / 42 ≤ t / 28 := by linarith
  exact theta_window_ge'_of_psi hε.le hKε hK t h1 h2 h3 h4 (h5.trans this)

/-- Heath-Brown 1985, Corollary 3, from Theorem 1 at `C = 2` and the ported PNT. CONDITIONAL ON
Theorem 1. -/
theorem corollary3_of_theorem1 (hT1 : Theorem1) : Corollary3 := by
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
  have G2 : ∀ᶠ y in atTop, 2 * Real.sqrt y * Real.log y ≤ y / 42 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 84 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hy
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith
  have G3 : ∀ᶠ y in atTop, 1 ≤ Real.log y := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hf1 : Tendsto (fun t : ℝ => t + 1) atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_id
  have hf2 : Tendsto (fun t : ℝ => 3 * t / 2 - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-1)
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num)).atTop_div_const
        (show (0 : ℝ) < 2 by norm_num))
    refine this.congr (fun t => ?_)
    simp only [id]; ring
  have G4 : ∀ᶠ t in atTop, 4 * |K1| * Real.exp 6 + 1 ≤ Real.log t :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hev : ∀ᶠ t : ℝ in atTop, 16 ≤ t ∧ 1 ≤ Real.log (t + 1) ∧
      Real.exp (-c * Real.sqrt (Real.log (t + 1))) ≤ ε ∧
      Real.exp (-c * Real.sqrt (Real.log (3 * t / 2 - 1))) ≤ ε ∧
      2 * Real.sqrt (3 * t / 2 - 1) * Real.log (3 * t / 2 - 1) ≤ t / 28 ∧
      4 * |K1| * Real.exp 6 + 1 ≤ Real.log t := by
    filter_upwards [eventually_ge_atTop (16 : ℝ), hf1.eventually G3, hf1.eventually G1,
      hf2.eventually G1, hf2.eventually G2, G4] with t h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, h4, ?_, h6⟩
    have : (3 * t / 2 - 1) / 42 ≤ t / 28 := by linarith
    exact h5.trans this
  obtain ⟨t0, ht0⟩ := eventually_atTop.mp hev
  -- the middle terms are unbounded
  have hunb : ∀ B : ℕ, ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧ (p + 2 * d).Prime ∧ 0 < d ∧
      B < p + d := by
    intro B
    set t := max t0 (B : ℝ) + 16
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht0 t (by simp only [t]; linarith [le_max_left t0 (B : ℝ)])
    obtain ⟨p, d, hp, hpd, hp2d, hd, hlt⟩ := ap3_of_bounds t K1 h1
      (theta_window_ge'_of_psi hε.le hKε hK t h1 h2 h3 h4 h5) (hK1 t (by linarith))
      (win3_of_large K1 t h1 h6)
    refine ⟨p, d, hp, hpd, hp2d, hd, ?_⟩
    have : (B : ℝ) < (p + d : ℕ) := by
      have : (B : ℝ) ≤ t := by simp only [t]; linarith [le_max_right t0 (B : ℝ)]
      linarith
    exact_mod_cast this
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image (fun s : ℕ × ℕ => s.1 + s.2)).bddAbove
  obtain ⟨p, d, hp, hpd, hp2d, hd, hlt⟩ := hunb B
  have : p + d ∈ (fun s : ℕ × ℕ => s.1 + s.2) ''
      {t : ℕ × ℕ | t.1.Prime ∧ (t.1 + t.2).Prime ∧ (t.1 + 2 * t.2).Prime ∧ 0 < t.2} :=
    ⟨(p, d), ⟨hp, hpd, hp2d, hd⟩, rfl⟩
  have := hB this
  omega

/-- Consistency check: the old route factors through the new one. -/
theorem corollary3_of_siegelWalfisz' (hSW : SiegelWalfisz) : Corollary3 :=
  corollary3_of_theorem1 (theorem1_of_siegelWalfisz hSW)

end LeanLab.HeathBrown1985
