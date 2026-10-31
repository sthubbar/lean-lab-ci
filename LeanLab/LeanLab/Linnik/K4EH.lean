/-
U-1131, T2 FRONTIER, Linnik-Goldbach K: how much Elliott-Halberstam does K = 4 need
inside Li-Liu's criterion (58). Run 20261020T0103Z-16649.

Plain math. Li-Liu arXiv 2610.15784 v1, criterion (58), in the degree d form the lab uses in
KLadder.lean, K = 2d, F(z) = z^d + ... + c z, v_i the coefficient of z^i:
  vᵀAv + v₁² (p/2) log 2 + H((C₁-2)/2 C₀R₀ + ((1-p)/2) log 2) < F(1)²,  H = max_{D_λ} |F(z)/z|².
C₁ is the Goldbach pair upper sieve constant, normalised so that Hardy-Littlewood is 2.
A Selberg upper sieve with level of distribution θ for primes in progressions gives C₁ = 4/θ:
θ = 1/2, Bombieri-Vinogradov, gives 8; θ = 1, Elliott-Halberstam, gives 4. JT arXiv 2605.17825
Theorem 3 already states: EH implies K = 4. This file checks the same in Li-Liu's setup and
measures the room:

- `region_z_56`, `region_z_2532`: |z|² < 0.6232 on D_{5/6} and < 0.527 on D_{25/32}.
- `region_c_56`: |z - 1/12|² < 0.4972 on D_{5/6}.
- `k4_uncond_z2`: F = z², Section 6 arcs p = 11/25, λ = 5/6, the same exceptional set step as
  Li-Liu's own K = 6: the criterion holds for every C₁ ≤ 4.06, from the cited A₂₂ < 0.0555 of
  (22) and C₀R₀ < 1.279. `k4_uncond_EH` is C₁ = 4.
- `k4_uncond_c`: F = z² - z/12: holds for every C₁ ≤ 4.1, with vᵀA_*v exact, `vAv_c_exact`, and
  the (23) tails, `vAv_c_tail`.
- `k4_grh_z2`: F = z², GRH arcs p = 1/2, λ = 25/32: holds for every C₁ ≤ 4.5.
- `level_uncond`, `level_grh`: 4/θ ≤ 4.1 once θ ≥ 0.9757, and 4/θ ≤ 4.5 once θ ≥ 0.89.

So, in this MODEL, K = 4 needs a Goldbach pair upper sieve at level about 0.976 with the
unconditional arcs, or about 0.89 with GRH arcs; full EH, θ = 1, is not needed. Python,
numerics/k4_eh_U1131.py: with c optimised the thresholds are C₁ < 4.137 unconditional and
C₁ < 4.722 under GRH, levels 0.967 and 0.847; JT's Table 1 needs 4.069 and 4.608.
CONDITIONAL ON: the cited C₀R₀ < 1.279 and A₂₂ < 0.0555, the analytic steps of Li-Liu that
turn (58) into K = 2d, and the MODEL that (58) holds for degree 2 with the paper's constants.
KNOWN in substance, JT Theorem 3. AI-written Lean code, Claude, 2026-10-20. Goldbach is open.
-/
import Mathlib
import LeanLab.Linnik.LiLiu2026

namespace LeanLab.Linnik.K4EH

open LeanLab.Linnik.LiLiu

/-- |z|² < 0.6232 on D_{5/6}; the maximum is r/(1 + r - β) ≈ 0.6208 at z = β. -/
theorem region_z_56 (z : ℂ) (hz : z ∈ Dl (5 / 6)) : Complex.normSq z < 0.6232 := by
  obtain ⟨hx2, hD, hx⟩ := mem_Dl_poly beta56_le (by norm_num) (by unfold rl; positivity) hz
  have hr : rl (5 / 6) = 25 / 72 := by unfold rl; norm_num
  rw [hr] at hD
  have hu : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  nlinarith

/-- |z|² < 0.527 on D_{25/32}. -/
theorem region_z_2532 (z : ℂ) (hz : z ∈ Dl (25 / 32)) : Complex.normSq z < 0.527 := by
  obtain ⟨hx2, hD, hx⟩ := mem_Dl_poly beta2532_le (by norm_num) (by unfold rl; positivity) hz
  have hr : rl (25 / 32) = 625 / 2048 := by unfold rl; norm_num
  rw [hr] at hD
  have hu : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  nlinarith

lemma normSq_sub12 (z : ℂ) : Complex.normSq (z - 1 / 12) = Complex.normSq z - z.re / 6 + 1 / 144 := by
  simp [Complex.normSq_apply]; ring

/-- |z - 1/12|² < 0.4972 on D_{5/6}; numerically the maximum is 0.4964 at z = β. -/
theorem region_c_56 (z : ℂ) (hz : z ∈ Dl (5 / 6)) : Complex.normSq (z - 1 / 12) < 0.4972 := by
  obtain ⟨hx2, hD, hx⟩ := mem_Dl_poly beta56_le (by norm_num) (by unfold rl; positivity) hz
  have hr : rl (5 / 6) = 25 / 72 := by unfold rl; norm_num
  rw [hr] at hD
  rw [normSq_sub12]
  set x := z.re; set u := Complex.normSq z
  have hu : 0 ≤ u := Complex.normSq_nonneg z
  have hpos : 0 < 1 + 25 / 72 - x := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hx) hu, sq_nonneg (x - 79 / 100), sq_nonneg (x + 1 / 2),
    mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hx)]

/-- K = 4 with F = z², v = (0, 1), F(1) = 1, Section 6 arcs p = 11/25: criterion (58) holds for
every C₁ in [2, 4.06], CONDITIONAL ON the cited A₂₂ < 0.0555 and C₀R₀ < 1.279. -/
theorem k4_uncond_z2 {A22 CR C1 H : ℝ} (hA : A22 < 0.0555) (hCR0 : 0 ≤ CR) (hCR : CR < 1.279)
    (hC0 : 2 ≤ C1) (hC1 : C1 ≤ 4.06) (hH0 : 0 ≤ H) (hH : H < 0.6232) :
    A22 + 0 ^ 2 * (11 / 25 / 2 * Real.log 2)
      + H * ((C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2) < (1 : ℝ) ^ 2 := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : (C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2 < 1.5115 := by
    have : (C1 - 2) / 2 * CR ≤ 1.03 * 1.279 := by
      apply mul_le_mul (by linarith) hCR.le hCR0 (by norm_num)
    nlinarith
  have hX0 : 0 ≤ (C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2 := by
    have : 0 ≤ (C1 - 2) / 2 * CR := mul_nonneg (by linarith) hCR0
    nlinarith
  have : H * ((C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2) ≤ 0.6232 * 1.5115 :=
    mul_le_mul hH.le hX.le hX0 (by norm_num)
  norm_num at this ⊢; linarith

/-- The EH value C₁ = 4: K = 4 in Li-Liu's setup, F = z², unconditional arcs. -/
theorem k4_uncond_EH {A22 CR H : ℝ} (hA : A22 < 0.0555) (hCR0 : 0 ≤ CR) (hCR : CR < 1.279)
    (hH0 : 0 ≤ H) (hH : H < 0.6232) :
    A22 + 0 ^ 2 * (11 / 25 / 2 * Real.log 2)
      + H * ((4 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2) < (1 : ℝ) ^ 2 :=
  k4_uncond_z2 hA hCR0 hCR (by norm_num) (by norm_num) hH0 hH

/-- v = (-1/12, 1): vᵀ A_* v exactly, from the five printed Gram matrices. -/
def vc : Fin 3 → ℚ := ![-1/12, 1, 0]

theorem vAv_c_exact : qf Astar vc = 12155897 / 194400000 := by
  simp [qf, Astar, A3, A5, A7, A15, A31, vc, Fin.sum_univ_three]; norm_num

/-- With the (23) tails T₁₁ < 0.254², T₂₂ < 0.077², as in (59) to (60): vᵀAv < 0.0723. -/
theorem vAv_c_tail : (12155897 / 194400000 : ℚ) + (0.254 / 12 + 0.077) ^ 2 < 0.0723 := by norm_num

/-- K = 4 with F = z² - z/12, F(1) = 11/12, unconditional arcs: (58) holds for every C₁ in
[2, 4.1], CONDITIONAL ON C₀R₀ < 1.279 and the tail form of vᵀAv. -/
theorem k4_uncond_c {VA CR C1 H : ℝ} (hA : VA < 0.0723) (hCR0 : 0 ≤ CR) (hCR : CR < 1.279)
    (hC0 : 2 ≤ C1) (hC1 : C1 ≤ 4.1) (hH0 : 0 ≤ H) (hH : H < 0.4972) :
    VA + (-1 / 12 : ℝ) ^ 2 * (11 / 25 / 2 * Real.log 2)
      + H * ((C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2) < (11 / 12 : ℝ) ^ 2 := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : (C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2 < 1.53704 := by
    have : (C1 - 2) / 2 * CR ≤ 1.05 * 1.279 := by
      apply mul_le_mul (by linarith) hCR.le hCR0 (by norm_num)
    nlinarith
  have hX0 : 0 ≤ (C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2 := by
    have : 0 ≤ (C1 - 2) / 2 * CR := mul_nonneg (by linarith) hCR0
    nlinarith
  have : H * ((C1 - 2) / 2 * CR + (1 - 11 / 25) / 2 * Real.log 2) ≤ 0.4972 * 1.53704 :=
    mul_le_mul hH.le hX.le hX0 (by norm_num)
  norm_num at this ⊢; nlinarith

/-- K = 4 with F = z², GRH arcs p = 1/2, λ = 25/32 as in Li-Liu Section 7: (58) holds for every
C₁ in [2, 4.5], CONDITIONAL ON A₂₂ < 0.0555, C₀R₀ < 1.279 and GRH through the arcs. -/
theorem k4_grh_z2 {A22 CR C1 H : ℝ} (hA : A22 < 0.0555) (hCR0 : 0 ≤ CR) (hCR : CR < 1.279)
    (hC0 : 2 ≤ C1) (hC1 : C1 ≤ 4.5) (hH0 : 0 ≤ H) (hH : H < 0.527) :
    A22 + 0 ^ 2 * (Real.log 2 / 4) + H * ((C1 - 2) / 2 * CR + Real.log 2 / 4) < (1 : ℝ) ^ 2 := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : (C1 - 2) / 2 * CR + Real.log 2 / 4 < 1.7721 := by
    have : (C1 - 2) / 2 * CR ≤ 1.25 * 1.279 := by
      apply mul_le_mul (by linarith) hCR.le hCR0 (by norm_num)
    nlinarith
  have hX0 : 0 ≤ (C1 - 2) / 2 * CR + Real.log 2 / 4 := by
    have : 0 ≤ (C1 - 2) / 2 * CR := mul_nonneg (by linarith) hCR0
    nlinarith
  have : H * ((C1 - 2) / 2 * CR + Real.log 2 / 4) ≤ 0.527 * 1.7721 :=
    mul_le_mul hH.le hX.le hX0 (by norm_num)
  norm_num at this ⊢; linarith

/-- The Selberg level conversion C₁ = 4/θ, the MODEL input: θ ≥ 0.9757 gives C₁ ≤ 4.1. -/
theorem level_uncond {θ : ℝ} (h : 0.9757 ≤ θ) : 4 / θ ≤ 4.1 := by
  rw [div_le_iff₀ (by linarith)]; linarith

/-- θ ≥ 0.89 gives C₁ = 4/θ ≤ 4.5. -/
theorem level_grh {θ : ℝ} (h : 0.89 ≤ θ) : 4 / θ ≤ 4.5 := by
  rw [div_le_iff₀ (by linarith)]; linarith

/-- Vacuity: β-like points are in the regions and the hypotheses hold at C₀R₀ = 1.2784. -/
theorem vacuity : (0 : ℂ) ∈ Dl (5 / 6) ∧ ∃ A22 CR H : ℝ, A22 < 0.0555 ∧ 0 ≤ CR ∧ CR < 1.279 ∧
    0 ≤ H ∧ H < 0.527 :=
  ⟨zero_mem_Dl.1, 0.0555 - 0.0001, 1.2784, 0.5266, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

end LeanLab.Linnik.K4EH
