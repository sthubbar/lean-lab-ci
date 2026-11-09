/- AI wrote the Lean code for CODEX task333. Goldbach is open.
Strictness from the exact lab error normalization in Theorem 5.
Journal pp. 1228 and 1229. This is a derived scalar comparison.
The factor two is the existing UNfull convention, not a new paper claim. -/
import LeanLab.BS2022GRH.Scalar333
import LeanLab.BS2022GRH.DecompC169a

namespace LeanLab.BS2022GRH.Slack333
open Real ChenThresholdGRH DecompC169a

/-- Keep the full factor two in the exact lab error normalization.
The main mass estimates are explicit premises. Journal pp. 1228 and 1229.
CONDITIONAL ON the two supplied estimates. -/
theorem endpoint_comparison_with_slack (α A ε C₂ X₂ : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X₂) (hn : X₂ ≤ (n : ℝ)) (hLX : 3200 ≤ log X₂)
    (hcoef : 0 ≤ lowerCoefficient α ε C₂)
    (hdensity : 8 * UNfull n / log n *
      (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤ density n)
    (hcard : (n : ℝ) / log n ≤ (U7153.Aset n).card) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n ≤
      sieveMain n α ε C₂ - 2 * (cGJ X₂ * n / log n ^ A) := by
  have hX0 : 0 < X₂ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hLX0 : 0 < log X₂ := by linarith
  have hLN : 0 < log (n : ℝ) := hLX0.trans_le (log_le_log hX0 hn)
  have hLNne : log (n : ℝ) ≠ 0 := hLN.ne'
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  let δ := 1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)
  let scale := 8 * (UNfull n * n / log n ^ 2)
  have hδ : 0 < δ := EndpointC169.density_factor_pos X₂ hX0 hLX
  have hδle : δ ≤ 1 := by
    have hnn : 0 ≤ 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ) := by positivity
    dsimp [δ]
    linarith
  have hmono := lower_density_factor_mono X₂ n hX0 (by linarith) hn
  have hden : 8 * UNfull n / log n * δ ≤ density n :=
    (mul_le_mul_of_nonneg_left hmono (by positivity)).trans hdensity
  have hd0 : 0 ≤ density n := (show 0 ≤ 8 * UNfull n / log n * δ by positivity).trans hden
  have hmass := mul_le_mul hden hcard (div_nonneg hn0.le hLN.le) hd0
  have hnorm : (8 * UNfull n / log n * δ) * ((n : ℝ) / log n) = scale * δ := by
    dsimp [scale]
    field_simp
    <;> ring
  rw [hnorm] at hmass
  have hmain : scale * (δ * lowerCoefficient α ε C₂) ≤ sieveMain n α ε C₂ := by
    have h := mul_le_mul_of_nonneg_left hmass hcoef
    unfold sieveMain
    nlinarith
  have hTw : exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC ≠ 0 :=
    (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos).ne'
  have hUinv : UNfull n * invTw = 2 * UN n := by
    rw [UNfull_eq]
    unfold invTw
    field_simp [LeanLab.ChenExplicit.twinC_pos.ne']
    <;> ring
  have hUinv2 : 2 ≤ UNfull n * invTw := by
    rw [hUinv]
    linarith [one_le_UN n]
  have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδle
  have hfactor : 2 ≤ UNfull n * invTw * δ⁻¹ := by nlinarith
  have hcG : 0 ≤ cGJ X₂ := EndpointC169.cGJ_nonneg X₂ hX0 (by linarith)
  have hPA : 0 < log (n : ℝ) ^ A := rpow_pos_of_pos hLN _
  have hPA2 : 0 < log (n : ℝ) ^ (A - 2) := rpow_pos_of_pos hLN _
  have hpow : log (n : ℝ) ^ A = log (n : ℝ) ^ (A - 2) * log n ^ 2 := by
    rw [← rpow_natCast, ← rpow_add hLN]
    congr 1
    norm_num
  have herrEq : scale * (1 / 8 * δ⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2)) =
      (UNfull n * invTw * δ⁻¹) * (cGJ X₂ * n / log (n : ℝ) ^ A) := by
    rw [hpow]
    dsimp [scale]
    field_simp
    <;> ring
  have herr : 2 * (cGJ X₂ * n / log (n : ℝ) ^ A) ≤
      scale * (1 / 8 * δ⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2)) := by
    rw [herrEq]
    exact mul_le_mul_of_nonneg_right hfactor (by positivity)
  change scale * (δ * lowerCoefficient α ε C₂ -
    1 / 8 * δ⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2)) ≤ _
  rw [mul_sub]
  linarith

/-- A non-strict lower sieve estimate suffices for the strict target.
The correction term is positive, so the second error budget gives strictness.
Journal p. 1229 and display 20 on p. 1230.
CONDITIONAL ON the supplied sieve, residue, density and cardinality estimates. -/
theorem target_of_weak_sieve (α A u ε C₂ X : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X) (hn : X ≤ (n : ℝ)) (hLX : 3200 ≤ log X)
    (hc : 0 ≤ lowerCoefficient α ε C₂)
    (hS : sieveMain n α ε C₂ - remainder n α u ≤ (U7153.SA n : ℝ))
    (hR : remainder n α u ≤ cGJ X * n / log n ^ A)
    (hV : 8 * UNfull n / log n *
      (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤ density n)
    (hCard : (n : ℝ) / log n ≤ (U7153.Aset n).card) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X n < (U7153.SA n : ℝ) := by
  have hM := endpoint_comparison_with_slack α A ε C₂ X n hX hn hLX hc hV hCard
  have hX0 : 0 < X := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < log (n : ℝ) := log_pos (by linarith : (1 : ℝ) < n)
  have hE : 0 < cGJ X * n / log (n : ℝ) ^ A := by
    have hg := Scalar333.cGJ_pos X hX0 (by linarith)
    positivity
  linarith

end LeanLab.BS2022GRH.Slack333

#print axioms LeanLab.BS2022GRH.Slack333.endpoint_comparison_with_slack
#print axioms LeanLab.BS2022GRH.Slack333.target_of_weak_sieve
