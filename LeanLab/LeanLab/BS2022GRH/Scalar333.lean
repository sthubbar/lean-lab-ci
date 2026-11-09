/- AI wrote the Lean code for CODEX task333. Goldbach is open.
Scalar cases of Theorem 5, journal pp. 1228 and 1229. -/
import LeanLab.BS2022GRH.EndpointC169
import LeanLab.BS2022GRH.ModelC233

namespace LeanLab.BS2022GRH.Scalar333
open Real ChenThresholdGRH DecompC169a

/-- The printed correction is strictly positive above log X equal to two.
Journal p. 1230 display 20 and the pG definition on p. 1229. -/
theorem cGJ_pos (X : ℝ) (hX : 0 < X) (hL : 2 ≤ log X) : 0 < cGJ X := by
  have hq := EndpointC169.qG_nonneg X hX hL
  have hp : 0 < pGJ X := by unfold pGJ; nlinarith
  have hll : 0 ≤ log (log X) := log_nonneg (by linarith)
  unfold cGJ
  exact add_pos_of_pos_of_nonneg hp (by positivity)

/-- A nonpositive main coefficient makes the exact bracket negative.
This includes the zero coefficient case. Journal p. 1228 Theorem 5. -/
theorem bracket_neg_of_coefficient_nonpos (α A ε C₂ X N : ℝ)
    (hX : 0 < X) (hLX : 3200 ≤ log X) (hN : 1 < N)
    (hc : lowerCoefficient α ε C₂ ≤ 0) : B5J α A ε C₂ X N < 0 := by
  have hd := EndpointC169.density_factor_pos X hX hLX
  have hg := cGJ_pos X hX (by linarith)
  have hi : 0 < invTw := by
    unfold invTw
    exact inv_pos.mpr (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos)
  have hmain : (1 - 0.62 * log X / X ^ (1 / 16 : ℝ)) *
      lowerCoefficient α ε C₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le hc
  have hLN : 0 < log N := log_pos hN
  have herr : 0 < 1 / 8 * (1 - 0.62 * log X / X ^ (1 / 16 : ℝ))⁻¹ *
      invTw * cGJ X / log N ^ (A - 2) := by positivity
  change (1 - 0.62 * log X / X ^ (1 / 16 : ℝ)) * lowerCoefficient α ε C₂ - _ < 0
  exact sub_neg.mpr (hmain.trans_lt herr)

/-- The nonpositive coefficient branch needs only the scalar endpoint guards.
Journal pp. 1228 and 1229. No sieve or GRH input is used. -/
theorem target_of_coefficient_nonpos (α A ε C₂ X : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X) (hn : X ≤ (n : ℝ)) (hLX : 3200 ≤ log X)
    (hc : lowerCoefficient α ε C₂ ≤ 0) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X n < (U7153.SA n : ℝ) := by
  have hn1 : (1 : ℝ) < n := by linarith
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hlog : 0 < log (n : ℝ) := log_pos hn1
  have hs : 0 < 8 * (UNfull n * n / log n ^ 2) := by positivity
  have hb := bracket_neg_of_coefficient_nonpos α A ε C₂ X n (by linarith) hLX hn1 hc
  exact (mul_neg_of_pos_of_neg hs hb).trans_le (Nat.cast_nonneg _)

end LeanLab.BS2022GRH.Scalar333

#print axioms LeanLab.BS2022GRH.Scalar333.cGJ_pos
#print axioms LeanLab.BS2022GRH.Scalar333.bracket_neg_of_coefficient_nonpos
#print axioms LeanLab.BS2022GRH.Scalar333.target_of_coefficient_nonpos
