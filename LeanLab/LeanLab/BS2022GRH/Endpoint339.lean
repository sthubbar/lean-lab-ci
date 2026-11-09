/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Separate the elementary endpoint terms of display 33 on p. 1241.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp339a

namespace LeanLab.BS2022GRH.Endpoint339
open Real ChenThresholdGRH DecompC164c
noncomputable section

/-- The normalized coprimality error decreases above log X equal to forty.
Journal p. 1241 display 33. The parameter A cancels from this term. -/
theorem correction_antitone (X N : ℝ) (hX : 1 < X) (hLX : 40 ≤ log X) (hXN : X ≤ N) :
    log N ^ (5 : ℕ) / N ^ (1 / 8 : ℝ) ≤ log X ^ (5 : ℕ) / X ^ (1 / 8 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := hX0.trans_le hXN
  have hlN : 0 < log N := log_pos (hX.trans_le hXN)
  have hXexp : exp (1 / (1 / 40 : ℝ)) ≤ X := by
    apply (le_log_iff_exp_le hX0).mp
    norm_num
    exact hLX
  have h := log_div_self_rpow_antitoneOn (a := 1 / 40) (by norm_num)
    (show X ∈ Set.Ici (exp ((1 / 40 : ℝ)⁻¹)) by simpa [one_div] using hXexp)
    (show N ∈ Set.Ici (exp ((1 / 40 : ℝ)⁻¹)) by simpa [one_div] using hXexp.trans hXN) hXN
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ log N / N ^ (1 / 40 : ℝ)) h 5
  have hpow (v : ℝ) (hv : 0 ≤ v) : (v ^ (1 / 40 : ℝ)) ^ (5 : ℕ) = v ^ (1 / 8 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hv]
    norm_num
  rw [div_pow, div_pow, hpow N hN0.le, hpow X hX0.le] at hp
  exact hp

/-- Exact separation of the endpoint bracket into its majorant and correction terms.
Journal p. 1241 display 33. No endpoint inequality is asserted here. -/
theorem error_normalization (N A ε : ℝ) (hN : 1 < N) (hε : 0 < ε) :
    errorBracket A N ε = invTw * (1 + ε) / log (1 + ε) *
      (0.053 * (1 + ε) ^ (-(1 / 2) : ℝ) *
        (mbarJ N A (N ^ (1 / 8 : ℝ)) / log N ^ (A - 4)) +
        0.08 * (log N ^ (5 : ℕ) / N ^ (1 / 8 : ℝ))) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  have hpow : log N ^ (A + 1) = log N ^ (A - 4) * log N ^ (5 : ℕ) := by
    rw [← rpow_natCast, ← rpow_add hL]
    congr 1
    ring
  unfold errorBracket
  rw [hpow, rpow_neg hN0.le]
  field_simp
  <;> ring

/-- Only the weighted majorant comparison remains after correction monotonicity.
Journal p. 1241 after display 33. The premise is explicit and is not supplied here. -/
theorem error_transfer (X N A ε : ℝ) (hX : 1 < X) (hLX : 40 ≤ log X)
    (hXN : X ≤ N) (hε : 0 < ε)
    (hmain : mbarJ N A (N ^ (1 / 8 : ℝ)) / log N ^ (A - 4) ≤
      mbarJ X A (X ^ (1 / 8 : ℝ)) / log X ^ (A - 4)) :
    errorBracket A N ε ≤ errorBracket A X ε := by
  have hN : 1 < N := hX.trans_le hXN
  rw [error_normalization N A ε hN hε, error_normalization X A ε hX hε]
  have hinv : 0 < invTw := by
    unfold invTw
    exact inv_pos.mpr (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos)
  have hb : 0 < 1 + ε := by linarith
  have hlb : 0 < log (1 + ε) := log_pos (by linarith)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hmain (by positivity))
    (mul_le_mul_of_nonneg_left (correction_antitone X N hX hLX hXN) (by norm_num))

/-- The scalar slice budget is nonnegative without a GRH or Lemma 8 premise.
Journal p. 1240 display 32. This is a direct positivity check of the printed formula. -/
theorem mainScale_nonneg (n : ℕ) (A ε : ℝ) (hN : exp (exp 10) ≤ (n : ℝ))
    (hD : 1e8 ≤ √(n : ℝ) / log n ^ (A + 1)) (hε : 0 < ε) :
    0 ≤ Decomp339a.mainScale n A ε := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hN
  have hn1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hN
  have hL := Lemma11C164.log_lower n hN
  have hz : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
  have hlz : 2750 ≤ log (U7153.zz n) := by
    rw [U7153.zz, log_rpow hn0]
    linarith
  have hm := MbarCompare339.mbar_nonneg n A (U7153.zz n) hn1 hz hlz hD
  unfold Decomp339a.mainScale
  positivity

end
end LeanLab.BS2022GRH.Endpoint339
#print axioms LeanLab.BS2022GRH.Endpoint339.correction_antitone
#print axioms LeanLab.BS2022GRH.Endpoint339.error_normalization
#print axioms LeanLab.BS2022GRH.Endpoint339.error_transfer
#print axioms LeanLab.BS2022GRH.Endpoint339.mainScale_nonneg
