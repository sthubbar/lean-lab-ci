/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Scalar ranges for the remaining balancing guard, journal p. 1239.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Cutoff339

namespace LeanLab.BS2022GRH.Scalar339
open Real Finset Classical ChenThresholdGRH DecompC164c DecompC164a
noncomputable section

/-- The explicit prime error coefficient is below 0.17 at log Y at least 2750.
An elementary coefficient estimate used for the cutoff on journal p. 1239. -/
theorem qG_upper (Y : ℝ) (hY : 0 < Y) (hL : 2750 ≤ log Y) : qG Y ≤ 0.17 := by
  have he : (1e12 : ℝ) ≤ exp ((2750 : ℝ) / 4) := by
    have hpow : (1e12 : ℝ) ≤ exp 1 ^ (30 : ℕ) := by
      calc (1e12 : ℝ) ≤ (2.7 : ℝ) ^ (30 : ℕ) := by norm_num
        _ ≤ exp 1 ^ (30 : ℕ) := pow_le_pow_left₀ (by norm_num)
          (by linarith [exp_one_gt_d9]) _
    rw [← exp_nat_mul] at hpow
    norm_num only [Nat.cast_ofNat, mul_one] at hpow
    convert hpow.trans (show exp (30 : ℝ) ≤ exp ((2750 : ℝ) / 4) from exp_le_exp.mpr (by norm_num)) using 1 <;> norm_num
  have hlog : log (2750 : ℝ) ≤ 2750 :=
    (log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2750)).trans (by norm_num)
  have hfirst : firstGroup 2750 ≤ 1e-6 := by
    unfold firstGroup
    apply (div_le_iff₀ (exp_pos _)).mpr
    nlinarith
  have hsecond : secondGroup 2750 ≤ 1e-6 := by
    unfold secondGroup
    apply (div_le_iff₀ (by positivity : 0 < exp ((2750 : ℝ) / 4) * 2750)).mpr
    nlinarith
  have hthird : thirdGroup 2750 ≤ 1e-6 := by
    unfold thirdGroup
    have hneg : 0 ≤ 237.934 / (exp ((2750 : ℝ) / 2) * 2750) := by positivity
    have hpos : 939.260 / (exp ((2750 : ℝ) / 4) * 2750) ≤ (1e-6 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < exp ((2750 : ℝ) / 4) * 2750)).mpr
      nlinarith
    linarith
  have hmem : log Y ∈ Set.Ici 2 := by change 2 ≤ log Y; linarith
  have hf := (firstGroup_antitone (by norm_num : (2750 : ℝ) ∈ Set.Ici 2) hmem hL).trans hfirst
  have hs := (secondGroup_antitone (by norm_num : (2750 : ℝ) ∈ Set.Ici 2) hmem hL).trans hsecond
  have ht := (thirdGroup_antitone (by norm_num : (2750 : ℝ) ∈ Set.Ici 2) hmem hL).trans hthird
  have h1 : 12.683 / log Y ≤ (12.683 : ℝ) / 2750 := by gcongr
  have h2 : 254.980 / log Y ^ 2 ≤ (254.980 : ℝ) / 2750 ^ 2 := by gcongr
  have h3 : 2607.854 / log Y ^ 3 ≤ (2607.854 : ℝ) / 2750 ^ 3 := by gcongr
  have h4 : 11605.056 / log Y ^ 4 ≤ (11605.056 : ℝ) / 2750 ^ 4 := by gcongr
  rw [qG_groups Y hY]
  linarith

/-- The third condition of display 25 propagates from X2 to larger N.
This applies the existing logarithmic monotonicity theorem with exponent one over 48.
Journal pp. 1234 and 1239. -/
theorem third_condition_at (α A u X N : ℝ) (hA : 0 < A)
    (hc : Cond25 α A u X) (hX : 1 < X) (hXN : X ≤ N) :
    0.44 ≤ N ^ (1 / 48 : ℝ) / log N ^ (A + 4 / 3) := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by linarith
  have hLX : 0 < log X := log_pos hX
  have hLN : 0 < log N := log_pos (hX.trans_le hXN)
  have hstart : (A + 4 / 3) / (1 / 48 : ℝ) ≤ log X := by
    convert (le_max_right ((A + 1) / α) (48 * (A + 4 / 3))).trans hc.1 using 1 <;> ring
  have hm := Journal.mono_step (by norm_num : (0 : ℝ) < 1 / 48)
    (by linarith : 0 < A + 4 / 3) hstart (log_le_log hX0 hXN)
  have heq (t : ℝ) (ht : 0 < t) (hlt : 0 < log t) :
      t ^ (1 / 48 : ℝ) / log t ^ (A + 4 / 3) =
        exp ((1 / 48 : ℝ) * log t - (A + 4 / 3) * log (log t)) := by
    rw [rpow_def_of_pos ht, rpow_def_of_pos hlt, ← exp_sub]
    congr 1
    ring
  apply hc.2.2.1.trans
  rw [heq X hX0 hLX, heq N hN0 hLN]
  exact exp_le_exp.mpr hm

end
end LeanLab.BS2022GRH.Scalar339
#print axioms LeanLab.BS2022GRH.Scalar339.qG_upper
#print axioms LeanLab.BS2022GRH.Scalar339.third_condition_at
