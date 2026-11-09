/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Scale normalization in journal display 31 on p. 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.MbarCompare339

namespace LeanLab.BS2022GRH.Scale339
open Real ChenThresholdGRH
noncomputable section

/-- The rectangle scale contributes the factor one quarter in display 31.
Journal p. 1240. No estimate on the bilinear coefficient is assumed. -/
theorem scale_bound (N W Y A ε : ℝ) (hN : 1 < N) (hW : 0 < W)
    (hY : 0 ≤ Y) (hε : 0 < ε) (hYW : Y ≤ (1 + ε) * W)
    (hA : 0 ≤ A) (hL1 : 1 ≤ log N) (hD : 1 ≤ √N / log N ^ (A + 1)) :
    Decomp148a.scale (N / W) Y (√N / log N ^ (A + 1)) ≤
      N * √(1 + ε) / (4 * log N ^ (A - 1)) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  have hD0 : 0 < √N / log N ^ (A + 1) := by positivity
  have hlD : 0 ≤ log (√N / log N ^ (A + 1)) := log_nonneg hD
  have hlogL : 0 ≤ log (log N) := log_nonneg hL1
  have hlDu : log (√N / log N ^ (A + 1)) ≤ log N / 2 := by
    rw [log_div (sqrt_pos.mpr hN0).ne' (rpow_pos_of_pos hL _).ne',
      log_sqrt hN0.le, log_rpow hL]
    nlinarith
  have hs : √((N / W) * Y) ≤ √N * √(1 + ε) := by
    have hc : (N / W) * Y ≤ N * (1 + ε) := by
      calc _ ≤ (N / W) * ((1 + ε) * W) := mul_le_mul_of_nonneg_left hYW (by positivity)
           _ = _ := by field_simp
    calc _ ≤ √(N * (1 + ε)) := sqrt_le_sqrt hc
         _ = _ := sqrt_mul hN0.le _
  have hp : log N ^ (A + 1) = log N ^ (A - 1) * log N ^ 2 := by
    rw [← rpow_natCast, ← rpow_add hL]
    congr 1
    ring
  unfold Decomp148a.scale
  calc _ ≤ (√N / log N ^ (A + 1)) * (√N * √(1 + ε)) * (log N / 2) ^ 2 := by
          gcongr
       _ = _ := by rw [hp]; field_simp; rw [sq_sqrt hN0.le]; ring

end
end LeanLab.BS2022GRH.Scale339
#print axioms LeanLab.BS2022GRH.Scale339.scale_bound
