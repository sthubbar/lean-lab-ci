import LeanLab.AlmostPrimeSums.Decomp243a

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
The logarithmic coprimality correction in BJS p. 60 equation 193
is absorbed even by the smaller relative error envelope used in the supply files.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Error243

open Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527c LeanLab.AlmostPrimeSums.Decomp243a

/-- The switched coprimality error with its logarithmic square is negligible
even compared to sieveError. Derived absorption of BJS p. 60 equation 193. -/
theorem switched_error_small (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + log N) ^ 2 ≤ η * sieveError N := by
  let c : ℝ := 2 * exp eulerMascheroniConstant / 1000
  have hc : 0 < c := by dsimp [c]; positivity
  have hlog : (fun x : ℝ => log x ^ 5) =o[atTop] (fun x => x ^ ((1 : ℝ) / 8)) := by
    simpa only [rpow_ofNat] using
      isLittleO_log_rpow_rpow_atTop 5 (by norm_num : (0 : ℝ) < 1 / 8)
  have hb := tendsto_natCast_atTop_atTop.eventually
    (hlog.bound (show 0 < η * c / 4 by positivity))
  have hLtop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hb, hLtop.eventually_ge_atTop 1, eventually_ge_atTop (2 : ℕ)] with N hN hL1 hN2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < log (N : ℝ) := by linarith
  have hL2 : 0 < log (N : ℝ) ^ 2 := sq_pos_of_pos hL
  have hquarter : 0 < log (N : ℝ) ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hL _
  have hquarter_le : log (N : ℝ) ^ ((1 : ℝ) / 4) ≤ log N := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 : ℝ) / 4 ≤ 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ log (N : ℝ) ^ 5),
    Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hNp.le _)] at hN
  have hpoly : (1 + log (N : ℝ)) ^ 2 * log N ^ ((1 : ℝ) / 4) * log N ^ 2 ≤
      4 * log N ^ 5 := by
    calc
      _ ≤ (4 * log N ^ 2) * log N * log N ^ 2 := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hcancel : (N : ℝ) ^ ((7 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 8) = N := by
    rw [← rpow_add hNp]
    norm_num
  have hbig : ((N : ℝ) ^ ((7 : ℝ) / 8) * (1 + log N) ^ 2 *
      log N ^ ((1 : ℝ) / 4)) * log N ^ 2 ≤ η * c * N := by
    calc
      _ = (N : ℝ) ^ ((7 : ℝ) / 8) *
        ((1 + log N) ^ 2 * log N ^ ((1 : ℝ) / 4) * log N ^ 2) := by ring
      _ ≤ (N : ℝ) ^ ((7 : ℝ) / 8) * (4 * log N ^ 5) := by gcongr
      _ ≤ (N : ℝ) ^ ((7 : ℝ) / 8) * (4 * (η * c / 4 * (N : ℝ) ^ ((1 : ℝ) / 8))) := by gcongr
      _ = η * c * ((N : ℝ) ^ ((7 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 8)) := by ring
      _ = _ := by rw [hcancel]
  have hM : c * N / log N ^ 2 ≤ Mchen N := by
    unfold Mchen
    apply div_le_div_of_nonneg_right _ hL2.le
    have hu := U_ge N
    dsimp [c]
    calc
      _ = (2 * exp eulerMascheroniConstant * (1 / 1000)) * N := by ring
      _ ≤ _ := by gcongr
  have hmain : (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + log N) ^ 2 *
      log N ^ ((1 : ℝ) / 4) ≤ η * Mchen N := by
    calc
      _ ≤ η * c * N / log N ^ 2 := (le_div_iff₀ hL2).mpr hbig
      _ = η * (c * N / log N ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM hη.le
  simpa only [sieveError, ← mul_div_assoc] using (le_div_iff₀ hquarter).mpr hmain

end LeanLab.AlmostPrimeSums.Error243
