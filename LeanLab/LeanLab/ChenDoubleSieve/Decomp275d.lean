import LeanLab.ChenDoubleSieve.Statements

/-!
Absorption of the power remainder in Wu 2004 equation 9.4.
Source: https://arxiv.org/pdf/0705.1652, pages 34 and 41.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Filter Asymptotics
namespace LeanLab.ChenDoubleSieve.Task275

/-- The logarithmic square is smaller than the twelfth root at infinity. -/
theorem log_sq_littleO_power :
    (fun x : ℝ => log x ^ 2) =o[atTop] (fun x : ℝ => x ^ (1 / 12 : ℝ)) := by
  simpa only [Real.rpow_two] using
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 / 12) (by norm_num))

/-- Every fixed nonnegative multiple of the power remainder is eventually at most
an arbitrary positive multiple of the actual singular series normalizer. -/
theorem power_remainder_absorbed (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      C * (N : ℝ) ^ (11 / 12 : ℝ) ≤ ε * Θ N := by
  have hlo := log_sq_littleO_power.const_mul_left C
  have hb := hlo.bound (mul_pos hε LeanLab.ChenExplicit.twinC_pos)
  have hnat : ∀ᶠ N : ℕ in atTop,
      ‖C * log (N : ℝ) ^ 2‖ ≤
        (ε * LeanLab.ChenExplicit.twinC) * ‖(N : ℝ) ^ (1 / 12 : ℝ)‖ :=
    (tendsto_natCast_atTop_atTop.eventually hb)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hnat
  refine ⟨max M 2, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_right M 2).trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hsq : 0 < log (N : ℝ) ^ 2 := sq_pos_of_pos hlog
  have hbound := hM N ((le_max_left M 2).trans hN)
  rw [Real.norm_of_nonneg (mul_nonneg hC (sq_nonneg _)),
    Real.norm_of_nonneg (Real.rpow_nonneg hNr.le _)] at hbound
  have hp : (N : ℝ) ^ (1 / 12 : ℝ) * (N : ℝ) ^ (11 / 12 : ℝ) = N := by
    rw [← Real.rpow_add hNr]
    norm_num
  have hcn : LeanLab.ChenExplicit.twinC ≤ CN N := by
    unfold CN
    nlinarith [oddFactor_one_le N, LeanLab.ChenExplicit.twinC_pos]
  change C * (N : ℝ) ^ (11 / 12 : ℝ) ≤ ε * (CN N * N / log (N : ℝ) ^ 2)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hsq).2
  calc
    C * (N : ℝ) ^ (11 / 12 : ℝ) * log (N : ℝ) ^ 2 =
        (C * log (N : ℝ) ^ 2) * (N : ℝ) ^ (11 / 12 : ℝ) := by ring
    _ ≤ ((ε * LeanLab.ChenExplicit.twinC) * (N : ℝ) ^ (1 / 12 : ℝ)) *
        (N : ℝ) ^ (11 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hNr.le _)
    _ = (ε * (N : ℝ)) * LeanLab.ChenExplicit.twinC := by
      calc
        _ = (ε * LeanLab.ChenExplicit.twinC) *
            ((N : ℝ) ^ (1 / 12 : ℝ) * (N : ℝ) ^ (11 / 12 : ℝ)) := by ring
        _ = _ := by rw [hp]; ring
    _ ≤ (ε * (N : ℝ)) * CN N :=
      mul_le_mul_of_nonneg_left hcn (mul_nonneg hε.le hNr.le)
    _ = ε * (CN N * N) := by ring

end LeanLab.ChenDoubleSieve.Task275
