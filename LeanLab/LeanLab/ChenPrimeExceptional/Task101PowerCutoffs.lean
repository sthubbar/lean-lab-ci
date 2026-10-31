/-
AI wrote this Lean code for CODEX task101.
Actual power cutoffs for the Mertens ratio in P0039 equation 3.7.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101MertensLimit

open Real Filter Topology

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- The logarithm of a floored power cutoff has the expected exponent. -/
theorem log_floor_rpow_limit {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => log (⌊(n : ℝ) ^ a⌋₊ : ℝ) / log n) atTop (𝓝 a) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hr := tendsto_nat_floor_div_atTop.comp ht
  have hl := hr.log (by norm_num : (1 : ℝ) ≠ 0)
  have h0 := hl.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun n : ℕ => a +
      log ((⌊(n : ℝ) ^ a⌋₊ : ℝ) / ((n : ℝ) ^ a)) / log n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add h0
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), ht.eventually_ge_atTop 2] with n hn hx
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hfloor : 0 < (⌊(n : ℝ) ^ a⌋₊ : ℝ) := by
    exact_mod_cast (Nat.floor_pos.mpr (show (1 : ℝ) ≤ (n : ℝ) ^ a by linarith))
  rw [log_div hfloor.ne' (rpow_pos_of_pos (by linarith : (0 : ℝ) < n) a).ne',
    log_rpow (by linarith : (0 : ℝ) < n)]
  field_simp [(log_pos hn').ne']
  ring

/-- Ratios of logarithms of floored power cutoffs tend to the ratio of exponents. -/
theorem log_floor_rpow_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => log (⌊(n : ℝ) ^ a⌋₊ : ℝ) /
      log (⌊(n : ℝ) ^ b⌋₊ : ℝ)) atTop (𝓝 (a / b)) := by
  have h := (log_floor_rpow_limit ha).div (log_floor_rpow_limit hb) hb.ne'
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact div_div_div_cancel_right₀ (log_pos hn').ne' _ _

/-- Actual inverse Euler products at ordered positive power cutoffs have exponent-ratio limit. -/
theorem inverseEuler_power_cutoffs {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => inverseEuler ⌊(n : ℝ) ^ a⌋₊ /
      inverseEuler ⌊(n : ℝ) ^ b⌋₊) atTop (𝓝 (a / b)) := by
  have hb : 0 < b := ha.trans_le hab
  apply inverseEuler_ratio_limit
  · exact tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact Nat.floor_mono (rpow_le_rpow_of_exponent_le hn' hab)
  · exact div_pos ha hb
  · exact log_floor_rpow_ratio ha hb

/-- The paper's one-tenth and one-sixth actual power cutoffs give the original three-fifths input. -/
theorem actual_mertens_paper_cutoffs :
    Task58.MertensNormalization (fun n => inverseEuler ⌊(n : ℝ) ^ ((1 : ℝ) / 10)⌋₊)
      (fun n => inverseEuler ⌊(n : ℝ) ^ ((1 : ℝ) / 6)⌋₊) := by
  have h := inverseEuler_power_cutoffs (a := (1 : ℝ) / 10) (b := (1 : ℝ) / 6)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.log_floor_rpow_limit
#print axioms LeanLab.ChenPrimeExceptional.Task101.log_floor_rpow_ratio
#print axioms LeanLab.ChenPrimeExceptional.Task101.inverseEuler_power_cutoffs
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_mertens_paper_cutoffs
