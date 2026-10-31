import LeanLab.ChenDoubleSieve.TupleLevel
import LeanLab.ChenDoubleSieve.SigmaIntegral

/-!
# A nonempty admissible tuple witness

Source: https://arxiv.org/pdf/0705.1652, page 9, equation 3.1.
This witness checks the hypotheses of the tuple level implications.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
namespace LeanLab.ChenDoubleSieve.Wu04

def witnessEps : ℝ := (log 256)⁻¹ ^ 4

theorem witnessEps_bounds : 0 < witnessEps ∧ witnessEps ≤ 1 := by
  have hlog : (1 : ℝ) ≤ log 256 := by
    have hh := (Wu04Integral.log_bounds 1 (y := 2) (by norm_num)).1
    norm_num [Wu04Integral.logLower, Finset.sum_range_succ] at hh
    have he : log (256 : ℝ) = 8 * log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, log_pow]
      norm_num
    linarith
  constructor
  · unfold witnessEps; positivity
  · exact pow_le_one₀ (by positivity) ((inv_le_one₀ (by linarith : (0 : ℝ) < log 256)).mpr hlog)

/-- The single endpoint lies between three and four, and its square is below Q. -/
theorem nonempty_UkData_instance :
    UkData 0 1 256 1 (fun _ => 3 + witnessEps) (1 + 3/2 * witnessEps) := by
  have he := witnessEps_bounds
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change 1 + witnessEps ≤ 1 + 3/2 * witnessEps
    linarith
  · change 1 + 3/2 * witnessEps < 1 + 2 * witnessEps
    linarith
  · intro a b hab
    exact le_rfl
  · intro j
    norm_num [W]
    linarith
  · intro j
    fin_cases j
    norm_num [Q, ← Real.sqrt_eq_rpow]
    nlinarith

/-- Prime three occurs in the interval and is coprime to the even parameter 256. -/
theorem witness_tuple_mem : (fun _ : Fin 1 => 3) ∈
    Wu41.Tset 256 1 (fun _ => 3 + witnessEps) (1 + 3/2*witnessEps) := by
  have he := witnessEps_bounds
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Wu41.mem_Pset.mpr
  refine ⟨by norm_num, ?_, ?_, by norm_num⟩
  · rw [div_le_iff₀ (by linarith : 0 < 1 + 3/2*witnessEps)]
    norm_num
    linarith
  · norm_num
    exact he.1

def positiveEps : ℝ := (log 65536)⁻¹ ^ 4

theorem positiveEps_bounds : 0 < positiveEps ∧ positiveEps ≤ 1 := by
  have hlog : (1 : ℝ) ≤ log 65536 := by
    have hh := (Wu04Integral.log_bounds 1 (y := 2) (by norm_num)).1
    norm_num [Wu04Integral.logLower, Finset.sum_range_succ] at hh
    have he : log (65536 : ℝ) = 16 * log 2 := by
      rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow]
      norm_num
    linarith
  constructor
  · unfold positiveEps; positivity
  · exact pow_le_one₀ (by positivity) ((inv_le_one₀ (by linarith : (0 : ℝ) < log 65536)).mpr hlog)

/-- The single endpoint lies between three and four, and its square is below Q. -/
theorem positive_delta_instance :
    UkData (1/4) 1 65536 1 (fun _ => 3 + positiveEps) (1 + 3/2 * positiveEps) := by
  have he := positiveEps_bounds
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change 1 + positiveEps ≤ 1 + 3/2 * positiveEps
    linarith
  · change 1 + 3/2 * positiveEps < 1 + 2 * positiveEps
    linarith
  · intro a b hab
    exact le_rfl
  · intro j
    have hw : W (1/4) 1 65536 = 2 := by
      convert Real.pow_rpow_inv_natCast (x := 2) (n := 16) (by norm_num) (by decide) using 1 <;> norm_num [W]
    rw [hw]
    linarith
  · intro j
    fin_cases j
    have hq : Q (1/4) 65536 = 16 := by
      convert Real.pow_rpow_inv_natCast (x := 16) (n := 4) (by norm_num) (by decide) using 1 <;> norm_num [Q]
    rw [hq]
    norm_num
    nlinarith

/-- Prime three occurs in the interval and is coprime to the even parameter 65536. -/
theorem positive_tuple_mem : (fun _ : Fin 1 => 3) ∈
    Wu41.Tset 65536 1 (fun _ => 3 + positiveEps) (1 + 3/2*positiveEps) := by
  have he := positiveEps_bounds
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Wu41.mem_Pset.mpr
  refine ⟨by norm_num, ?_, ?_, by norm_num⟩
  · rw [div_le_iff₀ (by linarith : 0 < 1 + 3/2*positiveEps)]
    norm_num
    linarith
  · norm_num
    exact he.1

end LeanLab.ChenDoubleSieve.Wu04

#print axioms LeanLab.ChenDoubleSieve.Wu04.witnessEps_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04.nonempty_UkData_instance
#print axioms LeanLab.ChenDoubleSieve.Wu04.witness_tuple_mem

#print axioms LeanLab.ChenDoubleSieve.Wu04.positiveEps_bounds

#print axioms LeanLab.ChenDoubleSieve.Wu04.positive_delta_instance

#print axioms LeanLab.ChenDoubleSieve.Wu04.positive_tuple_mem
