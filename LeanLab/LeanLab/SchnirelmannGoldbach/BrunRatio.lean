/-
Brun 1919, page 127: Goldbach decompositions divided by the prime count tend to zero.
The lab counts ordered decompositions. This proof uses the proved Selberg upper bound,
Chebyshev and the elementary singular product square bound.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.SingularProductGrowth
import LeanLab.SchnirelmannExplicit.Constants

open Finset Filter
open scoped Classical Topology

namespace LeanLab.SchnirelmannGoldbach

open LeanLab.SchnirelmannExplicit

/-- A quantitative square bound for the ratio in Brun's page 127 consequence. -/
theorem r_div_primeCounting_sq_le (n : ℕ) (hn : 100 ≤ n) :
    ((r n : ℝ) / Nat.primeCounting n) ^ 2 ≤
      (36 * C1 ^ 2 / (Real.log 2) ^ 2) / Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C1 := by norm_num [C1]
  have hsp0 := S1.singProd_pos n
  have hr := S1u_explicit n (by omega) n (mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hpi := pi_lower_explicit n hn
  have hlow : 0 < Real.log 2 / 2 * n / Real.log n := by positivity
  have hpi0 : (0 : ℝ) < Nat.primeCounting n := hlow.trans_le hpi
  have hratio : (r n : ℝ) / Nat.primeCounting n ≤
      2 * C1 * singProd n / (Real.log 2 * Real.log n) := by
    calc (r n : ℝ) / Nat.primeCounting n
        ≤ (C1 * n / Real.log n ^ 2 * singProd n) / Nat.primeCounting n :=
          div_le_div_of_nonneg_right hr hpi0.le
      _ ≤ (C1 * n / Real.log n ^ 2 * singProd n) /
          (Real.log 2 / 2 * n / Real.log n) :=
          div_le_div_of_nonneg_left (by positivity) hlow hpi
      _ = 2 * C1 * singProd n / (Real.log 2 * Real.log n) := by
          field_simp
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (r n : ℝ) / Nat.primeCounting n) hratio 2
  have hsp := singProd_sq_le_log n (by omega)
  calc ((r n : ℝ) / Nat.primeCounting n) ^ 2
      ≤ (2 * C1 * singProd n / (Real.log 2 * Real.log n)) ^ 2 := hsq
    _ = 4 * C1 ^ 2 * singProd n ^ 2 / ((Real.log 2) ^ 2 * (Real.log n) ^ 2) := by ring
    _ ≤ 4 * C1 ^ 2 * (9 * Real.log n) / ((Real.log 2) ^ 2 * (Real.log n) ^ 2) := by
        gcongr
    _ = (36 * C1 ^ 2 / (Real.log 2) ^ 2) / Real.log n := by
        field_simp
        ring

/-- Brun's page 127 limit, for the lab's ordered Goldbach representation count. -/
theorem goldbach_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (r n : ℝ) / Nat.primeCounting n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun n : ℕ =>
      (36 * C1 ^ 2 / (Real.log 2) ^ 2) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hsquare : Tendsto (fun n : ℕ => ((r n : ℝ) / Nat.primeCounting n) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => sq_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop 100] with n hn
    exact r_div_primeCounting_sq_le n hn
  convert hsquare.sqrt using 1
  · ext n
    exact (Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (r n : ℝ) / Nat.primeCounting n)).symm
  · simp

end LeanLab.SchnirelmannGoldbach

#print axioms LeanLab.SchnirelmannGoldbach.r_div_primeCounting_sq_le

#print axioms LeanLab.SchnirelmannGoldbach.goldbach_ratio_tendsto_zero
