import LeanLab.ChenDoubleSieve.XiKernelBounds

/-!
# Sign checks for the four printed Xi2 kernels

Source: https://arxiv.org/pdf/0705.1652, page 14, equation 3.22 and Table 1 on page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace LeanLab.ChenDoubleSieve.Wu04Functional

/-- A supported logarithmic summand is nonnegative when its ratio is at least one. -/
theorem supported_log_nonneg {a b t d num den : ℝ} (hd : 0 ≤ d)
    (h : a ≤ t ∧ t ≤ b → 0 < den ∧ den ≤ num) :
    0 ≤ ind a b t / d * log (num/den) := by
  by_cases hi : a ≤ t ∧ t ≤ b
  · rw [ind, if_pos hi]
    exact mul_nonneg (div_nonneg (by norm_num) hd)
      (log_nonneg ((le_div_iff₀ (h hi).1).mpr (by simpa using (h hi).2)))
  · simp only [ind, if_neg hi, zero_div, zero_mul, le_refl]

/-- The common product and denominator are positive for all four printed rows. -/
theorem tableXi2_parameters (i : Fin 4) {t : ℝ} (ht : t ∈ Icc 1 3) :
    let p := tableParams i
    let P := (p.s-1)*(p.sp-1)*(p.k1-1)*(p.k2-1)*(p.k3-1)
    0 < P ∧ P ≤ 1024 ∧ 0 ≤ 5*t*(1-t/p.sp) := by
  fin_cases i <;> norm_num [tableParams] <;> nlinarith [ht.1, ht.2]

/-- Exact rational interval checks for every supported logarithm in Xi2. -/
theorem tableXi2_log_signs (i : Fin 4) {t : ℝ} (ht : t ∈ Icc 1 3) :
    let p := tableParams i
    let a := alpha p
    let P := (p.s-1)*(p.sp-1)*(p.k1-1)*(p.k2-1)*(p.k3-1)
    ((a 1 ≤ t ∧ t ≤ 3) → 0 < P ∧ P ≤ (t+1)^5) ∧
    ((a 8 ≤ t ∧ t ≤ a 0) → 0 < (p.k2-1)*(p.k1-1-t) ∧ (p.k2-1)*(p.k1-1-t) ≤ t+1) ∧
    ((a 4 ≤ t ∧ t ≤ a 1) → 0 < (p.k3-1)*(p.sp-1-t) ∧ (p.k3-1)*(p.sp-1-t) ≤ t+1) ∧
    ((a 2 ≤ t ∧ t ≤ a 1) → 0 < (p.s-1)*(p.sp-1-t) ∧ (p.s-1)*(p.sp-1-t) ≤ t+1) ∧
    ((a 0 ≤ t ∧ t ≤ a 1) → 0 < (p.k1-1)*(p.k2-1) ∧ (p.k1-1)*(p.k2-1) ≤ (t+1)^2) ∧
    ((a 6 ≤ t ∧ t ≤ a 4) →
      0 < (p.k1*p.sp-p.sp-p.k1*t)*(p.k3*p.sp-p.sp-p.k3*t) ∧
      (p.k1*p.sp-p.sp-p.k1*t)*(p.k3*p.sp-p.sp-p.k3*t) ≤ p.sp^2) ∧
    ((a 4 ≤ t ∧ t ≤ a 7) → 0 < p.k1*p.sp-p.sp-p.k1*t ∧
      p.k1*p.sp-p.sp-p.k1*t ≤ p.sp*(p.sp-1-t)) ∧
    ((a 5 ≤ t ∧ t ≤ a 7) → 0 < p.k2*p.sp-p.sp-p.k2*t ∧
      p.k2*p.sp-p.sp-p.k2*t ≤ p.sp) ∧
    ((a 7 ≤ t ∧ t ≤ a 1) → 0 < (1 : ℝ) ∧ 1 ≤ p.sp-1-t) := by
  fin_cases i <;> norm_num [tableParams, alpha]
  all_goals repeat' apply And.intro
  all_goals intro hlo hhi
  all_goals try constructor
  all_goals
    have hfour := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith [ht.1] : (2 : ℝ) ≤ t+1) 4
    have hfive := mul_le_mul_of_nonneg_right hfour (by linarith [ht.1] : 0 ≤ t+1)
    rw [← pow_succ] at hfive
    norm_num at hfive
    have hprod := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
    nlinarith [ht.1, ht.2, sq_nonneg (t-2), sq_nonneg (t+1-5/2)]

/-- Every printed Xi2 kernel is nonnegative on its full integration interval. -/
theorem Xi2_table_nonneg (i : Fin 4) {t : ℝ} (ht : t ∈ Icc 1 3) :
    0 ≤ Xi2 (tableParams i) t := by
  let p := tableParams i
  let P := (p.s-1)*(p.sp-1)*(p.k1-1)*(p.k2-1)*(p.k3-1)
  have hp := tableXi2_parameters i ht
  have hq := hp.2.2
  have hd : (0 : ℝ) ≤ 5*t := by nlinarith [ht.1]
  have hbase : 0 ≤ Wu04Integral.sigma0 t / (5*t) * log (1024/P) :=
    mul_nonneg (div_nonneg (Wu04Integral.sigma0_nonneg ht.1) hd)
      (log_nonneg ((le_div_iff₀ hp.1).mpr (by simpa using hp.2.1)))
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := tableXi2_log_signs i ht
  have hs1 := supported_log_nonneg hd h1
  have hs2 := supported_log_nonneg hd h2
  have hs3 := supported_log_nonneg hd h3
  have hs4 := supported_log_nonneg hd h4
  have hs5 := supported_log_nonneg hd h5
  have hs6 := supported_log_nonneg hq h6
  have hs7 := supported_log_nonneg hq h7
  have hs8 := supported_log_nonneg hq h8
  have hs9 := supported_log_nonneg hq h9
  simp only [div_one] at hs9
  unfold Xi2
  dsimp [p, P] at hbase
  linarith

end LeanLab.ChenDoubleSieve.Wu04Functional

#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.supported_log_nonneg
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.tableXi2_parameters
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.tableXi2_log_signs
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.Xi2_table_nonneg
