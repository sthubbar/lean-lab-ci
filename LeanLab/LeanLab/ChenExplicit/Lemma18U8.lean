/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2.
P0009 BJS 2022, Lemma 18 at u₀ = 10⁸, from Lemma18General.lean of PC U-1235:
`epsU0_1e8_le`: epsU0 10⁸ ≤ 1.91·10⁻⁷, true value 1.90906·10⁻⁷, so (53) holds with ε = 1.91·10⁻⁷ for
all 10⁸ ≤ u < z, z > exp 4000, `lemma18_1e8`; and `inv_eps_ge`: 1/ε ≥ 10⁵, so Table 1's row
1/ε = 100000, C₁ = 106, C₂ = 107, applies, the paper stating that C₁ and C₂ decrease in 1/ε.
This is the ε of Section9U8.lean. CONDITIONAL ON Lemma 17 (48) and (49) of the paper, as in
Lemma18General. The brief's figure 1.81·10⁻⁷ for this ε was a slip; the formula gives 1.909·10⁻⁷.
Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.Lemma18General

namespace LeanLab.ChenExplicit.Lemma18U8

open Real LeanLab.ChenExplicit.Lemma18General

/-- `log 10⁸ ≥ 18.4205`. -/
lemma log1e8_ge : (18.4205 : ℝ) ≤ log 100000000 := by
  apply log_ge_of_exp_le (by norm_num)
  have e : exp (18.4205 : ℝ) = exp 1 ^ 18 * exp 0.4205 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h1 : exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 18
  have h2 : exp (0.4205 : ℝ) ≤ 1.5228 := by
    have h := Real.exp_bound' (x := (0.4205 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have h3 : exp 1 ^ 18 * exp 0.4205 ≤ (2.7182818286 : ℝ) ^ 18 * 1.5228 :=
    mul_le_mul h1 h2 (exp_pos _).le (by positivity)
  have h4 : (2.7182818286 : ℝ) ^ 18 * 1.5228 ≤ 100000000 := by norm_num
  rw [e]; linarith

/-- **`epsU0 10⁸ ≤ 1.91·10⁻⁷`**. -/
theorem epsU0_1e8_le : epsU0 100000000 ≤ 191 / 10 ^ 9 := by
  unfold epsU0
  have hl := log1e8_ge
  have hfrac : 2.964e-6 / log (100000000 : ℝ) ≤ 1.60908e-7 := by
    rw [div_le_iff₀ (by linarith)]; norm_num; nlinarith
  set y := 1 / ((100000000 : ℝ) - 2) + 1 / (100000000 - 1) + 1 / 100000000 +
    2.964e-6 / log 100000000 + 1.436e-16 / 4000
  have hy0 : 0 ≤ y := by
    have : 0 ≤ 2.964e-6 / log (100000000 : ℝ) := by positivity
    simp only [y]; norm_num; linarith
  have hy1 : y ≤ 1.90909e-7 := by simp only [y]; norm_num; linarith
  have := exp_le_quad hy0 (by linarith)
  nlinarith

/-- 1/ε ≥ 10⁵ at ε = 1.91·10⁻⁷, so Table 1's last row applies. -/
theorem inv_eps_ge : (100000 : ℝ) ≤ 1 / (191 / 10 ^ 9) := by norm_num

/-- **(53) at u₀ = 10⁸ with ε = 1.91·10⁻⁷**, CONDITIONAL ON Lemma 17 (48), (49). -/
theorem lemma18_1e8 (M : ℝ) (h48 : Lemma17Lower M) (h49 : Lemma17Upper M) (u z : ℝ)
    (hu : 100000000 ≤ u) (huz : u < z) (hz : exp 4000 < z) :
    ∏ p ∈ primesIco u z, (1 - 1 / ((p : ℝ) - 1))⁻¹ < (1 + 191 / 10 ^ 9) * (log z / log u) := by
  have h := lemma18_u0 M h48 h49 100000000 u z (by norm_num) hu huz hz
  have hlu : 0 < log u := Real.log_pos (by linarith)
  have hlz : 0 < log z := by
    have : 4000 < log z := by
      rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos (4000 : ℝ)])]; exact hz
    linarith
  have hr : 0 ≤ log z / log u := (div_pos hlz hlu).le
  have := mul_le_mul_of_nonneg_right (by linarith [epsU0_1e8_le] : 1 + epsU0 100000000 ≤ 1 + 191 / 10 ^ 9) hr
  linarith

end LeanLab.ChenExplicit.Lemma18U8

#print axioms LeanLab.ChenExplicit.Lemma18U8.epsU0_1e8_le
#print axioms LeanLab.ChenExplicit.Lemma18U8.lemma18_1e8
