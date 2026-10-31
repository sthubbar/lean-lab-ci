/-
AI wrote this Lean code for CODEX task101.
Actual prime-product ratios underlying P0039 equation 3.7.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101MertensBlocks
import LeanLab.ChenPrimeExceptional.Task58SieveLimits

open Finset Real Filter Topology

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- The actual prime Euler product up to a natural cutoff. -/
def eulerProduct (z : ℕ) : ℝ :=
  ∏ p ∈ (Icc 1 z).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-- The actual inverse sieve normalization up to a natural cutoff. -/
def inverseEuler (z : ℕ) : ℝ := (eulerProduct z)⁻¹

/-- Every finite prime Euler product is positive. -/
theorem eulerProduct_pos (z : ℕ) : 0 < eulerProduct z := by
  unfold eulerProduct
  apply prod_pos
  intro p hp
  have hp' : (1 : ℝ) < p := by
    exact_mod_cast (mem_filter.mp hp).2.one_lt
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp')

/-- Splitting the actual Euler product at an intermediate cutoff. -/
theorem eulerProduct_split {y w : ℕ} (hyw : y ≤ w) :
    eulerProduct w = eulerProduct y * eulerBlock y w := by
  unfold eulerProduct eulerBlock
  simp only [prod_filter]
  have hs := prod_Ioc_consecutive (fun p : ℕ => if p.Prime then (1 - (1 : ℝ) / p) else 1)
    (Nat.zero_le y) hyw
  have hI (N : ℕ) : Ioc 0 N = Icc 1 N := by ext n; simp; omega
  rw [hI, hI] at hs
  exact hs.symm

/-- The ratio of inverse sieve products is the actual Euler block between the cutoffs. -/
theorem inverseEuler_ratio {y w : ℕ} (hyw : y ≤ w) :
    inverseEuler y / inverseEuler w = eulerBlock y w := by
  unfold inverseEuler
  rw [inv_div_inv, eulerProduct_split hyw]
  exact mul_div_cancel_left₀ _ (eulerProduct_pos y).ne'

/-- The actual Euler block tends to the limiting ratio of logarithmic cutoffs. -/
theorem eulerBlock_limit {y w : ℕ → ℕ} {ρ : ℝ}
    (hy : Tendsto y atTop atTop) (hyw : ∀ᶠ n in atTop, y n ≤ w n)
    (hρ : 0 < ρ)
    (hRatio : Tendsto (fun n => log (y n) / log (w n)) atTop (𝓝 ρ)) :
    Tendsto (fun n => eulerBlock (y n) (w n)) atTop (𝓝 ρ) := by
  have hyR : Tendsto (fun n => (y n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hy
  have h1 := (tendsto_log_atTop.comp hyR).const_div_atTop (22 : ℝ)
  have h2 := hyR.const_div_atTop (2 : ℝ)
  have hb : Tendsto (fun n => 22 / log (y n) + 2 / (y n : ℝ)) atTop (𝓝 0) := by
    simpa using h1.add h2
  have hError : Tendsto (fun n => log (eulerBlock (y n) (w n)) -
      log (log (y n) / log (w n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hb
    filter_upwards [hy.eventually_ge_atTop 2, hyw] with n hn hnw
    exact eulerBlock_log_ratio_error hn hnw
  have hLog := hError.add (hRatio.log hρ.ne')
  simp only [sub_add_cancel, zero_add] at hLog
  have hExp := (Real.continuous_exp.tendsto (log ρ)).comp hLog
  rw [exp_log hρ] at hExp
  apply hExp.congr'
  filter_upwards [hy.eventually_ge_atTop 2] with n hn
  exact exp_log (eulerBlock_pos hn)

/-- Inverse sieve products have the same logarithmic-cutoff ratio limit. -/
theorem inverseEuler_ratio_limit {y w : ℕ → ℕ} {ρ : ℝ}
    (hy : Tendsto y atTop atTop) (hyw : ∀ᶠ n in atTop, y n ≤ w n)
    (hρ : 0 < ρ)
    (hRatio : Tendsto (fun n => log (y n) / log (w n)) atTop (𝓝 ρ)) :
    Tendsto (fun n => inverseEuler (y n) / inverseEuler (w n)) atTop (𝓝 ρ) := by
  apply (eulerBlock_limit hy hyw hρ hRatio).congr'
  filter_upwards [hyw] with n hn
  exact (inverseEuler_ratio hn).symm

/-- The actual normalization ratio for cutoffs n cubed and n to the fifth is three fifths. -/
theorem actual_mertens_three_fifths :
    Task58.MertensNormalization (fun n => inverseEuler (n ^ 3))
      (fun n => inverseEuler (n ^ 5)) := by
  apply inverseEuler_ratio_limit (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact Nat.pow_le_pow_right hn (by norm_num)
  · norm_num
  · have heq : (fun n : ℕ => log ((n ^ 3 : ℕ) : ℝ) / log ((n ^ 5 : ℕ) : ℝ)) =ᶠ[atTop]
        (fun _ : ℕ => (3 / 5 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
      have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      rw [Nat.cast_pow, Nat.cast_pow, log_pow, log_pow]
      field_simp [(log_pos hn').ne']
      norm_num
    exact tendsto_const_nhds.congr' heq.symm

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.eulerProduct_pos
#print axioms LeanLab.ChenPrimeExceptional.Task101.eulerProduct_split
#print axioms LeanLab.ChenPrimeExceptional.Task101.inverseEuler_ratio
#print axioms LeanLab.ChenPrimeExceptional.Task101.eulerBlock_limit
#print axioms LeanLab.ChenPrimeExceptional.Task101.inverseEuler_ratio_limit
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_mertens_three_fifths
