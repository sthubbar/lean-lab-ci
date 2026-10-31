/-
AI wrote this Lean code for CODEX task101.
Strict prime cutoffs for P0039 equation 3.7 and pages 66 to 67.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101PowerCutoffs

open Finset Real Filter Topology

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- Largest natural number strictly below the real cutoff, truncated at zero. -/
def strictCutoff (x : ℝ) : ℕ := ⌈x⌉₊ - 1

/-- Actual inverse Euler product over primes strictly below a real cutoff. -/
def strictInverseEuler (x : ℝ) : ℝ := inverseEuler (strictCutoff x)

/-- The natural cutoff selects exactly the primes strictly below the real number. -/
theorem strictCutoff_primes (x : ℝ) :
    ((Icc 1 (strictCutoff x)).filter Nat.Prime) =
      ((range ⌈x⌉₊).filter Nat.Prime) := by
  ext p
  simp only [mem_filter, mem_Icc, mem_range, strictCutoff]
  constructor
  · rintro ⟨⟨hp1, hpc⟩, hp⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨hpc, hp⟩
    exact ⟨⟨by have := hp.two_le; omega, by omega⟩, hp⟩

/-- The natural cutoff is asymptotic to the real cutoff. -/
theorem strictCutoff_ratio :
    Tendsto (fun x : ℝ => (strictCutoff x : ℝ) / x) atTop (𝓝 1) := by
  have h := (tendsto_nat_ceil_div_atTop :
      Tendsto (fun x : ℝ => (⌈x⌉₊ : ℝ) / x) atTop (𝓝 1)).sub
    (tendsto_id.const_div_atTop (1 : ℝ))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hceil : 1 ≤ ⌈x⌉₊ := by
    have hc := Nat.le_ceil x
    by_contra hn
    have hz : ⌈x⌉₊ = 0 := by omega
    rw [hz] at hc
    norm_num at hc
    linarith
  rw [strictCutoff, Nat.cast_sub hceil, Nat.cast_one, sub_div]
  rfl

/-- Logarithms of strict power cutoffs have the expected exponent. -/
theorem log_strict_rpow_limit {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => log (strictCutoff ((n : ℝ) ^ a) : ℝ) / log n) atTop (𝓝 a) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hr := strictCutoff_ratio.comp ht
  have hl := hr.log (by norm_num : (1 : ℝ) ≠ 0)
  have h0 := hl.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun n : ℕ => a +
      log ((strictCutoff ((n : ℝ) ^ a) : ℝ) / ((n : ℝ) ^ a)) / log n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add h0
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), hr.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn hc
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hpow : 0 < (n : ℝ) ^ a := rpow_pos_of_pos (by linarith) a
  have hcut : 0 < (strictCutoff ((n : ℝ) ^ a) : ℝ) := by
    change 0 < (strictCutoff ((n : ℝ) ^ a) : ℝ) / ((n : ℝ) ^ a) at hc
    rw [lt_div_iff₀ hpow] at hc
    simpa using hc
  rw [log_div hcut.ne' hpow.ne', log_rpow (by linarith : (0 : ℝ) < n)]
  field_simp [(log_pos hn').ne']
  ring

/-- Strict positive power cutoffs have the same exponent-ratio limit. -/
theorem strictInverseEuler_power_cutoffs {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => strictInverseEuler ((n : ℝ) ^ a) /
      strictInverseEuler ((n : ℝ) ^ b)) atTop (𝓝 (a / b)) := by
  have hb : 0 < b := ha.trans_le hab
  apply inverseEuler_ratio_limit
  · have h : Tendsto strictCutoff atTop atTop := by
      rw [tendsto_atTop]
      intro m
      filter_upwards [eventually_ge_atTop ((m : ℝ) + 2)] with x hx
      have hc := Nat.le_ceil x
      have hm : m + 1 ≤ ⌈x⌉₊ := by
        exact_mod_cast (show (m : ℝ) + 1 ≤ ⌈x⌉₊ by linarith)
      exact Nat.le_sub_one_of_lt (by omega)
    exact h.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply Nat.sub_le_sub_right
    exact Nat.ceil_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab)
  · exact div_pos ha hb
  · have h := (log_strict_rpow_limit ha).div (log_strict_rpow_limit hb) hb.ne'
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_div_div_cancel_right₀ (log_pos hn').ne' _ _

/-- The literal strict prime cutoffs in the paper satisfy the named three-fifths input. -/
theorem actual_mertens_strict_paper_cutoffs :
    Task58.MertensNormalization (fun n => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 10)))
      (fun n => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6))) := by
  have h := strictInverseEuler_power_cutoffs (a := (1 : ℝ) / 10) (b := (1 : ℝ) / 6)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Strict prime membership uses the literal real inequality of the paper. -/
theorem strictCutoff_prime_mem (x : ℝ) (p : ℕ) :
    p ∈ ((Icc 1 (strictCutoff x)).filter Nat.Prime) ↔ p.Prime ∧ (p : ℝ) < x := by
  rw [strictCutoff_primes]
  simp only [mem_filter, mem_range, Nat.lt_ceil]
  exact and_comm

/-- The strict normalization is the actual product over primes below the real cutoff. -/
theorem strictInverseEuler_eq_prod (x : ℝ) :
    strictInverseEuler x =
      ∏ p ∈ (range ⌈x⌉₊).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ := by
  rw [strictInverseEuler, inverseEuler, eulerProduct, strictCutoff_primes, Finset.prod_inv_distrib]

/-- The actual strict-cutoff inverse products are nonzero at every argument. -/
theorem strictInverseEuler_ne_zero (x : ℝ) : strictInverseEuler x ≠ 0 :=
  inv_ne_zero (eulerProduct_pos (strictCutoff x)).ne'

/-- The common lower roughness cutoff cancels exactly from the paper's Mertens ratio. -/
theorem actual_mertens_common_lower (lo : ℕ → ℝ) :
    Tendsto (fun n : ℕ =>
      (strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 10)) / strictInverseEuler (lo n)) /
      (strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6)) / strictInverseEuler (lo n)))
      atTop (𝓝 (3 / 5 : ℝ)) := by
  apply actual_mertens_strict_paper_cutoffs.congr
  intro n
  exact (div_div_div_cancel_right₀ (strictInverseEuler_ne_zero (lo n)) _ _).symm

/-- CONDITIONAL ON StandardSieveEvaluation alone for the actual strict-cutoff products. -/
theorem actual_sieve_normalization_limit {S : ℕ → ℝ}
    (hS : Task58.StandardSieveEvaluation
      (fun n => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6))) S) :
    Tendsto (fun n : ℕ => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 10)) * S n)
      atTop (𝓝 Task58.page66F3Model) := by
  exact Task58.sieve_normalization_limit (fun n => strictInverseEuler_ne_zero _)
    actual_mertens_strict_paper_cutoffs hS

/-- CONDITIONAL ON StandardSieveEvaluation alone, the smaller-cutoff product has a distinct limit. -/
theorem actual_not_standard_normalization_limit {S : ℕ → ℝ}
    (hS : Task58.StandardSieveEvaluation
      (fun n => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6))) S) :
    ¬ Tendsto (fun n : ℕ => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 10)) * S n)
      atTop (𝓝 Task58.standardF3) := by
  exact Task58.not_standard_normalization_limit (fun n => strictInverseEuler_ne_zero _)
    actual_mertens_strict_paper_cutoffs hS

/-- The remaining standard sieve input is satisfiable for the actual normalization sequence. -/
theorem actual_standard_sieve_vacuity :
    Task58.StandardSieveEvaluation
      (fun n => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6)))
      (fun n => Task58.standardF3 / strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6))) := by
  have heq : (fun n : ℕ => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6)) *
      (Task58.standardF3 / strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6)))) =
        (fun _ : ℕ => Task58.standardF3) := by
    funext n
    field_simp [strictInverseEuler_ne_zero]
  unfold Task58.StandardSieveEvaluation
  rw [heq]
  exact tendsto_const_nhds

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.strictCutoff_primes
#print axioms LeanLab.ChenPrimeExceptional.Task101.strictCutoff_ratio
#print axioms LeanLab.ChenPrimeExceptional.Task101.log_strict_rpow_limit
#print axioms LeanLab.ChenPrimeExceptional.Task101.strictInverseEuler_power_cutoffs
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_mertens_strict_paper_cutoffs
#print axioms LeanLab.ChenPrimeExceptional.Task101.strictCutoff_prime_mem
#print axioms LeanLab.ChenPrimeExceptional.Task101.strictInverseEuler_eq_prod
#print axioms LeanLab.ChenPrimeExceptional.Task101.strictInverseEuler_ne_zero
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_mertens_common_lower
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_sieve_normalization_limit
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_not_standard_normalization_limit
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_standard_sieve_vacuity
