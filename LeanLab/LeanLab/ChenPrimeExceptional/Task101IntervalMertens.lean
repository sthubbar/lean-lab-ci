/-
AI wrote this Lean code for CODEX task101.
Literal interval products in the Mertens calculation on P0039 page 17.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101StrictCutoffs

open Finset Real Filter Topology

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- The literal inverse Euler product over primes from lo inclusive to hi exclusive. -/
def intervalEulerNorm (lo hi : ℝ) : ℝ :=
  ∏ p ∈ (range ⌈hi⌉₊).filter (fun p : ℕ => p.Prime ∧ lo ≤ (p : ℝ)), (1 - (1 : ℝ) / p)⁻¹

/-- Splitting a strict inverse Euler product into its lower and interval factors. -/
theorem strictInverseEuler_split {lo hi : ℝ} (hlohi : lo ≤ hi) :
    strictInverseEuler hi = strictInverseEuler lo * intervalEulerNorm lo hi := by
  rw [strictInverseEuler_eq_prod, strictInverseEuler_eq_prod, intervalEulerNorm]
  let s := (range ⌈hi⌉₊).filter Nat.Prime
  have hlo : s.filter (fun p : ℕ => (p : ℝ) < lo) = (range ⌈lo⌉₊).filter Nat.Prime := by
    ext p
    simp only [s, mem_filter, mem_range, Nat.lt_ceil]
    constructor
    · rintro ⟨⟨_, hp⟩, hpl⟩
      exact ⟨hpl, hp⟩
    · rintro ⟨hpl, hp⟩
      exact ⟨⟨hpl.trans_le hlohi, hp⟩, hpl⟩
  have hhi : s.filter (fun p : ℕ => ¬ (p : ℝ) < lo) =
      (range ⌈hi⌉₊).filter (fun p : ℕ => p.Prime ∧ lo ≤ (p : ℝ)) := by
    ext p
    simp only [s, mem_filter, not_lt]
    tauto
  have h := prod_filter_mul_prod_filter_not (s := s) (fun p : ℕ => (p : ℝ) < lo)
    (fun p => (1 - (1 : ℝ) / p)⁻¹)
  rw [hlo, hhi] at h
  exact h.symm

/-- The actual interval normalization is the quotient of strict inverse products. -/
theorem intervalEulerNorm_eq_ratio {lo hi : ℝ} (hlohi : lo ≤ hi) :
    intervalEulerNorm lo hi = strictInverseEuler hi / strictInverseEuler lo := by
  apply (eq_div_iff (strictInverseEuler_ne_zero lo)).mpr
  have h := strictInverseEuler_split hlohi
  nlinarith

/-- A common lower cutoff cancels in the ratio of the literal interval products. -/
theorem intervalEulerNorm_ratio {lo hi₀ hi₁ : ℝ} (hlo : lo ≤ hi₀) (hhi : hi₀ ≤ hi₁) :
    intervalEulerNorm lo hi₀ / intervalEulerNorm lo hi₁ =
      strictInverseEuler hi₀ / strictInverseEuler hi₁ := by
  rw [intervalEulerNorm_eq_ratio hlo, intervalEulerNorm_eq_ratio (hlo.trans hhi)]
  exact div_div_div_cancel_right₀ (strictInverseEuler_ne_zero lo) _ _

/-- The actual interval products in the paper satisfy the original Mertens input. -/
theorem actual_interval_mertens {a : ℝ} (ha : a ≤ (1 : ℝ) / 10) :
    Task58.MertensNormalization
      (fun n => intervalEulerNorm ((n : ℝ) ^ a) ((n : ℝ) ^ ((1 : ℝ) / 10)))
      (fun n => intervalEulerNorm ((n : ℝ) ^ a) ((n : ℝ) ^ ((1 : ℝ) / 6))) := by
  apply actual_mertens_strict_paper_cutoffs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (intervalEulerNorm_ratio (rpow_le_rpow_of_exponent_le hn' ha)
    (rpow_le_rpow_of_exponent_le hn' (by norm_num : (1 : ℝ) / 10 ≤ 1 / 6))).symm

/-- Every literal interval normalization is strictly positive. -/
theorem intervalEulerNorm_pos (lo hi : ℝ) : 0 < intervalEulerNorm lo hi := by
  unfold intervalEulerNorm
  apply prod_pos
  intro p hp
  apply inv_pos.mpr
  have hp' : (1 : ℝ) < p := by
    exact_mod_cast (mem_filter.mp hp).2.1.one_lt
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp')

/-- CONDITIONAL ON the standard sieve evaluation alone for the literal interval products. -/
theorem actual_interval_sieve_normalization {a : ℝ} (ha : a ≤ (1 : ℝ) / 10) {S : ℕ → ℝ}
    (hS : Task58.StandardSieveEvaluation
      (fun n => intervalEulerNorm ((n : ℝ) ^ a) ((n : ℝ) ^ ((1 : ℝ) / 6))) S) :
    Tendsto (fun n : ℕ => intervalEulerNorm ((n : ℝ) ^ a) ((n : ℝ) ^ ((1 : ℝ) / 10)) * S n)
      atTop (𝓝 Task58.page66F3Model) := by
  exact Task58.sieve_normalization_limit (fun n => (intervalEulerNorm_pos _ _).ne')
    (actual_interval_mertens ha) hS

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.strictInverseEuler_split
#print axioms LeanLab.ChenPrimeExceptional.Task101.intervalEulerNorm_eq_ratio
#print axioms LeanLab.ChenPrimeExceptional.Task101.intervalEulerNorm_ratio
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_interval_mertens
#print axioms LeanLab.ChenPrimeExceptional.Task101.intervalEulerNorm_pos
#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_interval_sieve_normalization
