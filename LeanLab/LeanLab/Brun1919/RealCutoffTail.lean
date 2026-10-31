/-
AI-written Lean code, Codex task05, 2026-10-22.
Natural cutoffs for the reciprocal-tail bound.
All explicit constants are lab consequences, not claims about printed 1919 constants.
-/
import LeanLab.Brun1919.ReciprocalTail

open Finset

noncomputable section
namespace LeanLab.Brun1919

/-- The real logarithm is controlled by twice the natural dyadic block index. -/
lemma log_nat_le_twice_dyadic_index (N : ℕ) (hN : 2 ≤ N) :
    Real.log (N : ℝ) ≤ 2 * (Nat.log 2 N : ℝ) * Real.log 2 := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N
  have hlog := Real.log_le_log hN0 (by exact_mod_cast hpow.le : (N : ℝ) ≤ 2 ^ (Nat.log 2 N).succ)
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hk : 1 ≤ (Nat.log 2 N : ℝ) := by
    have hkNat : 1 ≤ Nat.log 2 N := by
      have := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) hN
      omega
    exact_mod_cast hkNat
  have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) hl2]

/-- Every natural cutoff of the twin-pair reciprocal series is summable. -/
lemma brun_cutoff_summable (N : ℕ) : Summable (fun p : ℕ =>
    if N ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) := by
  refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) ?_ brun
  intro p
  by_cases hp : N ≤ p ∧ IsTwin p
  · simp only [if_pos hp, if_pos hp.2]
    exact le_rfl
  · rw [if_neg hp]
    split_ifs <;> positivity

/-- A reciprocal-tail bound at every natural cutoff at least two. -/
theorem brun_tail_bound_nat (N : ℕ) (hN : 2 ≤ N) :
    (∑' p : ℕ, if N ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) ≤
      8192 / (Real.log 2 * Real.log N) := by
  let K := Nat.log 2 N
  have hK : 1 ≤ K := by
    have := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) hN
    omega
  have hpow : 2 ^ K ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hpoint : ∀ p : ℕ,
      (if N ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) ≤
        (if 2 ^ K ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) := by
    intro p
    by_cases hp : N ≤ p ∧ IsTwin p
    · have hd : 2 ^ K ≤ p ∧ IsTwin p := ⟨hpow.trans hp.1, hp.2⟩
      simp [hp, hd]
    · rw [if_neg hp]
      split_ifs <;> positivity
  calc
    _ ≤ ∑' p : ℕ, if 2 ^ K ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0 :=
      (brun_cutoff_summable N).tsum_le_tsum hpoint (brun_cutoff_summable (2 ^ K))
    _ ≤ (4096 / Real.log 2 ^ 2) / (K : ℝ) := brun_tail_bound K hK
    _ ≤ 8192 / (Real.log 2 * Real.log N) := by
      have hK0 : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
      have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hL := log_nat_le_twice_dyadic_index N hN
      change Real.log (N : ℝ) ≤ 2 * (K : ℝ) * Real.log 2 at hL
      rw [div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg hl2.le (sub_nonneg.mpr hL)]

#print axioms brun_tail_bound_nat

#print axioms brun_cutoff_summable

#print axioms log_nat_le_twice_dyadic_index

end LeanLab.Brun1919
