/-
AI wrote this Lean code for CODEX task101.
P0039 Lemma 5.2, page 29. Smooth logarithmic weights have controlled total variation.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101PartialSummation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset Real

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- A reciprocal derivative bound gives a logarithmic bound for each increment. -/
theorem logarithmic_increment_bound {f f' : ℝ → ℂ} {L R C : ℝ}
    (hL : 0 < L) (hLR : L ≤ R)
    (hf : ∀ t ∈ Set.Icc L R, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Ico L R, ‖f' t‖ ≤ C / t) :
    ‖f R - f L‖ ≤ C * (log R - log L) := by
  have hg : ContinuousOn (fun t => f t - f L) (Set.Icc L R) := by
    apply ContinuousOn.sub _ continuousOn_const
    intro t ht
    exact (hf t ht).continuousAt.continuousWithinAt
  have hg' : ∀ t ∈ Set.Ico L R,
      HasDerivWithinAt (fun t => f t - f L) (f' t) (Set.Ici t) t := by
    intro t ht
    exact ((hf t (Set.Ico_subset_Icc_self ht)).sub_const (f L)).hasDerivWithinAt
  have hB : ContinuousOn (fun t => C * (log t - log L)) (Set.Icc L R) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub _ continuousOn_const
    intro t ht
    exact (continuousAt_log (hL.trans_le ht.1).ne').continuousWithinAt
  have hB' : ∀ t ∈ Set.Ico L R,
      HasDerivWithinAt (fun t => C * (log t - log L)) (C / t) (Set.Ici t) t := by
    intro t ht
    simpa only [div_eq_mul_inv] using
      (((hasDerivAt_log (hL.trans_le ht.1).ne').sub_const (log L)).const_mul C).hasDerivWithinAt
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary' hg hg'
    (show ‖f L - f L‖ ≤ C * (log L - log L) by simp) hB hB' hbound
  exact h ⟨hLR, le_rfl⟩

/-- Sampling a smooth weight preserves its logarithmic total-variation bound. -/
theorem smooth_variation_bound {f f' : ℝ → ℂ} {L C : ℝ} (n : ℕ)
    (hL : 0 < L)
    (hf : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), ‖f' t‖ ≤ C / t) :
    variation (fun i => f (L + i)) n ≤ C * (log (L + (n - 1 : ℕ)) - log L) := by
  unfold variation
  calc
    _ ≤ ∑ i ∈ range (n - 1), C * (log (L + (i + 1 : ℕ)) - log (L + i)) := by
      apply sum_le_sum
      intro i hi
      have hi' : i + 1 ≤ n - 1 := by simp only [mem_range] at hi; omega
      have hiR : (i + 1 : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hi'
      have hsub : Set.Icc (L + i) (L + (i + 1 : ℕ)) ⊆ Set.Icc L (L + (n - 1 : ℕ)) := by
        intro t ht
        rcases ht with ⟨ht0, ht1⟩
        push_cast at hiR ht0 ht1
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i]
      exact logarithmic_increment_bound (by positivity) (by push_cast; linarith)
        (fun t ht => hf t (hsub ht)) (fun t ht => hbound t (hsub (Set.Ico_subset_Icc_self ht)))
    _ = _ := by
      rw [← mul_sum]
      have hs := sum_range_sub (fun i : ℕ => log (L + i)) (n - 1)
      simpa using congrArg (fun x : ℝ => C * x) hs

/-- Lemma 5.2 with explicit prefix bounds and a sampled smooth weight. -/
theorem lemma52_smooth (a : ℕ → ℂ) {f f' : ℝ → ℂ} (n : ℕ)
    {L H c W C M U : ℝ} (hL : 0 < L) (hH : 0 < H) (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), ‖f' t‖ ≤ C / t)
    (hlog : log (L + (n - 1 : ℕ)) - log L ≤ H)
    (hlo : ∀ i < n, c * H ≤ ‖f (L + i)‖)
    (hhi : ‖f (L + (n - 1 : ℕ))‖ ≤ W * H)
    (hM : ∀ k ≤ n, ‖∑ i ∈ range k, a i‖ ≤ M)
    (hU : ∀ k ≤ n, ‖∑ i ∈ range k, f (L + i) * a i‖ ≤ U) :
    ‖∑ i ∈ range n, f (L + i) * a i‖ ≤ (W + C) * H * M ∧
      ‖∑ i ∈ range n, a i‖ ≤ ((1 / c + C / c ^ 2) / H) * U := by
  apply lemma52_discrete a (fun i => f (L + i)) n hH hc hlo hhi _ hM hU
  exact (smooth_variation_bound n hL hf hbound).trans
    (mul_le_mul_of_nonneg_left hlog hC)

/-- The logarithmic scale in Lemma 5.2 gives explicit constants in both directions. -/
theorem lemma52_logarithmic (a : ℕ → ℂ) {f f' : ℝ → ℂ} (n : ℕ)
    {L N c W C M U : ℝ} (hL : 1 ≤ L) (hN : 1 < N)
    (hR : L + (n - 1 : ℕ) ≤ N) (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), ‖f' t‖ ≤ C / t)
    (hlo : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), c * log N ≤ ‖f t‖)
    (hhi : ∀ t ∈ Set.Icc L (L + (n - 1 : ℕ)), ‖f t‖ ≤ W * log N)
    (hM : ∀ k ≤ n, ‖∑ i ∈ range k, a i‖ ≤ M)
    (hU : ∀ k ≤ n, ‖∑ i ∈ range k, f (L + i) * a i‖ ≤ U) :
    ‖∑ i ∈ range n, f (L + i) * a i‖ ≤ (W + C) * log N * M ∧
      ‖∑ i ∈ range n, a i‖ ≤ ((1 / c + C / c ^ 2) / log N) * U := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hR0 : 0 < L + (n - 1 : ℕ) := by positivity
  have hLR : L ≤ L + (n - 1 : ℕ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  apply lemma52_smooth a n hL0 (log_pos hN) hc hC hf hbound
  · have h1 := log_le_log hR0 hR
    have h2 := log_nonneg hL
    linarith
  · intro i hi
    apply hlo
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · have hi' : i ≤ n - 1 := by omega
      exact add_le_add le_rfl (show (i : ℝ) ≤ (n - 1 : ℕ) by exact_mod_cast hi')
  · exact hhi _ ⟨hLR, le_rfl⟩
  · exact hM
  · exact hU

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.logarithmic_increment_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.smooth_variation_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.lemma52_smooth
#print axioms LeanLab.ChenPrimeExceptional.Task101.lemma52_logarithmic
