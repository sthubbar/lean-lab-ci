/-
AI-written Lean code, Codex task05, 2026-10-22.
Discrete reciprocal summation by parts.
Source: the identity used in Teissier, Crible de Brun, printed p. 11-09,
formula 11, to present Brun's convergence argument. This is an elementary
identity, with no assertion that the original 1919 scan was checked.
-/
import LeanLab.Brun1919.Final

open Finset

noncomputable section
namespace LeanLab.Brun1919

/-- Reciprocal summation by parts, with positive denominator indices. -/
lemma reciprocal_summation_by_parts (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1), f (k + 1) / ((k : ℝ) + 1)) =
      (∑ k ∈ range (n + 1), f (k + 1)) / ((n : ℝ) + 1) +
        ∑ k ∈ range n, (∑ j ∈ range (k + 1), f (j + 1)) /
          (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    change (∑ k ∈ range ((n + 1) + 1), f (k + 1) / ((k : ℝ) + 1)) =
      (∑ k ∈ range ((n + 1) + 1), f (k + 1)) / ((n : ℝ) + 1 + 1) +
        ∑ k ∈ range (n + 1), (∑ j ∈ range (k + 1), f (j + 1)) /
          (((k : ℝ) + 1) * ((k : ℝ) + 2))
    rw [sum_range_succ, ih]
    conv_rhs => arg 1; rw [sum_range_succ]
    conv_rhs => arg 2; rw [sum_range_succ]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    <;> ring

/-- The indicator sum over positive indices is exactly the twin count at the shifted endpoint. -/
lemma twinCount_shifted_sum (n : ℕ) :
    (∑ k ∈ range n, if IsTwin (k + 1) then (1 : ℝ) else 0) = (twinCount (n + 1) : ℝ) := by
  have hs := sum_range_succ' (fun p : ℕ => if IsTwin p then (1 : ℝ) else 0) n
  have hzero : (if IsTwin 0 then (1 : ℝ) else 0) = 0 := by norm_num [IsTwin]
  rw [hzero, add_zero] at hs
  calc
    _ = ∑ p ∈ range (n + 1), if IsTwin p then (1 : ℝ) else 0 := hs.symm
    _ = (twinCount (n + 1) : ℝ) := by rw [sum_boole]; rfl

/-- Exact finite reciprocal partial summation in terms of the twin-count function. -/
lemma twin_reciprocal_partial_sum (n : ℕ) :
    (∑ k ∈ range (n + 1), if IsTwin (k + 1) then (1 : ℝ) / ((k : ℝ) + 1) else 0) =
      (twinCount (n + 2) : ℝ) / ((n : ℝ) + 1) +
        ∑ k ∈ range n, (twinCount (k + 2) : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have h := reciprocal_summation_by_parts (fun p : ℕ => if IsTwin p then (1 : ℝ) else 0) n
  simp_rw [twinCount_shifted_sum] at h
  simpa only [ite_div, zero_div] using h

#print axioms twin_reciprocal_partial_sum

#print axioms twinCount_shifted_sum

#print axioms reciprocal_summation_by_parts

end LeanLab.Brun1919
