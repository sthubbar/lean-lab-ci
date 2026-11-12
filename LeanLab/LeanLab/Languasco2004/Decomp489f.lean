/-
PP1993 page 48 display 24, the Saffari and Vaughan dyadic reduction.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
This step is separated from density and the explicit formula.
New paper proposition definitions require source review.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp489a

namespace LeanLab.Languasco2004.Decomp489f
open Finset Real MeasureTheory Decomp279b Decomp489a
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 48 display 24: the untruncated short character sum on the right.
Unlike the left side, the right side has no cutoff at Y. -/
def untruncatedShortSum {q : ℕ} (χ : DirichletCharacter ℂ q) (x h : ℝ) : ℂ :=
  ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, ((Λ n : ℂ) * χ n - if χ = 1 then 1 else 0)

/-- Page 48 display 24, in an upper bound form avoiding a supremum.
The M and theta intervals retain the printed strict upper endpoints.
V bounds all integrals under the two suprema, before any zero estimate.
The final clipped strip retains an additional C qQ log squared N term. -/
def DyadicCharacterReduction : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N Y Q : ℝ, Real.exp 1 ≤ N → Y ≤ N → 1 ≤ Q →
    ∀ q : ℕ, 1 ≤ q → 100 * (q : ℝ) * Q ≤ Y → ∀ χ : DirichletCharacter ℂ q,
    ∀ V : ℝ, 0 ≤ V →
      (∀ M θ : ℝ, 100 * (q : ℝ) * Q ≤ M → M < Y →
        (q : ℝ) * Q / (20 * M) ≤ θ → θ < 20 * (q : ℝ) * Q / M →
        (∫ x in Set.Icc M (3 * M), ‖untruncatedShortSum χ x (θ * x)‖ ^ 2) ≤ V) →
      (1 / ((q : ℝ) * Q) ^ 2) *
        (∫ x in Set.Icc (100 * (q : ℝ) * Q) Y,
          ‖shortCharacterSum χ Y x ((q : ℝ) * Q / 2)‖ ^ 2) ≤
        C * Real.log N / ((q : ℝ) * Q) ^ 2 * V +
          C * ((q : ℝ) * Q) * Real.log N ^ (2 : ℕ)

/-- LEAF. Page 48 display 24, citing Saffari and Vaughan Lemmas 5 and 6
and PP1992 Section 5. The variable window reduction retains an explicit
edge allowance for the strip from Y minus qQ divided by two to Y.
It has no L function or zero count hypothesis. -/
theorem dyadic_input : DyadicCharacterReduction := by sorry

/-- Page 47 display 21: a zero length short window has no summands. -/
theorem shortCharacterSum_zero_window {q : ℕ} (χ : DirichletCharacter ℂ q) (Y x : ℝ) :
    shortCharacterSum χ Y x 0 = 0 := by
  have hempty : (Icc 1 ⌊Y⌋₊).filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 0) = ∅ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, add_zero, Finset.notMem_empty, iff_false]
    intro h
    exact (not_lt_of_ge h.2.2) h.2.1
  unfold shortCharacterSum
  rw [hempty]
  simp

/-- Page 48 display 24: its untruncated zero length window is empty too. -/
theorem untruncated_zero_window {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    untruncatedShortSum χ x 0 = 0 := by simp [untruncatedShortSum]

/-- Page 48 display 24: the two supremum ranges have a concrete interior point. -/
theorem dyadic_domain_instance :
    (100 : ℝ) ≤ 200 ∧ (200 : ℝ) < 1000 ∧
      (1 : ℝ) / (20 * 200) ≤ 1 / 200 ∧ (1 / 200 : ℝ) < 20 / 200 := by norm_num

#print axioms untruncatedShortSum
#print axioms DyadicCharacterReduction
#print axioms dyadic_input
#print axioms shortCharacterSum_zero_window
#print axioms untruncated_zero_window
#print axioms dyadic_domain_instance
end
end LeanLab.Languasco2004.Decomp489f
