/-
P0069 Baker, Harman, Pintz 1997, Section 2. ROUTE BURST session 7, step
`section2_circle_method-p2`, QUESTION 1: faithfulness review of the three defs of
`Section2MeanSquare.lean`, `Section2MS.MeanSquare`, `Section2MS.Conclusion` and
`Section2MS.Theorem2With`, against the page images, pages 2, 3 and 6 of
papers/P0069-original.pdf. The line by line review is in
research/burst-20261112/BHP1997-section2_circle_method-p2.md; all three were found to MATCH.

This file adds small PROVED sanity lemmas that pin each def, none of which changes a
statement:
* `conclusion_u_zero_iff`: with u = 0 the threshold of 1.6 is zero and `Conclusion` says
  exactly that the convolution vanishes at all but fewer than x^{θ₁θ₂}/ℒ^A even N.
  This pins how `Conclusion` reads the factor 1 + O(ℒ^{-1}) of display 1.6, page 2.
* `meanSquare_of_exact`: if the convolution equals the main term uvY/(ℒℒ') 𝔖(2n) at
  every even N of K for large x, then `MeanSquare` holds; this pins that the right side of
  the page 6 display is nonnegative for large x and that the left side is the sum of
  squared deviations from the main term.
* `theorem2With_mono`: `Theorem2With` is monotone in its conclusion, so it carries exactly
  the hypotheses i to iv of page 3 and nothing else.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Section2MeanSquare

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2

/-- P0069 Baker Harman Pintz 1997, page 2 display 1.6 and page 3 Theorem 2, the sanity
check that pins `Conclusion`: when u = 0 the threshold `K |uv| Y/(ℒℒ') 𝔖(2n)/ℒ` is zero for
every K, so the exceptional set of 1.6 is the set of even N in [x, x + x^{θ₁θ₂}] where the
convolution Σ_{k+m=N} a(k)b(m) is not zero. PROVED. -/
theorem conclusion_u_zero_iff (ε : ℝ) (a b : ℝ → ℕ → ℂ) (v : ℝ) :
    Conclusion ε a b 0 v ↔
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        (((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N : ℕ => Even N ∧
            (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
              ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
                if k + m = N then a x k * b x m else 0) ≠ 0)).card : ℝ) <
          x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) / Real.log x ^ A := by
  unfold Conclusion
  simp only [zero_mul, abs_zero, mul_zero, zero_div, Complex.ofReal_zero, sub_zero,
    norm_pos_iff]
  constructor
  · intro h A hA
    obtain ⟨K, C, hC⟩ := h A hA
    exact ⟨C, hC⟩
  · intro h A hA
    obtain ⟨C, hC⟩ := h A hA
    exact ⟨0, C, hC⟩

/-- P0069 Baker Harman Pintz 1997, page 6, the display after 2.1, the sanity check that
pins `MeanSquare`: if for all large x the convolution equals the main term
uvY/(ℒℒ') 𝔖(2n) at every even N of K = [x, x + x^{θ₁θ₂}], then the left side of the
display is zero and the display holds with C = max X 1. PROVED. -/
theorem meanSquare_of_exact (ε : ℝ) (a b : ℝ → ℕ → ℂ) (u v : ℝ)
    (h : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N : ℕ => Even N),
        (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
          ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            if k + m = N then a x k * b x m else 0) =
          (u : ℂ) * v * ((x ^ (11 / 20 + ε) : ℝ) : ℂ) /
            ((Real.log x : ℂ) * (Real.log (x ^ (11 / 20 + ε)) : ℂ)) * (sing (N / 2) : ℂ)) :
    MeanSquare ε a b u v := by
  obtain ⟨X, hX⟩ := h
  unfold MeanSquare
  dsimp only
  intro A _
  refine ⟨max X 1, fun x hx => ?_⟩
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hsum : ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
        (fun N : ℕ => Even N),
      ‖(∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
          ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            if k + m = N then a x k * b x m else 0) -
        (u : ℂ) * v * ((x ^ (11 / 20 + ε) : ℝ) : ℂ) /
          ((Real.log x : ℂ) * (Real.log (x ^ (11 / 20 + ε)) : ℂ)) * (sing (N / 2) : ℂ)‖ ^ 2
        = 0 := by
    apply Finset.sum_eq_zero
    intro N hN
    rw [hX x hxX N hN]
    simp
  rw [hsum]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have h1 : 0 ≤ max X 1 := le_trans zero_le_one (le_max_right _ _)
  have h2 : 0 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    Real.rpow_nonneg hx0.le _
  have h3 : 0 ≤ (x ^ (11 / 20 + ε)) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ Real.log x ^ (-A - 7) := Real.rpow_nonneg hL _
  have : 0 ≤ max X 1 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
      (x ^ (11 / 20 + ε)) ^ 2 * Real.log x ^ (-A - 7) := by positivity
  exact this

/-- P0069 Baker Harman Pintz 1997, page 3, Theorem 2: `Theorem2With` carries exactly the
hypotheses i to iv, so any implication between conclusions transfers. PROVED. -/
theorem theorem2With_mono {ε B : ℝ}
    {P P' : (ℝ → ℕ → ℂ) → (ℝ → ℕ → ℂ) → ℝ → ℝ →
      (ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)) → Prop}
    (hPP : ∀ a b u v E, P a b u v E → P' a b u v E) (h : Theorem2With ε B P) :
    Theorem2With ε B P' := by
  intro a b u v E θ₁ θ₂ Y Q I J h1 h2 h3 h4 h5
  exact hPP a b u v E (h a b u v E h1 h2 h3 h4 h5)

end LeanLab.BHP1997.Section2MS
