import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_cor42_window_extension131

/-!
Split of `leaf_exceptional_absolute131` of `SPLIT_cor42_window_extension131`.

The target asks for one absolute constant `A` with
`|binaryMajor131 X n P| ≤ A n Sing n` on the whole window `[X/2, X]`, for the `n` that the
exceptional set covers, uniformly in the major arc parameter `P` and in the exceptional set `E`
with its two parameters `K₁` and `c`.

The argument here is a scale and window decomposition, with the same constant demanded of each
piece:

* `leaf_exceptional_absolute_finite_scale131`: the scales `X ≤ 3`. The window is empty for
  `X ≤ 1` and is `{2}` for `X = 2, 3`, so only two values of `n` and one value of the integral
  are involved and a single constant dominates them.
* `leaf_exceptional_absolute_upper_part131`: the scales `X ≥ 4` and the part of the window
  above `2X/3`, that is the part `J(X)` of the relative estimate.
* `leaf_exceptional_absolute_lower_part131`: the scales `X ≥ 4` and the part of the window
  below `2X/3`, the strip that `J(X)` does not see.

Every piece is a proper restriction of the target: a smaller set of scales or a smaller set of
`n`. `leaf_exceptional_absolute131_split` below is proved from the three pieces with no `sorry`,
does not use the target, and takes the maximum of the three constants.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- LEAF. The small scales `X ≤ 3`: the bound holds with a constant that may depend on nothing,
because at these scales the window `[X/2, X]` contains only the even integer `2` (and no integer
at all for `X ≤ 1`), so the set of integrals to dominate is finite. -/
theorem leaf_exceptional_absolute_finite_scale131 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E → X ≤ 3 →
      ∀ n ∈ evenWindow131 X, ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  sorry

/-- LEAF. The scales `X ≥ 4` on the upper part of the window, `2X/3 ≤ n`: the same absolute
bound, restricted to the `n` that the relative estimate already reaches. -/
theorem leaf_exceptional_absolute_upper_part131 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E → 4 ≤ X →
      ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 ≤ n → ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  sorry

/-- LEAF. The scales `X ≥ 4` on the strip `n < 2X/3` of the window, the part the estimate on
`J(X)` does not reach: the same absolute bound on that strip. -/
theorem leaf_exceptional_absolute_lower_part131 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E → 4 ≤ X →
      ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  sorry

/-- The split target: the same statement as `leaf_exceptional_absolute131`, proved from the three
leaves above and not from the target. The constants are compared with `max`, and `n * Sing n` is
nonnegative, so the largest of the three constants serves the whole window and every scale. -/
theorem leaf_exceptional_absolute131_split :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E →
      ∀ n ∈ evenWindow131 X, ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := leaf_exceptional_absolute_finite_scale131
  obtain ⟨A₂, -, hA₂⟩ := leaf_exceptional_absolute_upper_part131
  obtain ⟨A₃, -, hA₃⟩ := leaf_exceptional_absolute_lower_part131
  refine ⟨max A₁ (max A₂ A₃), le_trans hA₁0 (le_max_left _ _), ?_⟩
  intro X Cstar K₁ c P E hc hAdm hExc n hn hnone
  have hstep : ∀ A' : ℝ, A' ≤ max A₁ (max A₂ A₃) →
      |binaryMajor131 X n P| ≤ A' * n * Sing n →
      |binaryMajor131 X n P| ≤ max A₁ (max A₂ A₃) * n * Sing n := by
    intro A' hle h
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ (Sing_nonneg131 n))
    exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg n)
  by_cases hX : X ≤ 3
  · exact hstep A₁ (le_max_left _ _) (hA₁ X Cstar K₁ c P E hc hAdm hExc hX n hn hnone)
  · have h3 : 3 < X := lt_of_not_ge hX
    have h4 : 4 ≤ X := h3
    by_cases hge : 2 * (X : ℝ) / 3 ≤ n
    · refine hstep A₂ ?_ (hA₂ X Cstar K₁ c P E hc hAdm hExc h4 n hn hge hnone)
      exact le_trans (le_max_left A₂ A₃) (le_max_right A₁ (max A₂ A₃))
    · refine hstep A₃ ?_
        (hA₃ X Cstar K₁ c P E hc hAdm hExc h4 n hn (lt_of_not_ge hge) hnone)
      exact le_trans (le_max_right A₂ A₃) (le_max_right A₁ (max A₂ A₃))

#print axioms LeanLab.LPZ2007.leaf_exceptional_absolute131_split

end

end LeanLab.LPZ2007
