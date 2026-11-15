import Mathlib

/-!
The repair record for the branch free-ms-leanstral/task507.

That branch tried to close `LeanLab.KumchevLiu2007.Task516a.eq53_large_eps` by splitting on
`5 / 6 ≤ ε` and claiming that in that case the window set `windowPairs` of display 53 is empty,
so that the error term `err53` vanishes and the count is zero. The claim is false. The window
height is `Y = X ^ (7 / 12 + ε / 2)` and the window set is empty only when the spacing
`Y ^ (1 / 4)` beats `X + H`, whose exponent in `X` is `(7 / 12 + ε / 2) / 4`. At `ε = 5 / 6`
that exponent is `1 / 4`, far below the `1` the branch assumed, and the window set at `X = 2`
contains the pair `(0, 1)`. The two statements below record the refutation, so the branch's two
inner `sorry`s are not a split of the leaf but the gap of a false case split.

This file is imported by nothing and adds no definition. `Decomp516a` keeps main's blob, so
`eq53_large_eps` stays open with main's single `sorry`.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task507

/-- The branch's case `5 / 6 ≤ ε` assumed the window exponent `(7 / 12 + ε / 2) / 4` exceeds
`1`, so that the window spacing `Y ^ (1 / 4)` beats `X + H`. At `ε = 5 / 6` the exponent is
`1 / 4`, so the step fails at the left end of the very case the branch claimed.
Source: arXiv 0801.0130 page 16 display 53, with the window height `Y = X ^ (7 / 12 + ε / 2)`
of page 15. -/
theorem windowExponent_not_gt_one_at_five_sixths :
    ¬ (1 : ℝ) < (7 / 12 + (5 / 6) / 2) * (1 / 4) := by
  norm_num

/-- The window set of display 53 at `X = 2` and `ε = 5 / 6` is not empty: it contains the pair
`(0, 1)`, that is `n = 1` with `v.1 = 0` and `v.2 = 1`. So the branch's
`windowPairs_empty_of_big_eps` fails at `ε = 5 / 6`, and `err53` does not vanish there.
Source: arXiv 0801.0130 page 16 display 53, with window support `X - Y ≤ v.1 < X` and
`Y ^ (1 / 2) / 2 ≤ v.2 < Y ^ (1 / 2)`. -/
theorem windowPairs_nonempty_at_five_sixths :
    ((Finset.range (⌊(2 : ℝ)⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2))⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        (2 : ℝ) - (2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2) ≤ (v.1 : ℝ) ∧
        (v.1 : ℝ) < 2 ∧
        Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) ∧
        v.1 + v.2 ^ 2 = 1) ≠ ∅ := by
  have hexp : (7 / 12 : ℝ) + (5 / 6) / 2 = 1 := by norm_num
  have hY : (2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2) = 2 := by
    rw [hexp, Real.rpow_one]
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hfloor : ⌊Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2))⌋₊ = 1 := by
    rw [hY, Nat.floor_eq_iff (Real.sqrt_nonneg 2)]
    exact ⟨by norm_num, by norm_num⟩
  have hnat : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_natCast 2
  intro h
  have hmem : (0, 1) ∈
      ((Finset.range (⌊(2 : ℝ)⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2))⌋₊ + 1))).filter
        (fun v : ℕ × ℕ =>
          (2 : ℝ) - (2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2) ≤ (v.1 : ℝ) ∧
          (v.1 : ℝ) < 2 ∧
          Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) / 2 ≤ (v.2 : ℝ) ∧
          (v.2 : ℝ) < Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) ∧
          v.1 + v.2 ^ 2 = 1) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · rw [Finset.mem_range]
      omega
    · rw [hY]
      show (2 : ℝ) - 2 ≤ ((0 : ℕ) : ℝ)
      norm_num
    · show ((0 : ℕ) : ℝ) < 2
      norm_num
    · rw [hY]
      show Real.sqrt 2 / 2 ≤ ((1 : ℕ) : ℝ)
      norm_num
      linarith
    · rw [hY]
      show ((1 : ℕ) : ℝ) < Real.sqrt 2
      norm_num
      exact hs1
    · show (0 : ℕ) + 1 ^ 2 = 1
      norm_num
  rw [h] at hmem
  simp at hmem

end LeanLab.KumchevLiu2007.Task507
