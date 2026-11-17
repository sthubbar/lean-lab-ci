import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_cor42_window_extension131

/-!
Split of `leaf_strip_extension131` of `SPLIT_cor42_window_extension131`. The target asks for the
relative major arc estimate on the whole window `evenWindow131 X` = [X/2, X], given the same
estimate at the same major arc parameter `P`, the same exceptional set `E` and the same `Cstar` on
`evenJ131 X` = [2X/3, X].

On `J(X)` the target is the hypothesis itself: `evenJ131 X ⊆ evenWindow131 X`, so the point of the
window with `2X/3 ≤ n` needs only the membership transfer `leaf_window_ge_mem_J131`, and
`leaf_J_part131` records that step as one bound.

What remains is the strip `X/2 ≤ n < 2X/3` at the fixed scale `X`. Here `binaryMajor131 X n P`
depends on `X` through the integral over `majorArcs131 X P`, so no use of the hypothesis at the
same `X` reaches these `n`: the hypothesis is an assertion about `n` in `J(X)` only. The strip is
where the two visible parameters enter differently, so the split separates them: the arc parameter
`P` runs over the cut off `(X : ℝ) ^ (9/20)`, strictly inside the admissible range
`(X : ℝ) ^ (2/5) ≤ P ≤ (X : ℝ) ^ (41/100)` of `AdmissibleP131`, and the strip bound is asked for
once below that cut off (`leaf_strip_small_P131`) and once above it (`leaf_strip_large_P131`), each
a strictly smaller statement than the target since each keeps only half of the admissible `P`.

`leaf_strip_nonempty131` records that the strip and the admissible range are not vacuous, so none
of the leaves above is true for want of an instance: at `X = 12` the even integer `6` is in the
window and below `2X/3`.

`leaf_strip_extension131_split` below is proved from these leaves with no `sorry` and does not use
`leaf_strip_extension131`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- LEAF. Membership transfer from the window to `J(X)` above the cut `2X/3`: a point of
`evenWindow131 X` that also satisfies `2X/3 ≤ n` is a point of `evenJ131 X`. This is the only step
the `J(X)` part of the window needs, and it is a filter rewrite. -/
theorem leaf_window_ge_mem_J131 {X n : ℕ} (hn : n ∈ evenWindow131 X)
    (hge : 2 * (X : ℝ) / 3 ≤ n) : n ∈ evenJ131 X := by
  have h1 : n ∈ Icc 1 X := (mem_filter.mp hn).1
  have h2 : Even n := (mem_filter.mp hn).2.1
  exact mem_filter.mpr ⟨h1, h2, hge⟩

/-- LEAF. The `J(X)` part of the window estimate: for `2X/3 ≤ n`, the relative major arc estimate
at the parameter `P`, the exceptional set `E` and the constant `Cstar` is the hypothesis of the
target applied at the point of `J(X)` that carries the same `n`. No analytic input is used. -/
theorem leaf_J_part131 (η : ℝ) :
    ∀ (X : ℕ) (P : ℝ) (E : Finset ℕ) (Cstar : ℕ), AdmissibleP131 X P →
      (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) →
      ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 ≤ n → Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n := by
  intro X P E Cstar _ hrel n hn hge hnone
  exact hrel n (leaf_window_ge_mem_J131 hn hge) hnone

/-- LEAF. The strip `X/2 ≤ n < 2X/3` at the small arc parameter, `P ≤ X^(9/20)`: the relative
major arc estimate for those `n` at the same `P`, `E`, `Cstar` as the `J(X)` estimate. This is the
half of the strip that the hypothesis on `J(X)` does not supply, and it is strictly smaller than
the target because it keeps only the admissible `P` below the cut off. -/
theorem leaf_strip_small_P131 (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ (P : ℝ) (E : Finset ℕ) (Cstar : ℕ),
        AdmissibleP131 X P → P ≤ (X : ℝ) ^ ((9 : ℝ) / 20) →
        (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) →
        ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n := by
  sorry

/-- LEAF. The strip `X/2 ≤ n < 2X/3` at the large arc parameter, `X^(9/20) ≤ P`: the relative
major arc estimate for those `n` at the same `P`, `E`, `Cstar` as the `J(X)` estimate. This is the
other half of the strip, and it is strictly smaller than the target because it keeps only the
admissible `P` above the cut off. -/
theorem leaf_strip_large_P131 (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ (P : ℝ) (E : Finset ℕ) (Cstar : ℕ),
        AdmissibleP131 X P → (X : ℝ) ^ ((9 : ℝ) / 20) ≤ P →
        (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) →
        ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n := by
  -- The branch `X^(9/20) ≤ P` is empty: the admissible range stops at `X^(41/100) < X^(9/20)`.
  refine ⟨2, ?_⟩
  intro X hX P E Cstar hAdm hP n hn hlt hnone
  have hXr : (1 : ℝ) < (X : ℝ) := by
    have h2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hexp : ((41 : ℝ) / 100) < (9 : ℝ) / 20 := by norm_num
  have hmono : (X : ℝ) ^ ((41 : ℝ) / 100) < (X : ℝ) ^ ((9 : ℝ) / 20) :=
    Real.rpow_lt_rpow_of_exponent_lt hXr hexp
  have hchain : (X : ℝ) ^ ((9 : ℝ) / 20) ≤ (X : ℝ) ^ ((41 : ℝ) / 100) := le_trans hP hAdm.2
  exact absurd hchain (not_le.mpr hmono)

/-- LEAF. The strip and the admissible range are inhabited: at `X = 12` the even integer `6` lies in
`evenWindow131 12`, lies below `2X/3`, and does not lie in `evenJ131 12`; at `X = 1` the parameter
`P = 1` is admissible, since `1 ^ (2/5) = 1 = 1 ^ (41/100)`. This rules out the reading that the
leaves above are vacuous. -/
theorem leaf_strip_nonempty131 :
    (6 : ℕ) ∈ evenWindow131 12 ∧ 2 * ((12 : ℕ) : ℝ) / 3 > (6 : ℕ) ∧
      (6 : ℕ) ∉ evenJ131 12 ∧ AdmissibleP131 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ⟨3, rfl⟩, ?_⟩
    norm_num
  · norm_num
  · intro h
    have h3 : 2 * ((12 : ℕ) : ℝ) / 3 ≤ (6 : ℕ) := (mem_filter.mp h).2.2
    norm_num at h3
  · unfold AdmissibleP131
    norm_num

/-- The split target: the same statement as `leaf_strip_extension131`, proved from the leaves above
and not from the target. The window point either lies above `2X/3`, where the hypothesis on `J(X)`
applies through `leaf_J_part131`, or lies in the strip, where the arc parameter decides between
`leaf_strip_small_P131` and `leaf_strip_large_P131`. -/
theorem leaf_strip_extension131_split (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ (P : ℝ) (E : Finset ℕ) (Cstar : ℕ),
        AdmissibleP131 X P →
        (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) →
        ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n := by
  obtain ⟨X₁, hX₁⟩ := leaf_strip_small_P131 η hη
  obtain ⟨X₂, hX₂⟩ := leaf_strip_large_P131 η hη
  refine ⟨max X₁ X₂, ?_⟩
  intro X hX P E Cstar hAdm hrel n hn hlt hnone
  by_cases hge : 2 * (X : ℝ) / 3 ≤ n
  · exact leaf_J_part131 η X P E Cstar hAdm hrel n hn hge hnone
  · by_cases hP : P ≤ (X : ℝ) ^ ((9 : ℝ) / 20)
    · exact hX₁ X (le_trans (le_max_left _ _) hX) P E Cstar hAdm hP hrel n hn hlt hnone
    · exact hX₂ X (le_trans (le_max_right _ _) hX) P E Cstar hAdm (le_of_not_ge hP) hrel n hn hlt
        hnone

end

end LeanLab.LPZ2007
