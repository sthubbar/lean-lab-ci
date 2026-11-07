/-
Split of `akeno_thm3_1`, the statement

  `∀ θ : ℝ, 0 < θ → θ < 1 / 6 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η`.

`BetaLevel θ η` has two counted sums: the first runs over `m + n = N` with the product
weight `β`, the second over the switched problem `2m + n = N` with odd modulus. Each of
them bounds an exceptional count by `C₁ X (ln X)^{-A}` for one pair of constants `C₁, C₂`.
Inside each sum the admissible ranges of `β` split into the single factor case `k = 1`,
where the ranges are pinned to `lo i = 1` and `hi i = X` and `β` is `Λ` on `[1, ⌊X⌋]`, and
the multi factor case `1 < k`, where the ranges satisfy `X ^ η < lo i < hi i ≤ 2 lo i` and
`∏ i, lo i ≤ X`. The two cases are proved by different arguments, so they are separate
leaves:

  LEAF 1: first sum, single factor ranges.
  LEAF 2: first sum, multi factor ranges.
  LEAF 3: second switched sum, single factor ranges.
  LEAF 4: second switched sum, multi factor ranges.

Each leaf carries the whole `∃ η₀, ∀ η ≤ η₀` shape of the target for its own piece, so
`akeno_thm3_1_split` takes the smallest of the four thresholds, and for each `X`, each
`A` and each admissible range takes the larger of the constants: raising the constant of
the threshold inside `excCount` can only remove exceptions, which is `split_excCount_le_const`
below. The assembly uses no `sorry` and does not use `akeno_thm3_1`.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026
open Real Finset
open scoped ContDiff ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-! ### Elementary bookkeeping for the assembly -/

/-- Multiplying an inequality by the nonnegative factor `X / L` preserves it. -/
private theorem split_div_const_mono {X L c c' : ℝ} (hX : 0 ≤ X) (hL : 0 < L) (h : c ≤ c') :
    c * X / L ≤ c' * X / L := by
  have h0 : 0 ≤ X / L := div_nonneg hX (le_of_lt hL)
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right h h0

/-- The exception count at a larger threshold constant is at most the count at a smaller
one, at the same scale `X / L`. -/
private theorem split_excCount_le_const {S : ℕ → Prop} {f : ℕ → ℝ} {X L c c' : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (h : c ≤ c') :
    excCount S (fun N => f N ≤ c' * X / L) X ≤
      excCount S (fun N => f N ≤ c * X / L) X :=
  excCount_mono (fun _ _ hN => le_trans hN (split_div_const_mono hX hL h)) X

private theorem split_le_max_four_a {a b c d : ℝ} : a ≤ max a (max b (max c d)) :=
  le_max_left a _

private theorem split_le_max_four_b {a b c d : ℝ} : b ≤ max a (max b (max c d)) :=
  le_trans (le_max_left b (max c d)) (le_max_right a (max b (max c d)))

private theorem split_le_max_four_c {a b c d : ℝ} : c ≤ max a (max b (max c d)) :=
  le_trans (le_max_left c d)
    (le_trans (le_max_right b (max c d)) (le_max_right a (max b (max c d))))

private theorem split_le_max_four_d {a b c d : ℝ} : d ≤ max a (max b (max c d)) :=
  le_trans (le_max_right c d)
    (le_trans (le_max_right b (max c d)) (le_max_right a (max b (max c d))))

/-! ### The four leaves -/

/-- LEAF 1 of the split. The first sum of `BetaLevel` in the single factor range
`k = 1`, `lo i = 1`, `hi i = X`, where `β` is `Λ` on `[1, ⌊X⌋]`: the threshold `η₀` is
produced here, and for every `η ∈ (0, η₀]`, every factor count, every pair of smooth
weights supported in `[η, 1]` and every `A > 0` there are constants `C₁, C₂` such that for
every `X ≥ 2` the `betaSum`-exceptions among all integers of `(X/2, X]` number at most
`C₁ X (ln X)^{-A}`. -/
theorem leaf_first_sum_single_factor :
    ∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ k : ℕ, 1 ≤ k → ∀ w₁ w₂ : ℝ → ℝ, SmoothWeight η w₁ → SmoothWeight η w₂ →
          ∀ A : ℝ, 0 < A → ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ lo hi : Fin k → ℝ,
            (k = 1 ∧ ∀ i, lo i = 1 ∧ hi i = X) →
              (excCount (fun _ => True)
                  (fun N => betaSum θ (beta k lo hi) w₁ w₂ X N ≤
                    C₂ * X / Real.log X ^ A) X : ℝ)
                ≤ C₁ * X / Real.log X ^ A := by
  sorry

/-- LEAF 2 of the split. The first sum of `BetaLevel` in the multi factor range
`1 < k`, `X ^ η < lo i < hi i ≤ 2 lo i`, `∏ i, lo i ≤ X`: the same conclusion as LEAF 1,
now for a product of `k ≥ 2` von Mangoldt factors, where the threshold `η₀` has to be
small enough for the ranges themselves to satisfy `X ^ η < lo i`. -/
theorem leaf_first_sum_multi_factor :
    ∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ k : ℕ, 1 ≤ k → ∀ w₁ w₂ : ℝ → ℝ, SmoothWeight η w₁ → SmoothWeight η w₂ →
          ∀ A : ℝ, 0 < A → ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ lo hi : Fin k → ℝ,
            (1 < k ∧ (∀ i, X ^ η < lo i ∧ lo i < hi i ∧ hi i ≤ 2 * lo i) ∧
              ∏ i, lo i ≤ X) →
              (excCount (fun _ => True)
                  (fun N => betaSum θ (beta k lo hi) w₁ w₂ X N ≤
                    C₂ * X / Real.log X ^ A) X : ℝ)
                ≤ C₁ * X / Real.log X ^ A := by
  sorry

/-- LEAF 3 of the split. The second, switched sum of `BetaLevel`, `2m + n = N` over odd
modulus `d`, in the single factor range `k = 1`, `lo i = 1`, `hi i = X`: its threshold
`η₀` and its constants are produced here, with `β` reducing to `Λ` as in LEAF 1. -/
theorem leaf_second_sum_single_factor :
    ∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ k : ℕ, 1 ≤ k → ∀ w₁ w₂ : ℝ → ℝ, SmoothWeight η w₁ → SmoothWeight η w₂ →
          ∀ A : ℝ, 0 < A → ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ lo hi : Fin k → ℝ,
            (k = 1 ∧ ∀ i, lo i = 1 ∧ hi i = X) →
              (excCount (fun _ => True)
                  (fun N => betaSum' θ (beta k lo hi) w₁ w₂ X N ≤
                    C₂ * X / Real.log X ^ A) X : ℝ)
                ≤ C₁ * X / Real.log X ^ A := by
  sorry

/-- LEAF 4 of the split. The second, switched sum of `BetaLevel` in the multi factor range
`1 < k`: the same conclusion as LEAF 3 for a product of `k ≥ 2` von Mangoldt factors. -/
theorem leaf_second_sum_multi_factor :
    ∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ k : ℕ, 1 ≤ k → ∀ w₁ w₂ : ℝ → ℝ, SmoothWeight η w₁ → SmoothWeight η w₂ →
          ∀ A : ℝ, 0 < A → ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ lo hi : Fin k → ℝ,
            (1 < k ∧ (∀ i, X ^ η < lo i ∧ lo i < hi i ∧ hi i ≤ 2 * lo i) ∧
              ∏ i, lo i ≤ X) →
              (excCount (fun _ => True)
                  (fun N => betaSum' θ (beta k lo hi) w₁ w₂ X N ≤
                    C₂ * X / Real.log X ^ A) X : ℝ)
                ≤ C₁ * X / Real.log X ^ A := by
  sorry

/-! ### Assembly -/

/-- The assembled statement: `∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η`, from the four leaves,
without using `akeno_thm3_1`. The threshold is the smallest of the four thresholds, and
each admissible range is dispatched to the leaf that covers its case, at the larger
constant. -/
theorem akeno_thm3_1_split :
    ∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η := by
  intro θ hθ hθ6
  obtain ⟨η₁, hη₁, H₁⟩ := leaf_first_sum_single_factor θ hθ hθ6
  obtain ⟨η₂, hη₂, H₂⟩ := leaf_first_sum_multi_factor θ hθ hθ6
  obtain ⟨η₃, hη₃, H₃⟩ := leaf_second_sum_single_factor θ hθ hθ6
  obtain ⟨η₄, hη₄, H₄⟩ := leaf_second_sum_multi_factor θ hθ hθ6
  refine ⟨min η₁ (min η₂ (min η₃ η₄)), ?_, ?_⟩
  · exact lt_min hη₁ (lt_min hη₂ (lt_min hη₃ hη₄))
  · intro η hη hηle
    have hle₁ : η ≤ η₁ := le_trans hηle (min_le_left η₁ (min η₂ (min η₃ η₄)))
    have hle₂ : η ≤ η₂ := le_trans hηle
      (le_trans (min_le_right η₁ (min η₂ (min η₃ η₄))) (min_le_left η₂ (min η₃ η₄)))
    have hle₃ : η ≤ η₃ := le_trans hηle
      (le_trans (min_le_right η₁ (min η₂ (min η₃ η₄)))
        (le_trans (min_le_right η₂ (min η₃ η₄)) (min_le_left η₃ η₄)))
    have hle₄ : η ≤ η₄ := le_trans hηle
      (le_trans (min_le_right η₁ (min η₂ (min η₃ η₄)))
        (le_trans (min_le_right η₂ (min η₃ η₄)) (min_le_right η₃ η₄)))
    intro k hk w₁ w₂ hw₁ hw₂ A hA
    obtain ⟨C₁a, C₂a, Ha⟩ := H₁ η hη hle₁ k hk w₁ w₂ hw₁ hw₂ A hA
    obtain ⟨C₁b, C₂b, Hb⟩ := H₂ η hη hle₂ k hk w₁ w₂ hw₁ hw₂ A hA
    obtain ⟨C₁c, C₂c, Hc⟩ := H₃ η hη hle₃ k hk w₁ w₂ hw₁ hw₂ A hA
    obtain ⟨C₁d, C₂d, Hd⟩ := H₄ η hη hle₄ k hk w₁ w₂ hw₁ hw₂ A hA
    refine ⟨max C₁a (max C₁b (max C₁c C₁d)),
      max C₂a (max C₂b (max C₂c C₂d)), ?_⟩
    intro X hX lo hi hAdm
    have hX0 : (0 : ℝ) < X := by linarith
    have hL : (0 : ℝ) < Real.log X ^ A :=
      Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A
    have hC₁a : C₁a ≤ max C₁a (max C₁b (max C₁c C₁d)) := split_le_max_four_a
    have hC₁b : C₁b ≤ max C₁a (max C₁b (max C₁c C₁d)) := split_le_max_four_b
    have hC₁c : C₁c ≤ max C₁a (max C₁b (max C₁c C₁d)) := split_le_max_four_c
    have hC₁d : C₁d ≤ max C₁a (max C₁b (max C₁c C₁d)) := split_le_max_four_d
    have hC₂a : C₂a ≤ max C₂a (max C₂b (max C₂c C₂d)) := split_le_max_four_a
    have hC₂b : C₂b ≤ max C₂a (max C₂b (max C₂c C₂d)) := split_le_max_four_b
    have hC₂c : C₂c ≤ max C₂a (max C₂b (max C₂c C₂d)) := split_le_max_four_c
    have hC₂d : C₂d ≤ max C₂a (max C₂b (max C₂c C₂d)) := split_le_max_four_d
    refine ⟨?_, ?_⟩
    · rcases hAdm with h1 | h2
      · exact le_trans (Nat.cast_le.mpr (split_excCount_le_const hX0.le hL hC₂a))
          (le_trans (Ha X hX lo hi h1) (split_div_const_mono hX0.le hL hC₁a))
      · exact le_trans (Nat.cast_le.mpr (split_excCount_le_const hX0.le hL hC₂b))
          (le_trans (Hb X hX lo hi h2) (split_div_const_mono hX0.le hL hC₁b))
    · rcases hAdm with h1 | h2
      · exact le_trans (Nat.cast_le.mpr (split_excCount_le_const hX0.le hL hC₂c))
          (le_trans (Hc X hX lo hi h1) (split_div_const_mono hX0.le hL hC₁c))
      · exact le_trans (Nat.cast_le.mpr (split_excCount_le_const hX0.le hL hC₂d))
          (le_trans (Hd X hX lo hi h2) (split_div_const_mono hX0.le hL hC₁d))

end LeanLab.Akeno2026
