/-
Split of `akeno_thm1_3` of `LeanLab.Akeno2026.Statements` into four leaves.

`akeno_thm1_3` asserts `AlmostAllDyadic (fun N => 6 ∣ N) (ProdForm 13)`, that is: for every
`A > 0` there is `C` with, for every `X ≥ 2`, at most `C X (log X)^{-A}` integers
`N ∈ (X/2, X]` divisible by `6` fail to be a sum of two primes `p₁ + p₂` with
`2 p₁ p₂ + 1` a product of at most thirteen primes.

The split follows the laboratory route for this conclusion. The weighted sieve applied to the
Goldbach primes produces an exceptional set that is much smaller than any power of a logarithm,
but only from a threshold on `X`; the range below that threshold is settled by the trivial
count `excCount ≤ ⌊X⌋`, and the two are glued by the real-variable comparison
`t e^{-(log t)^{1/100}} ≪ t (log t)^{-A}`.

* LEAF 1, the analytic half: the exceptional set of the product form, among the `N` divisible
  by `6`, is `O(X e^{-(log X)^{1/100}})` from some threshold `X₀ ≥ 2` on.
* LEAF 2, the real-variable half: `c t e^{-(log t)^{1/100}}` is dominated by `C t (log t)^{-A}`
  for every `A > 0` and every `t ≥ 2`, so leaf 1 gives all logarithmic savings at once.
* LEAF 3, the bounded range: below the threshold the trivial count gives the same shape of
  bound, with the single constant `(log X₀)^A`.
* LEAF 4, the count itself: `excCount` never exceeds `⌊X⌋`, which is what leaf 3 uses.

Leaves 3 and 4 are proved here; leaves 1 and 2 are open. `akeno_thm1_3_split` is proved from
the four leaves with no `sorry` and does not use the sealed statement.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026

open Real Finset

open scoped ContDiff ArithmeticFunction.vonMangoldt

/-- LEAF 4 of 4, the count: the number of exceptions in the window `(X/2, X]` among the
integers up to `⌊X⌋` never exceeds `⌊X⌋` itself, whatever the two properties are. This is the
trivial bound used below the threshold of leaf 1. -/
theorem leaf_excCount_le_floor (S P : ℕ → Prop) (X : ℝ) :
    excCount S P X ≤ ⌊X⌋₊ := by
  classical
  unfold excCount
  have h := Finset.card_filter_le (Finset.Icc 1 ⌊X⌋₊)
    (fun N : ℕ => X / 2 < (N : ℝ) ∧ S N ∧ ¬ P N)
  rw [Nat.card_Icc] at h
  omega

/-- LEAF 3 of 4, the bounded range below the threshold: for `X` in `[2, X₀]` the trivial count
gives `excCount ≤ ⌊X⌋ ≤ (log X₀)^A · X / (log X)^A`, since `0 < log X ≤ log X₀`. Only this
range is asserted; no decay is claimed. -/
theorem leaf_small_range_bound (X₀ : ℝ) (_hX₀ : 2 ≤ X₀) (A : ℝ) (hA : 0 < A) (X : ℝ)
    (hX : 2 ≤ X) (hle : X ≤ X₀) :
    (excCount (fun N => 6 ∣ N) (ProdForm 13) X : ℝ) ≤
      Real.log X₀ ^ A * X / Real.log X ^ A := by
  classical
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hcount : (excCount (fun N => 6 ∣ N) (ProdForm 13) X : ℝ) ≤ X := by
    have h1 := leaf_excCount_le_floor (fun N => 6 ∣ N) (ProdForm 13) X
    have h2 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0
    have h3 : (excCount (fun N => 6 ∣ N) (ProdForm 13) X : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
      exact_mod_cast h1
    exact le_trans h3 h2
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogle : Real.log X ≤ Real.log X₀ := Real.log_le_log (by linarith) hle
  have hpow : Real.log X ^ A ≤ Real.log X₀ ^ A := Real.rpow_le_rpow hlogX.le hlogle hA.le
  have hpos : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
  have hratio : 1 ≤ Real.log X₀ ^ A / Real.log X ^ A := by
    rw [le_div_iff₀ hpos]
    simpa using hpow
  calc (excCount (fun N => 6 ∣ N) (ProdForm 13) X : ℝ) ≤ X := hcount
    _ = X * 1 := by ring
    _ ≤ X * (Real.log X₀ ^ A / Real.log X ^ A) := mul_le_mul_of_nonneg_left hratio hX0
    _ = Real.log X₀ ^ A * X / Real.log X ^ A := by ring

/-- LEAF 2 of 4, the real-variable half: for a fixed `A > 0` and a nonnegative constant `c`, the
decaying factor `e^{-(log t)^{1/100}}` beats every power of the logarithm, so
`c t e^{-(log t)^{1/100}} ≤ C t (log t)^{-A}` for all `t ≥ 2` with one constant `C > 0`. -/
theorem leaf_exp_decay_dominates_log_powers (c A : ℝ) (hA : 0 < A) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      c * t * Real.exp (-(Real.log t) ^ ((1 : ℝ) / 100)) ≤ C * t / Real.log t ^ A := by
  sorry

/-- LEAF 1 of 4, the analytic half: from some threshold `X₀ ≥ 2` on, the integers `N` in the
window `(X/2, X]` divisible by `6` which are not a sum of two primes `p₁ + p₂` with
`2 p₁ p₂ + 1` in `P₁₃` number at most `C X e^{-(log X)^{1/100}}`. This is the product form
estimate of the weighted sieve; no uniformity in `A` is asked of it. -/
theorem leaf_sieve_exception_decay :
    ∃ (C X₀ : ℝ), 0 ≤ C ∧ 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      (excCount (fun N => 6 ∣ N) (ProdForm 13) X : ℝ) ≤
        C * X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 100)) := by
  sorry

/-- Assembly: `akeno_thm1_3` from the four leaves. Write `C` for the larger of the constant of
leaf 2 and `(log X₀)^A`. For `X ≥ X₀` the decay of leaf 1 is turned into the logarithmic
saving by leaf 2; for `2 ≤ X ≤ X₀` the trivial count of leaf 4, through leaf 3, gives the same
bound, because `log X ≤ log X₀`. -/
theorem akeno_thm1_3_split : AlmostAllDyadic (fun N => 6 ∣ N) (ProdForm 13) := by
  classical
  intro A hA
  obtain ⟨C₀, X₀, hC₀, hX₀, hdecay⟩ := leaf_sieve_exception_decay
  obtain ⟨C₁, hC₁pos, hC₁⟩ := leaf_exp_decay_dominates_log_powers C₀ A hA hC₀
  refine ⟨max C₁ (Real.log X₀ ^ A), ?_⟩
  intro X hX
  rcases le_total X X₀ with h | h
  · refine le_trans (leaf_small_range_bound X₀ hX₀ A hA X hX h) ?_
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hpos : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
    have hmax : Real.log X₀ ^ A ≤ max C₁ (Real.log X₀ ^ A) := le_max_right _ _
    have hmono : Real.log X₀ ^ A * X / Real.log X ^ A ≤
        max C₁ (Real.log X₀ ^ A) * X / Real.log X ^ A := by
      gcongr
    exact hmono
  · refine le_trans (hdecay X h) ?_
    refine le_trans (hC₁ X hX) ?_
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hpos : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
    have hmax : C₁ ≤ max C₁ (Real.log X₀ ^ A) := le_max_left _ _
    gcongr

end LeanLab.Akeno2026
