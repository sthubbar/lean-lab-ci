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

/-- Auxiliary bound for leaf 2: the function `u ↦ c u^A e^{-u^{1/100}}` is bounded above on the
half line `[log 2, ∞)`. It tends to `0` at infinity, because `u^A` grows slower than
`e^{u^{1/100}}`, and it is continuous, so it is bounded on `[log 2, M]` by the extreme value
theorem and by `1` beyond `M`. -/
private theorem leaf_exp_decay_aux (c A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, Real.log 2 ≤ u →
      c * u ^ A * Real.exp (-(u ^ ((1 : ℝ) / 100))) ≤ B := by
  have hcont : Continuous fun u : ℝ => c * u ^ A * Real.exp (-(u ^ ((1 : ℝ) / 100))) := by
    refine (continuous_const.mul (Real.continuous_rpow_const hA.le)).mul ?_
    exact Real.continuous_exp.comp (continuous_neg.comp (Real.continuous_rpow_const (by norm_num)))
  have htend : Filter.Tendsto (fun u : ℝ => c * u ^ A * Real.exp (-(u ^ ((1 : ℝ) / 100))))
      Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 100)) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    have hbase : Filter.Tendsto
        (fun x : ℝ => c * (x ^ (100 * A) * Real.exp (-1 * x))) Filter.atTop (nhds 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (100 * A) 1
        (one_pos : (0 : ℝ) < 1)).const_mul c
      simpa using h
    refine (hbase.comp hsub).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    simp only [Function.comp_apply]
    have hrw : (u ^ ((1 : ℝ) / 100)) ^ (100 * A) = u ^ A := by
      rw [← Real.rpow_mul hu]
      have : (1 : ℝ) / 100 * (100 * A) = A := by ring
      rw [this]
    rw [hrw]
    ring
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ u : ℝ, M ≤ u →
      c * u ^ A * Real.exp (-(u ^ ((1 : ℝ) / 100))) ≤ 1 := by
    have h := htend.eventually (eventually_le_nhds (zero_lt_one : (0 : ℝ) < 1))
    rwa [Filter.eventually_atTop] at h
  obtain ⟨u₀, -, hu₀max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (le_max_right M (Real.log 2))) hcont.continuousOn
  refine ⟨max 1 (c * u₀ ^ A * Real.exp (-(u₀ ^ ((1 : ℝ) / 100)))) + 1, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max 1 (c * u₀ ^ A * Real.exp (-(u₀ ^ ((1 : ℝ) / 100)))) := le_max_left _ _
    linarith
  · intro u hu
    rcases le_total u (max M (Real.log 2)) with hle | hgt
    · have hmem : u ∈ Set.Icc (Real.log 2) (max M (Real.log 2)) := ⟨hu, hle⟩
      have h1 : c * u ^ A * Real.exp (-(u ^ ((1 : ℝ) / 100))) ≤
          c * u₀ ^ A * Real.exp (-(u₀ ^ ((1 : ℝ) / 100))) := hu₀max hmem
      have h2 : c * u₀ ^ A * Real.exp (-(u₀ ^ ((1 : ℝ) / 100))) ≤
          max 1 (c * u₀ ^ A * Real.exp (-(u₀ ^ ((1 : ℝ) / 100)))) := le_max_right _ _
      linarith
    · have hMu : M ≤ u := le_trans (le_max_left M (Real.log 2)) hgt
      have h1 := hM u hMu
      have h2 : (1 : ℝ) ≤ max 1 (c * u₀ ^ A * Real.exp (-(u₀ ^ ((1 : ℝ) / 100)))) := le_max_left _ _
      linarith

/-- LEAF 2 of 4, the real-variable half: for a fixed `A > 0` and a nonnegative constant `c`, the
decaying factor `e^{-(log t)^{1/100}}` beats every power of the logarithm, so
`c t e^{-(log t)^{1/100}} ≤ C t (log t)^{-A}` for all `t ≥ 2` with one constant `C > 0`. -/
theorem leaf_exp_decay_dominates_log_powers (c A : ℝ) (hA : 0 < A) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      c * t * Real.exp (-(Real.log t) ^ ((1 : ℝ) / 100)) ≤ C * t / Real.log t ^ A := by
  obtain ⟨B, hBpos, hB⟩ := leaf_exp_decay_aux c A hA
  refine ⟨B, hBpos, ?_⟩
  intro t ht
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hu : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hupos : 0 < Real.log t := lt_of_lt_of_le hlog2 hu
  have htu : Real.exp (Real.log t) = t := Real.exp_log (by linarith)
  have key : ∀ u : ℝ, Real.log 2 ≤ u →
      c * Real.exp u * Real.exp (-(u ^ ((1 : ℝ) / 100))) ≤ B * Real.exp u / u ^ A := by
    intro u hu'
    have hupos' : 0 < u := lt_of_lt_of_le hlog2 hu'
    have hPu : (0 : ℝ) < u ^ A := Real.rpow_pos_of_pos hupos' A
    have hgu := hB u hu'
    have h := mul_le_mul_of_nonneg_right hgu
      (le_of_lt (div_pos (Real.exp_pos u) hPu))
    calc c * Real.exp u * Real.exp (-(u ^ ((1 : ℝ) / 100)))
        = c * u ^ A * Real.exp (-(u ^ ((1 : ℝ) / 100))) * (Real.exp u / u ^ A) := by
          field_simp
      _ ≤ B * (Real.exp u / u ^ A) := h
      _ = B * Real.exp u / u ^ A := by ring
  have h1 : c * t * Real.exp (-(Real.log t) ^ ((1 : ℝ) / 100))
      = c * Real.exp (Real.log t) * Real.exp (-(Real.log t) ^ ((1 : ℝ) / 100)) := by
    rw [← htu, Real.log_exp]
  have h3 : B * Real.exp (Real.log t) / Real.log t ^ A = B * t / Real.log t ^ A := by
    rw [htu]
  calc c * t * Real.exp (-(Real.log t) ^ ((1 : ℝ) / 100))
      = c * Real.exp (Real.log t) * Real.exp (-(Real.log t) ^ ((1 : ℝ) / 100)) := h1
    _ ≤ B * Real.exp (Real.log t) / Real.log t ^ A := key (Real.log t) hu
    _ = B * t / Real.log t ^ A := h3

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
