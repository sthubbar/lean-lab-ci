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

Leaves 2, 3 and 4 are proved here; leaf 1 is open. `akeno_thm1_3_split` is proved from
the four leaves with no direct `sorry` and does not use the sealed statement.

The comparison lemmas below show why logarithmic savings alone do not supply leaf 1.
The slower envelope `X exp(-(log X)^{1/200})` has every logarithmic saving but exceeds
every constant multiple of the requested envelope at arbitrarily large `X`.
Taking its natural floor gives the same obstruction for natural-valued counts below
the trivial floor bound. These comparisons do not give an estimate for `excCount`.
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

/-- The slower envelope still has every logarithmic saving. This is a real-variable
comparison, not an exceptional-set estimate. -/
theorem leaf_slower_exp_decay_log_powers320 (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 200)) ≤ C * X / Real.log X ^ A := by
  obtain ⟨B, hBpos, hB⟩ := leaf_exp_decay_aux 1 (2 * A) (by linarith)
  refine ⟨B, hBpos, ?_⟩
  intro X hX
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogle : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hlogpos : 0 < Real.log X := lt_of_lt_of_le hlog2pos hlogle
  have hu : Real.log 2 ≤ Real.sqrt (Real.log X) := by
    nlinarith [Real.sq_sqrt hlogpos.le, Real.sqrt_nonneg (Real.log X)]
  have hpow : Real.sqrt (Real.log X) ^ (2 * A) = Real.log X ^ A := by
    rw [← Real.rpow_div_two_eq_sqrt (2 * A) hlogpos.le]
    congr 1
    ring
  have hdecay : Real.sqrt (Real.log X) ^ ((1 : ℝ) / 100) =
      Real.log X ^ ((1 : ℝ) / 200) := by
    rw [← Real.rpow_div_two_eq_sqrt ((1 : ℝ) / 100) hlogpos.le]
    norm_num
  have hb := hB (Real.sqrt (Real.log X)) hu
  rw [hpow, hdecay, one_mul] at hb
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogpos A)).2
  calc
    X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 200)) * Real.log X ^ A =
        (Real.log X ^ A * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 200))) * X := by ring
    _ ≤ B * X := mul_le_mul_of_nonneg_right hb (by linarith)

/-- No constant and threshold compare the slower envelope to the one in leaf 1.
This does not assert that the actual exceptional count is as large as either envelope. -/
theorem leaf_slower_exp_decay_not_bounded320 (C X₀ : ℝ) :
    ∃ X : ℝ, 2 ≤ X ∧ X₀ ≤ X ∧
      C * X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 100)) <
        X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 200)) := by
  have hsmall : Filter.Tendsto (fun X : ℝ => Real.log X ^ ((1 : ℝ) / 200))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp Real.tendsto_log_atTop
  have hsq (X : ℝ) (hX : 2 ≤ X) :
      (Real.log X ^ ((1 : ℝ) / 200)) ^ 2 = Real.log X ^ ((1 : ℝ) / 100) := by
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
    norm_num
  have hexponent : Filter.Tendsto
      (fun X : ℝ => Real.log X ^ ((1 : ℝ) / 100) - Real.log X ^ ((1 : ℝ) / 200))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ hsmall
    filter_upwards [hsmall.eventually_ge_atTop 2, Filter.eventually_ge_atTop (2 : ℝ)] with X hu hX
    nlinarith [hsq X hX]
  have hratio := Real.tendsto_exp_atTop.comp hexponent
  obtain ⟨X, hX, hC⟩ :=
    ((Filter.eventually_ge_atTop (max 2 X₀)).and (hratio.eventually_gt_atTop C)).exists
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  refine ⟨X, hX2, le_trans (le_max_right _ _) hX, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hC
    (Real.exp_pos (-(Real.log X) ^ ((1 : ℝ) / 100)))
  have heq :
      Real.exp (Real.log X ^ ((1 : ℝ) / 100) - Real.log X ^ ((1 : ℝ) / 200)) *
          Real.exp (-(Real.log X) ^ ((1 : ℝ) / 100)) =
        Real.exp (-(Real.log X) ^ ((1 : ℝ) / 200)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Function.comp_apply, heq] at hmul
  convert mul_lt_mul_of_pos_left hmul (by linarith : 0 < X) using 1
  ring

/-- Even a natural-valued count below the trivial floor bound can have every logarithmic
saving without the stretched exponential saving of leaf 1. The witness is the floor of the
slower envelope, not the actual product-form exceptional count. -/
theorem leaf_log_savings_insufficient320 :
    ∃ E : ℝ → ℕ,
      (∀ X : ℝ, 2 ≤ X → E X ≤ ⌊X⌋₊) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
        (E X : ℝ) ≤ C * X / Real.log X ^ A) ∧
      ¬ (∃ C X₀ : ℝ, 0 ≤ C ∧ 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
        (E X : ℝ) ≤ C * X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 100))) := by
  let f : ℝ → ℝ := fun X => X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 200))
  have hf_nonneg (X : ℝ) (hX : 2 ≤ X) : 0 ≤ f X := by
    dsimp [f]
    positivity
  have hf_le (X : ℝ) (hX : 2 ≤ X) : f X ≤ X := by
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hexp : Real.exp (-(Real.log X) ^ ((1 : ℝ) / 200)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg hlog _))
    simpa [f] using mul_le_mul_of_nonneg_left hexp (by linarith : 0 ≤ X)
  have hf_top : Filter.Tendsto f Filter.atTop Filter.atTop := by
    have hhalf : Filter.Tendsto (fun X : ℝ => Real.log X / 2) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.atTop_div_const (by norm_num)
    have hdiff : Filter.Tendsto
        (fun X : ℝ => Real.log X - Real.log X ^ ((1 : ℝ) / 200))
        Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono' _ ?_ hhalf
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 4] with X hX
      have hlog : 0 ≤ Real.log X := by linarith
      have hsmall : Real.log X ^ ((1 : ℝ) / 200) ≤ Real.sqrt (Real.log X) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      nlinarith [Real.sq_sqrt hlog, Real.sqrt_nonneg (Real.log X)]
    refine (Real.tendsto_exp_atTop.comp hdiff).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with X hX
    have hpos : 0 < X := by linarith
    simp only [Function.comp_apply, f, Real.exp_sub, Real.exp_neg, Real.exp_log hpos,
      div_eq_mul_inv]
  refine ⟨fun X => ⌊f X⌋₊, ?_, ?_, ?_⟩
  · intro X hX
    exact Nat.floor_mono (hf_le X hX)
  · intro A hA
    obtain ⟨C, hC, hbound⟩ := leaf_slower_exp_decay_log_powers320 A hA
    exact ⟨C, hC, fun X hX => le_trans (Nat.floor_le (hf_nonneg X hX)) (hbound X hX)⟩
  · rintro ⟨C, X₀, -, -, hbound⟩
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hf_top.eventually_ge_atTop 2)
    obtain ⟨X, hX2, hXmax, hlt⟩ :=
      leaf_slower_exp_decay_not_bounded320 (2 * C) (max M X₀)
    have hf2 : 2 ≤ f X := hM X (le_trans (le_max_left _ _) hXmax)
    have hlower : f X / 2 ≤ (⌊f X⌋₊ : ℝ) := by
      linarith [Nat.lt_floor_add_one (f X)]
    have hupper := hbound X (le_trans (le_max_right _ _) hXmax)
    change 2 * C * X * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 100)) < f X at hlt
    linarith

/-- LEAF 1 of 4, the analytic half: from some threshold `X₀ ≥ 2` on, the integers `N` in the
window `(X/2, X]` divisible by `6` which are not a sum of two primes `p₁ + p₂` with
`2 p₁ p₂ + 1` in `P₁₃` number at most `C X e^{-(log X)^{1/100}}`. This asks for a weighted
sieve estimate stronger than the logarithmic exceptional rate stated in the paper's
Lemma 4.6 and Theorem 1.3. Lemma 4.5 has this exponential exceptional rate for a different
quadratic-character condition. No uniformity in `A` is asked of this leaf. -/
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
