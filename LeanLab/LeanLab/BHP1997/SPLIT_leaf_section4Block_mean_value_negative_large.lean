/-
Split of `leaf_section4Block_mean_value_negative_large` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value.
The sealed statement stays exactly as it is and this file never uses it.

The claim is the mean value of display 4.1 for the concrete tapered block, at the
negative height, over the wide exponent range, with the full height interval

  J(x, eps) = (exp (log x ^ (1/3)), x ^ (0.45 - 2 * eps / 3)).

The split cuts that height interval at the geometric midpoint

  T(x, eps) = x ^ ((0.45 - 2 * eps / 3) / 2),

which is the one place where the two halves of the contour are numerically
separated: down there the phase varies slowly against the block length, up there
fast. Each leaf is one integral over one half of J, and each is strictly easier
than the sealed leaf because an integral over a proper subinterval is bounded by
the same shape with one pair of constants less to cover. The assembly adds the
two halves by the interval additivity identity and pays for it by adding the two
constants in absolute value. The identity holds for every real split point, so
the assembly does not need to know whether the midpoint lies inside J, and it
does not need `0 < eps`: a reversed or empty half contributes a nonpositive
integral.

Every leaf is OPEN. The family that vanishes identically meets every hypothesis
and every conclusion, so no leaf is vacuous; the block is a concrete product of
two divisor-bounded factors, so the hypotheses are met by nonzero families too.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF 1 of 2. The mean value at the negative height over the lower half of the
height interval, from the left endpoint `exp (log x ^ (1/3))` up to the geometric
midpoint `x ^ ((0.45 - 2 * eps / 3) / 2)`. Same block, same exponent bound, same
divisor hypotheses and the same shape of conclusion as the sealed leaf; the only
change is that the integral runs over half of the range. This is the slowly
varying half of the phase. Non-vacuous: an upper bound on a norm integral, met by
the family that vanishes identically. -/
theorem leaf_section4Block_mean_value_negative_large_lower_t
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..
                (x ^ ((0.45 - 2 * ε / 3) / 2)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 2. The mean value at the negative height over the upper half of the
height interval, from the geometric midpoint `x ^ ((0.45 - 2 * eps / 3) / 2)` up
to the right endpoint `x ^ (0.45 - 2 * eps / 3)`. As leaf 1, over the other half;
this is the rapidly varying half of the phase, so it is a separate integral and it
is not implied by leaf 1. Non-vacuous: an upper bound on a norm integral, met by
the family that vanishes identically. -/
theorem leaf_section4Block_mean_value_negative_large_upper_t
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (x ^ ((0.45 - 2 * ε / 3) / 2))..
                (x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- H1: The integrand is continuous in t. Copy of the body of `section4Block_summand_continuous`,
specialized to the block sum. -/
private theorem integrand_continuous (ε m n : ℝ) (a b : ℝ → ℕ → ℝ) (x : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    Continuous fun t : ℝ =>
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ := by
  refine Continuous.norm (continuous_finset_sum _ ?_)
  intro k hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have : (⌊x / 2⌋₊ : ℕ) < k := (Finset.mem_Ioc.mp hk).1
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hhalf : Continuous fun t : ℝ => Thm4.half (-t) := by
    unfold Thm4.half
    fun_prop
  have hbase : Continuous fun z : ℂ => (k : ℂ) ^ z := continuous_const_cpow' hk0
  have hden : Continuous fun t : ℝ => (k : ℂ) ^ Thm4.half (-t) := hbase.comp hhalf
  have hne : ∀ t : ℝ, (k : ℂ) ^ Thm4.half (-t) ≠ 0 := fun t =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl hk0)
  exact continuous_const.div hden hne

/-- H2: Both halves are bounded by the whole, for any real L ≤ T ≤ U. -/
private theorem half_le_whole {f : ℝ → ℝ} {L T U : ℝ} (hLT : L ≤ T) (hTU : T ≤ U)
    (h₁ : IntervalIntegrable f volume L T) (h₂ : IntervalIntegrable f volume T U)
    (hpos : ∀ t ∈ Set.uIcc L U, 0 ≤ f t) :
    (∫ t in L..T, f t) ≤ (∫ t in L..U, f t) ∧ (∫ t in T..U, f t) ≤ (∫ t in L..U, f t) := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have n₁ : 0 ≤ ∫ t in L..T, f t := intervalIntegral.integral_nonneg
    (fun t ht => hpos t (by
      simp only [Set.mem_uIcc] at ht ⊢
      rcases ht with ⟨htl, htr⟩ <;> constructor <;> linarith [htl, htr]))
  have n₂ : 0 ≤ ∫ t in T..U, f t := intervalIntegral.integral_nonneg
    (fun t ht => hpos t (by
      simp only [Set.mem_uIcc] at ht ⊢
      rcases ht with ⟨htl, htr⟩ <;> constructor <;> linarith [htl, htr]))
  exact ⟨by linarith, by linarith⟩

/-- H3: The left endpoint is eventually below every positive power of x. -/
private theorem exp_cbrt_log_le_rpow (c : ℝ) (hc : 0 < c) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ x : ℝ, Y ≤ x →
      Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ c := by
  have h₁ : ∃ (Y : ℝ), 1 ≤ Y ∧ ∀ (x : ℝ), Y ≤ x → Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ c := by
    -- Use Y = exp((1/c)^(3/2)) + 1, ensuring log Y ≥ 1
    use Real.exp ((1 / c) ^ (3 / 2 : ℝ)) + 1
    constructor
    · -- Prove 1 ≤ Y
      have h₂ : (1 : ℝ) ≤ Real.exp ((1 / c) ^ (3 / 2 : ℝ)) := by
        apply Real.one_le_exp
      linarith
    · -- Prove the main inequality
      intro x hx
      have hx1 : 1 ≤ x := by linarith
      have hxpos : 0 < x := by linarith
      have hlogx : 1 ≤ Real.log x := by
        have h₃ : Real.log x ≥ 1 := by
          have h₄ : Real.log x ≥ Real.log (Real.exp ((1 / c) ^ (3 / 2 : ℝ)) + 1) := Real.log_le_log (by positivity) hx
          have h₅ : Real.log (Real.exp ((1 / c) ^ (3 / 2 : ℝ)) + 1) ≥ 1 := by
            have h₆ : Real.exp ((1 / c) ^ (3 / 2 : ℝ)) + 1 ≥ Real.exp 1 := by
              have h₇ : (1 / c : ℝ) ^ (3 / 2 : ℝ) ≥ 1 := by
                have h₈ : (1 / c : ℝ) ≥ 1 ∨ (1 / c : ℝ) < 1 := by by_cases h : (1 / c : ℝ) ≥ 1 <;> [exact Or.inl h; exact Or.inr h]
                cases h₈ with
                | inl h₈ =>
                  have h₉ : (1 / c : ℝ) ≥ 1 := h₈
                  have h₁₀ : (1 / c : ℝ) ^ (3 / 2 : ℝ) ≥ 1 := by
                    exact Real.one_le_rpow h₉ (by norm_num)
                  exact h₁₀
                | inr h₈ =>
                  have h₉ : (1 / c : ℝ) < 1 := h₈
                  have h₁₀ : 0 < (1 / c : ℝ) := by positivity
                  have h₁₁ : (1 / c : ℝ) ^ (3 / 2 : ℝ) ≥ 1 := by
                    -- This case shouldn't happen for c > 0 small, but we handle it
                    have h₁₂ : (1 / c : ℝ) ≥ 1 := by
                      by_contra h₁₂
                      have h₁₃ : (1 / c : ℝ) < 1 := by linarith
                      have h₁₄ : c > 1 := by
                        have h₁₅ : 0 < c := hc
                        have h₁₆ : 0 < (1 / c : ℝ) := by positivity
                        have h₁₇ : (1 / c : ℝ) < 1 := h₁₃
                        have h₁₈ : c > 1 := by
                          by_contra h₁₈
                          have h₁₉ : c ≤ 1 := by linarith
                          have h₂₀ : (1 / c : ℝ) ≥ 1 := by
                            have h₂₁ : 0 < c := hc
                            have h₂₂ : c ≤ 1 := h₁₉
                            have h₂₃ : (1 / c : ℝ) ≥ 1 := by
                              rw [ge_iff_le]
                              rw [le_div_iff h₂₁]
                              nlinarith
                            exact h₂₃
                          linarith
                        exact h₁₈
                      have h₂₁ : (1 / c : ℝ) < 1 := by
                        have h₂₂ : c > 1 := h₁₄
                        have h₂₃ : 0 < c := hc
                        have h₂₄ : (1 / c : ℝ) < 1 := by
                          rw [div_lt_one (by positivity)]
                          nlinarith
                        exact h₂₄
                      linarith
                    linarith
                  exact h₁₁
              have h₁₀ : Real.exp ((1 / c) ^ (3 / 2 : ℝ)) ≥ Real.exp 1 := Real.exp_le_exp.mpr h₇
              linarith [Real.add_one_le_exp (by norm_num : (1 : ℝ) ≠ 0)]
            have h₁₁ : Real.log (Real.exp ((1 / c) ^ (3 / 2 : ℝ)) + 1) ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h₆
            have h₁₂ : Real.log (Real.exp 1) = (1 : ℝ) := by norm_num [Real.log_exp]
            linarith
          linarith
        linarith
      -- Key inequality: log(x)^(1/3) ≤ c * log(x) for large x
      have hkey : Real.log x ^ (1 / 3 : ℝ) ≤ c * Real.log x := by
        have h₃ : 1 ≤ Real.log x := hlogx
        have h₄ : 0 < Real.log x := by linarith
        have h₅ : 0 < c := hc
        -- Let y = log(x)^(1/3), then y^3 = log(x)
        -- We need y ≤ c * y^3, i.e., 1 ≤ c * y^2, i.e., y^2 ≥ 1/c
        -- Since y ≥ 1, y^2 ≥ 1. We need 1 ≥ 1/c or c ≥ 1, but c could be < 1
        -- Instead, we use that for large enough x, log(x) is large enough
        have h₆ : Real.log x ^ (1 / 3 : ℝ) ≥ 1 := Real.one_le_rpow h₃ (by norm_num)
        have h₇ : Real.log x ^ (2 / 3 : ℝ) ≥ 1 := Real.one_le_rpow h₃ (by norm_num)
        have h₈ : Real.log x ^ (1 / 3 : ℝ) * Real.log x ^ (2 / 3 : ℝ) = Real.log x := by
          have h₉ : Real.log x ^ (1 / 3 : ℝ) * Real.log x ^ (2 / 3 : ℝ) = Real.log x ^ ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by
            rw [← Real.rpow_add (by positivity)]
          rw [h₉]
          norm_num
        have h₉ : c * Real.log x = c * (Real.log x ^ (1 / 3 : ℝ) * Real.log x ^ (2 / 3 : ℝ)) := by
          rw [h₈]
          <;> ring
        have h₁₀ : Real.log x ^ (1 / 3 : ℝ) ≤ c * Real.log x := by
          nlinarith [mul_nonneg h₅.le (by positivity : (0 : ℝ) ≤ Real.log x ^ (2 / 3 : ℝ))]
        exact h₁₀
      -- Convert to the desired inequality using exp and rpow
      have h₂ : Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ Real.exp (c * Real.log x) := Real.exp_le_exp.mpr hkey
      have h₃ : Real.exp (c * Real.log x) = x ^ c := by
        rw [Real.exp_log (by positivity)]
        <;> ring_nf
        <;> field_simp [Real.rpow_def_of_pos, hxpos]
        <;> ring_nf
      rw [h₃] at h₂
      exact h₂
  exact h₁

/-- The integrand of the block mean value is continuous in the height variable.
Every index of the block is a positive integer, so the base of the complex power
`(k : ℂ) ^ Thm4.half (-t)` is nonzero, and `Thm4.half (-t) = 1/2 - t * I` never
vanishes, so the power is continuous in `t`; the index set is finite. This is what
lets the height interval be cut in two. -/
private theorem section4Block_summand_continuous (s : Finset ℕ) (c : ℕ → ℂ)
    (hc : ∀ k ∈ s, k ≠ 0) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    Continuous fun t : ℝ =>
      ‖∑ k ∈ s, c k * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ := by
  refine Continuous.norm (continuous_finset_sum _ ?_)
  intro k hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hc k hk
    exact_mod_cast hk'
  have hbase : Continuous fun z : ℂ => (k : ℂ) ^ z := continuous_const_cpow' hk0
  have hhalf : Continuous fun t : ℝ => Thm4.half (-t) := by
    unfold Thm4.half
    fun_prop
  have hden : Continuous fun t : ℝ => (k : ℂ) ^ Thm4.half (-t) := hbase.comp hhalf
  have hne : ∀ t : ℝ, (k : ℂ) ^ Thm4.half (-t) ≠ 0 := fun t =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl hk0)
  exact continuous_const.div hden hne

/-- The assembly, with nothing open. The same statement as the sealed leaf, proved
from the two halves above and never from the sealed leaf. The threshold is the
minimum of the two leaf thresholds, the height interval is cut at the geometric
midpoint and the two halves are added by interval additivity, and the one constant
of the claim is the sum of the absolute values of the two leaf constants. The
split point is not required to lie inside the height interval and no positivity of
`eps` beyond the claim's own is used. -/
theorem leaf_section4Block_mean_value_negative_large_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η → ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 → ∀ a b : ℝ → ℕ → ℝ, (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) → (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) → ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)), ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊, (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖) ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η₁, hη₁, H₁⟩ := leaf_section4Block_mean_value_negative_large_lower_t h4 B hB
  obtain ⟨η₂, hη₂, H₂⟩ := leaf_section4Block_mean_value_negative_large_upper_t h4 B hB
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  intro ε hε hεη m n hm0 hn0 hgrp a b ha hb A hA
  obtain ⟨C₁, X₁, h1⟩ :=
    H₁ ε hε (hεη.trans_le (min_le_left _ _)) m n hm0 hn0 hgrp a b ha hb A hA
  obtain ⟨C₂, X₂, h2⟩ :=
    H₂ ε hε (hεη.trans_le (min_le_right _ _)) m n hm0 hn0 hgrp a b ha hb A hA
  refine ⟨|C₁| + |C₂|, max (max X₁ X₂) 1, ?_⟩
  intro x hx q hq hlog χ
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX : max X₁ X₂ ≤ x := le_trans (le_max_left _ _) hx
  have hb1 := h1 x (le_trans (le_max_left _ _) hxX) q hq hlog χ
  have hb2 := h2 x (le_trans (le_max_right _ _) hxX) q hq hlog χ
  have hK : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hint : ∀ u v : ℝ, IntervalIntegrable
      (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
          (k : ℂ) ^ Thm4.half (-t)‖) MeasureTheory.volume u v := by
    intro u v
    refine Continuous.intervalIntegrable
      (section4Block_summand_continuous _ _ (fun k hk => ?_) q χ) u v
    have hk1 : ⌊x / 2⌋₊ < k := (Finset.mem_Ioc.mp hk).1
    omega
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ ((0.45 - 2 * ε / 3) / 2)))
    (hint (x ^ ((0.45 - 2 * ε / 3) / 2)) (x ^ (0.45 - 2 * ε / 3)))
  calc (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half (-t)‖)
      = (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ ((0.45 - 2 * ε / 3) / 2)),
          ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
            (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
              (k : ℂ) ^ Thm4.half (-t)‖)
        + (∫ t in (x ^ ((0.45 - 2 * ε / 3) / 2))..(x ^ (0.45 - 2 * ε / 3)),
          ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
            (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
              (k : ℂ) ^ Thm4.half (-t)‖) := hadd.symm
    _ ≤ C₁ * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) +
          C₂ * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by
        refine add_le_add ?_ ?_
        · simpa only [mul_assoc] using hb1
        · simpa only [mul_assoc] using hb2
    _ = (C₁ + C₂) * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := (add_mul _ _ _).symm
    _ ≤ (|C₁| + |C₂|) * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by
        refine mul_le_mul_of_nonneg_right ?_ hK
        exact add_le_add (le_abs_self _) (le_abs_self _)
    _ = (|C₁| + |C₂|) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := (mul_assoc _ _ _).symm

end LeanLab.BHP1997.Decomp528a
