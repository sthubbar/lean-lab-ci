/-
Split of `leaf_section4Block_mean_value` in LeanLab.BHP1997.Decomp528a.
The sealed statement stays exactly as it is and this file never uses it.

The claim is the mean value of display 4.1 for the concrete tapered block of pages 26
and 27, at both signs of the height and over the two exponent regions printed there.
The split cuts it along those two independent axes. Each leaf fixes one sign of the
height, so it carries `Thm4.half t` or `Thm4.half (-t)` in place of
`Thm4.half (σ * t)`, and one of the two regions in place of their disjunction. Each
leaf is therefore strictly easier than the sealed leaf, which needs both signs and both
regions with one pair of constants for the whole disjunction. The assembly takes the
minimum of the four thresholds and the sum of the absolute values of the constants, and
it splits on the sign of the height at the point where the disjunction has already been
resolved by the region hypothesis.

Every leaf is OPEN. The family that vanishes identically meets every hypothesis and every
conclusion, so no leaf is vacuous. The paper hypothesis `h4` and the bound `hB` are
carried unchanged from the sealed statement; they play no role in the estimate, and the
same is true there.
-/
import LeanLab.BHP1997.Decomp528a

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF 1 of 4. The mean value at the positive height over the small exponent region.
The second alternative `max m n ≤ 0.46` of the exponent region replaces the disjunction,
and the exponent is the fixed `Thm4.half t` rather than `Thm4.half (σ * t)`. The
conclusion is an upper bound with the same shape as display 4.1, one sign of the height
only, one region only. Non-vacuous: an upper bound on a norm integral, met by the family
that vanishes identically. -/
theorem leaf_section4Block_mean_value_positive_small
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 4. The mean value at the negative height over the small exponent region.
As leaf 1, with the exponent `Thm4.half (-t)` in place of `Thm4.half t`. This is the
conjugate half of the contour on page 25 and it is a separate integral, so it is not
implied by leaf 1. Non-vacuous: an upper bound on a norm integral, met by the family
that vanishes identically. -/
theorem leaf_section4Block_mean_value_negative_small
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 3 of 4. The mean value at the positive height over the large exponent region.
The first alternative `max 0.45 m + max 0.225 n ≤ 0.775` of the exponent region replaces
the disjunction, and the exponent is the fixed `Thm4.half t`. This is the wider range,
where the two coefficients are allowed to be larger at the cost of a smaller second one.
Non-vacuous: an upper bound on a norm integral, met by the family that vanishes
identically. -/
theorem leaf_section4Block_mean_value_positive_large
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 4 of 4. The mean value at the negative height over the large exponent region.
As leaf 3, with the exponent `Thm4.half (-t)` in place of `Thm4.half t`. This is the last
of the four independent faces of the claim: the other sign of the height over the wider
exponent range. Non-vacuous: an upper bound on a norm integral, met by the family that
vanishes identically. -/
theorem leaf_section4Block_mean_value_negative_large
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- The two heights combined for one fixed block, with a full proof. Given the estimate
at the positive height and the estimate at the negative height for the same block, the
mean value of display 4.1 follows: the two thresholds are compared through `min` at the
caller, the two constants are added in absolute value here, and the height sign is read
off the finite set `{-1, 1}`. Enlarging the constant is legitimate only after `x ≥ 1` is
forced, so every real power that appears is nonnegative. -/
private theorem mean_value_of_two_heights (ε : ℝ) (m n : ℝ) (a b : ℝ → ℕ → ℝ)
    (hp : ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
          ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
            (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
              (k : ℂ) ^ Thm4.half t‖) ≤
        C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A))
    (hn : ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
          ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
            (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
              (k : ℂ) ^ Thm4.half (-t)‖) ≤
        C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :
    MeanValue41 ε (section4Block ε m n a b) := by
  intro A hA
  obtain ⟨C₁, X₁, h1⟩ := hp A hA
  obtain ⟨C₂, X₂, h2⟩ := hn A hA
  refine ⟨|C₁| + |C₂|, max (max X₁ X₂) 1, ?_⟩
  intro x hx q hq hlog χ σ hσ
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX : max X₁ X₂ ≤ x := le_trans (le_max_left _ _) hx
  have hhalf : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hlogA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hC₁ : C₁ ≤ |C₁| + |C₂| := by
    have h' := le_abs_self C₁
    have h'' := abs_nonneg C₂
    linarith
  have hC₂ : C₂ ≤ |C₁| + |C₂| := by
    have h' := le_abs_self C₂
    have h'' := abs_nonneg C₁
    linarith
  have hσ' : σ = -1 ∨ σ = 1 := by simpa using hσ
  rcases hσ' with rfl | rfl
  · simpa using
      (h2 x (le_trans (le_max_right _ _) hxX) q hq hlog χ).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂ hhalf) hlogA)
  · simpa using
      (h1 x (le_trans (le_max_left _ _) hxX) q hq hlog χ).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hhalf) hlogA)

/-- The assembly, with nothing open. The same statement as the sealed leaf, proved from
the four leaves above and never from the sealed leaf. The threshold is the minimum of the
four leaves, the region disjunction is resolved by the region hypothesis of the claim, and
the sign of the height is resolved inside `mean_value_of_two_heights`. -/
theorem leaf_section4Block_mean_value_split (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      (max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 ∨ max m n ≤ 0.46) →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        MeanValue41 ε (section4Block ε m n a b) := by
  obtain ⟨η₁, hη₁, H₁⟩ := leaf_section4Block_mean_value_positive_small h4 B hB
  obtain ⟨η₂, hη₂, H₂⟩ := leaf_section4Block_mean_value_negative_small h4 B hB
  obtain ⟨η₃, hη₃, H₃⟩ := leaf_section4Block_mean_value_positive_large h4 B hB
  obtain ⟨η₄, hη₄, H₄⟩ := leaf_section4Block_mean_value_negative_large h4 B hB
  refine ⟨min (min η₁ η₂) (min η₃ η₄), lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hη₄), ?_⟩
  intro ε hε hεη m n hm0 hn0 hgrp a b ha hb
  have hε₁ : ε < η₁ := hεη.trans_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε₂ : ε < η₂ := hεη.trans_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε₃ : ε < η₃ := hεη.trans_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₄ : ε < η₄ := hεη.trans_le (le_trans (min_le_right _ _) (min_le_right _ _))
  by_cases hsm : max m n ≤ 0.46
  · exact mean_value_of_two_heights ε m n a b
      (H₁ ε hε hε₁ m n hm0 hn0 hsm a b ha hb)
      (H₂ ε hε hε₂ m n hm0 hn0 hsm a b ha hb)
  · exact mean_value_of_two_heights ε m n a b
      (H₃ ε hε hε₃ m n hm0 hn0 (hgrp.resolve_right hsm) a b ha hb)
      (H₄ ε hε hε₄ m n hm0 hn0 (hgrp.resolve_right hsm) a b ha hb)

end LeanLab.BHP1997.Decomp528a
