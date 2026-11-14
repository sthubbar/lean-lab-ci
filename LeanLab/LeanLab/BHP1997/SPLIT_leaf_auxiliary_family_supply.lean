/-
Split of `leaf_auxiliary_family_supply` in LeanLab.BHP1997.SPLIT_lower_mean_value_supply
into leaves. The sealed leaf is unchanged; it is neither imported under another name nor used.

The claim asks for an auxiliary family `b` with a divisor-count bound, the character mean
value on both heights, the normalised reference density and the absolute approximation of
the sifted family on the window. This split takes the auxiliary family to be the sifted
family itself. Then the absolute approximation is exact (the defect vanishes identically)
and the divisor-count bound is exactly the hypothesis, so the two remaining steps are the
mean value at one fixed height and the reference average, the latter split between the
non-principal and the principal characters because the normalising factor is one only for
the principal character.

Every leaf is OPEN. AI wrote the Lean code. The split is a re-cut: the mean value and the
density are asserted for the sifted family, so all of the analytic content sits in those
three leaves, and the hypothesis used is only the divisor-count bound.
-/
import LeanLab.BHP1997.SPLIT_lower_mean_value_supply

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- LEAF 1 of 3. The character mean value at one fixed height. For a height `σ` in
`{-1, 1}` the integral of the character-weighted sum of the sifted family over the short
height interval is at most `C * x^(1/2) * (log x)^(-A)`. Only one height at a time, so
this is strictly easier than the mean value of the claim, which asks both heights with one
pair of constants. Non-vacuous: the conclusion is an upper bound, satisfied for a family
that vanishes, and the hypotheses are met by `c0 = 0`. -/
theorem leaf_mean_value_at_fixed_height
    (B0 : ℝ) (hB0 : 1 ≤ B0) (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (c0 : ℝ → ℕ → ℝ)
    (hc0 : ∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ B0)
    (σ : ℝ) (hσ : σ ∈ ({-1, 1} : Finset ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
          ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
            (section4SiftedFamily c0 x k : ℂ) * χ (k : ZMod q) /
              (k : ℂ) ^ Thm4.half (σ * t)‖) ≤
          C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 3. The reference average at the non-principal characters. For a character
other than the principal one the normalising factor is zero, so the claim is that the
window average of the sifted family is at most `C * (log x)^(-A)` with no main term at all.
This is the cancellation half of the density step and does not mention `u0`. Non-vacuous:
it is an upper bound and the hypotheses on `c0` are unused. -/
theorem leaf_nonprincipal_reference_average (c0 : ℝ → ℕ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ‖referenceAverage (section4SiftedFamily c0) x χ‖ ≤ C * Real.log x ^ (-A) := by
  sorry

/-- LEAF 3 of 3. The reference average at the principal character. For the principal
character the normalising factor is one, so the window average of the sifted family must
equal `u0 / log x` up to any logarithmic saving. This is the main term half of the density
step, and it is the only leaf that mentions `u0`. Non-vacuous: it is an estimate with a
free constant, and the hypotheses on `c0` are unused. -/
theorem leaf_principal_reference_average (u0 : ℝ) (c0 : ℝ → ℕ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 →
        ‖referenceAverage (section4SiftedFamily c0) x χ - (u0 : ℂ) / (Real.log x : ℂ)‖ ≤
          C * Real.log x ^ (-A) := by
  sorry

/-- The assembly, with nothing open. The same statement as the sealed leaf, proved from
the three leaves above and never from the sealed leaf. The auxiliary family is the sifted
family: the divisor-count bound is the hypothesis, the two heights of the mean value come
from leaf 1 with the constants added in absolute value, the reference average splits on
whether the character is principal (leaves 2 and 3), and the absolute approximation is
zero because the two families coincide. Each constant is enlarged only after `x ≥ 1` is
forced, so every real power that appears is nonnegative. -/
theorem leaf_auxiliary_family_supply_split
    (B0 : ℝ) (hB0 : 1 ≤ B0) (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (u0 : ℝ) (hu0 : 0.9953 < u0) (hu01 : u0 ≤ 1)
    (c0 : ℝ → ℕ → ℝ)
    (hc0 : ∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ B0) :
    ∃ b : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u0 b ∧
      ShortApproximation ε (section4SiftedFamily c0) b := by
  refine ⟨section4SiftedFamily c0, hc0, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨C₁, X₁, h1⟩ :=
      leaf_mean_value_at_fixed_height B0 hB0 ε hε hε10 c0 hc0 1 (by simp) A hA
    obtain ⟨C₂, X₂, h2⟩ :=
      leaf_mean_value_at_fixed_height B0 hB0 ε hε hε10 c0 hc0 (-1) (by simp) A hA
    refine ⟨|C₁| + |C₂|, max (max X₁ X₂) 1, ?_⟩
    intro x hx q hq hlog χ σ hσ
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hxX : max X₁ X₂ ≤ x := le_trans (le_max_left _ _) hx
    have hhalf : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hlogA : 0 ≤ Real.log x ^ (-A) :=
      Real.rpow_nonneg (Real.log_nonneg hx1) _
    have hC₁ : C₁ ≤ |C₁| + |C₂| := by
      have h₁ := le_abs_self C₁
      have h₂ := abs_nonneg C₂
      linarith
    have hC₂ : C₂ ≤ |C₁| + |C₂| := by
      have h₁ := le_abs_self C₂
      have h₂ := abs_nonneg C₁
      linarith
    have hσ' : σ = -1 ∨ σ = 1 := by simpa using hσ
    rcases hσ' with rfl | rfl
    · exact (h2 x (le_trans (le_max_right _ _) hxX) q hq hlog χ).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂ hhalf) hlogA)
    · exact (h1 x (le_trans (le_max_left _ _) hxX) q hq hlog χ).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hhalf) hlogA)
  · intro A hA
    obtain ⟨C₁, X₁, h1⟩ := leaf_nonprincipal_reference_average c0 A hA
    obtain ⟨C₂, X₂, h2⟩ := leaf_principal_reference_average u0 c0 A hA
    refine ⟨|C₁| + |C₂|, max (max X₁ X₂) 1, ?_⟩
    intro x hx q hq hlog χ
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hxX : max X₁ X₂ ≤ x := le_trans (le_max_left _ _) hx
    have hlogA : 0 ≤ Real.log x ^ (-A) :=
      Real.rpow_nonneg (Real.log_nonneg hx1) _
    have hC₁ : C₁ ≤ |C₁| + |C₂| := by
      have h₁ := le_abs_self C₁
      have h₂ := abs_nonneg C₂
      linarith
    have hC₂ : C₂ ≤ |C₁| + |C₂| := by
      have h₁ := le_abs_self C₂
      have h₂ := abs_nonneg C₁
      linarith
    by_cases hχ : χ = 1
    · have h₀ := h2 x (le_trans (le_max_right _ _) hxX) q hq hlog χ hχ
      simp only [Thm2.delta, if_pos hχ, one_mul] at h₀ ⊢
      exact h₀.trans (mul_le_mul_of_nonneg_right hC₂ hlogA)
    · have h₀ := h1 x (le_trans (le_max_left _ _) hxX) q hq hlog χ hχ
      simp only [Thm2.delta, if_neg hχ, zero_mul, zero_div, sub_zero] at h₀ ⊢
      exact h₀.trans (mul_le_mul_of_nonneg_right hC₁ hlogA)
  · intro A hA
    refine ⟨0, 0, ?_⟩
    intro x hx
    simp

end LeanLab.BHP1997.Decomp312a
