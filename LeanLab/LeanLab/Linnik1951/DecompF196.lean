/-
Split of the positive outer Mellin estimate from pages 157 to 159.
The leaves isolate the interval geometry, the oscillatory radial estimate,
the contour integration, and the Mellin representation of the prime sum.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357a

namespace LeanLab.Linnik1951

open scoped ComplexConjugate Classical

/-- The truncation height on the shifted Mellin line. -/
noncomputable def farHeight196 (N q : ℕ) : ℝ :=
  (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3

/-- The complex Mellin kernel used on the shifted line. -/
noncomputable def farMellinKernel196 (M : ℂ → ℂ) (N : ℕ) (t : ℝ)
    (α : ℝ) : ℂ :=
  let σ : ℝ := 1 / 2 + 1 / Real.log N
  let s : ℂ := (σ : ℂ) + t * Complex.I
  let x : ℂ := (1 / (N : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (α : ℂ)
  Complex.cpow x (-s) * Complex.Gamma s * M s

/-- The full vertical Mellin integral on the shifted line. -/
noncomputable def farMellinProfile196 (M : ℂ → ℂ) (N : ℕ) (α : ℝ) : ℂ :=
  if h : MeasureTheory.Integrable (fun t : ℝ => farMellinKernel196 M N t α)
      MeasureTheory.volume then
    (1 / (2 * Real.pi * Complex.I)) *
      ∫ t : ℝ, farMellinKernel196 M N t α
  else
    0

/-- The radial oscillatory kernel in the alpha integration. -/
noncomputable def farRadialKernel196 (N σ : ℝ) (t t₁ : ℝ) (α : ℝ) : ℂ :=
  let x : ℂ := (1 / N : ℂ) + 2 * Real.pi * Complex.I * (α : ℂ)
  Complex.cpow x (-((2 * σ : ℝ) : ℂ) - (t - t₁) * Complex.I)

/-- LEAF. Page 158 equation 4.6 uses the truncation height equal to N
over q times N to one seventh times the logarithm of N cubed. This leaf
records that height as one identity before the oscillatory estimates. -/
theorem far_height_identity196 (N q : ℕ) :
    farHeight196 N q =
      (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3 := by
  rfl

/-- LEAF. Page 158 equation 4.6 applies the second mean value theorem to
the radial kernel. The resulting modulus has the denominator one plus the
absolute difference of the two vertical parameters and the radial factor
bounded by one over the square root of one minus N to the minus two times
u to the minus two. -/
theorem far_radial_oscillation196 (N σ : ℝ) (t t₁ ξ ξ₁ : ℝ)
    (hN : 0 < N) (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hξ1 : ξ < ξ₁)
    (huξ : 8 * Real.pi / N ≤
      Real.sqrt ((1 / N ^ 2) + 4 * Real.pi ^ 2 * ξ ^ 2)) :
    ‖∫ α in ξ..ξ₁, farRadialKernel196 N σ t t₁ α‖ ≤
      (1 / Real.sqrt (1 - 1 / (N ^ 2 *
        (Real.sqrt ((1 / N ^ 2) + 4 * Real.pi ^ 2 * ξ ^ 2)) ^ 2))) *
        (Real.sqrt ((1 / N ^ 2) + 4 * Real.pi ^ 2 * ξ ^ 2)) ^ (1 - 2 * σ) /
          (|t - t₁| + 1) := by
  sorry

/-- LEAF. Page 158 equations 4.4 to 4.7 integrate the vertical parameters
after the radial estimate. Every multiplier with logarithmic growth of
order three then has square integral on the positive outer interval at
most one fixed constant times N over q times N to one seventh times log N
to the tenth for all sufficiently large N. -/
theorem far_contour_integration196
    (hrad : ∀ N : ℕ, 1 < N → ∀ t t₁ ξ ξ₁ : ℝ,
      4 / (N : ℝ) ≤ ξ → ξ < ξ₁ →
        ‖∫ α in ξ..ξ₁, farRadialKernel196 N
          (1 / 2 + 1 / Real.log N) t t₁ α‖ ≤
          (1 / Real.sqrt (1 - 1 / (N ^ 2 *
            (Real.sqrt ((1 / N ^ 2) + 4 * Real.pi ^ 2 * ξ ^ 2)) ^ 2))) *
            (Real.sqrt ((1 / N ^ 2) + 4 * Real.pi ^ 2 * ξ ^ 2)) ^
              (1 - 2 * (1 / 2 + 1 / Real.log N)) / (|t - t₁| + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ C : ℝ, 0 < C → ∀ M : ℂ → ℂ,
          (∀ t : ℝ,
            ‖M (((1 / 2 + 1 / Real.log N : ℝ) : ℂ) + t * Complex.I)‖ ≤
              C * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖farMellinProfile196 M N α‖ ^ 2) ≤
              K * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) *
                Real.log N ^ 10 := by
  sorry

/-- LEAF. Pages 157 to 159 represent the nonprincipal character weighted
prime sum by the vertical Mellin integral on the shifted line. The
multiplier has logarithmic growth of order three on that line. -/
theorem far_mellin_representation196 (hG : LeanLab.DERZ1997.GRH)
    (q N : ℕ) (hN : 1 < N) (hq : 1 ≤ q)
    (hqt : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ))
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ M : ℂ → ℂ, ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ,
        ‖M (((1 / 2 + 1 / Real.log N : ℝ) : ℂ) + t * Complex.I)‖ ≤
          C * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧
      (∀ α : ℝ,
        characterPrime280 χ N α = farMellinProfile196 M N α) := by
  sorry

/-- The positive outer Mellin estimate is assembled from the radial
oscillation estimate, the vertical integration estimate, and the Mellin
representation of the character weighted prime sum. -/
theorem mellin_positive_far357_F196 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  have hrad : ∀ N : ℕ, 1 < N → ∀ t t₁ ξ ξ₁ : ℝ,
      4 / (N : ℝ) ≤ ξ → ξ < ξ₁ →
        ‖∫ α in ξ..ξ₁, farRadialKernel196 N
          (1 / 2 + 1 / Real.log N) t t₁ α‖ ≤
          (1 / Real.sqrt (1 - 1 / (N ^ 2 *
            (Real.sqrt ((1 / N ^ 2) + 4 * Real.pi ^ 2 * ξ ^ 2)) ^ 2))) *
            (Real.sqrt ((1 / N ^ 2) + 4 * Real.pi ^ 2 * ξ ^ 2)) ^
              (1 - 2 * (1 / 2 + 1 / Real.log N)) / (|t - t₁| + 1) := by
    intro N hN t t₁ ξ ξ₁ hξ hξ₁
    apply far_radial_oscillation196 N (1 / 2 + 1 / Real.log N) t t₁ ξ ξ₁
    · positivity
    · have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
      have hinv : 0 < 1 / Real.log N := one_div_pos.mpr hlog
      linarith
    · have hNpos : 0 < (N : ℝ) := by positivity
      exact lt_of_le_of_lt (by positivity) hξ
    · exact hξ₁
    · apply (Real.le_sqrt' (by positivity)).2
      have hξsq : (4 / N) ^ 2 ≤ ξ ^ 2 := by
        have hξ0 : 0 ≤ ξ := le_of_lt (by positivity)
        have h4 : 0 ≤ 4 / N := by positivity
        exact mul_self_le_mul_self h4 hξ
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
  obtain ⟨K, hK, N0, hN0⟩ := far_contour_integration196 hrad
  refine ⟨K, hK, max 1 N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have hN1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  obtain ⟨M, C, hC, hM, hrepr⟩ :=
    far_mellin_representation196 hG q N hN1 hq hqt χ hχ
  have hbound := hN0 N (lt_of_lt_of_le hN (le_max_right _ _)) q hq hqt C hC M hM
  have hfun : (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) =
      (fun α : ℝ => ‖farMellinProfile196 M N α‖ ^ 2) := by
    funext α
    rw [hrepr α]
  rw [hfun]
  exact hbound

end LeanLab.Linnik1951
