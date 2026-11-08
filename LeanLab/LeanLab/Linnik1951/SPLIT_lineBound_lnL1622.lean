/-
Split of lineBound_lnL1622 into five leaves. The line bound of the logarithm of the
L-function of a nonprincipal character is cut into the vanishing statement on the
line, the continuity of the logarithm there, and the size of the logarithm, the last
taken in three ranges of the height: bounded, short and tall. The assembly at the end
has no sorry and does not use lineBound_lnL1622.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mellin_transfer1622

namespace LeanLab.Linnik1951

/-- LEAF. Vanishing step. Under the hypothesis on the zeros of the L-functions, the
L-function of a nonprincipal character does not vanish anywhere on the line
1/2 + 1/ln N + i t, for N at least two. The line lies to the right of the critical
line, so a zero there would either be a zero of the open strip with real part
different from one half, which the hypothesis excludes, or a zero with real part at
least one, where the Euler product converges. This step carries no continuity
statement and no size estimate. -/
theorem lnL_ne_zero_on_line1622 (hG : LeanLab.DERZ1997.GRH) :
    ∀ N : ℕ, 1 < N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0 := by
  sorry

/-- LEAF. Continuity step. The logarithm of the L-function of a nonprincipal character,
followed along the line, is continuous in the height as soon as it is nowhere zero
there: the L-function is differentiable, the line is continuous in the height, and the
logarithm is continuous away from zero. This step carries no estimate at all. -/
theorem continuous_lnL_line1622 :
    ∀ (N : ℕ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      (∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0) →
        Continuous fun t : ℝ =>
          Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t)) := by
  sorry

/-- LEAF. Size step, bounded height. Under the hypothesis on the zeros, the logarithm
of the L-function on the line is at most a constant independent of everything, times
ln cubed of N times the sum of the height and two, as long as the height stays in the
fixed window of absolute value at most two. The height window is compact, so this is
the part of the size estimate where the height does not grow. -/
theorem lnL_growth_bounded_height1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, |t| ≤ 2 →
          ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  sorry

/-- LEAF. Size step, short height. Under the hypothesis on the zeros, the logarithm of
the L-function on the line is at most a constant times ln cubed of N times the sum of
the height and two, as long as the height is at least two and at most N. Here the
height dominates neither the modulus nor the logarithm of the modulus, so the bound is
read against ln of N alone. -/
theorem lnL_growth_short_height1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, 2 ≤ |t| → |t| ≤ (N : ℝ) →
          ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  sorry

/-- LEAF. Size step, tall height. Under the hypothesis on the zeros, the logarithm of
the L-function on the line is at most a constant times ln cubed of N times the sum of
the height and two, as long as the height is at least N. Here the height dominates the
modulus, so the bound is read against ln of the height alone, and the modulus enters
only through the conductor bound. -/
theorem lnL_growth_tall_height1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, (N : ℝ) ≤ |t| →
          ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  sorry

/-- The five leaves together give the line bound of the logarithm of the L-function:
the line meets no zero, so the logarithm is continuous there, and the three height
ranges carry the size estimate with constants joined by a maximum. -/
theorem lineBound_lnL1622_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          LineBound1622 N B0
            (fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))) := by
  obtain ⟨B1, hB1, N1, h1⟩ := lnL_growth_bounded_height1622 hG
  obtain ⟨B2, hB2, N2, h2⟩ := lnL_growth_short_height1622 hG
  obtain ⟨B3, hB3, N3, h3⟩ := lnL_growth_tall_height1622 hG
  refine ⟨max B1 (max B2 B3), lt_of_lt_of_le hB1 (le_max_left _ _),
    max N1 (max N2 (max N3 1)), ?_⟩
  intro N hN q hqinst hq hqt χ hχ
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : N3 < N :=
    lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNgt : 1 < N :=
    lt_of_le_of_lt
      (le_trans (le_max_right N3 1)
        (le_trans (le_max_right N2 (max N3 1)) (le_max_right N1 (max N2 (max N3 1))))) hN
  refine ⟨continuous_lnL_line1622 N q χ hχ (lnL_ne_zero_on_line1622 hG N hNgt q χ hχ), ?_⟩
  intro t
  have htwo : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hlog : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg
    have h3 : (2 : ℝ) ≤ |t| + 2 := by linarith
    have h0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
    have hmul : (2 : ℝ) * 2 ≤ (N : ℝ) * (|t| + 2) :=
      mul_le_mul htwo h3 (by norm_num) h0
    linarith
  have hcube : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := pow_nonneg hlog 3
  rcases le_total (abs t) 2 with hlow | hhigh
  · exact le_trans (h1 N hN1 q hq hqt χ hχ t hlow)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hcube)
  · rcases le_total (abs t) (N : ℝ) with hshort | htall
    · exact le_trans (h2 N hN2 q hq hqt χ hχ t hhigh hshort)
        (mul_le_mul_of_nonneg_right
          (le_trans (le_max_left _ _) (le_max_right _ _)) hcube)
    · exact le_trans (h3 N hN3 q hq hqt χ hχ t htall)
        (mul_le_mul_of_nonneg_right
          (le_trans (le_max_right _ _) (le_max_right _ _)) hcube)

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.lineBound_lnL1622_split
