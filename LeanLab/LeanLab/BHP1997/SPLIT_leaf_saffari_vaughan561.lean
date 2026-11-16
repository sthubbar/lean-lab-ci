/-
Independent split of the multiplicative window comparison after display 2.16.
The fixed additive window of half width T over 4 is compared with the
multiplicative windows of the printed z range. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561d

namespace LeanLab.BHP1997.Decomp561d
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- LEAF. First step of the comparison: the lower part of the y range carries no
fixed window at all. The short polynomial is supported above Y while the upper
end y plus T over 4 stays below Y once y is at most Y minus T over 4, so the
filtered sum vanishes there and only the truncated y interval remains. -/
theorem leaf_fixed_window_empty_below561 :
    ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        fixedWindowMoment561 Y T b v q E =
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 4)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
                centered561 Y b v χ m‖ ^ 2 := by
  sorry

/-- LEAF. Second step: the two sided fixed window of half width T over 4 is the
one sided window of length T over 2 read at the translated centre. Shifting the
y variable by T over 4 turns y minus T over 4 into y and y plus T over 4 into
y plus T over 2, so the truncated fixed window integral is the one sided window
integral over the translated interval. -/
theorem leaf_window_translation561 :
    ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 4)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
                centered561 Y b v χ m‖ ^ 2) =
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
                centered561 Y b v χ m‖ ^ 2 := by
  sorry

/-- LEAF. Third step: the one sided window of length T over 2 is the
multiplicative window of the printed shape with the parameter T over 2 y. On the
translated interval every centre y is positive, so y times T over 2 y is T over
2 and the two filtered sums agree term by term. -/
theorem leaf_window_parameter_scale561 :
    ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
                centered561 Y b v χ m‖ ^ 2) ≤
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * (T / (2 * y))),
                centered561 Y b v χ m‖ ^ 2 := by
  intro Y T hY hT hTY b v q E
  refine Finset.sum_le_sum (fun χ _ => ?_)
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro y hy
  have hab : Y - T / 2 ≤ 3 * Y - T / 4 := by linarith
  rw [Set.uIcc_of_le hab] at hy
  have hypos : 0 < y := by linarith [hy.1]
  have hz : y * (T / (2 * y)) = T / 2 := by
    have hy0 : y ≠ 0 := ne_of_gt hypos
    field_simp
  simp only [hz]

/-- LEAF. Fourth step, the comparison itself: a nonnegative uniform bound M for
every multiplicative window whose parameter lies in the printed z range bounds
the translated additive window moment by a universal constant times M. The
parameter T over 2 y stays inside the printed range on the translated interval,
and the additive windows of length T over 2 are covered by finitely many
multiplicative windows of the family, so no pointwise choice of z and no
character dependent constant is needed. OPEN. -/
theorem leaf_multiplicative_windows_bound_diagonal561 :
    ∃ C : ℝ, 0 < C ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) (M : ℝ),
        0 ≤ M →
        (∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
          multiplicativeWindowMoment561 Y z b v q E ≤ M) →
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * (T / (2 * y))),
                centered561 Y b v χ m‖ ^ 2) ≤
          C * M := by
  sorry

/-- The sealed target, assembled from the four leaves above. Step one drops the
empty lower half of the y range, step two translates the two sided fixed window
to the one sided window, step three rewrites its length as a multiplicative
parameter at the centre, and step four applies the multiplicative window bound.
The constant is the one supplied by the last leaf. -/
theorem leaf_saffari_vaughan561_split :
    ∃ V : ℝ, 0 < V ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) (M : ℝ),
        0 ≤ M →
        (∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
          multiplicativeWindowMoment561 Y z b v q E ≤ M) →
        fixedWindowMoment561 Y T b v q E ≤ V * M := by
  obtain ⟨C, hCpos, hC⟩ := leaf_multiplicative_windows_bound_diagonal561
  refine ⟨C, hCpos, ?_⟩
  intro Y T hY hT hTY b v q E M hM hmulti
  exact (leaf_fixed_window_empty_below561 Y T hY hT hTY b v q E).trans_le
    ((leaf_window_translation561 Y T hY hT hTY b v q E).trans_le
      ((leaf_window_parameter_scale561 Y T hY hT hTY b v q E).trans
        (hC Y T hY hT hTY b v q E M hM hmulti)))

end LeanLab.BHP1997.Decomp561d
