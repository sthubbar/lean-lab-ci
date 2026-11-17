/-
Split of the diagonal multiplicative window comparison that follows display 2.16.
The two sided fixed additive window is compared with the family of multiplicative
windows whose parameter lies in the printed range from T over 6Y to 6T over Y.
The first leaf rewrites the diagonal window of the target as a window of fixed
length T over 2, the second leaf covers that fixed window by finitely many members
of the family, and the third leaf applies the uniform bound to those members.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_saffari_vaughan561

namespace LeanLab.BHP1997.Decomp561d
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- LEAF. Step one, the rewrite. On the integration range every centre y is
positive, so the factor y times T over 2y is T over 2 and the diagonal window of
the target is the window of fixed length T over 2. The two character sums of
squared integrals are therefore equal, with no estimate and no constant. -/
theorem leaf_diagonal_window_identity561 :
    ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * (T / (2 * y))),
                centered561 Y b v χ m‖ ^ 2) =
          (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
                centered561 Y b v χ m‖ ^ 2) := by
  intro Y T hY hT hTY b v q E
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  apply intervalIntegral.integral_congr
  intro y hy
  have hab : Y - T / 2 ≤ 3 * Y - T / 4 := by linarith
  rw [Set.uIcc_of_le hab] at hy
  have hypos : 0 < y := by linarith [hy.1]
  have hz : y * (T / (2 * y)) = T / 2 := by
    have hy0 : y ≠ 0 := ne_of_gt hypos
    field_simp
  simp only [hz]

/-- LEAF. Step two, the covering. A window of fixed length T over 2 at a centre
y is covered by finitely many members of the multiplicative family, the members
taken at the three fixed parameters T over 6Y, T over 3Y and 2T over 3Y, each of
them read over the whole printed range of centres. Hence the fixed window moment
is at most a universal constant times the sum of those three family moments, and
the constant does not depend on the character, on the modulus or on the data. -/
theorem leaf_diagonal_fixed_window_cover561 :
    ∃ K : ℝ, 0 < K ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
                centered561 Y b v χ m‖ ^ 2) ≤
          K * (∑ j ∈ Finset.range 3,
                multiplicativeWindowMoment561 Y (T / (6 * Y) * 2 ^ j) b v q E) := by
  sorry

/-- LEAF. Step three, the uniform bound. Each of the three parameters T over 6Y,
T over 3Y and 2T over 3Y lies in the printed range, so the hypothesis bounds each
of the three family moments by the same M and their sum by a universal multiple
of M. No character dependent choice of parameter is made here. -/
theorem leaf_diagonal_ladder_sum_le_bound561 :
    ∃ K : ℝ, 0 < K ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) (M : ℝ),
        0 ≤ M →
        (∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
          multiplicativeWindowMoment561 Y z b v q E ≤ M) →
        (∑ j ∈ Finset.range 3,
            multiplicativeWindowMoment561 Y (T / (6 * Y) * 2 ^ j) b v q E) ≤ K * M := by
  refine ⟨4, by norm_num, ?_⟩
  intro Y T hY hT hTY b v q E M hM hmult
  have hYpos : (0 : ℝ) < Y := by linarith
  have hXY : (0 : ℝ) ≤ T / (6 * Y) := by positivity
  have hkey : ∀ j ∈ Finset.range 3,
      multiplicativeWindowMoment561 Y (T / (6 * Y) * 2 ^ j) b v q E ≤ M := by
    intro j hj
    have hj3 : j < 3 := Finset.mem_range.mp hj
    have h2j1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (a := (2 : ℝ)) (by norm_num)
    have h2j4 : (2 : ℝ) ^ j ≤ 4 := by
      have h2 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
      calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (2 : ℕ) :=
            pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by omega : j ≤ 2)
        _ = 4 := h2
    refine hmult _ ?_ ?_
    · calc T / (6 * Y) = T / (6 * Y) * 1 := by ring
        _ ≤ T / (6 * Y) * (2 : ℝ) ^ j := mul_le_mul_of_nonneg_left h2j1 hXY
    · have hstep : T / (6 * Y) * 4 = 2 * T / (3 * Y) := by
        field_simp
        ring
      calc T / (6 * Y) * (2 : ℝ) ^ j ≤ T / (6 * Y) * 4 :=
            mul_le_mul_of_nonneg_left h2j4 hXY
        _ = 2 * T / (3 * Y) := hstep
        _ ≤ 6 * T / Y := by
            rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * Y) hYpos]
            nlinarith [hT]
  calc ∑ j ∈ Finset.range 3,
        multiplicativeWindowMoment561 Y (T / (6 * Y) * 2 ^ j) b v q E
      ≤ ∑ j ∈ Finset.range 3, M := Finset.sum_le_sum hkey
    _ = 3 * M := by simp
    _ ≤ 4 * M := by linarith

/-- The split target, assembled from the three leaves above. The rewrite turns the
diagonal window into the fixed window, the covering bounds the fixed window by the
three family moments, and the uniform bound bounds those moments by M. The
constant of the assembly is the product of the two covering constants. -/
theorem leaf_multiplicative_windows_bound_diagonal561_split :
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
  obtain ⟨K₁, hK₁pos, hK₁⟩ := leaf_diagonal_fixed_window_cover561
  obtain ⟨K₂, hK₂pos, hK₂⟩ := leaf_diagonal_ladder_sum_le_bound561
  refine ⟨K₁ * K₂, mul_pos hK₁pos hK₂pos, ?_⟩
  intro Y T hY hT hTY b v q E M hM hmult
  calc
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ y in (Y - T / 2)..(3 * Y - T / 4),
          ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * (T / (2 * y))),
            centered561 Y b v χ m‖ ^ 2)
        = (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
                centered561 Y b v χ m‖ ^ 2) :=
          leaf_diagonal_window_identity561 Y T hY hT hTY b v q E
    _ ≤ K₁ * (∑ j ∈ Finset.range 3,
                multiplicativeWindowMoment561 Y (T / (6 * Y) * 2 ^ j) b v q E) :=
          hK₁ Y T hY hT hTY b v q E
    _ ≤ K₁ * (K₂ * M) :=
          mul_le_mul_of_nonneg_left (hK₂ Y T hY hT hTY b v q E M hM hmult) (le_of_lt hK₁pos)
    _ = (K₁ * K₂) * M := by ring

end LeanLab.BHP1997.Decomp561d
