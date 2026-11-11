import LeanLab.LanguascoPerelli1996.Window422

/-!
P0071 pages 355 through 359. Separate the three actual Gallagher regions.
The integer windows are a derived version of the real windows in display 14.
The boundary terms stay explicit as required by Section 5.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp422a
open Real MeasureTheory intervalIntegral

/-- LEAF. Page 356, the leading integral I1 after display 14 and its treatment on page 357.
Derived discrete window estimate for the stopped remainder in page 358 display 21.
Only this region is bounded. The other two regions remain separate obligations.
The character explicit formula and GMCxi cancellation are still required.
Page 358 also uses estimate 3 when the zero cutoff exceeds X. -/
theorem leading_window_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                Window422.leadingMass X Y q a L ≤ B * L * X ^ (1 + ε) := by
  sorry

/-- LEAF. Pages 356 and 357 displays 15 and 16, the interior integral I2.
Derived discrete window estimate for the stopped remainder in page 358 display 21.
Only this region is bounded. The other two regions remain separate obligations.
The character explicit formula and GMCxi cancellation are still required.
Page 358 also uses estimate 3 when the zero cutoff exceeds X. -/
theorem interior_window_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                Window422.interiorMass X Y q a L ≤ B * L * X ^ (1 + ε) := by
  sorry

/-- LEAF. Page 357 displays 17 through 19, the trailing integral I3.
Derived discrete window estimate for the stopped remainder in page 358 display 21.
Only this region is bounded. The other two regions remain separate obligations.
The character explicit formula and GMCxi cancellation are still required.
Page 358 also uses estimate 3 when the zero cutoff exceeds X. -/
theorem trailing_window_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            ∀ L : ℕ, 0 < L → 1 / (4 * (L : ℝ)) ≤ ξ X q →
              ξ X q ≤ 1 / (2 * (L : ℝ)) →
                Window422.trailingMass X Y q a L ≤ B * L * X ^ (1 + ε) := by
  sorry

/-- Pages 358 and 359 displays 21 through 24, assembled from the three
strictly smaller window estimates and the proved discrete Gallagher transfer.
Exactly the existing partial_remainder_mean_square statement.
CONDITIONAL ON the three window leaves. The proof does not use the old leaf. -/
theorem partial_remainder_mean_square_decomposed :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            (∫ t in (-(ξ X q))..(ξ X q), ‖Decomp381a.partialR X Y t q a‖ ^ 2) ≤
              B * ξ X q * X ^ (1 + ε) := by
  intro θ hθ hθ2 ξ hG ε hε
  obtain ⟨A, X1, hA, h1⟩ := leading_window_bound θ hθ hθ2 ξ hG ε hε
  obtain ⟨B, X2, hB, h2⟩ := interior_window_bound θ hθ hθ2 ξ hG ε hε
  obtain ⟨C, X3, hC, h3⟩ := trailing_window_bound θ hθ hθ2 ξ hG ε hε
  refine ⟨Real.pi ^ 2 * (A + B + C), max X1 (max X2 X3), by positivity, ?_⟩
  intro X hX hX1 q inst hq a ha Y hY hY2
  have hx := (hG.2.1 X q).1
  obtain ⟨L, hL, hlo, hhi⟩ := Window422.window_length_exists hx (hG.2.1 X q).2
  have hXone : X1 ≤ X := (le_max_left _ _).trans hX
  have hXtwo : X2 ≤ X := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hX
  have hXthree : X3 ≤ X := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hX
  exact (Window422.remainder_mass_le_windows X Y q a L hL hx hhi).trans
    (Window422.window_scale hL hx hlo (Real.rpow_nonneg (by linarith) _) hA hB hC
      (h1 X hXone hX1 q hq a ha Y hY hY2 L hL hlo hhi)
      (h2 X hXtwo hX1 q hq a ha Y hY hY2 L hL hlo hhi)
      (h3 X hXthree hX1 q hq a ha Y hY hY2 L hL hlo hhi))

end LeanLab.LanguascoPerelli1996.Decomp422a

#print axioms LeanLab.LanguascoPerelli1996.Decomp422a.leading_window_bound
#print axioms LeanLab.LanguascoPerelli1996.Decomp422a.interior_window_bound
#print axioms LeanLab.LanguascoPerelli1996.Decomp422a.trailing_window_bound
#print axioms LeanLab.LanguascoPerelli1996.Decomp422a.partial_remainder_mean_square_decomposed
