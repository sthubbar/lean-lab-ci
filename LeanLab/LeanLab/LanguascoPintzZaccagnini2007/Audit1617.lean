/-
P0045, Corollary 4.2 and display 12. Unit U-1617. What a covering of windows gives.
`window_cover1617` proves that J(X) and J(X') with X' = 3X/4 cover [X/2, X].
This does not close `cor42_window_extension131`, because `binaryMajor131 X n P` is built from the
sum S and the arcs at parameter X. Only the full integral over the unit interval is free of X
for n at most X. The minor arc part is controlled in mean square, not pointwise.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218
open Finset

namespace LeanLab.LPZ2007

/-- Two published windows cover the needed one, as sets of even integers, X at least 9. -/
theorem window_cover1617 {X n : ℕ} (hX : 9 ≤ X) (hn : n ∈ evenWindow131 X) :
    n ∈ evenJ131 X ∨ n ∈ evenJ131 (3 * X / 4) := by
  obtain ⟨hIcc, hev, hlow⟩ := mem_filter.mp hn
  have hn1 := mem_Icc.mp hIcc
  by_cases h : 2 * (X : ℝ) / 3 ≤ n
  · exact Or.inl (mem_filter.mpr ⟨hIcc, hev, h⟩)
  · right
    have hlt : (n : ℝ) < 2 * (X : ℝ) / 3 := not_le.mp h
    have h3 : 3 * n < 2 * X := by
      have : (3 * n : ℝ) < 2 * X := by linarith
      exact_mod_cast this
    have hXn : X ≤ 2 * n := by
      have : (X : ℝ) ≤ 2 * n := by linarith
      exact_mod_cast this
    have hle : n ≤ 3 * X / 4 := by omega
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1.1, hle⟩, hev, ?_⟩
    have hd : 2 * (3 * X / 4) ≤ 3 * n := by omega
    have hd' : (2 * ((3 * X / 4 : ℕ) : ℝ)) ≤ 3 * n := by exact_mod_cast hd
    linarith

/-- The split reassembles the old leaf with no change of statement. -/
theorem cor42Statement_eq_window1617 :
    Cor42Statement131 = Cor42OnWindow131 evenWindow131 := rfl

/-- J(X) sits inside the window, so the extension leaf is not a change of target on J(X). -/
theorem evenJ_subset_window1617 (X : ℕ) : evenJ131 X ⊆ evenWindow131 X := by
  intro n hn
  obtain ⟨hIcc, hev, hlow⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨hIcc, hev, ?_⟩
  have : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  linarith

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.window_cover1617
#print axioms LeanLab.LPZ2007.cor42Statement_eq_window1617
#print axioms LeanLab.LPZ2007.evenJ_subset_window1617
#print axioms LeanLab.LPZ2007.major_arcs_j1_131
#print axioms LeanLab.LPZ2007.cor42_published131
#print axioms LeanLab.LPZ2007.cor42_window_extension131
