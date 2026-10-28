import LeanLab.Halupczok2012.Statements
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

open scoped BigOperators

namespace LeanLab.Halupczok2012

/-- LEAF: page 345. Wu's Theorem in [17], as used for Corollary 1.3.
The number of `p1 ∈ [X1, X1+Y]` with `p1 + 2 = P_2` and `3 ∤ p1 + 2`
is `≫ Y L^{-2}` if `Y = X1^{θ1}` for `θ1 ≥ 0.971`.
We state it as: there exists `c > 0` such that for large `Y`,
the count is `≥ c Y / (log Y)^2`. -/
theorem leaf_wu_theorem :
  ∃ c > 0, ∃ Y0 > 0, ∀ (X Y : ℝ), Y0 ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
    c * Y / (Real.log Y) ^ 2 ≤ (@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) (Classical.decPred _) (kRange X Y)).card := by
  sorry

/-- LEAF: page 346. The number of exceptions in Corollary 1.2 is `≪ Y L^{-A}`.
This directly extracts the bound from `Corollary2`. -/
theorem leaf_cor2_bound (hCor2 : Corollary2) (A ε c : ℝ) (hA : 0 < A) (hε : 0 < ε) (hc : 0 < c) :
  ∃ C Y0 : ℝ, ∀ X1 X2 Y : ℝ, Y0 ≤ Y →
    X2 ^ (0.861 : ℝ) ≤ Y → Y ≤ X2 → X2 + Y ≤ 2 * X1 → 2 * X1 ≤ c * Y ^ (3 / 2 - ε) →
    (cor2Exc X1 X2 Y : ℝ) ≤ C * Y * Real.log Y ^ (-A) := by
  exact hCor2 A ε c hA hε hc

/-- LEAF: page 346. For `A = 3`, `Y L^{-2}` eventually dominates `C Y L^{-3}`. -/
theorem leaf_wu_dominates_exc (c C : ℝ) (hc : 0 < c) :
  ∃ Y0 > 0, ∀ Y : ℝ, Y0 ≤ Y →
    C * Y * Real.log Y ^ (-3 : ℝ) < c * Y / (Real.log Y) ^ 2 := by
  sorry

/-- LEAF: The assembly theorem for Corollary 3.
"So not all of them can be exceptions in Corollary 1.2, so there is at least one of them being the sum of two primes p2 and p3... Note that Corollary 1.2 is applicable since we assumed that X1 + X2 + 2Y <= n << Y^{3/2 - \epsilon}..." -/
theorem corollary_3_assembly_leaf (hCor2 : Corollary2) : Corollary3 := by
  intro ε c hε hc
  obtain ⟨c_wu, hc_wu, Y0_wu, Y0_wu_pos, hwu⟩ := leaf_wu_theorem
  obtain ⟨C_cor, Y0_cor, hcor⟩ := leaf_cor2_bound hCor2 3 ε c (by norm_num) hε hc
  obtain ⟨Y0_dom, Y0_dom_pos, hdom⟩ := leaf_wu_dominates_exc c_wu C_cor hc_wu
  use max (max Y0_wu Y0_cor) Y0_dom
  intro X1 X2 Y n hY_large hX1 hY_le_X1 hX2 hY_le_X2 h_odd h_n6 h_n_lower h_n_upper
  have hY_wu : Y0_wu ≤ Y := le_trans (le_trans (le_max_left Y0_wu Y0_cor) (le_max_left (max Y0_wu Y0_cor) Y0_dom)) hY_large
  have hY_cor : Y0_cor ≤ Y := le_trans (le_trans (le_max_right Y0_wu Y0_cor) (le_max_left (max Y0_wu Y0_cor) Y0_dom)) hY_large
  have hY_dom : Y0_dom ≤ Y := le_trans (le_max_right (max Y0_wu Y0_cor) Y0_dom) hY_large
  have wu_bound := hwu X1 Y hY_wu hX1 hY_le_X1
  have dom_bound := hdom Y hY_dom
  have exc_bound : (cor2Exc X1 X2 Y : ℝ) ≤ C_cor * Y * Real.log Y ^ (-3 : ℝ) := by
    apply hcor X1 X2 Y hY_cor hX2 hY_le_X2
    · sorry
    · sorry
  sorry

/-- The assembly theorem for Corollary 3.
Blocked. -/
theorem corollary_3_assembly (hCor2 : Corollary2) : Corollary3 := corollary_3_assembly_leaf hCor2

end LeanLab.Halupczok2012
