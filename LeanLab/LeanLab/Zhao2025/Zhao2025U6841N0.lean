import Mathlib
import LeanLab.Zhao2025.Zhao2025U6825Lemma31
import LeanLab.Zhao2025.Zhao2025U6841G

/-!
# Zhao 2025, the first Theorem I count `n₀ = 6` at `Λ = 1.363`, `λ₀ = 0.857`, from (3.26)

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6841, CLOUD 20261021T0316Z-cloud57.
AI wrote the Lean code.  Binary Goldbach is open.

With `x = 1.548`, `z₁ = -λ₀/x = -857/1548`, `z₂ = (Λ-λ₀)/x = 253/774`,
`Δ = G(z₂)/G(z₁) - (ϕ/2) x g(0)/G(z₁)`, `ϕ = 1/3`, `g(0) = 16/15`.  Proved: `0.378 < Δ`, so
`1/Δ² < 7`; Python `Δ = 0.39865`, `1/Δ² = 6.2923`.  Conditional on (3.26) as the named
hypothesis `h326`, `N(1.363) ≤ 6` for an integer count.
-/

namespace LeanLab.Zhao2025.U6841

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6825

/-- `G` of (3.22). -/
noncomputable def Gz (z : ℝ) : ℝ := ∫ u in (0 : ℝ)..2, gpoly u * Real.exp (-(u * z))

/-- `Δ` of (3.26) with `ϕ = 1/3`, `g(0) = 16/15`. -/
noncomputable def Delta (x L l0 : ℝ) : ℝ :=
  Gz ((L - l0) / x) / Gz (-l0 / x) - 1 / 6 * x * (16 / 15) / Gz (-l0 / x)

theorem xa : 0.3304714055 ≤ Real.exp (-(857 / 774)) ∧ Real.exp (-(857 / 774)) ≤ 0.3304714056 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem xb : 0.5200934510 ≤ Real.exp (-(253 / 387)) ∧ Real.exp (-(253 / 387)) ≤ 0.5200934511 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem G1_bounds : 1.2076 ≤ Gz (-857 / 1548) ∧ Gz (-857 / 1548) ≤ 1.2078 := by
  have h := G_closed (-857 / 1548) (by norm_num)
  have e : -(2 * (-857 / 1548 : ℝ)) = 857 / 774 := by norm_num
  rw [e] at h
  have hm : Real.exp (857 / 774) * Real.exp (-(857 / 774)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (857 / 774)
  obtain ⟨a1, a2⟩ := xa
  have l1 : 3.0259 ≤ Real.exp (857 / 774) := by nlinarith
  have l2 : Real.exp (857 / 774) ≤ 3.0261 := by nlinarith
  unfold Gz; rw [h]; norm_num
  constructor <;> nlinarith

theorem G2_bounds : 0.7565 ≤ Gz (253 / 774) ∧ Gz (253 / 774) ≤ 0.7568 := by
  have h := G_closed (253 / 774) (by norm_num)
  have e : -(2 * (253 / 774 : ℝ)) = -(253 / 387) := by norm_num
  rw [e] at h
  obtain ⟨b1, b2⟩ := xb
  unfold Gz; rw [h]; norm_num
  constructor <;> nlinarith

/-- PROVED unconditional: `Δ(1.548, 1.363, 0.857) > 0.378`. -/
theorem Delta0_gt : 0.378 < Delta 1.548 1.363 0.857 := by
  unfold Delta
  have e1 : ((1.363 : ℝ) - 0.857) / 1.548 = 253 / 774 := by norm_num
  have e2 : -(0.857 : ℝ) / 1.548 = -857 / 1548 := by norm_num
  rw [e1, e2]
  obtain ⟨g1, g2⟩ := G1_bounds
  obtain ⟨h1, h2⟩ := G2_bounds
  have hpos : 0 < Gz (-857 / 1548) := by linarith
  rw [← sub_div, lt_div_iff₀ hpos]
  nlinarith

/-- PROVED unconditional: `1/Δ² < 7` at these values. -/
theorem n0_bound : 0 < Delta 1.548 1.363 0.857 ∧ 1 / (Delta 1.548 1.363 0.857) ^ 2 < 7 := by
  have h := Delta0_gt
  refine ⟨by linarith, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- CONDITIONAL ON Zhao Theorem I (3.26) in the form `h326`: for `x ≥ 4λ₀/5` with `Δ > 0`,
`N(Λ) ≤ 1/Δ²`.  Then the integer count at `Λ = 1.363`, `λ₀ = 0.857` is at most `6`. -/
theorem n0_conditional (N : ℕ)
    (h326 : ∀ x : ℝ, 4 * 0.857 / 5 ≤ x → 0 < Delta x 1.363 0.857 →
      (N : ℝ) ≤ 1 / (Delta x 1.363 0.857) ^ 2) : N ≤ 6 := by
  obtain ⟨hp, hb⟩ := n0_bound
  have := h326 1.548 (by norm_num) hp
  have : (N : ℝ) < 7 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Vacuity: `N = 0` satisfies the hypothesis. -/
theorem n0_vacuity : ∀ x : ℝ, 4 * 0.857 / 5 ≤ x → 0 < Delta x 1.363 0.857 →
    ((0 : ℕ) : ℝ) ≤ 1 / (Delta x 1.363 0.857) ^ 2 := by
  intro x _ _; simp; positivity

end LeanLab.Zhao2025.U6841

#print axioms LeanLab.Zhao2025.U6841.G1_bounds
#print axioms LeanLab.Zhao2025.U6841.G2_bounds
#print axioms LeanLab.Zhao2025.U6841.Delta0_gt
#print axioms LeanLab.Zhao2025.U6841.n0_bound
#print axioms LeanLab.Zhao2025.U6841.n0_conditional
#print axioms LeanLab.Zhao2025.U6841.n0_vacuity
