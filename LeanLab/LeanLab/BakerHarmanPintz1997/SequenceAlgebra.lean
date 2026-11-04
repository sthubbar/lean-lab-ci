/-
P0069, Section 4, equation 4.2. Linear closure of the transfer estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
open Finset
attribute [local instance] Classical.propDecidable

/-- The transfer error in the repaired equation 4.2, window y, display 4.5 on page 25. -/
noncomputable def transferError (c : ℝ → ℕ → ℂ) (x y : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ k ∈ Ioc ⌊x - y⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)) -
    ((y / y1 x : ℝ) : ℂ) *
      ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)

/-- The finite transfer error is additive in its coefficient family. -/
theorem transferError_add (c d : ℝ → ℕ → ℂ) (x y : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    transferError (c + d) x y χ = transferError c x y χ + transferError d x y χ := by
  simp only [transferError, Pi.add_apply, add_mul, sum_add_distrib, mul_add]
  ring

/-- The finite transfer error commutes with multiplication by a constant. -/
theorem transferError_smul (c : ℝ → ℕ → ℂ) (x y : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℂ) :
    transferError (fun x k => z * c x k) x y χ = z * transferError c x y χ := by
  simp only [transferError, mul_assoc, ← mul_sum]
  ring

/-- Equation 4.2 is closed under addition of two coefficient families. -/
theorem holds42_add {ε : ℝ} {c d : ℝ → ℕ → ℂ}
    (hc : Holds42 ε c) (hd : Holds42 ε d) : Holds42 ε (c + d) := by
  intro A hA
  obtain ⟨C, Xc, hc⟩ := hc A hA
  obtain ⟨D, Xd, hd⟩ := hd A hA
  refine ⟨C + D, max Xc Xd, fun x hx q hq hqA χ y hy hy1 => ?_⟩
  change ‖transferError (c + d) x y χ‖ ≤ _
  rw [transferError_add]
  calc ‖transferError c x y χ + transferError d x y χ‖ ≤
        ‖transferError c x y χ‖ + ‖transferError d x y χ‖ := norm_add_le _ _
    _ ≤ C * (y / L x ^ A + x ^ (0.55 + 11 * ε / 12)) +
          D * (y / L x ^ A + x ^ (0.55 + 11 * ε / 12)) :=
        add_le_add (hc x (le_trans (le_max_left _ _) hx) q hqA χ y hy hy1)
          (hd x (le_trans (le_max_right _ _) hx) q hqA χ y hy hy1)
    _ = _ := by ring

/-- Equation 4.2 is closed under a constant complex multiple. -/
theorem holds42_smul {ε : ℝ} {c : ℝ → ℕ → ℂ} (hc : Holds42 ε c) (z : ℂ) :
    Holds42 ε (fun x k => z * c x k) := by
  intro A hA
  obtain ⟨C, X, hc⟩ := hc A hA
  refine ⟨‖z‖ * C, X, fun x hx q hq hqA χ y hy hy1 => ?_⟩
  change ‖transferError (fun x k => z * c x k) x y χ‖ ≤ _
  rw [transferError_smul, norm_mul]
  calc ‖z‖ * ‖transferError c x y χ‖ ≤
        ‖z‖ * (C * (y / L x ^ A + x ^ (0.55 + 11 * ε / 12))) :=
        mul_le_mul_of_nonneg_left (hc x hx q hqA χ y hy hy1) (norm_nonneg z)
    _ = _ := by ring

/-- Equation 4.2 is closed under subtraction of coefficient families. -/
theorem holds42_sub {ε : ℝ} {c d : ℝ → ℕ → ℂ}
    (hc : Holds42 ε c) (hd : Holds42 ε d) : Holds42 ε (c - d) := by
  have heq : c - d = c + (fun x k => (-1 : ℂ) * d x k) := by
    funext x k
    simp [sub_eq_add_neg]
  rw [heq]
  exact holds42_add hc (holds42_smul hd (-1))

#print axioms transferError_add
#print axioms transferError_smul
#print axioms holds42_add
#print axioms holds42_smul
#print axioms holds42_sub
end LeanLab.BakerHarmanPintz1997
