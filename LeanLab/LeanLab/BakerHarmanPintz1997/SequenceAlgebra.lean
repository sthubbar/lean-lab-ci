/-
P0069, Section 4, equation 4.2. Linear closure of the transfer estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
open Finset
attribute [local instance] Classical.propDecidable

/-- The transfer error in equation 4.2. -/
noncomputable def transferError (ε : ℝ) (c : ℝ → ℕ → ℂ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ k ∈ Iset ε x, c x k * χ (k : ZMod q)) -
    ((Yof ε x / y1 x : ℝ) : ℂ) *
      ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)

/-- The finite transfer error is additive in its coefficient family. -/
theorem transferError_add (ε : ℝ) (c d : ℝ → ℕ → ℂ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    transferError ε (c + d) x χ = transferError ε c x χ + transferError ε d x χ := by
  simp only [transferError, Pi.add_apply, add_mul, sum_add_distrib, mul_add]
  ring

/-- The finite transfer error commutes with multiplication by a constant. -/
theorem transferError_smul (ε : ℝ) (c : ℝ → ℕ → ℂ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℂ) :
    transferError ε (fun x k => z * c x k) x χ = z * transferError ε c x χ := by
  simp only [transferError, mul_assoc, ← mul_sum]
  ring

/-- Equation 4.2 is closed under addition of two coefficient families. -/
theorem holds42_add {ε : ℝ} {c d : ℝ → ℕ → ℂ}
    (hc : Holds42 ε c) (hd : Holds42 ε d) : Holds42 ε (c + d) := by
  intro A hA
  obtain ⟨C, Xc, hc⟩ := hc A hA
  obtain ⟨D, Xd, hd⟩ := hd A hA
  refine ⟨C + D, max Xc Xd, fun x hx q hq hqA χ => ?_⟩
  change ‖transferError ε (c + d) x χ‖ ≤ _
  rw [transferError_add]
  calc ‖transferError ε c x χ + transferError ε d x χ‖ ≤
        ‖transferError ε c x χ‖ + ‖transferError ε d x χ‖ := norm_add_le _ _
    _ ≤ C * Yof ε x / L x ^ A + D * Yof ε x / L x ^ A :=
        add_le_add (hc x (le_trans (le_max_left _ _) hx) q hqA χ)
          (hd x (le_trans (le_max_right _ _) hx) q hqA χ)
    _ = _ := by ring

/-- Equation 4.2 is closed under a constant complex multiple. -/
theorem holds42_smul {ε : ℝ} {c : ℝ → ℕ → ℂ} (hc : Holds42 ε c) (z : ℂ) :
    Holds42 ε (fun x k => z * c x k) := by
  intro A hA
  obtain ⟨C, X, hc⟩ := hc A hA
  refine ⟨‖z‖ * C, X, fun x hx q hq hqA χ => ?_⟩
  change ‖transferError ε (fun x k => z * c x k) x χ‖ ≤ _
  rw [transferError_smul, norm_mul]
  calc ‖z‖ * ‖transferError ε c x χ‖ ≤ ‖z‖ * (C * Yof ε x / L x ^ A) :=
        mul_le_mul_of_nonneg_left (hc x hx q hqA χ) (norm_nonneg z)
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
