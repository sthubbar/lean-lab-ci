import LeanLab.Zhao2025.Estimate38FromKernel

/-!
Relative row errors are absorbed using an explicit epsilon budget.
Source: Zhao 2025, displays 3.6 to 3.8, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON 3.6 and inflated row bounds, with the full error budget shown. -/
theorem estimate38_with_error {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (A : ι → ι → ℝ) (k x y z L l0 e0 e r : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (he0 : 0 ≤ e0) (hr : 0 ≤ r)
    (hbudget : (1 + e0) * r ≤ 1 + e)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (hSym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hRows : ∀ i ∈ s, (∑ j ∈ s, A i j) ≤
      r * Real.sqrt (B (1 / 3 + x + y) (lam i) l0 * B z (lam i) l0))
    (h36 : Estimate36 s lam A k x y z L e0) :
    Estimate38 s lam k x y z L l0 e := by
  intro M hM hEnvelope
  let a := (1 / 3 + x + y + z) / 2
  let w : ι → ℝ := fun i => smoothingWeight k a L (lam i)
  let S := ∑ i ∈ s, w i
  let p := 1 / (x * z) * (1 / 2 + (1 / 3 + x) / y)
  let c := (1 + e0) * p
  let D : ι → ℝ := fun i => r * Real.sqrt (B (1 / 3 + x + y) (lam i) l0 * B z (lam i) l0)
  have hc : 0 ≤ c := by dsimp [c, p]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hEnv : ∀ i ∈ s, Real.exp (-(a * max (L - lam i) 0)) * D i ≤ r * M := by
    intro i hi
    dsimp [D]
    calc
      _ = r * (Real.exp (-(a * max (L - lam i) 0)) *
          Real.sqrt (B (1 / 3 + x + y) (lam i) l0 * B z (lam i) l0)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hEnvelope i hi) hr
  have hQ := smoothing_kernel_envelope s lam A D k a L (r * M) hA hSym hRows hEnv
  have hInitial : S ^ 2 ≤ c * kernelEnergy s w lam k A := h36
  have hSq : S ^ 2 ≤ c * (r * M * S) := hInitial.trans (mul_le_mul_of_nonneg_left hQ hc)
  have hS : S ≤ c * (r * M) := by
    by_contra hn
    have hgt : c * (r * M) < S := lt_of_not_ge hn
    have hCM : 0 ≤ c * (r * M) := mul_nonneg hc (mul_nonneg hr hM)
    have hpos : 0 < S * (S - c * (r * M)) :=
      mul_pos (lt_of_le_of_lt hCM hgt) (sub_pos.mpr hgt)
    nlinarith only [hSq, hpos]
  change S ≤ (1 + e) * p * M
  calc
    _ ≤ c * (r * M) := hS
    _ = ((1 + e0) * r) * (p * M) := by dsimp [c]; ring
    _ ≤ (1 + e) * (p * M) := mul_le_mul_of_nonneg_right hbudget (mul_nonneg hp hM)
    _ = _ := by ring

#print axioms estimate38_with_error
end LeanLab.Zhao2025.Task56
