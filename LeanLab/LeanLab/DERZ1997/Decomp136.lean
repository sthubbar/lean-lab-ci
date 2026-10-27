/-
P0011 page 100, Section 2, the Fourier orthogonality display.
AI wrote the Lean code. Goldbach is open.
The named cited theorems with written proofs were already treated in this folder.
This supplementary unit formalizes the remaining elementary display.
-/
import Mathlib

namespace LeanLab.DERZ1997.Decomp136

/-- LEAF. P0011 page 100, orthogonality display, zero-frequency case. -/
theorem zero_frequency :
    (∫ α : ℝ in (0 : ℝ)..1,
      Complex.exp (2 * Real.pi * Complex.I * α * (0 : ℤ))) = 1 := by
  simp

/-- LEAF. P0011 page 100, orthogonality display, integer endpoint periodicity. -/
theorem integer_endpoint (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * m) = 1 := by
  simpa only [mul_comm] using Complex.exp_int_mul_two_pi_mul_I m

/-- LEAF. P0011 page 100, orthogonality display, nonzero-frequency case.
Use the exponential primitive and integer endpoint periodicity. -/
theorem nonzero_frequency (m : ℤ) (hm : m ≠ 0) :
    (∫ α : ℝ in (0 : ℝ)..1,
      Complex.exp (2 * Real.pi * Complex.I * α * m)) = 0 := by
  have hc : (2 * Real.pi * Complex.I * (m : ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Int.cast_ne_zero.mpr hm)
  have hi := integral_exp_mul_complex (a := 0) (b := 1) hc
  have heq : (fun α : ℝ => Complex.exp (2 * Real.pi * Complex.I * α * m)) =
      (fun α : ℝ => Complex.exp ((2 * Real.pi * Complex.I * m) * α)) := by
    funext α
    congr 1
    ring
  rw [heq, hi]
  simp [integer_endpoint]

/-- P0011 page 100, CITED orthogonality display, assembled from the leaves.
The statement uses every integer frequency, including negative frequencies. -/
theorem fourier_orthogonality (m : ℤ) :
    (∫ α : ℝ in (0 : ℝ)..1,
      Complex.exp (2 * Real.pi * Complex.I * α * m)) =
        if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simpa using zero_frequency
  · simpa [hm] using nonzero_frequency m hm

end LeanLab.DERZ1997.Decomp136
