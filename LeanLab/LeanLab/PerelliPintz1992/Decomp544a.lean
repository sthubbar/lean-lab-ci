/-
P0070, page 364, Gallagher normalization for the averaged WA route.
The moving window has length D divided by two at frequency radius one divided by D.
The kernel is positive on the entire closed frequency interval.
These bounds keep the finite coefficient window integral explicit.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Decomp97a

namespace LeanLab.PerelliPintz1992.Decomp544a
open Real MeasureTheory
open LeanLab.PerelliPintz1992.Section6
noncomputable section

/-- Page 364, Gallagher at the full Farey radius with the matching half length window.
Specialize D to q Q. The coefficient window integral is over the whole real line. -/
theorem gallagher_half_window (s : Finset ℕ) (a : ℕ → ℂ) {D : ℝ} (hD : 0 < D) :
    (∫ t in (-(1 / D))..(1 / D), ‖∑ n ∈ s, a n * e ((n : ℝ) * t)‖ ^ 2) ≤
      (Real.pi ^ 2 / D ^ 2) * ∫ x : ℝ,
        ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + D / 2), a n‖ ^ 2 := by
  have hlen : 1 / (2 * (1 / D)) = D / 2 := by field_simp
  have h := gallagher_nat_window s a (one_div_pos.mpr hD)
  rw [hlen] at h
  convert h using 1
  ring

/-- Page 364, the half length kernel has no zero anywhere on the closed Farey interval.
For D equal to q Q, its sinc argument has absolute value at most pi divided by two. -/
theorem half_window_kernel_pos {D η : ℝ} (hD : 0 < D) (hη : |η| ≤ 1 / D) :
    0 < ((D / 2) * Real.sinc (Real.pi * (D / 2) * η)) ^ 2 := by
  have hscale : 0 < Real.pi * (D / 2) := by positivity
  have heq : (Real.pi * (D / 2)) * (1 / D) = Real.pi / 2 := by field_simp
  have harg : |Real.pi * (D / 2) * η| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hscale]
    exact (mul_le_mul_of_nonneg_left hη hscale.le).trans_eq heq
  have hsinc : 0 < Real.sinc (Real.pi * (D / 2) * η) :=
    Real.sinc_pos (harg.trans_lt (by linarith [Real.pi_pos]))
  positivity

#print axioms gallagher_half_window
#print axioms half_window_kernel_pos
end
end LeanLab.PerelliPintz1992.Decomp544a
