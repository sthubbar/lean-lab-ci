import LeanLab.ChirreHagen2025.Decomp358e
import LeanLab.ChirreHagen2025.Decomp272b

/-!
P0075 page 6 first display, differentiating equation 2.11.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358g
open Decomp272a Decomp358e

/-- P0075 page 6 first display, the Taylor series of the entire derivative.
The coefficient identity uses the successor factorial and iterated derivative. -/
theorem regularPart_deriv_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * laurentCoeff (n + 1) * z ^ n)
      (deriv regularPart z) := by
  convert Complex.hasSum_taylorSeries_of_entire regularPart_entire.deriv 0 z using 1
  ext n
  simp only [laurentCoeff, ← iteratedDeriv_succ', sub_zero, smul_eq_mul,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  field_simp

/-- P0075 page 6 first display, derivative after removing the pole.
The square of it supplies the sign in the paper's 1 over t squared. -/
theorem regularPart_deriv_at_imaginary (t : ℝ) (ht : 0 < t) :
    deriv regularPart ((t : ℂ) * Complex.I) =
      deriv riemannZeta (1 + t * Complex.I) - 1 / (t : ℂ) ^ 2 := by
  have hz : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') Complex.I_ne_zero
  have heq : deriv regularPart ((t : ℂ) * Complex.I) =
      deriv riemannZeta₀ (1 + t * Complex.I) := by
    rw [show regularPart = fun z => riemannZeta₀ (1 + z) from funext regularPart_eq]
    exact deriv_comp_const_add riemannZeta₀ 1 _
  rw [heq, deriv_riemannZeta_eq_neg_inv_sub_sq_add (by simpa using hz)]
  simp only [add_sub_cancel_left]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  simp [Complex.I_sq]
  <;> ring

/-- P0075 page 6 first display. Exact target statement from Decomp272b.
This differentiated identity is unconditional. -/
theorem differentiated_laurent_series (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * laurentCoeff (n + 1) *
      ((t : ℂ) * Complex.I) ^ n)
      (deriv riemannZeta (1 + t * Complex.I) - 1 / (t : ℂ) ^ 2) := by
  rw [← regularPart_deriv_at_imaginary t ht]
  exact regularPart_deriv_hasSum _

end LeanLab.ChirreHagen2025.Decomp358g
