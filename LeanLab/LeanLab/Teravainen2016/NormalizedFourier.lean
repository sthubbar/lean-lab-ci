/-
P0076, Section 2, page 6. Normalized Fourier analysis on Z_N.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Transference
import LeanLab.Routes.R0001Parseval

open Finset
open scoped Classical ZMod

namespace LeanLab.Teravainen2016

/-- Representatives turn a sum on Z_N into a sum on the natural interval. -/
theorem sum_zmod_val {N : ℕ} [NeZero N] {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ x : ZMod N, f x.val = ∑ n ∈ range N, f n := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n + 1)

/-- Normalized transform for complex functions on Z_N. -/
noncomputable def normalizedDFT {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (ξ : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ZMod.dft f ξ

/-- Parseval with the normalization used on page 6. -/
theorem normalized_parseval {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ∑ n, ‖f n‖ ^ 2 = (N : ℝ) * ∑ ξ, ‖normalizedDFT f ξ‖ ^ 2 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp_rw [normalizedDFT, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  rw [← mul_sum, LeanLab.Routes.R0001.dft_parseval_norm]
  field_simp

/-- The additive character agrees with the exponential used by fhat. -/
theorem stdAddChar_nat_mul (N : ℕ) [NeZero N] (n ξ : ℕ) :
    ZMod.stdAddChar (-((n : ZMod N) * (ξ : ZMod N))) = eC (-((ξ : ℝ) * n / N)) := by
  have h := ZMod.stdAddChar_coe (N := N) (-((n : ℤ) * ξ))
  calc
    _ = Complex.exp (2 * Real.pi * Complex.I * ((-((n : ℤ) * ξ) : ℤ) : ℂ) / N) := by
      convert h using 1 <;> push_cast <;> rfl
    _ = _ := by
      unfold eC
      congr 1
      push_cast
      ring

/-- The natural representative transform is the normalized ZMod transform. -/
theorem fhat_eq_normalizedDFT (N : ℕ) [NeZero N] (f : ℕ → ℝ) (ξ : ℕ) :
    fhat N f ξ = normalizedDFT (fun n : ZMod N => (f n.val : ℂ)) ξ := by
  unfold fhat normalizedDFT
  congr 1
  rw [ZMod.dft_apply]
  have h : ∀ n : ZMod N, ZMod.stdAddChar (-(n * (ξ : ZMod N))) * (f n.val : ℂ) =
      (f n.val : ℂ) * eC (-((ξ : ℝ) * n.val / N)) := by
    intro n
    rw [← ZMod.natCast_zmod_val n, stdAddChar_nat_mul]
    simp only [ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (ZMod.val_lt n)]
    ring
  simp only [smul_eq_mul]
  rw [sum_congr rfl (fun n _ => h n),
    sum_zmod_val (fun n => (f n : ℂ) * eC (-((ξ : ℝ) * n / N)))]

/-- Parseval for the exact fhat definition used by Proposition 2.1. -/
theorem fhat_parseval (N : ℕ) [NeZero N] (f : ℕ → ℝ) :
    ∑ n ∈ range N, (f n) ^ 2 = (N : ℝ) * ∑ ξ ∈ range N, ‖fhat N f ξ‖ ^ 2 := by
  have h := normalized_parseval (fun n : ZMod N => (f n.val : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [sum_zmod_val (fun n => (f n) ^ 2)] at h
  convert h using 1
  congr 1
  rw [← sum_zmod_val (fun ξ => ‖fhat N f ξ‖ ^ 2)]
  apply sum_congr rfl
  intro ξ _
  rw [fhat_eq_normalizedDFT, ZMod.natCast_zmod_val]

example : ∑ ξ ∈ range 1, ‖fhat 1 (fun _ => 1) ξ‖ ^ 2 = 1 := by
  have h := fhat_parseval 1 (fun _ => 1)
  simpa using h.symm

#print axioms sum_zmod_val
#print axioms normalized_parseval
#print axioms stdAddChar_nat_mul
#print axioms fhat_eq_normalizedDFT
#print axioms fhat_parseval

end LeanLab.Teravainen2016
