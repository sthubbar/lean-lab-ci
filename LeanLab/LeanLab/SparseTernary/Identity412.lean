/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 4, display (4.12).
`Identity412` of `Section4.lean`, PROVED: the weighted count `𝔑(m)` of (4.11) equals
`∫₀¹ S(α)³ e(-mα) dα`, by orthogonality `∫₀¹ e(nα) dα = [n = 0]` for integers `n`.
AI-written Lean code, Claude, run 20261021T0103Z-19411, unit U-1308. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Section4

open Finset Complex
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Identity

open LeanLab.SparseTernary.Section4

@[fun_prop] theorem continuous_ee : Continuous ee := by unfold ee; fun_prop

/-- Orthogonality: `∫₀¹ e(nα) dα = 1` if `n = 0`, else `0`, for every integer `n`. -/
theorem integral_ee_int (n : ℤ) :
    ∫ α in (0 : ℝ)..1, ee ((n : ℝ) * α) = if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [ee]
  · have hc : (2 * (Real.pi : ℂ) * I * n) ≠ 0 := by
      have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast h
      have h2 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h2) I_ne_zero) h1
    have heq : (fun α : ℝ => ee ((n : ℝ) * α)) =
        fun α : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * I * n) * α) := by
      funext α; unfold ee; congr 1; push_cast; ring
    rw [heq, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]; congr 1; push_cast; ring
    rw [h1]; simp

/-- Expansion of the integrand: `S(α)³ e(-mα) = Σ Λ(k₁)Λ(k₂)Λ(k₃) e((k₁+k₂+k₃-m)α)`. -/
theorem expand (Z : ℕ) (u : ℝ) (m : ℕ) (α : ℝ) :
    Sexp Z u α ^ 3 * ee (-(m * α)) =
      ∑ k₁ ∈ Aset Z u, ∑ k₂ ∈ Aset Z u, ∑ k₃ ∈ Aset Z u,
        ((ArithmeticFunction.vonMangoldt k₁ * ArithmeticFunction.vonMangoldt k₂ *
          ArithmeticFunction.vonMangoldt k₃ : ℝ) : ℂ) *
          ee ((((k₁ + k₂ + k₃ : ℤ) - m : ℤ) : ℝ) * α) := by
  unfold Sexp
  rw [pow_three]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine sum_congr rfl fun k₁ _ => sum_congr rfl fun k₂ _ => sum_congr rfl fun k₃ _ => ?_
  have he : ee ((((k₁ + k₂ + k₃ : ℤ) - m : ℤ) : ℝ) * α) =
      ee (k₁ * α) * ee (k₂ * α) * ee (k₃ * α) * ee (-(m * α)) := by
    unfold ee; simp only [← Complex.exp_add]; congr 1; push_cast; ring
  rw [he]; push_cast; ring

/-- **(4.12), PROVED**: `𝔑(m) = ∫₀¹ S(α)³ e(-mα) dα`. -/
theorem identity412 : Identity412 := by
  intro Z u m
  have hfun : (fun α : ℝ => Sexp Z u α ^ 3 * ee (-(m * α))) = fun α : ℝ =>
      ∑ k₁ ∈ Aset Z u, ∑ k₂ ∈ Aset Z u, ∑ k₃ ∈ Aset Z u,
        ((ArithmeticFunction.vonMangoldt k₁ * ArithmeticFunction.vonMangoldt k₂ *
          ArithmeticFunction.vonMangoldt k₃ : ℝ) : ℂ) *
          ee ((((k₁ + k₂ + k₃ : ℤ) - m : ℤ) : ℝ) * α) := funext (expand Z u m)
  rw [hfun]
  rw [intervalIntegral.integral_finset_sum fun k₁ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _]
  unfold Rfrak
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k₂ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _, Complex.ofReal_sum]
  refine sum_congr rfl fun k₂ _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k₃ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _, Complex.ofReal_sum]
  refine sum_congr rfl fun k₃ _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_ee_int]
  split_ifs with h1 h2 h2
  · simp
  · exfalso; apply h2; omega
  · exfalso; apply h1; omega
  · simp

/-- Vacuity test: with `Z = 0`, `u = 1`, `m = 7` the identity is a genuine instance. -/
example : ((Rfrak 0 1 7 : ℝ) : ℂ) = ∫ α in (0 : ℝ)..1, Sexp 0 1 α ^ 3 * ee (-((7 : ℕ) * α)) :=
  identity412 0 1 7

end LeanLab.SparseTernary.Identity

#print axioms LeanLab.SparseTernary.Identity.identity412
