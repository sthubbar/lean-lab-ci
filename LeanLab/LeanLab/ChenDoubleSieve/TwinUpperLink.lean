import LeanLab.ChenDoubleSieve.Statements
import LeanLab.Brun1919.Final

/-!
# `∃ a, TwinUpper a`, unconditional, from the lab's Brun theorem

Lab proof, unit U-5314, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Brun 1919 and 1920. Wu 2004 Theorem 3, `TwinUpper 3.3996`, stays cited; this gives the same form with
an unspecified constant from `Brun1919.twinUpper`, `π₂(N) ≤ C N/log² N` for `N ≥ 3`.
* `pi2_eq_twinCount`: `π₂(x) = twinCount(⌊x⌋ + 1)`;
* `twinUpper_exists`: `∃ a, TwinUpper a`.
Twin primes are not known to be infinite; this is an upper bound.
-/

open Finset Real
open scoped ArithmeticFunction.Omega

noncomputable section
namespace LeanLab.ChenDoubleSieve

open LeanLab.ChenExplicit (twinC twinC_pos)

lemma pi2_eq_twinCount (x : ℝ) : (π2 x : ℝ) = (Brun1919.twinCount (⌊x⌋₊ + 1) : ℝ) := by
  classical
  unfold π2 Brun1919.twinCount Brun1919.IsTwin
  simp only [ArithmeticFunction.cardFactors_eq_one_iff_prime]

theorem twinUpper_exists : ∃ a : ℝ, TwinUpper a := by
  obtain ⟨C, hC⟩ := Brun1919.twinUpper
  set C' := max C 0 with hC'
  refine ⟨C' / twinC, 3, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set M := ⌊x⌋₊ + 1 with hM
  have hM3 : 3 ≤ M := by
    have : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    omega
  have hMx : x < M := by rw [hM]; push_cast; exact Nat.lt_floor_add_one x
  have hM2x : (M : ℝ) ≤ 2 * x := by
    rw [hM]; push_cast
    have := Nat.floor_le hx0.le
    linarith
  have hlog : Real.log x ≤ Real.log M := Real.log_le_log hx0 hMx.le
  have hb := hC M hM3
  rw [pi2_eq_twinCount]
  have htw := twinC_pos
  unfold PiX
  calc (Brun1919.twinCount M : ℝ) ≤ C * M / Real.log M ^ 2 := hb
    _ ≤ C' * M / Real.log M ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    _ ≤ C' * (2 * x) / Real.log x ^ 2 := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left hM2x (le_max_right _ _)) (by positivity)
        exact pow_le_pow_left₀ hlx.le hlog 2
    _ = C' / twinC * (2 * twinC * x / Real.log x ^ 2) := by field_simp

end LeanLab.ChenDoubleSieve
