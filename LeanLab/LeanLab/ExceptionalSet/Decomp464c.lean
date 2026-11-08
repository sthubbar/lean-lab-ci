import LeanLab.ExceptionalSet.SPLIT_leaf_poisson_summation
import LeanLab.ExceptionalSet.Decomp464a
import LeanLab.ExceptionalSet.Decomp464b

/-!
P0082 page 356, periodization and finite Fourier series inputs.
These exact companions leave the open analytic convergence input explicit.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464c

open Real MeasureTheory Function
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- P0082 page 356 Poisson display, elementary periodization and Fourier series step.
Exact clean companion for the corresponding open summation leaf. -/
theorem leaf_summation_periodic (K : ℝ → ℂ) (v : ℝ) :
    Function.Periodic (fun x : ℝ => ∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) 1 := by
  intro x
  convert (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => K (x + n) * eC (-((x + n) * v))) using 1
  apply tsum_congr
  intro n
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  have he : x + 1 + (n : ℝ) = x + ((n : ℝ) + 1) := by ring
  rw [he]

/-- P0082 page 356 Poisson display, elementary periodization and Fourier series step.
Exact clean companion for the corresponding open summation leaf. -/
theorem leaf_summation_coefficient_vanishes (K : ℝ → ℂ) (hK : Integrable K)
    (hcont : Continuous K) (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → ftR K (v + (m : ℝ)) = 0 := by
  intro m hm₀ hm₁
  exact Decomp371d.leaf_poisson_endpoint K hK hcont hsupp _
    (Decomp371d.leaf_poisson_index v m hm₀ hm₁)

/-- P0082 page 356 Poisson display, elementary periodization and Fourier series step.
Exact clean companion for the corresponding open summation leaf. -/
theorem leaf_summation_fourier_series (F : ℝ → ℂ) (hper : Function.Periodic F 1)
    (hcont : Continuous F) (a b : ℤ) (hab : a ≠ b)
    (hfin : ∀ m : ℤ, m ≠ a → m ≠ b →
      (∫ x in (0 : ℝ)..1, F x * eC (-(x * (m : ℝ)))) = 0) (α : ℝ) :
    F α = ∑' m : ℤ, eC (α * (m : ℝ)) * ∫ x in (0 : ℝ)..1, F x * eC (-(x * (m : ℝ))) := by
  let f : C(UnitAddCircle, ℂ) :=
    ⟨hper.lift, continuous_coinduced_dom.mpr hcont⟩
  have hc (m : ℤ) : fourierCoeff f m =
      ∫ x in (0 : ℝ)..1, F x * eC (-(x * (m : ℝ))) := by
    rw [fourierCoeff_eq_intervalIntegral _ m 0]
    simp only [div_one, one_smul, zero_add, f, ContinuousMap.coe_mk,
      Function.Periodic.lift_coe, smul_eq_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [fourier_coe_apply]
    unfold eC
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    ring
  have hs : Summable (fourierCoeff f) := by
    apply summable_of_ne_finset_zero (s := {a, b})
    intro m hm
    rw [hc]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact hfin m hm.1 hm.2
  have hp := (has_pointwise_sum_fourier_series_of_summable hs
    (α : UnitAddCircle)).tsum_eq.symm
  have hval : f (α : UnitAddCircle) = F α := by
    simp only [f, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  rw [hval] at hp
  rw [hp]
  apply tsum_congr
  intro m
  rw [hc, smul_eq_mul, mul_comm]
  congr 1
  rw [fourier_coe_apply]
  unfold eC
  congr 1
  push_cast
  ring

end LeanLab.ExceptionalSet.Decomp464c
