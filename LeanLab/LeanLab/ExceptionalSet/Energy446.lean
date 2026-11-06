import LeanLab.ExceptionalSet.Decomp428b
import LeanLab.ExceptionalSet.Decomp428c

/-!
Absolute prime kernel energy for P0082 pages 365 and 366.
The compact part uses periodic prime energy. The tails use inverse square decay.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Energy446

open Real MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp Kfun)
open LeanLab.ExceptionalSet.Decomp404e (truncatedDomain)

/-- P0082 page 365 before display 24. Four unit periods have four times
the prime energy. This is an auxiliary compact interval bound. -/
theorem prime_energy_four (P X : ℝ) (hX : 2 ≤ X) :
    (∫ α in (-2 : ℝ)..2, ‖Sp P X α‖ ^ 2) ≤
      4 * (Real.log 4 * X * Real.log X) := by
  have hc : Continuous (fun α => ‖Sp P X α‖ ^ 2) := by
    unfold Sp U1539.eC
    fun_prop
  have hp : Function.Periodic (fun α => ‖Sp P X α‖ ^ 2) 1 := by
    intro α
    dsimp only
    rw [Decomp371a.Sp_periodic P X α]
  have he := hp.intervalIntegral_add_zsmul_eq (4 : ℤ) (-2)
    (fun a b => hc.intervalIntegrable a b)
  norm_num [zsmul_eq_mul] at he
  rw [he]
  have hb := PrimeEnergy385.prime_energy_le P X (-2) hX
  norm_num at hb
  linarith

/-- P0082 page 365 before display 24 and page 366 display 27.
The integral over the whole real line is bounded with constant 9 log 4.
This retains the inverse Delta loss allowed by the supply statement. -/
theorem weighted_energy_all (P X Δ : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α : ℝ, ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖) ≤
      9 * Real.log 4 * X * Real.log X / Δ := by
  let g : ℝ → ℝ := fun α => ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖
  let A := Real.log 4 * X * Real.log X
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hX0 : 0 ≤ X := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hg : Integrable g := by
    simpa only [g, PrimeTail385.integrand, norm_mul, U1539.norm_eC, mul_one]
      using (PrimeKernel264.total_integrable hΔ hΔ1 P X 0).norm
  have hc : Continuous (fun α => ‖Sp P X α‖ ^ 2) := by
    unfold Sp U1539.eC
    fun_prop
  have hgc : Continuous g := by
    apply Continuous.norm
    apply Continuous.mul
    · unfold Sp U1539.eC
      fun_prop
    · exact KernelTransform264.Kfun_continuous Δ
  have hcenter : (∫ α in Icc (-2 : ℝ) 2, g α) ≤ 8 * A := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    calc
      _ ≤ ∫ α in (-2 : ℝ)..2, 2 * ‖Sp P X α‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hgc.intervalIntegrable _ _) ((hc.const_mul 2).intervalIntegrable _ _)
        intro α hα
        dsimp [g]
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        have hk := KernelTail385.kernel_abs_le_two_sub Δ α hΔ hΔ1
        nlinarith [sq_nonneg ‖Sp P X α‖]
      _ = 2 * (∫ α in (-2 : ℝ)..2, ‖Sp P X α‖ ^ 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ 8 * A := by
        have hb := prime_energy_four P X hX
        change _ ≤ 4 * A at hb
        linarith
  have htail : (∫ α in (Icc (-2 : ℝ) 2)ᶜ, g α) ≤ A / Δ := by
    have ht := PrimeTail385.outside_nat_tail_le P X Δ 0 hX hΔ hΔ1 2 (by norm_num)
    simp only [PrimeTail385.integrand, norm_mul, U1539.norm_eC, mul_one, Nat.cast_ofNat] at ht
    change (∫ α in (Icc (-2 : ℝ) 2)ᶜ, g α) ≤ _
    have he : (∫ α in (Icc (-2 : ℝ) 2)ᶜ, g α) ≤
        2 * A / (Δ * Real.pi ^ 2 * (2 - 1)) := by
      simpa only [g, A, norm_mul] using ht
    refine he.trans ?_
    apply (div_le_div_iff₀ (by positivity : 0 < Δ * Real.pi ^ 2 * ((2 : ℝ) - 1)) hΔ).mpr
    dsimp [A]
    have hpi : (2 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hpi)]
  have hs := integral_add_compl (μ := volume) (s := Icc (-2 : ℝ) 2) measurableSet_Icc hg
  have hscale : A ≤ A / Δ := (le_div_iff₀ hΔ).mpr (by nlinarith)
  change (∫ α, g α) ≤ _
  calc
    _ = (∫ α in Icc (-2 : ℝ) 2, g α) + (∫ α in (Icc (-2 : ℝ) 2)ᶜ, g α) := hs.symm
    _ ≤ 8 * A + A / Δ := add_le_add hcenter htail
    _ ≤ 8 * (A / Δ) + A / Δ := by linarith
    _ = 9 * A / Δ := by ring
    _ = _ := by dsimp [A]; ring

/-- Exact supply for Decomp428c.leaf_weighted_energy.
Source: P0082 page 365 before display 24 and page 366 display 27. -/
theorem leaf_weighted_energy_supplied : ∃ C : ℝ, 0 < C ∧
    ∀ P X Δ : ℝ, 0 < P → 2 ≤ X → 0 < Δ → Δ < 1 →
      (∫ α in truncatedDomain P X, ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖) ≤
        C * X * Real.log X / Δ := by
  refine ⟨9 * Real.log 4, by positivity, fun P X Δ _hP hX hΔ hΔ1 => ?_⟩
  have hg : Integrable (fun α => ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖) := by
    simpa only [PrimeTail385.integrand, norm_mul, U1539.norm_eC, mul_one]
      using (PrimeKernel264.total_integrable hΔ hΔ1 P X 0).norm
  exact (setIntegral_le_integral hg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).trans
    (weighted_energy_all P X Δ hX hΔ hΔ1)

end LeanLab.ExceptionalSet.Energy446
