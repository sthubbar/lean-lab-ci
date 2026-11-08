import LeanLab.ExceptionalSet.Decomp462d

/-!
P0082 page 356, generic sampling convergence for the Poisson display.
Source: https://doi.org/10.5802/aif.1621
The smoothing factor, reproducing convolution and nonnegative bounds give
summable interval suprema. Finite compact covers give local normal convergence.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462e

open Real MeasureTheory
open scoped ENNReal
open LeanLab.ExceptionalSet.U1539 (ftR)

/-- P0082 page 356, auxiliary compact convergence bridge.
Summable unit interval suprema give summable translate norms on every compact.
A compact set is covered by finitely many integer unit intervals. -/
theorem translate_norm_of_interval_sup (K : ℝ → ℂ) (hcont : Continuous K)
    (hsum : (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1),
      ENNReal.ofReal ‖K t‖) ≠ ⊤) :
    ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
  let w : ℤ → ℝ≥0∞ := fun n =>
    ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖
  have hw : ∑' n, w n ≠ ⊤ := hsum
  have hb : Summable (fun n : ℤ => (w n).toReal) := ENNReal.summable_toReal hw
  intro S
  obtain ⟨R, hR⟩ := (S.isCompact.image continuous_abs).bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt R
  let J : Finset ℤ := Finset.Icc (-(M : ℤ) - 1) (M : ℤ)
  have hdom : Summable (fun n : ℤ => ∑ j ∈ J, (w (n + j)).toReal) := by
    induction J using Finset.induction_on with
    | empty => simpa using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact ((Equiv.addRight j).summable_iff.mpr hb).add ih
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hdom
  intro n
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg fun j hj => ENNReal.toReal_nonneg)).mpr
  intro x
  have hxR : |(x : ℝ)| ≤ R := hR (Set.mem_image_of_mem abs x.property)
  have hxlo : -(M : ℝ) ≤ (x : ℝ) := by linarith [(abs_le.mp (hxR.trans hM.le)).1]
  have hxhi : (x : ℝ) ≤ (M : ℝ) := (abs_le.mp (hxR.trans hM.le)).2
  let j : ℤ := ⌈(x : ℝ)⌉ - 1
  have hjlo : -(M : ℤ) - 1 ≤ j := by
    have hr : -(M : ℝ) - 1 ≤ (j : ℝ) := by
      dsimp only [j]
      push_cast
      linarith [Int.le_ceil (x : ℝ)]
    exact_mod_cast hr
  have hjhi : j ≤ (M : ℤ) := by
    have hr : (j : ℝ) ≤ (M : ℝ) := by
      dsimp only [j]
      push_cast
      linarith [Int.ceil_lt_add_one (x : ℝ)]
    exact_mod_cast hr
  have hj : j ∈ J := Finset.mem_Icc.mpr ⟨hjlo, hjhi⟩
  have ht : (x : ℝ) + (n : ℝ) ∈ Set.Ioc ((n + j : ℤ) : ℝ) (((n + j : ℤ) : ℝ) + 1) := by
    simp only [Set.mem_Ioc, Int.cast_add]
    dsimp only [j]
    push_cast
    constructor <;> linarith [Int.le_ceil (x : ℝ), Int.ceil_lt_add_one (x : ℝ)]
  have hxbound : ‖K ((x : ℝ) + (n : ℝ))‖ ≤ (w (n + j)).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal (ENNReal.ne_top_of_tsum_ne_top hw (n + j))).mp
    exact le_iSup₂_of_le ((x : ℝ) + n) ht le_rfl
  exact hxbound.trans (Finset.single_le_sum (f := fun k => (w (n + k)).toReal) (fun k hk => ENNReal.toReal_nonneg) hj)

/-- P0082 page 356, summability of the integer interval suprema of the kernel.
This is the exact leaf_kernel_sup_summable statement with a new name. -/
theorem kernel_sup_summable_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ := by
  classical
  obtain ⟨φ, C, hφ, hφhat, hC, hCbound⟩ := Decomp462d.split_bump_exists_supplied
  have hk : (∫⁻ y : ℝ, ENNReal.ofReal ‖K y‖) < ⊤ := by
    have h := hK.2
    rw [hasFiniteIntegral_iff_norm] at h
    exact h
  have hmul : (∫⁻ y : ℝ, C * ENNReal.ofReal ‖K y‖) ≠ ⊤ := by
    rw [lintegral_const_mul'' C hK.1.norm.aemeasurable.ennreal_ofReal]
    exact (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hk).ne
  refine ne_top_of_le_ne_top hmul ?_
  calc
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖)
        ≤ ∑' n : ℤ, ∫⁻ y : ℝ,
            (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
              ENNReal.ofReal ‖K y‖ :=
          ENNReal.tsum_le_tsum fun n => Decomp462c.split_interval_sup_le_supplied K hK hcont hsupp φ hφ hφhat n
    _ ≤ ∫⁻ y : ℝ,
          (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
            ENNReal.ofReal ‖K y‖ :=
        Decomp462c.split_tsum_integral_le_supplied K φ
    _ ≤ ∫⁻ y : ℝ, C * ENNReal.ofReal ‖K y‖ := by
        refine lintegral_mono fun y => ?_
        have hy := hCbound y
        gcongr


/-- P0082 page 356, auxiliary convergence justification for Poisson summation.
This is the exact Decomp450a.leaf_translate_norm statement with a new name. -/
theorem translate_norm_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) :
    ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
  exact translate_norm_of_interval_sup K hcont (kernel_sup_summable_supplied K hK hcont hsupp)

end LeanLab.ExceptionalSet.Decomp462e
