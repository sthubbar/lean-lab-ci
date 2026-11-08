import LeanLab.ExceptionalSet.Decomp462c

/-!
P0082 pages 356 and 357, auxiliary smoothing factor for Poisson summation.
Source: https://doi.org/10.5802/aif.1621
The factor uses Delta one half and spatial scale two.
Those auxiliary choices are not printed parameters of the paper application.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462d

open Real MeasureTheory Filter Asymptotics
open scoped ENNReal
open LeanLab.ExceptionalSet.U1539 (ftR eC Kfun)

/-- P0082 page 356, auxiliary scaled trapezoid factor.
The scale two widens its plateau to the closed unit interval. -/
theorem scaled_kernel_fourier (ξ : ℝ) :
    ftR (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 2) (2 * x) : ℂ)) ξ =
      (KernelTransform264.weight (1 / 2) (ξ / 2) : ℂ) := by
  rw [← KernelTransform264.ftR_Kfun (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (ξ / 2)]
  unfold ftR
  have he : (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 2) (2 * x) : ℂ) * eC (-(ξ * x))) =
      fun x : ℝ => (2 : ℂ) * ((Kfun (1 / 2) (2 * x) : ℂ) * eC (-((ξ / 2) * (2 * x)))) := by
    funext x
    rw [show -(ξ * x) = -((ξ / 2) * (2 * x)) by ring, mul_assoc]
  rw [he, integral_const_mul]
  change (2 : ℂ) * (∫ x : ℝ, (fun y : ℝ => (Kfun (1 / 2) y : ℂ) * eC (-((ξ / 2) * y))) (2 * x)) = _
  rw [Measure.integral_comp_mul_left (fun y : ℝ => (Kfun (1 / 2) y : ℂ) * eC (-((ξ / 2) * y))) (2 : ℝ)]
  norm_num [smul_eq_mul]
  ring

/-- P0082 page 356, integrability of the auxiliary scaled factor. -/
theorem scaled_kernel_integrable : Integrable (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 2) (2 * x) : ℂ)) := by
  exact ((KernelTransform264.Kfun_integrable (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul _

open Filter Asymptotics
/-- P0082 page 357 display 4, quadratic decay of the auxiliary factor. -/
theorem scaled_kernel_isBigO : (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 2) (2 * x) : ℂ)) =O[cocompact ℝ]
    (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  apply IsBigO.of_bound (8 / Real.pi ^ 2)
  filter_upwards [(isCompact_singleton : IsCompact ({0} : Set ℝ)).compl_mem_cocompact] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hdec := Decomp404b.kernel_decay (1 / 2) (2 * x) (by norm_num) (by norm_num)
    (mul_ne_zero (by norm_num) hx0)
  have hp : |2 * x| ^ (-2 : ℝ) ≤ |x| ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hx0)
      (by rw [abs_mul]; norm_num; linarith [abs_nonneg x]) (by norm_num)
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  simp only [norm_mul, htwo, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  calc
    _ ≤ 2 * ((2 / ((1 / 2) * Real.pi ^ 2)) * |2 * x| ^ (-2 : ℝ)) := by gcongr
    _ ≤ 2 * ((2 / ((1 / 2) * Real.pi ^ 2)) * |x| ^ (-2 : ℝ)) := by gcongr
    _ = _ := by ring

/-- P0082 page 356, auxiliary uniform bound for translated unit intervals.
A compact translate norm sum controls every real translation by reindexing
with the integer floor of that translation. -/
theorem uniform_lattice_bound (φ : C(ℝ, ℂ))
    (hnorm : Summable (fun n : ℤ =>
      ‖(φ.comp (ContinuousMap.addRight (n : ℝ))).restrict (Set.Icc (-1 : ℝ) 1)‖)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ y : ℝ,
      (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1),
        ENNReal.ofReal ‖φ (t - y)‖) ≤ C := by
  let b : ℤ → ℝ := fun n =>
    ‖(φ.comp (ContinuousMap.addRight (n : ℝ))).restrict (Set.Icc (-1 : ℝ) 1)‖
  refine ⟨∑' n : ℤ, ENNReal.ofReal (b n), hnorm.tsum_ofReal_ne_top, fun y => ?_⟩
  calc
    _ ≤ ∑' n : ℤ, ENNReal.ofReal (b (n - ⌊y⌋)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      refine iSup₂_le fun t ht => ?_
      have hu : t - y - ((n - ⌊y⌋ : ℤ) : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
        simp only [Set.mem_Icc, Int.cast_sub]
        have hf := Int.floor_le y
        have hf' := Int.lt_floor_add_one y
        constructor <;> linarith [ht.1, ht.2]
      apply ENNReal.ofReal_le_ofReal
      have hb := ContinuousMap.norm_coe_le_norm
        ((φ.comp (ContinuousMap.addRight ((n - ⌊y⌋ : ℤ) : ℝ))).restrict
          (Set.Icc (-1 : ℝ) 1)) ⟨_, hu⟩
      simpa only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
        ContinuousMap.coe_addRight, sub_add_cancel] using hb
    _ = _ := by
      simpa only [sub_eq_add_neg, Equiv.coe_addRight] using
        (Equiv.addRight (-⌊y⌋)).tsum_eq (fun n : ℤ => ENNReal.ofReal (b n))

/-- P0082 page 356, auxiliary smoothing factor for the generic sampling proof.
This is the exact leaf_split_bump_exists statement with a new name. -/
theorem split_bump_exists_supplied :
    ∃ (φ : ℝ → ℂ) (C : ℝ≥0∞),
      Integrable φ ∧
        (∀ α : ℝ, |α| ≤ 1 → ftR φ α = 1) ∧
          C ≠ ⊤ ∧
            (∀ y : ℝ,
              (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1),
                ENNReal.ofReal ‖φ (t - y)‖) ≤ C) := by
  let φ : C(ℝ, ℂ) := ⟨fun x => (2 : ℂ) * (Kfun (1 / 2) (2 * x) : ℂ),
    continuous_const.mul ((KernelTransform264.Kfun_continuous _).comp
      (continuous_const.mul continuous_id))⟩
  have hnorm : Summable (fun n : ℤ =>
      ‖(φ.comp (ContinuousMap.addRight (n : ℝ))).restrict (Set.Icc (-1 : ℝ) 1)‖) := by
    exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      ((isBigO_norm_restrict_cocompact φ (by norm_num : (0 : ℝ) < 2)
        scaled_kernel_isBigO ⟨Set.Icc (-1 : ℝ) 1, isCompact_Icc⟩).comp_tendsto
          Int.tendsto_coe_cofinite)
  obtain ⟨C, hC, hbound⟩ := uniform_lattice_bound φ hnorm
  refine ⟨φ, C, scaled_kernel_integrable, ?_, hC, hbound⟩
  intro α hα
  change ftR (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 2) (2 * x) : ℂ)) α = 1
  rw [scaled_kernel_fourier, KernelTransform264.weight_one (by norm_num) (by norm_num)]
  · simp
  · rw [abs_div]
    norm_num
    linarith

end LeanLab.ExceptionalSet.Decomp462d
