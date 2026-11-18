/-
Unit task393. Assembly of the weighted prime power difference bound: from the pointwise bounds
`Dpt_le_small`, `Dpt_le_mid`, `Dpt_le_far`, the first-moment bound `int_Dpt_g_le` and the
weight integrals `integrableOn_y_W`, `integral_y_W_le`, this file proves `dpt_W_full`, which is
word for word the statement of the leaf `leaf_dpt_W_le` in DqtWeight.lean: `D(y)² W(y/X)` is
integrable on `y > 2` and its integral is at most `10^-6 δ log²(2.0001/δ) X²`.
The range is split at `T = 1/(4δ²)`. Nothing here is new mathematics, and binary Goldbach
stays open. AI wrote the Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.ThetaPsi
import LeanLab.ChirreHagen2025.SmoothY
import LeanLab.task393.DqtPointwise
import LeanLab.task393.DqtFar
import LeanLab.task393.DqtIntegral

namespace LeanLab.Task393

open Real MeasureTheory Set Filter Topology
open LeanLab.ChirreHagen2025 LeanLab.ChirreHagen2025.SmoothKernel

/-! ### Numeric lemmas -/

theorem asm_exp30_le : Real.exp 30 ≤ 2.0001 * 10 ^ 13 := by
  have h : Real.exp 30 = Real.exp 1 ^ 30 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
  calc Real.exp 1 ^ 30 ≤ (2.72 : ℝ) ^ 30 := pow_le_pow_left₀ (Real.exp_pos 1).le h1 30
    _ ≤ 2.0001 * 10 ^ 13 := by norm_num

theorem asm_exp30_ge : (10 : ℝ) ^ 13 ≤ Real.exp 30 := by
  have h : Real.exp 30 = Real.exp 1 ^ 30 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  calc (10 : ℝ) ^ 13 ≤ (2.718 : ℝ) ^ 30 := by norm_num
    _ ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) h1 30

theorem asm_le_exp31 : (2.0001 : ℝ) * 10 ^ 13 ≤ Real.exp 31 := by
  have h : Real.exp 31 = Real.exp 1 ^ 31 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  calc (2.0001 : ℝ) * 10 ^ 13 ≤ (2.718 : ℝ) ^ 31 := by norm_num
    _ ≤ Real.exp 1 ^ 31 := pow_le_pow_left₀ (by norm_num) h1 31

/-- `log s ≤ 2 (√s - 1)` for `s ≥ 1`. -/
theorem asm_log_le_two_sqrt {s : ℝ} (hs1 : 1 ≤ s) : Real.log s ≤ 2 * (√s - 1) := by
  have hs0 : 0 < s := by linarith
  have hr : 0 < √s := Real.sqrt_pos.mpr hs0
  have h1 := Real.log_le_sub_one_of_pos hr
  have h2 : Real.log s = 2 * Real.log (√s) := by
    rw [Real.log_sqrt hs0.le]; ring
  linarith

/-- N1: `30 ≤ log (2.0001 / δ)`. -/
theorem asm_L_ge {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) :
    30 ≤ Real.log (2.0001 / δ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  refine asm_exp30_le.trans ?_
  rw [le_div_iff₀ hδ]
  have h : δ * 10 ^ 13 ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδ1; exact hδ1
  calc (2.0001 : ℝ) * 10 ^ 13 * δ = 2.0001 * (δ * 10 ^ 13) := by ring
    _ ≤ 2.0001 * 1 := by gcongr
    _ = 2.0001 := by norm_num

/-- N2: `δ log² (2.0001 / δ) ≤ 961 / 10^13`. -/
theorem asm_delta_L_sq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) :
    δ * Real.log (2.0001 / δ) ^ 2 ≤ 961 / 10 ^ 13 := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (1 / 10 ^ 13) / δ := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hδ]; linarith
  have hs0 : 0 < s := by linarith
  have hsplit : (2.0001 : ℝ) / δ = (2.0001 * 10 ^ 13) * s := by rw [hs]; field_simp
  have hδs : δ * s = 1 / 10 ^ 13 := by rw [hs]; field_simp
  have hL0 : Real.log (2.0001 * 10 ^ 13) ≤ 31 := by
    rw [Real.log_le_iff_le_exp (by positivity)]; exact asm_le_exp31
  have hL0' : 30 ≤ Real.log (2.0001 * 10 ^ 13) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; exact asm_exp30_le
  have hr1 : 1 ≤ √s := by rw [Real.one_le_sqrt]; exact hs1
  have hlogs := asm_log_le_two_sqrt hs1
  have hL : Real.log (2.0001 / δ) ≤ 31 * √s := by
    rw [hsplit, Real.log_mul (by positivity) hs0.ne']
    have p1 := mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log (2.0001 * 10 ^ 13) - 2)
      (by linarith : (0 : ℝ) ≤ √s - 1)
    have p2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 31 - Real.log (2.0001 * 10 ^ 13))
      (by linarith : (0 : ℝ) ≤ √s)
    linarith
  have hLn : 0 ≤ Real.log (2.0001 / δ) := by linarith [asm_L_ge hδ hδ1]
  have hsq : Real.log (2.0001 / δ) ^ 2 ≤ 961 * s := by
    have h2 := mul_self_le_mul_self hLn hL
    have h3 : √s * √s = s := Real.mul_self_sqrt hs0.le
    nlinarith
  calc δ * Real.log (2.0001 / δ) ^ 2 ≤ δ * (961 * s) := by gcongr
    _ = 961 * (δ * s) := by ring
    _ = 961 / 10 ^ 13 := by rw [hδs]; ring

/-- N3: `log ((1+δ) X) ≤ 96 / 10^7 * √X` for `X ≥ 10^13`. -/
theorem asm_log_le_sqrt {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X) :
    Real.log ((1 + δ) * X) ≤ 96 / 10 ^ 7 * √X := by
  have hX0 : 0 < X := by linarith [show (0 : ℝ) < 10 ^ 13 by positivity]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = X / 10 ^ 13 := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ (by positivity)]; linarith
  have ht0 : 0 < t := by linarith
  have hXt : X = 10 ^ 13 * t := by rw [ht]; field_simp
  have hc : (3162277 : ℝ) ≤ √(10 ^ 13) := (Real.le_sqrt' (by norm_num)).mpr (by norm_num)
  have hr1 : 1 ≤ √t := by rw [Real.one_le_sqrt]; exact ht1
  have hsq : √X = √(10 ^ 13) * √t := by rw [hXt, Real.sqrt_mul (by positivity)]
  have h1 : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + δ); linarith
  have h2 : Real.log (10 ^ 13) ≤ 30 := by
    rw [Real.log_le_iff_le_exp (by positivity)]; exact asm_exp30_ge
  have h3 := asm_log_le_two_sqrt ht1
  have h4 : Real.log ((1 + δ) * X) = Real.log (1 + δ) + (Real.log (10 ^ 13) + Real.log t) := by
    rw [hXt, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ht0.ne']
  have h5 : 3162277 * √t ≤ √(10 ^ 13) * √t := mul_le_mul_of_nonneg_right hc (by positivity)
  have h6 : 96 / 10 ^ 7 * (3162277 * √t) ≤ 96 / 10 ^ 7 * (√(10 ^ 13) * √t) :=
    mul_le_mul_of_nonneg_left h5 (by norm_num)
  have hδ1' : δ ≤ 1 / 10000000000000 := by norm_num at hδ1; linarith
  rw [h4, hsq]
  refine le_trans ?_ h6
  generalize √t = r at hr1 h3
  generalize Real.log (10 ^ 13) = a at h2
  generalize Real.log (1 + δ) = b at h1
  generalize Real.log t = c at h3
  norm_num
  linarith

/-! ### Measurability and the weight -/

theorem asm_measurable_Dpt (δ : ℝ) : Measurable (Dpt δ) := by
  have hp : Measurable (fun t : ℝ => Chebyshev.psi t) := Chebyshev.psi_mono.measurable
  have ht : Measurable (fun t : ℝ => Chebyshev.theta t) := Chebyshev.theta_mono.measurable
  have hl : Measurable (fun y : ℝ => (1 + δ) * y) := measurable_const.mul measurable_id
  unfold Dpt fpt
  exact ((hp.comp hl).sub (ht.comp hl)).sub (hp.sub ht)

theorem asm_measurable_W_div (X : ℝ) : Measurable (fun y : ℝ => W (y / X)) := by
  unfold W
  exact Measurable.ite (measurableSet_le (measurable_id.div_const X) measurable_const)
    measurable_const ((measurable_id.div_const X).pow_const 4).inv

theorem asm_W_le_one (u : ℝ) : W u ≤ 1 := by
  unfold W; split_ifs with h
  · exact le_rfl
  · push Not at h
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h.le)

/-- The cutoff `g(y) = 1` for `y ≤ X`, `(X/y)^3` beyond, lies in `[0, 1]` for `y > 0`. -/
theorem asm_g_bounds {X y : ℝ} (hX : 0 < X) (hy : 0 < y) :
    0 ≤ (if y ≤ X then (1 : ℝ) else (X / y) ^ 3) ∧ (if y ≤ X then (1 : ℝ) else (X / y) ^ 3) ≤ 1 := by
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl⟩
  · push Not at h
    exact ⟨by positivity, pow_le_one₀ (by positivity) ((div_le_one hy).mpr h.le)⟩

/-- `log ((1+δ) y) W(y/X) ≤ log ((1+δ) X) g(y)`. -/
theorem asm_log_W_le {δ X y : ℝ} (hδ : 0 < δ) (hX : 10 ^ 13 ≤ X) (hy : 0 < y) :
    Real.log ((1 + δ) * y) * W (y / X)
      ≤ Real.log ((1 + δ) * X) * (if y ≤ X then 1 else (X / y) ^ 3) := by
  have hX0 : 0 < X := by linarith [show (0 : ℝ) < 10 ^ 13 by positivity]
  have hℓ : 1 ≤ Real.log ((1 + δ) * X) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith [mul_pos hδ hX0]
  by_cases h : y ≤ X
  · have h1 : y / X ≤ 1 := (div_le_one hX0).mpr h
    unfold W
    rw [ite_eq_left h, ite_eq_left h1, mul_one, mul_one]
    exact Real.log_le_log (by positivity) (by gcongr)
  · have h' : X < y := not_le.mp h
    have h1 : 1 < y / X := (one_lt_div hX0).mpr h'
    unfold W
    rw [ite_eq_right h, ite_eq_right (not_le.mpr h1)]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = y / X := ⟨_, rfl⟩
    have hy' : y = r * X := by rw [hr]; field_simp
    subst hy'
    have hr1 : 1 < r := by rwa [← hr] at h1
    have hr0 : 0 < r := by linarith
    have e1 : (1 + δ) * (r * X) = (1 + δ) * X * r := by ring
    have e2 : X / (r * X) = r⁻¹ := by field_simp
    rw [mul_div_cancel_right₀ _ hX0.ne', e1, e2, Real.log_mul (by positivity) hr0.ne', inv_pow]
    have hlr := Real.log_le_sub_one_of_pos hr0
    have h3 : Real.log ((1 + δ) * X) + Real.log r ≤ Real.log ((1 + δ) * X) * r := by nlinarith
    calc (Real.log ((1 + δ) * X) + Real.log r) * (r ^ 4)⁻¹
        ≤ (Real.log ((1 + δ) * X) * r) * (r ^ 4)⁻¹ :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Real.log ((1 + δ) * X) * (r ^ 3)⁻¹ := by field_simp

/-! ### The large range `y > 1 / (4 δ²)` -/

theorem asm_Dpt_le_large {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13)
    (hyT : 1 / (4 * δ ^ 2) < y) :
    Dpt δ y ≤ 9 / 2 * Real.log (2.0001 / δ) ^ 2 * (δ * √y) := by
  by_cases h6 : y ≤ 1 / δ ^ 6
  · exact Dpt_le_mid hδ hδ1 hyT h6
  · refine (Dpt_le_far hδ hδ1 (not_le.mp h6).le).trans ?_
    have hL := asm_L_ge hδ hδ1
    have h4 : 4 ≤ 9 / 2 * Real.log (2.0001 / δ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h4 (by positivity)

theorem asm_f_le_large {δ X y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13)
    (hyT : 1 / (4 * δ ^ 2) < y) :
    Dpt δ y ^ 2 * W (y / X)
      ≤ 81 / 4 * Real.log (2.0001 / δ) ^ 4 * δ ^ 2 * (y * W (y / X)) := by
  have hy0 : 0 < y := lt_trans (by positivity) hyT
  have h1 := pow_le_pow_left₀ (Dpt_nonneg hδ.le hy0.le) (asm_Dpt_le_large hδ hδ1 hyT) 2
  have h2 : (9 / 2 * Real.log (2.0001 / δ) ^ 2 * (δ * √y)) ^ 2
      = 81 / 4 * Real.log (2.0001 / δ) ^ 4 * δ ^ 2 * y := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hy0.le]; ring
  rw [h2] at h1
  calc Dpt δ y ^ 2 * W (y / X)
      ≤ 81 / 4 * Real.log (2.0001 / δ) ^ 4 * δ ^ 2 * y * W (y / X) :=
        mul_le_mul_of_nonneg_right h1 (W_nonneg _)
    _ = _ := by ring

/-! ### Assembly -/

/-- The weighted prime power difference, unconditional: word for word the statement of
`leaf_dpt_W_le`. Unit task393. -/
theorem dpt_W_full {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X) :
    IntegrableOn (fun y => Dpt δ y ^ 2 * W (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Dpt δ y ^ 2 * W (y / X)
        ≤ 1 / 10 ^ 6 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  have hX0 : 0 < X := by linarith [show (0 : ℝ) < 10 ^ 13 by positivity]
  have hL30 := asm_L_ge hδ hδ1
  have hδL := asm_delta_L_sq hδ hδ1
  have hptL0 : ∀ y : ℝ, 1 / (4 * δ ^ 2) < y → Dpt δ y ^ 2 * W (y / X)
      ≤ 81 / 4 * Real.log (2.0001 / δ) ^ 4 * δ ^ 2 * (y * W (y / X)) :=
    fun y hy => asm_f_le_large hδ hδ1 hy
  have hsmall0 : ∀ y : ℝ, 2 < y → y ≤ 1 / (4 * δ ^ 2) →
      Dpt δ y ≤ Real.log (2.0001 / δ) / 6 * Real.log ((1 + δ) * y) :=
    fun y h1 h2 => Dpt_le_small hδ hδ1 h1 h2
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (2.0001 / δ) := ⟨_, rfl⟩
  rw [← hLdef] at hL30 hδL hptL0 hsmall0 ⊢
  have hL0 : 0 ≤ L := by linarith
  have hT2' : (2 : ℝ) < 1 / (4 * δ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    have h := pow_le_pow_left₀ hδ.le hδ1 2
    norm_num at h ⊢
    nlinarith
  have hint0 := int_Dpt_g_le hδ hδ1 hX hT2'.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 / (4 * δ ^ 2) := ⟨_, rfl⟩
  rw [← hT] at hptL0 hsmall0 hT2' hint0
  have hT2 : (2 : ℝ) < T := hT2'
  have hmf : Measurable (fun y => Dpt δ y ^ 2 * W (y / X)) :=
    ((asm_measurable_Dpt δ).pow_const 2).mul (asm_measurable_W_div X)
  -- the large range
  have hYW : IntegrableOn (fun y : ℝ => y * W (y / X)) (Ioi T) :=
    (integrableOn_y_W hX0).mono_set (Ioi_subset_Ioi (by linarith))
  have hptL : ∀ y ∈ Ioi T, Dpt δ y ^ 2 * W (y / X)
      ≤ 81 / 4 * L ^ 4 * δ ^ 2 * (y * W (y / X)) := fun y hy => hptL0 y hy
  have hIL : IntegrableOn (fun y => Dpt δ y ^ 2 * W (y / X)) (Ioi T) := by
    refine Integrable.mono' (hYW.const_mul (81 / 4 * L ^ 4 * δ ^ 2)) hmf.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (W_nonneg _))]
    exact hptL y hy
  have hBL : ∫ y in Ioi T, Dpt δ y ^ 2 * W (y / X) ≤ 81 / 4 * L ^ 4 * δ ^ 2 * X ^ 2 := by
    have h1 := setIntegral_mono_on hIL (hYW.const_mul (81 / 4 * L ^ 4 * δ ^ 2))
      measurableSet_Ioi hptL
    rw [integral_const_mul] at h1
    have h2 : ∫ y in Ioi T, y * W (y / X) ≤ ∫ y in Ioi (0 : ℝ), y * W (y / X) :=
      setIntegral_mono_set (integrableOn_y_W hX0)
        ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun y hy => mul_nonneg (le_of_lt hy) (W_nonneg _)))
        (Filter.Eventually.of_forall (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ T)))
    have h3 := integral_y_W_le hX0
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity))
  -- the small range
  have hmg : Measurable (fun y : ℝ => if y ≤ X then (1 : ℝ) else (X / y) ^ 3) :=
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
      ((measurable_const.div measurable_id).pow_const 3)
  have hD2 : IntegrableOn (fun y => Dpt δ y ^ 2) (Ioc 2 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT2.le).mp
      (Dpt_sq_ii hδ (by norm_num) hT2.le)
  have hD1 : IntegrableOn (Dpt δ) (Ioc 2 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT2.le).mp (Dpt_ii hδ 2 T)
  have hIS : IntegrableOn (fun y => Dpt δ y ^ 2 * W (y / X)) (Ioc 2 T) := by
    refine Integrable.mono' hD2 hmf.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y _ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (W_nonneg _))]
    calc Dpt δ y ^ 2 * W (y / X) ≤ Dpt δ y ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (asm_W_le_one _) (sq_nonneg _)
      _ = Dpt δ y ^ 2 := mul_one _
  have hIG : IntegrableOn (fun y => Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)) (Ioc 2 T) := by
    refine Integrable.mono' hD1 ((asm_measurable_Dpt δ).mul hmg).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans (by norm_num) hy.1
    have hD0 := Dpt_nonneg hδ.le hy0.le
    have hg := asm_g_bounds hX0 hy0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD0 hg.1)]
    calc Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3) ≤ Dpt δ y * 1 :=
          mul_le_mul_of_nonneg_left hg.2 hD0
      _ = Dpt δ y := mul_one _
  have hℓ0 : 0 ≤ Real.log ((1 + δ) * X) :=
    Real.log_nonneg (by nlinarith [mul_pos hδ hX0])
  have hptS : ∀ y ∈ Ioc 2 T, Dpt δ y ^ 2 * W (y / X)
      ≤ L / 6 * Real.log ((1 + δ) * X) * (Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_trans (by norm_num) hy.1
    have hD0 := Dpt_nonneg hδ.le hy0.le
    have h1 := hsmall0 y hy.1 hy.2
    have h2 := asm_log_W_le hδ hX hy0
    calc Dpt δ y ^ 2 * W (y / X) = Dpt δ y * (Dpt δ y * W (y / X)) := by ring
      _ ≤ Dpt δ y * (L / 6 * Real.log ((1 + δ) * y) * W (y / X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (W_nonneg _)) hD0
      _ = Dpt δ y * (L / 6) * (Real.log ((1 + δ) * y) * W (y / X)) := by ring
      _ ≤ Dpt δ y * (L / 6)
            * (Real.log ((1 + δ) * X) * (if y ≤ X then 1 else (X / y) ^ 3)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hD0 (by linarith))
      _ = _ := by ring
  have hBS : ∫ y in Ioc 2 T, Dpt δ y ^ 2 * W (y / X)
      ≤ 4272 / 10 ^ 10 * (δ * L ^ 2 * X ^ 2) := by
    have h1 := setIntegral_mono_on hIS (hIG.const_mul (L / 6 * Real.log ((1 + δ) * X)))
      measurableSet_Ioc hptS
    have e : ∫ y in Ioc 2 T, Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3)
        = ∫ y in (2 : ℝ)..T, Dpt δ y * (if y ≤ X then 1 else (X / y) ^ 3) :=
      (intervalIntegral.integral_of_le hT2.le).symm
    rw [integral_const_mul, e] at h1
    have h3 := asm_log_le_sqrt hδ hδ1 hX
    have hs : √X * √X = X := Real.mul_self_sqrt hX0.le
    have a1 := mul_le_mul_of_nonneg_left hint0
      (mul_nonneg (by linarith : (0 : ℝ) ≤ L / 6) hℓ0)
    have a2 : L / 6 * Real.log ((1 + δ) * X) * (801 / 100 * δ * (X * √X))
        ≤ L / 6 * (96 / 10 ^ 7 * √X) * (801 / 100 * δ * (X * √X)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by linarith)) (by positivity)
    have a3 : L / 6 * (96 / 10 ^ 7 * √X) * (801 / 100 * δ * (X * √X))
        = 12816 / 10 ^ 9 * (L * δ * X ^ 2) := by
      calc L / 6 * (96 / 10 ^ 7 * √X) * (801 / 100 * δ * (X * √X))
          = L / 6 * (96 / 10 ^ 7) * (801 / 100) * δ * X * (√X * √X) := by ring
        _ = _ := by rw [hs]; ring
    have a4 : 12816 / 10 ^ 9 * (L * δ * X ^ 2) ≤ 4272 / 10 ^ 10 * (δ * L ^ 2 * X ^ 2) := by
      have p : 0 ≤ δ * X ^ 2 * L * (L - 30) :=
        mul_nonneg (mul_nonneg (by positivity) hL0) (by linarith)
      nlinarith
    linarith
  -- assembly
  have hU : Ioc 2 T ∪ Ioi T = Ioi 2 := Ioc_union_Ioi_eq_Ioi hT2.le
  have hI : IntegrableOn (fun y => Dpt δ y ^ 2 * W (y / X)) (Ioi 2) := by
    rw [← hU]; exact hIS.union hIL
  refine ⟨hI, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIS hIL]
  have b0 : 0 ≤ δ * L ^ 2 * X ^ 2 := by positivity
  have b1 : 81 / 4 * L ^ 4 * δ ^ 2 * X ^ 2 ≤ 81 / 4 * (961 / 10 ^ 13 * (δ * L ^ 2 * X ^ 2)) := by
    calc 81 / 4 * L ^ 4 * δ ^ 2 * X ^ 2 = 81 / 4 * ((δ * L ^ 2) * (δ * L ^ 2 * X ^ 2)) := by ring
      _ ≤ 81 / 4 * (961 / 10 ^ 13 * (δ * L ^ 2 * X ^ 2)) := by gcongr
  linarith

end LeanLab.Task393
