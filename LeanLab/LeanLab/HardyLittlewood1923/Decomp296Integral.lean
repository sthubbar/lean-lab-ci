import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
AI wrote this Lean code for CODEX task296.
P0004 page 25 equations 3.151 to 3.153.
The bounds below concern the actual local integral kernel.
Binary Goldbach is OPEN.
-/

open Real Set MeasureTheory

namespace LeanLab.HardyLittlewood1923.Decomp296Integral

/-- P0004 page 25 equation 3.153, the pointwise inverse cube bound. -/
theorem inverse_cube_norm_le (a θ : ℝ) (hθ : θ ≠ 0) :
    ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ)‖ ≤ |θ| ^ (-3 : ℤ) := by
  have hnorm : |θ| ≤ ‖(a : ℂ) - Complex.I * θ‖ := by
    simpa using Complex.abs_im_le_norm ((a : ℂ) - Complex.I * θ)
  rw [norm_zpow]
  norm_num only [zpow_neg, zpow_ofNat]
  exact inv_anti₀ (pow_pos (abs_pos.mpr hθ) 3)
    (pow_le_pow_left₀ (abs_nonneg θ) hnorm 3)

#print axioms inverse_cube_norm_le

/-- P0004 page 25 equation 3.153, with the explicit constant one half. -/
theorem inverse_cube_tail {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    IntegrableOn (fun θ : ℝ => ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ)‖) (Ioi T) ∧
    (∫ θ : ℝ in Ioi T, ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ)‖) ≤
      1 / (2 * T ^ 2) := by
  have hne (θ : ℝ) : (a : ℂ) - Complex.I * θ ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp at this
    linarith
  have hc : Continuous (fun θ : ℝ => ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ)‖) := by
    exact ((show Continuous (fun θ : ℝ => (a : ℂ) - Complex.I * θ) by fun_prop).zpow₀
      (-3) (fun θ => Or.inl (hne θ))).norm
  have hg : IntegrableOn (fun θ : ℝ => θ ^ (-3 : ℝ)) (Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have hle (θ : ℝ) (hθ : θ ∈ Ioi T) :
      ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ)‖ ≤ θ ^ (-3 : ℝ) := by
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    simpa only [abs_of_pos (hT.trans hθ)] using
      inverse_cube_norm_le a θ (hT.trans hθ).ne'
  have hf : IntegrableOn (fun θ : ℝ => ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ)‖) (Ioi T) := by
    refine hg.mono' hc.aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with θ hθ
    simpa only [Real.norm_eq_abs, abs_norm] using hle θ hθ
  refine ⟨hf, (integral_mono_ae hf hg ?_).trans_eq ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with θ hθ
    exact hle θ hθ
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT]
    norm_num [Real.rpow_neg, Real.rpow_ofNat]
    ring

#print axioms inverse_cube_tail

/-- P0004 page 25 equations 3.151 to 3.153, including the exponential weight. -/
theorem weighted_cube_tail {a T : ℝ} (ha : 0 < a) (hT : 0 < T) (x : ℝ) :
    IntegrableOn (fun θ : ℝ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
      Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))) (Ioi T) ∧
    ‖∫ θ : ℝ in Ioi T, ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
      Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))‖ ≤
        Real.exp (x * a) / (2 * T ^ 2) := by
  obtain ⟨hi, hb⟩ := inverse_cube_tail ha hT
  have he (θ : ℝ) :
      ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
        Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))‖ =
          ‖((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ)‖ * Real.exp (x * a) := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hne (θ : ℝ) : (a : ℂ) - Complex.I * θ ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp at this
    linarith
  have hc : Continuous (fun θ : ℝ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
      Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))) := by
    apply Continuous.mul
    · exact (show Continuous (fun θ : ℝ => (a : ℂ) - Complex.I * θ) by fun_prop).zpow₀
        (-3) (fun θ => Or.inl (hne θ))
    · fun_prop
  have hf : IntegrableOn (fun θ : ℝ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
      Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))) (Ioi T) := by
    refine (hi.mul_const (Real.exp (x * a))).mono' hc.aestronglyMeasurable.restrict ?_
    exact Filter.Eventually.of_forall (fun θ => (he θ).le)
  refine ⟨hf, (norm_integral_le_integral_norm _).trans ?_⟩
  simp_rw [he]
  rw [integral_mul_const]
  calc _ ≤ (1 / (2 * T ^ 2)) * Real.exp (x * a) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = _ := by ring

#print axioms weighted_cube_tail

/-- P0004 page 25 equation 3.152, the reflected omitted tail. -/
theorem weighted_cube_tail_negative {a T : ℝ} (ha : 0 < a) (hT : 0 < T) (x : ℝ) :
    IntegrableOn (fun θ : ℝ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
      Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))) (Iio (-T)) ∧
    ‖∫ θ : ℝ in Iio (-T), ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
      Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))‖ ≤
        Real.exp (x * a) / (2 * T ^ 2) := by
  let f : ℝ → ℂ := fun θ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
    Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))
  obtain ⟨hf, hb⟩ := weighted_cube_tail ha hT x
  change IntegrableOn f (Ioi T) at hf
  change ‖∫ θ : ℝ in Ioi T, f θ‖ ≤ _ at hb
  have he (θ : ℝ) : f (-θ) = star (f θ) := by
    dsimp [f]
    rw [map_mul, map_zpow₀, ← Complex.exp_conj]
    simp
  have hs : IntegrableOn (fun θ => star (f θ)) (Ioi T) := by
    refine hf.norm.mono' hf.aestronglyMeasurable.star ?_
    exact Filter.Eventually.of_forall (fun θ => (norm_star (f θ)).le)
  have hp : IntegrableOn (fun θ => f (-θ)) (Ioi (-(-T))) := by
    simpa only [neg_neg, he] using hs
  have hn : IntegrableOn f (Iio (-T)) := by
    simpa only [neg_neg] using hp.comp_neg_Iio
  refine ⟨hn, ?_⟩
  change ‖∫ θ : ℝ in Iio (-T), f θ‖ ≤ _
  rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
  simp_rw [he]
  change ‖∫ θ : ℝ in Ioi T, (starRingEnd ℂ) (f θ)‖ ≤ _
  rw [integral_conj]
  simpa using hb

#print axioms weighted_cube_tail_negative

/-- P0004 page 25 equation 3.152, absolute convergence of the full line integral. -/
theorem weighted_cube_integrable {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (fun θ : ℝ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
      Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))) := by
  let f : ℝ → ℂ := fun θ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
    Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))
  have hp : IntegrableOn f (Ioi 1) := (weighted_cube_tail ha zero_lt_one x).1
  have hn : IntegrableOn f (Iio (-1)) := (weighted_cube_tail_negative ha zero_lt_one x).1
  have hne (θ : ℝ) : (a : ℂ) - Complex.I * θ ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp at this
    linarith
  have hc : Continuous f := by
    apply Continuous.mul
    · exact (show Continuous (fun θ : ℝ => (a : ℂ) - Complex.I * θ) by fun_prop).zpow₀
        (-3) (fun θ => Or.inl (hne θ))
    · fun_prop
  have hm : IntegrableOn f (Icc (-1) 1) := hc.continuousOn.integrableOn_compact isCompact_Icc
  have hu : Iio (-1 : ℝ) ∪ Icc (-1) 1 ∪ Ioi 1 = univ := by
    ext θ
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    rcases lt_or_ge θ (-1) with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt θ 1 with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr h'
  rw [← integrableOn_univ, ← hu]
  exact (hn.union hm).union hp

#print axioms weighted_cube_integrable

/-- P0004 page 25 equation 3.152, with both endpoint errors explicit. -/
theorem weighted_cube_truncation {a L R : ℝ} (ha : 0 < a) (hL : L < 0) (hR : 0 < R)
    (x : ℝ) :
    ‖(∫ θ in L..R, ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
        Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))) -
      ∫ θ : ℝ, ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
        Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))‖ ≤
          Real.exp (x * a) / (2 * L ^ 2) + Real.exp (x * a) / (2 * R ^ 2) := by
  let f : ℝ → ℂ := fun θ => ((a : ℂ) - Complex.I * θ) ^ (-3 : ℤ) *
    Complex.exp ((x : ℂ) * ((a : ℂ) - Complex.I * θ))
  have hf : Integrable f := weighted_cube_integrable ha x
  have hd : Disjoint (Iic L) (Ioi R) := by
    apply Set.disjoint_left.mpr
    intro θ hθ hθ'
    exact (not_lt_of_ge (hθ.trans (by linarith : L ≤ R))) hθ'
  have hs := integral_add_compl (s := Ioc L R) (f := f) measurableSet_Ioc hf
  rw [compl_Ioc, setIntegral_union hd measurableSet_Ioi hf.integrableOn hf.integrableOn] at hs
  have hleft : ‖∫ θ : ℝ in Iic L, f θ‖ ≤ Real.exp (x * a) / (2 * L ^ 2) := by
    have hb := (weighted_cube_tail_negative ha (neg_pos.mpr hL) x).2
    simpa only [neg_neg, neg_sq, integral_Iic_eq_integral_Iio] using hb
  have hright : ‖∫ θ : ℝ in Ioi R, f θ‖ ≤ Real.exp (x * a) / (2 * R ^ 2) :=
    (weighted_cube_tail ha hR x).2
  change ‖(∫ θ in L..R, f θ) - ∫ θ : ℝ, f θ‖ ≤ _
  rw [intervalIntegral.integral_of_le (by linarith : L ≤ R)]
  have he : (∫ θ in Ioc L R, f θ) - ∫ θ : ℝ, f θ =
      -((∫ θ in Iic L, f θ) + ∫ θ in Ioi R, f θ) := by
    linear_combination hs
  rw [he, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add hleft hright)

#print axioms weighted_cube_truncation

/-- P0004 page 25 equation 3.153, after supplying the lower bound on both Farey widths. -/
theorem model_segment_error {n : ℕ} (hn : 0 < n) {L R K : ℝ} (hK : 0 < K)
    (hL : 1 / (2 * K) ≤ -L) (hR : 1 / (2 * K) ≤ R) :
    ‖(∫ θ in L..R, ((1 / (n : ℂ)) - Complex.I * θ) ^ (-3 : ℤ) *
        Complex.exp ((n : ℂ) * ((1 / (n : ℂ)) - Complex.I * θ))) -
      ∫ θ : ℝ, ((1 / (n : ℂ)) - Complex.I * θ) ^ (-3 : ℤ) *
        Complex.exp ((n : ℂ) * ((1 / (n : ℂ)) - Complex.I * θ))‖ ≤
          4 * Real.exp 1 * K ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < 1 / (2 * K) := by positivity
  have hLp : 0 < -L := hw.trans_le hL
  have hRp : 0 < R := hw.trans_le hR
  have hb {b : ℝ} (hb : 0 < b) (hwb : 1 / (2 * K) ≤ b) :
      Real.exp 1 / (2 * b ^ 2) ≤ 2 * Real.exp 1 * K ^ 2 := by
    have hi : b⁻¹ ≤ 2 * K := by
      have hi := one_div_le_one_div_of_le hw hwb
      simpa using hi
    calc _ = Real.exp 1 * (b⁻¹ ^ 2) / 2 := by ring
      _ ≤ Real.exp 1 * ((2 * K) ^ 2) / 2 := by gcongr
      _ = _ := by ring
  have ht := weighted_cube_truncation (a := 1 / (n : ℝ)) (by positivity)
    (neg_pos.mp hLp) hRp (n : ℝ)
  rw [mul_one_div_cancel hnR.ne'] at ht
  push_cast at ht
  have hleft := hb hLp hL
  rw [neg_sq] at hleft
  exact ht.trans (by linarith [hb hRp hR])

#print axioms model_segment_error

end LeanLab.HardyLittlewood1923.Decomp296Integral
