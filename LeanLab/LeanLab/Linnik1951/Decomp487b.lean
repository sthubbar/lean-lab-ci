/-
P0093 route supplies for Assembly376.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp442b
import LeanLab.Linnik1951.Decomp487a
import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 157 truncation before equation 4.4. The signed Mellin integral on the finite frequency interval of radius N over R times log cubed N. -/
noncomputable def truncatedMellin487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (α : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
      mellinKernel442 N α t * M t

/-- P0093 page 157 equation 4.4. The signed kernel with a continuous coefficient is jointly continuous in alpha and the finite line parameter. -/
theorem continuous_mellin_integrand487 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2 * M p.2) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hNr
  let Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hZ : Continuous Z := by dsimp [Z]; fun_prop
  have hline : Continuous (fun t : ℝ => mellinLine1622 N t) := by
    dsimp [mellinLine1622]; fun_prop
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine1622 N t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp hline.continuousAt
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.neg_re, Complex.natCast_re] at hh
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hinv : 0 < 1 / Real.log N := by positivity
    linarith
  have hslit (p : ℝ × ℝ) : Z p.1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  exact (((hZ.comp continuous_fst).cpow (hline.comp continuous_snd).neg hslit).mul
    (hGamma.comp continuous_snd)).mul (hM.comp continuous_snd)

/-- P0093 page 157 finite contour before equation 4.4. Its Mellin value is continuous in alpha. -/
theorem continuous_truncatedMellin487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ)
    (M : ℝ → ℂ) (hM : Continuous M) :
    Continuous (truncatedMellin487 N R M) := by
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_mellin_integrand487 N hN M hM) _ _)

/-- P0093 page 156 equation 4.1. Parameter integration of the continuous signed kernel makes the full Mellin value strongly measurable. -/
theorem stronglyMeasurable_mellinU487 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    StronglyMeasurable (mellinU1622 N M) := by
  exact stronglyMeasurable_const.mul
    (continuous_mellin_integrand487 N hN M hM).stronglyMeasurable.integral_prod_right

/-- P0093 page 157 equation 4.4. The square of the finite Mellin integral is exactly its signed double kernel. No absolute value is inserted into either line integral. -/
theorem truncated_signed_square487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (α : ℝ) :
    ‖truncatedMellin487 N R M α‖ ^ 2 = (1 / (2 * Real.pi)) ^ 2 *
      (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
        ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          (mellinKernel442 N α t * M t) *
            (starRingEnd ℂ) (mellinKernel442 N α u * M u)).re := by
  let f : ℝ → ℂ := fun t => mellinKernel442 N α t * M t
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  have hprod : (∫ t in -T..T, ∫ u in -T..T, f t * (starRingEnd ℂ) (f u)) =
      ((‖∫ t in -T..T, f t‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.intervalIntegral_conj, intervalIntegral.integral_mul_const,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t in -T..T, f t)‖ ^ 2 =
    (1 / (2 * Real.pi)) ^ 2 * (∫ t in -T..T, ∫ u in -T..T, f t * (starRingEnd ℂ) (f u)).re
  rw [hprod, Complex.ofReal_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), mul_pow]

/-- P0093 page 157 equation 4.4. On the finite contour the alpha integral can be moved inside both signed frequency integrals. All exchanges follow from continuity on compact rectangles. -/
theorem truncated_signed_fubini487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ)
    (M : ℝ → ℂ) (hM : Continuous M) (a b : ℝ) :
    let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
    (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) =
      (1 / (2 * Real.pi)) ^ 2 *
        (∫ t in -T..T, ∫ u in -T..T, ∫ α in a..b,
          (mellinKernel442 N α t * M t) *
            (starRingEnd ℂ) (mellinKernel442 N α u * M u)).re := by
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  let F : ℝ → ℝ → ℝ → ℂ := fun α t u =>
    (mellinKernel442 N α t * M t) *
      (starRingEnd ℂ) (mellinKernel442 N α u * M u)
  have hK := continuous_mellin_integrand487 N hN M hM
  have hF : Continuous (fun p : (ℝ × ℝ) × ℝ => F p.1.1 p.1.2 p.2) := by
    exact (hK.comp (continuous_fst.fst.prodMk continuous_fst.snd)).mul
      ((hK.comp (continuous_fst.fst.prodMk continuous_snd)).star)
  have hFi : Continuous (fun p : ℝ × ℝ => ∫ u in -T..T, F p.1 p.2 u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF (-T) T
  have hFii : Continuous (fun α : ℝ => ∫ t in -T..T, ∫ u in -T..T, F α t u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFi (-T) T
  have hswap1 : (∫ α in a..b, ∫ t in -T..T, ∫ u in -T..T, F α t u) =
      ∫ t in -T..T, ∫ α in a..b, ∫ u in -T..T, F α t u := by
    apply intervalIntegral_intervalIntegral_swap
    exact (hFi.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap2 (t : ℝ) : (∫ α in a..b, ∫ u in -T..T, F α t u) =
      ∫ u in -T..T, ∫ α in a..b, F α t u := by
    have hFc : Continuous (fun p : ℝ × ℝ => F p.1 t p.2) := by
      exact (hK.comp (continuous_fst.prodMk continuous_const)).mul hK.star
    apply intervalIntegral_intervalIntegral_swap
    exact (hFc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  change (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) =
    (1 / (2 * Real.pi)) ^ 2 * (∫ t in -T..T, ∫ u in -T..T, ∫ α in a..b, F α t u).re
  calc
    _ = (1 / (2 * Real.pi)) ^ 2 *
        (∫ α in a..b, (∫ t in -T..T, ∫ u in -T..T, F α t u).re) := by
      simp_rw [truncated_signed_square487]
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / (2 * Real.pi)) ^ 2 *
        (∫ α in a..b, ∫ t in -T..T, ∫ u in -T..T, F α t u).re := by
      congr 1
      exact intervalIntegral.intervalIntegral_re (hFii.intervalIntegrable a b)
    _ = _ := by rw [hswap1]; simp_rw [hswap2]

/-- P0093 page 157 argument identity before equation 4.4. On the positive outer interval the angular gap has the quantitative lower bound R over ten N. Its dependence on N is retained. -/
theorem outer_angular_gap_scaled487 (N R α : ℝ) (hR : 0 < R) (hRN : R ≤ N)
    (hα : 0 ≤ α) (hcap : α ≤ 1 / R) :
    R / (10 * N) ≤ Real.pi / 2 -
      (((1 / N : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).arg := by
  have hN : 0 < N := hR.trans_le hRN
  let z : ℂ := ((1 / N : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hre : z.re = 1 / N := by simp [z]
  have him : z.im = 2 * Real.pi * α := by simp [z]
  have hzre : 0 < z.re := by rw [hre]; positivity
  have hz : z ≠ 0 := by intro hh; simp [hh] at hzre
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm : ‖z‖ ≤ 10 / R := by
    calc
      _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ = 1 / N + 2 * Real.pi * α := by
        rw [hre, him, abs_of_pos (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ 1 / R + 2 * Real.pi * (1 / R) :=
        add_le_add (one_div_le_one_div_of_le hR hRN)
          (mul_le_mul_of_nonneg_left hcap (by positivity))
      _ = (1 + 2 * Real.pi) / R := by ring
      _ ≤ 10 / R := div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) hR.le
  have hnormR : R * ‖z‖ ≤ 10 := by
    have hh := (le_div_iff₀ hR).mp hnorm
    nlinarith
  have hratio : R / (10 * N) ≤ z.re / ‖z‖ := by
    rw [div_le_div_iff₀ (by positivity : 0 < 10 * N) hn, hre]
    have he : 1 / N * (10 * N) = 10 := by field_simp
    rw [he]
    exact hnormR
  have harg : z.arg ≤ Real.pi / 2 :=
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl hzre.le)
  have hs := Real.sin_le (sub_nonneg.mpr harg)
  rw [Real.sin_pi_div_two_sub, Complex.cos_arg hz] at hs
  exact hratio.trans hs

/-- P0093 page 157 power factor before equation 4.4. For real part of z equal to one over N, the shifted power has norm at most exp one times square root N times exp of absolute t times absolute argument. -/
theorem mellin_power_factor487 (N : ℕ) (hN : 2 ≤ N) (z : ℂ)
    (hzre : z.re = 1 / (N : ℝ)) (t : ℝ) :
    ‖z ^ (-(mellinLine1622 N t))‖ ≤
      Real.exp 1 * Real.sqrt N * Real.exp (|t| * |z.arg|) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set σ : ℝ := 1 / 2 + 1 / Real.log N with hσdef
  have hσpos : 0 < σ := by
    have : 0 < 1 / Real.log N := div_pos one_pos hlog
    rw [hσdef]; linarith
  have hre : (-(mellinLine1622 N t)).re = -σ := by
    simp only [mellinLine1622, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, hσdef]
  have him : (-(mellinLine1622 N t)).im = -t := by
    simp only [mellinLine1622, Complex.neg_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
      add_zero, zero_add]
  have h := Complex.norm_cpow_le z (-(mellinLine1622 N t))
  rw [hre, him] at h
  have hznorm : (1 / (N : ℝ)) ≤ ‖z‖ := by
    have h1 := Complex.abs_re_le_norm z
    rw [hzre] at h1
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))] at h1
    exact h1
  have h1 : ‖z‖ ^ (-σ) ≤ (N : ℝ) ^ σ := by
    have hstep := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1 / (N:ℝ)) hznorm
      (show -σ ≤ 0 from by linarith)
    have hbase : ((1 : ℝ) / (N : ℝ)) ^ (-σ) = (N : ℝ) ^ σ := by
      rw [one_div, Real.inv_rpow hNpos.le, ← Real.rpow_neg]
      · ring_nf
      · exact hNpos.le
    rwa [hbase] at hstep
  have hNpow : (N : ℝ) ^ σ = Real.exp 1 * Real.sqrt N := by
    have hadd : (N : ℝ) ^ σ = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / Real.log N) := by
      rw [hσdef, Real.rpow_add hNpos]
    rw [hadd, ← Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos,
      show Real.log (N : ℝ) * (1 / Real.log (N : ℝ)) = 1 from by field_simp]
    ring
  have h3 : (Real.exp (z.arg * -t))⁻¹ ≤ Real.exp (|t| * |z.arg|) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [le_abs_self t, neg_abs_le z.arg, le_abs_self z.arg, neg_abs_le t,
      mul_le_mul_of_nonneg_left (le_abs_self t) (abs_nonneg z.arg)]
  calc ‖z ^ (-(mellinLine1622 N t))‖
      ≤ ‖z‖ ^ (-σ) / Real.exp (z.arg * -t) := h
    _ = ‖z‖ ^ (-σ) * (Real.exp (z.arg * -t))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (N : ℝ) ^ σ * Real.exp (|t| * |z.arg|) :=
        mul_le_mul h1 h3 (by positivity) (Real.rpow_nonneg hNpos.le σ)
    _ = Real.exp 1 * Real.sqrt N * Real.exp (|t| * |z.arg|) := by rw [hNpow]

/-- P0093 page 157 Gamma and power factors before equation 4.4. On the positive outer alpha interval the full signed kernel has decay rate R over ten N. This retains the shrinking angular gap. -/
theorem outer_kernel_scaled_decay487 (N : ℕ) (hN : 3 ≤ N) (R α t : ℝ)
    (hR : 0 < R) (hRN : R ≤ (N : ℝ)) (hα : 0 ≤ α) (hcap : α ≤ 1 / R) :
    ‖mellinKernel442 N α t‖ ≤
      (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) *
        (3 + |t|) * Real.exp (-(R / (10 * (N : ℝ))) * |t|) := by
  let z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hre : z.re = 1 / (N : ℝ) := by simp [z]
  have him : z.im = 2 * Real.pi * α := by simp [z]
  have harg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by rw [him]; positivity)
  have hp := mellin_power_factor487 N (by omega) z hre t
  rw [abs_of_nonneg harg] at hp
  have hg := gamma_mellin_line442 N hN t
  have hgap : R / (10 * (N : ℝ)) ≤ Real.pi / 2 - z.arg :=
    outer_angular_gap_scaled487 (N : ℝ) R α hR hRN hα hcap
  have he : Real.exp (|t| * (z.arg - Real.pi / 2)) ≤
      Real.exp (-(R / (10 * (N : ℝ))) * |t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hgap (abs_nonneg t)]
  calc
    _ = ‖z ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ := norm_mul _ _
    _ ≤ (Real.exp 1 * Real.sqrt N * Real.exp (|t| * z.arg)) *
        (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul hp hg (norm_nonneg _) (by positivity)
    _ = (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) *
        (3 + |t|) * Real.exp (|t| * (z.arg - Real.pi / 2)) := by
      rw [show |t| * (z.arg - Real.pi / 2) = |t| * z.arg + -(Real.pi * |t| / 2) by ring,
        Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

/-- P0093 page 157 truncation remainder. An auxiliary scalar absorption step for the scaled Gamma tail: every fixed positive C times N to power ten times exp of negative log cubed N over twenty is eventually at most one. -/
theorem outer_tail_polynomial_absorption487 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) ^ 10 * Real.exp (-(Real.log N ^ 3 / 20)) ≤ 1 := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max C (Real.exp 20))
  refine ⟨N0, ?_⟩
  intro N hN
  have hNr : (N0 : ℝ) < N := by exact_mod_cast hN
  have hCN : C ≤ (N : ℝ) := (le_max_left _ _).trans (hN0.trans hNr).le
  have hexp : Real.exp 20 ≤ (N : ℝ) := (le_max_right _ _).trans (hN0.trans hNr).le
  have hNp : (0 : ℝ) < N := (Real.exp_pos 20).trans_le hexp
  have hlog : 20 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 20) hexp
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hsq : (220 : ℝ) ≤ Real.log N ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq hlog0
  have hcube : 11 * Real.log N ≤ Real.log N ^ 3 / 20 := by nlinarith
  have hp : (N : ℝ) ^ 10 = Real.exp (10 * Real.log N) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hNp] using
      (Real.exp_nat_mul (Real.log (N : ℝ)) 10).symm
  calc
    _ = C * Real.exp (10 * Real.log N - Real.log N ^ 3 / 20) := by
      rw [hp, mul_assoc, ← Real.exp_add]
      congr 2
    _ ≤ C * Real.exp (-Real.log N) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
    _ = C / (N : ℝ) := by rw [Real.exp_neg, Real.exp_log hNp]; ring
    _ ≤ 1 := (div_le_one hNp).mpr hCN

/-- LEAF. P0093 page 157 truncation before equation 4.4. The written exponentially small remainder is eventually at most one, uniformly over the outer alpha interval and line bounded coefficients. No frequency square estimate occurs. -/
theorem outer_tail_pointwise487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ≤ 1 := by
  sorry

/-- P0093 page 157 truncation before equation 4.4. The tail square mass is bounded by one after integrating the pointwise remainder. CONDITIONAL only on outer_tail_pointwise487. -/
theorem outer_tail_square487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ =>
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2)
              volume (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R),
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2) ≤ D := by
  obtain ⟨Nt, ht⟩ := outer_tail_pointwise487 B0 hB0
  refine ⟨1, by norm_num, max 8 Nt, ?_⟩
  intro N hN R hR1 hR M hM
  have h8 : 8 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hab : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNp hRp]
    have hfour := four_rpow1622 N h8
    nlinarith
  have hbound (α : ℝ) (hα : α ∈ Set.Icc (4 / (N : ℝ)) (1 / R)) :
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2 ≤ 1 := by
    have hh := ht N (lt_of_le_of_lt (le_max_right _ _) hN) R hR1 hR M hM α hα
    have hn := norm_nonneg (mellinU1622 N M α - truncatedMellin487 N R M α)
    nlinarith
  have hmeas : StronglyMeasurable (fun α : ℝ =>
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2) := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using
      ((stronglyMeasurable_mellinU487 N (by omega) M hM.1).sub
        (continuous_truncatedMellin487 N (by omega) R M hM.1).stronglyMeasurable).norm.fun_pow 2
  have hInt : IntegrableOn (fun α : ℝ =>
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2)
      (Set.Icc (4 / (N : ℝ)) (1 / R)) := by
    change Integrable (fun α : ℝ =>
      ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2)
      (volume.restrict (Set.Icc (4 / (N : ℝ)) (1 / R)))
    refine (show IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (4 / (N : ℝ)) (1 / R)) volume from continuous_const.integrableOn_Icc).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound α hα
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hInt
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ _α in (4 / (N : ℝ))..(1 / R), (1 : ℝ) :=
      intervalIntegral.integral_mono_on hab hI intervalIntegrable_const hbound
    _ = 1 / R - 4 / (N : ℝ) := by simp
    _ ≤ 1 := by
      have hh : 1 / R ≤ 1 := (div_le_one hRp).mpr hR1
      have hn : 0 ≤ 4 / (N : ℝ) := by positivity
      linarith


/-- LEAF. P0093 pages 157 and 158 equations 4.4 through 4.7. The square mass of the finite signed contour is bounded by the difference and sum frequency kernels. Complex phases stay inside the t integral. This has no infinite contour or truncation error and no character or GRH. -/
theorem outer_finite_square487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2)
            volume (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  sorry

/-- P0093 pages 157 and 158 equations 4.3 through 4.7. Exact abstract_outer_kernels442 statement from the finite signed contour and its tail. CONDITIONAL only on outer_tail_square487 and outer_finite_square487. -/
theorem abstract_outer_kernels487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) volume
            (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
            A * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            A * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + A := by
  obtain ⟨D, hD, Nt, ht⟩ := outer_tail_square487 B0 hB0
  obtain ⟨C, hC, Nc, hc⟩ := outer_finite_square487 B0 hB0
  obtain ⟨Ni, hi⟩ := outer_mellin_sq_integrable442 B0 hB0
  refine ⟨2 * C + 2 * D, by positivity, max 8 (max Nt (max Nc Ni)), ?_⟩
  intro N hN R hR1 hR M hM
  have h8 : 8 ≤ N := by omega
  have hNt : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNc : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNi : Ni < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hab : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNp hRp]
    have hfour := four_rpow1622 N h8
    nlinarith
  obtain ⟨hIt, htail⟩ := ht N hNt R hR1 hR M hM
  obtain ⟨hIc, hcore⟩ := hc N hNc R hR1 hR M hM
  have hI := hi N hNi R hR1 hR M hM
  refine ⟨hI, ?_⟩
  have hpoint (α : ℝ) : ‖mellinU1622 N M α‖ ^ 2 ≤
      2 * ‖truncatedMellin487 N R M α‖ ^ 2 +
      2 * ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ^ 2 :=
    norm_sq_le_of_near1622 (le_refl _)
  have hmono := intervalIntegral.integral_mono_on hab hI
    ((hIc.const_mul 2).add (hIt.const_mul 2)) (fun α _ => hpoint α)
  rw [intervalIntegral.integral_add (hIc.const_mul 2) (hIt.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  let T := (N : ℝ) / R * Real.log N ^ 3
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hd : 0 ≤ differenceKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
  have hs : 0 ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => (Real.exp_pos _).le)
  have hx : 0 ≤ Real.log N ^ 6 * differenceKernel376 T := mul_nonneg (by positivity) hd
  have hy : 0 ≤ Real.log N ^ 7 * sumKernel376 T := mul_nonneg (by positivity) hs
  change _ ≤ C * Real.log N ^ 6 * differenceKernel376 T +
    C * Real.log N ^ 7 * sumKernel376 T at hcore
  change _ ≤ (2 * C + 2 * D) * Real.log N ^ 6 * differenceKernel376 T +
    (2 * C + 2 * D) * Real.log N ^ 7 * sumKernel376 T + (2 * C + 2 * D)
  nlinarith [mul_nonneg hD.le hx, mul_nonneg hD.le hy]


/-- P0093 pages 158 and 159 equations 4.4 through 5.1. Exact outer_to_kernels376 statement. CONDITIONAL on the two signed outer leaves, mellin_transfer1622 and GRH. -/
theorem outer_to_kernels487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * Real.log N ^ 6 * differenceKernel376
                ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3) +
              B * Real.log N ^ 7 * sumKernel376
                ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3) + B := by
  obtain ⟨B0, hB0, D, hD, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨A, hA, Na, ha⟩ := abstract_outer_kernels487 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * A + 2 * D ^ 2, by positivity, max 8 (max L (max Nt Na)), ?_⟩
  intro N hN q hq hqt χ hχ
  have h8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNt : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 1 ≤ Real.log N := by
    have hNrL : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hNrL).le
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set R := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hR
  obtain ⟨hR1, hR2⟩ := qtau_range1622 N q (by omega) hq hqt
  have hRp : 0 < R := by dsimp [R]; positivity
  have hRN : R ≤ N := by
    have := four_rpow1622 N (by omega)
    change R ≤ (N : ℝ) ^ (2 / 7 : ℝ) at hR2
    have : 0 ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by positivity
    linarith
  have huv : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNr hRp]
    have := four_rpow1622 N (by omega)
    change R ≤ (N : ℝ) ^ (2 / 7 : ℝ) at hR2
    linarith
  obtain ⟨M, hM, hm⟩ := ht N hNt q hq hqt χ hχ
  obtain ⟨hIU, hU⟩ := ha N hNa R hR1 hR2 M hM
  have hc := (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hmono : (∫ α in (4 / (N : ℝ))..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
      ∫ α in (4 / (N : ℝ))..(1 / R),
        2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (D * Real.sqrt N) ^ 2 :=
    intervalIntegral.integral_mono_on huv (hc.intervalIntegrable _ _)
      ((hIU.const_mul 2).add intervalIntegrable_const)
      (fun α _ => norm_sq_le_of_near1622 (hm α))
  rw [intervalIntegral.integral_add (hIU.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  set T := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hratio : 1 ≤ (N : ℝ) / R := (le_div_iff₀ hRp).mpr (by simpa using hRN)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hratio (one_le_pow₀ hl)
  have hdiff := difference_kernel_lower442 T hT1
  have hdiff0 : 0 ≤ differenceKernel376 T := by linarith
  have hsum0 : 0 ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => (Real.exp_pos _).le)
  have hratioT : (N : ℝ) / R ≤ T := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl)
  have herr : (1 / R - 4 / (N : ℝ)) * (2 * (D * Real.sqrt N) ^ 2) ≤
      2 * D ^ 2 * (Real.log N ^ 6 * differenceKernel376 T) := by
    have hsq : (D * Real.sqrt N) ^ 2 = D ^ 2 * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hNr.le]
    rw [hsq]
    have hh : (1 / R - 4 / (N : ℝ)) * (N : ℝ) ≤ (N : ℝ) / R := by
      have : 0 ≤ 4 / (N : ℝ) := by positivity
      calc
        _ ≤ (1 / R) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hNr.le
        _ = _ := by ring
    have hc := (hratioT.trans hdiff).trans
      (le_mul_of_one_le_left hdiff0 (one_le_pow₀ hl (n := 6)))
    calc
      _ = 2 * D ^ 2 * ((1 / R - 4 / (N : ℝ)) * (N : ℝ)) := by ring
      _ ≤ 2 * D ^ 2 * ((N : ℝ) / R) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
  change _ ≤ A * Real.log N ^ 6 * differenceKernel376 T +
    A * Real.log N ^ 7 * sumKernel376 T + A at hU
  change _ ≤ (2 * A + 2 * D ^ 2) * Real.log N ^ 6 * differenceKernel376 T +
    (2 * A + 2 * D ^ 2) * Real.log N ^ 7 * sumKernel376 T + (2 * A + 2 * D ^ 2)
  have hsumterm : 0 ≤ D ^ 2 * (Real.log N ^ 7 * sumKernel376 T) :=
    mul_nonneg (sq_nonneg D)
      (mul_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log N) 7) hsum0)
  nlinarith [sq_nonneg D]

/-- P0093 page 158 equation 4.7. Exact abstract outer integral bound from the two real kernel estimates. CONDITIONAL only on the finite signed contour and its tail. -/
theorem lemma2_outer487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) MeasureTheory.volume
          (4 / (N : ℝ)) (1 / R) ∧
        (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
          B * ((N : ℝ) / R * Real.log N ^ 3) * Real.log N ^ 7 := by
  obtain ⟨A, hA, N0, ha⟩ := abstract_outer_kernels487 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨57 * A, by positivity, max 3 (max N0 L), ?_⟩
  intro N hN R hR1 hR M hM
  have h3 : 3 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRp : 0 < R := by linarith
  have hl : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
  have hRN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  let V := (N : ℝ) / R
  let T := V * Real.log N ^ 3
  have hV1 : 1 ≤ V := (le_div_iff₀ hRp).mpr (by simpa using hRN)
  have hVN : V ≤ N := (div_le_iff₀ hRp).mpr (by nlinarith)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hV1 (one_le_pow₀ hl)
  have hd := difference_kernel_le376 T hT1
  have hs := sum_kernel_le376 T hT1
  have hw := frequency_window_log376 N V (by exact_mod_cast h3.le) (by linarith) hVN
  obtain ⟨hI, hU⟩ := ha N hN0 R hR1 hR M hM
  refine ⟨hI, ?_⟩
  change _ ≤ A * Real.log N ^ 6 * differenceKernel376 T +
    A * Real.log N ^ 7 * sumKernel376 T + A at hU
  have hdiff : A * Real.log N ^ 6 * differenceKernel376 T ≤
      40 * A * V * Real.log N ^ 10 := by
    calc
      _ ≤ A * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) :=
        mul_le_mul_of_nonneg_left
          (hd.trans (mul_le_mul_of_nonneg_left hw (by positivity))) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hsum : A * Real.log N ^ 7 * sumKernel376 T ≤
      16 * A * V * Real.log N ^ 10 := by
    calc
      _ ≤ A * Real.log N ^ 7 * (16 * T) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by dsimp [T]; ring
  have hconst : A ≤ A * V * Real.log N ^ 10 := by
    have hh := one_le_mul_of_one_le_of_one_le hV1 (one_le_pow₀ hl (n := 10))
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hh hA.le
  have htotal : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
      57 * A * V * Real.log N ^ 10 := by linarith
  refine htotal.trans (le_of_eq ?_)
  dsimp [V]
  ring

/-- P0093 page 158 equation 4.7. Exact positive outer integral supply from the two real kernel bounds. CONDITIONAL on the two signed outer leaves, mellin_transfer1622 and GRH. The refuted absolute mass child is not used. -/
theorem mellin_positive_far487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hb⟩ := outer_to_kernels487 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨57 * B, by positivity, max 3 (max N0 L), ?_⟩
  intro N hN q hq hqt χ hχ
  have h3 : 3 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
    simpa only [Real.log_exp] using hh
  let D := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)
  let R := (N : ℝ) / D
  let T := R * Real.log N ^ 3
  have htau : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le hqR htau
  have hDpos : 0 < D := by linarith
  have hDN : D ≤ N := by
    calc
      D ≤ (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right hqt (by positivity)
      _ = (N : ℝ) ^ (2 / 7 : ℝ) := by rw [← Real.rpow_add hNp]; congr 1; norm_num
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hR1 : 1 ≤ R := (le_div_iff₀ hDpos).mpr (by simpa using hDN)
  have hRN : R ≤ N := (div_le_iff₀ hDpos).mpr (by
    simpa using mul_le_mul_of_nonneg_left hD1 hNp.le)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hR1 (one_le_pow₀ hlog)
  have hdiff := difference_kernel_le376 T hT1
  have hsum := sum_kernel_le376 T hT1
  have hwindow := frequency_window_log376 N R (by exact_mod_cast h3.le) (by linarith) hRN
  have hsmall : 1 ≤ R * Real.log N ^ 10 := one_le_mul_of_one_le_of_one_le hR1 (one_le_pow₀ hlog)
  have h := hb N hN0 q hq hqt χ hχ
  change _ ≤ B * Real.log N ^ 6 * differenceKernel376 T +
    B * Real.log N ^ 7 * sumKernel376 T + B at h
  have hd : B * Real.log N ^ 6 * differenceKernel376 T ≤
      40 * B * R * Real.log N ^ 10 := by
    calc
      _ ≤ B * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) :=
        mul_le_mul_of_nonneg_left
          (hdiff.trans (mul_le_mul_of_nonneg_left hwindow (by positivity))) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hs : B * Real.log N ^ 7 * sumKernel376 T ≤
      16 * B * R * Real.log N ^ 10 := by
    calc
      _ ≤ B * Real.log N ^ 7 * (16 * T) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp [T]; ring
  have hconst : B ≤ B * R * Real.log N ^ 10 := by
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hsmall hB.le
  calc
    _ ≤ 57 * B * R * Real.log N ^ 10 := by linarith
    _ = _ := by dsimp [R, D]; ring

/-- P0093 page 158 equation 4.7 at a general radius. CONDITIONAL on the signed abstract outer kernels, the character transfer and GRH. -/
theorem mellin_outer_general487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 10 := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨C, hC, Nc, hc⟩ := lemma2_outer487 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C + 2 * B ^ 2, by positivity, max 8 (max L (max Nt Nc)), ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
  have h8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have htN : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hcN : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hlog : 1 ≤ Real.log N := by
    have hLNreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLNreal).le
    simpa only [Real.log_exp] using hh
  have huv : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNr hRpos]
    have := four_rpow1622 N (by omega)
    nlinarith
  obtain ⟨M, hM, hA⟩ := ht N htN q hq hqt χ hχ
  obtain ⟨hIU, hU⟩ := hc N hcN R hR1 hR M hM
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hmono : (∫ α in (4 / (N : ℝ))..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
      ∫ α in (4 / (N : ℝ))..(1 / R),
        (2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (B * Real.sqrt N) ^ 2) :=
    intervalIntegral.integral_mono_on huv (hcont.intervalIntegrable _ _)
      ((hIU.const_mul 2).add intervalIntegrable_const)
      (fun α _ => norm_sq_le_of_near1622 (hA α))
  have hsplit : (∫ α in (4 / (N : ℝ))..(1 / R),
      (2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (B * Real.sqrt N) ^ 2)) =
      2 * (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) +
        2 * (B * Real.sqrt N) ^ 2 * (1 / R - 4 / (N : ℝ)) := by
    rw [intervalIntegral.integral_add (hIU.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hsq : (B * Real.sqrt N) ^ 2 = B ^ 2 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hNr.le]
  have hNR : 0 ≤ (N : ℝ) / R := by positivity
  have hlen : (N : ℝ) * (1 / R - 4 / (N : ℝ)) ≤ (N : ℝ) / R := by
    have : 0 ≤ 4 / (N : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left (show 1 / R - 4 / (N : ℝ) ≤ 1 / R by linarith) hNr.le
    calc _ ≤ (N : ℝ) * (1 / R) := h
      _ = _ := by ring
  have h10 : 1 ≤ Real.log N ^ 10 := one_le_pow₀ hlog
  have hU' : B * 0 + C * ((N : ℝ) / R * Real.log N ^ 3) * Real.log N ^ 7 =
      C * ((N : ℝ) / R) * Real.log N ^ 10 := by ring
  rw [hsplit, hsq] at hmono
  have hA2 : 2 * B ^ 2 * (N : ℝ) * (1 / R - 4 / (N : ℝ)) ≤
      2 * B ^ 2 * ((N : ℝ) / R) * Real.log N ^ 10 := by
    have hb : 0 ≤ 2 * B ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hlen hb
    have h2 : (N : ℝ) / R ≤ (N : ℝ) / R * Real.log N ^ 10 := le_mul_of_one_le_right hNR h10
    have h3 := mul_le_mul_of_nonneg_left h2 hb
    nlinarith
  have hend : (2 * C + 2 * B ^ 2) * (N : ℝ) / R * Real.log N ^ 10 =
      2 * (C * ((N : ℝ) / R) * Real.log N ^ 10) + 2 * B ^ 2 * ((N : ℝ) / R) * Real.log N ^ 10 := by
    ring
  rw [hend]
  have hU2 : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
      C * ((N : ℝ) / R) * Real.log N ^ 10 := by
    refine hU.trans (le_of_eq ?_)
    ring
  linarith

/-- P0093 page 158 final sentence at a general radius. Reflection gives the negative interval. CONDITIONAL on the signed abstract outer kernels, the character transfer and GRH. -/
theorem mellin_outer_negative487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(1 / R)..-(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hpos⟩ := mellin_outer_general487 hG
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [character_norm_reflect357]
  exact hpos N hN q hq hqt (star χ) hstar R hR1 hR

/-- P0093 page 159 equation 5.2 at a general radius. CONDITIONAL on mellin_transfer1622, the finite signed contour and its tail, and GRH. No absolute outer mass estimate is used. -/
theorem mellin_radius487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ α in -(1 / R)..(1 / R), ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨B0, hB0, N0, h0⟩ := mellin_central_general487 hG
  obtain ⟨Bp, hBp, Np, hp⟩ := mellin_outer_general487 hG
  obtain ⟨Bm, hBm, Nm, hm⟩ := mellin_outer_negative487 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨Bm + B0 + Bp, by positivity, max 1 (max L (max N0 (max Np Nm))), ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h0N : N0 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hpN : Np < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hmN : Nm < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hlog : 1 ≤ Real.log N := by
    have hLNreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLNreal).le
    simpa only [Real.log_exp] using hh
  have hRpos : (0 : ℝ) < R := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h6 : Real.log N ^ 6 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have h10 : Real.log N ^ 10 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / R)) (-(4 / (N : ℝ))))
    (hcont.intervalIntegrable (-(4 / (N : ℝ))) (4 / (N : ℝ)))
  have hadd' := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / R)) (4 / (N : ℝ)))
    (hcont.intervalIntegrable (4 / (N : ℝ)) (1 / R))
  rw [← hadd', ← hadd]
  have b0 := (h0 N h0N q hq hqt χ hχ R hR1 hR).trans
    (mul_le_mul_of_nonneg_left h6 (by positivity))
  have bp := (hp N hpN q hq hqt χ hχ R hR1 hR).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  have bm := (hm N hmN q hq hqt χ hχ R hR1 hR).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  calc
    _ ≤ Bm * N / R * Real.log N ^ 13 + B0 * N / R * Real.log N ^ 13 +
        Bp * N / R * Real.log N ^ 13 := add_le_add (add_le_add bm b0) bp
    _ = _ := by ring

/-- P0093 page 157 truncation remainder, auxiliary scalar estimate. The quartic exponential tail on the positive half line is bounded by its half rate full Gamma moment times the cutoff exponential. -/
theorem quartic_exponential_tail487 (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) :
    (∫ x in Set.Ioi T, x ^ 4 * Real.exp (-(c * x))) ≤
      (24 / (c / 2) ^ 5) * Real.exp (-(c / 2 * T)) := by
  have hfull (d : ℝ) (hd : 0 < d) :
      (∫ x in Set.Ioi (0 : ℝ), x ^ 4 * Real.exp (-(d * x))) = 24 / d ^ 5 := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (5 : ℝ)) (r := d) (by norm_num) hd
    have hg : Real.Gamma (5 : ℝ) = 24 := by
      norm_num [Real.Gamma_nat_eq_factorial]
    norm_num only at hh
    rw [hg] at hh
    simpa [div_pow, div_eq_mul_inv, mul_comm] using hh
  have hIfull (d : ℝ) (hd : 0 < d) :
      IntegrableOn (fun x : ℝ => x ^ 4 * Real.exp (-(d * x))) (Set.Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hfull d hd]
    positivity
  have hd : 0 < c / 2 := by positivity
  have hI := (hIfull c hc).mono_set (Set.Ioi_subset_Ioi hT)
  have hIhalf := (hIfull (c / 2) hd).mono_set (Set.Ioi_subset_Ioi hT)
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi T) :
      x ^ 4 * Real.exp (-(c * x)) ≤
        Real.exp (-(c / 2 * T)) * (x ^ 4 * Real.exp (-(c / 2 * x))) := by
    have he : Real.exp (-(c / 2 * x)) ≤ Real.exp (-(c / 2 * T)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left (le_of_lt hx) hd.le)
    calc
      _ = (x ^ 4 * Real.exp (-(c / 2 * x))) * Real.exp (-(c / 2 * x)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ (x ^ 4 * Real.exp (-(c / 2 * x))) * Real.exp (-(c / 2 * T)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ x in Set.Ioi T,
        Real.exp (-(c / 2 * T)) * (x ^ 4 * Real.exp (-(c / 2 * x))) :=
      setIntegral_mono_on hI (hIhalf.const_mul _) measurableSet_Ioi hpoint
    _ = Real.exp (-(c / 2 * T)) * ∫ x in Set.Ioi T,
        x ^ 4 * Real.exp (-(c / 2 * x)) := integral_const_mul _ _
    _ ≤ Real.exp (-(c / 2 * T)) * ∫ x in Set.Ioi (0 : ℝ),
        x ^ 4 * Real.exp (-(c / 2 * x)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply setIntegral_mono_set (hIfull (c / 2) hd)
        (ae_of_all _ (fun x => by positivity))
      exact (Set.Ioi_subset_Ioi hT).eventuallySubset
    _ = _ := by rw [hfull (c / 2) hd]; ring

end LeanLab.Linnik1951
