/-
Split of lemma2_outer_square519 of Decomp519a into three leaves.  The signed
outer square estimate of Lemma 2 is cut in two ways.  One leaf carries the
measure theoretic half alone, that the square of the Mellin transform is
integrable on the outer interval; it asks for no constant and no size.  The
other two carry the mass bound itself, one on the range of the inverse radius
below the seventh root of N and one on the range above it.  The assembly at the
end has no sorry, splits on which range the inverse radius lies in and keeps the
larger of the two constants; it does not use the split theorem itself.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp519a

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- The outer margin `arctan (1 / (4 pi N))` is positive for `N ≥ 1`. -/
private lemma delta519_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < Real.arctan (1 / (4 * Real.pi * (N : ℝ))) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact Real.arctan_pos.mpr (by positivity)

private lemma four_piN_pos (N : ℕ) (hN : 1 ≤ N) :
    (0 : ℝ) < 4 * Real.pi * (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have := Real.pi_pos
  positivity

/-- `sin (arctan (1 / (4 pi N))) = 1 / sqrt (1 + (4 pi N) ^ 2)`. -/
private lemma sin_delta519 (N : ℕ) (hN : 1 ≤ N) :
    Real.sin (Real.arctan (1 / (4 * Real.pi * (N : ℝ)))) =
      1 / Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
  have ha : (0 : ℝ) < 4 * Real.pi * (N : ℝ) := four_piN_pos N hN
  rw [Real.sin_arctan]
  have h2 : (1 : ℝ) + (1 / (4 * Real.pi * (N : ℝ))) ^ 2 =
      ((4 * Real.pi * (N : ℝ)) ^ 2 + 1) / (4 * Real.pi * (N : ℝ)) ^ 2 := by
    field_simp
  rw [h2, Real.sqrt_div' _ (by positivity), Real.sqrt_sq ha.le]
  field_simp
  congr 1
  ring

/-- The base `1 / N + 2 pi i alpha` of the outer Mellin power has argument at most
`pi / 2 - arctan (1 / (4 pi N))` when `4 / N ≤ alpha ≤ 2`. -/
private lemma outer_arg519 (N : ℕ) (hN : 2 ≤ N) (α : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) (hα2 : α ≤ 2) :
    |Complex.arg (((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)| ≤
      Real.pi / 2 - Real.arctan (1 / (4 * Real.pi * (N : ℝ))) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hδpos : 0 < δ := delta519_pos N hN1
  have hδlt : δ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzim : z.im = 2 * Real.pi * α := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hzpos : 0 < ‖z‖ := by
    have h2 : 0 < ‖z‖ ^ 2 := by rw [hsq]; positivity
    nlinarith [norm_nonneg z]
  have himlo : 8 * Real.pi / (N : ℝ) ≤ z.im := by
    rw [hzim]
    calc 8 * Real.pi / (N : ℝ) = 2 * Real.pi * (4 / (N : ℝ)) := by field_simp; ring
      _ ≤ 2 * Real.pi * α := by
          apply mul_le_mul_of_nonneg_left hα0 (by positivity)
  have himhi : z.im ≤ 4 * Real.pi := by
    rw [hzim]
    have h := mul_le_mul_of_nonneg_left hα2 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    nlinarith [h]
  -- modulus bound
  have himpos : 0 < z.im := lt_of_lt_of_le (by positivity) himlo
  have h1 : z.im ^ 2 ≤ (4 * Real.pi) ^ 2 := pow_le_pow_left₀ himpos.le himhi 2
  have hsqle : ‖z‖ ^ 2 ≤ (1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2 := by
    rw [hsq, hzre]
    nlinarith [h1]
  have hnorm_le : ‖z‖ ≤ Real.sqrt ((1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2) := by
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsqle
  -- divide
  have hA : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hfac : (1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2 =
      (1 / (N : ℝ)) ^ 2 * (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
    field_simp
  have hsqrt_eq : Real.sqrt ((1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2) =
      (1 / (N : ℝ)) * Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
    rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hdiv : 1 / Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) ≤ z.re / ‖z‖ := by
    rw [hzre]
    have h2 : (1 / (N : ℝ)) / Real.sqrt ((1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2) =
        1 / Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
      rw [hsqrt_eq]
      field_simp
    rw [← h2]
    exact div_le_div_of_nonneg_left hA.le (by positivity) hnorm_le
  have hcos : Real.sin δ ≤ z.re / ‖z‖ := by
    rw [hδdef, sin_delta519 N hN1]
    exact hdiv
  have hθmem : Real.pi / 2 - δ ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hargmem : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hcosarg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  rw [← Real.cos_pi_div_two_sub δ, ← hcosarg] at hcos
  exact (Real.strictAntiOn_cos.le_iff_ge hθmem hargmem).mp hcos

/-- On the outer range the power factor of the Mellin kernel gains the exponential
decay of the normal direction: its modulus is at most `e sqrt N exp (-delta |t|)`. -/
private lemma outer_cpow_bound519 (N : ℕ) (hN : 3 ≤ N) (α t : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) (hα2 : α ≤ 2) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ ≤
      Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - Real.arctan (1 / (4 * Real.pi * (N : ℝ))))) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have harg : |Complex.arg z| ≤ Real.pi / 2 - δ := by
    rw [hδdef, hzdef]
    exact outer_arg519 N hN2 α hα0 hα2
  have hsre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hσ : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hmul : (1 / 2 + 1 / Real.log N) * Real.log N = Real.log N / 2 + 1 := by
    field_simp
  have hlogz : -(1 / 2 + 1 / Real.log N) * Real.log ‖z‖ ≤ Real.log N / 2 + 1 := by
    have h1 : Real.log (1 / (N : ℝ)) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by positivity) hnorm_ge
    have h2 : Real.log (1 / (N : ℝ)) = -Real.log N := by
      rw [Real.log_div one_ne_zero hNr.ne']; simp
    have hσ' : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := hσ
    nlinarith [h1, h2, hmul]
  have hargpos : 0 ≤ Complex.arg z := by
    rw [Complex.arg_nonneg_iff]
    rw [hzdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero]
    have h4 : (0 : ℝ) < 4 / (N : ℝ) := by positivity
    nlinarith [Real.pi_pos, hα0, h4]
  have htarg : t * Complex.arg z ≤ |t| * (Real.pi / 2 - δ) := by
    have hupper : Complex.arg z ≤ Real.pi / 2 - δ := (abs_le.mp harg).2
    rcases lt_or_ge t 0 with ht | ht
    · rw [abs_of_neg ht]
      have h3 : t * Complex.arg z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht.le hargpos
      nlinarith [h3]
    · rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hupper ht
  have hkey : (Complex.log z * (-(mellinLine519 N t))).re ≤
      Real.log N / 2 + 1 + |t| * (Real.pi / 2 - δ) := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im,
      hsre, hsim]
    nlinarith [hlogz, htarg]
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  refine (Real.exp_le_exp.mpr hkey).trans (le_of_eq ?_)
  have hexp_logN : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [← Real.log_sqrt hNr.le, Real.exp_log (Real.sqrt_pos.mpr hNr)]
  rw [Real.exp_add, Real.exp_add, hexp_logN]
  ring

/-- The outer kernel is dominated by the exponential of the normal direction with the
arithmetic weight: `sqrt (2 pi) (3 + |t|) exp (-delta |t|)`. -/
private lemma outer_kernel_bound519 (N : ℕ) (hN : 3 ≤ N) (α t : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) (hα2 : α ≤ 2) :
    ‖mellinKernel519 N α t‖ ≤
      Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
        Real.exp (-(Real.arctan (1 / (4 * Real.pi * (N : ℝ))) * |t|)) := by
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hcp := outer_cpow_bound519 N hN α t hα0 hα2
  have hg := gamma_mellin_line519 N hN t
  have hExp : Real.exp (|t| * (Real.pi / 2 - δ)) * Real.exp (-(Real.pi * |t| / 2)) =
      Real.exp (-(δ * |t|)) := by
    rw [← Real.exp_add, show |t| * (Real.pi / 2 - δ) + -(Real.pi * |t| / 2) = -(δ * |t|) by
      ring]
  unfold mellinKernel519
  rw [norm_mul]
  calc ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ * ‖Complex.Gamma (mellinLine519 N t)‖
      ≤ (Real.exp 1 * Real.sqrt N * Real.exp (|t| * (Real.pi / 2 - δ))) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) := by
        apply mul_le_mul hcp hg (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
          Real.exp (-(δ * |t|)) := by
        rw [← hExp]
        ring

/-- `exp (-b |t|)` is integrable on the line. -/
private lemma exp_neg_abs_integrable519 (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) (0 : ℝ)).congr_fun ?_
      measurableSet_Ioi
    intro t ht
    show Real.exp (-b * t) = Real.exp (-b * |t|)
    rw [abs_of_pos ht]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := b) hb (0 : ℝ)).congr_fun ?_ measurableSet_Iic
    intro t ht
    show Real.exp (b * t) = Real.exp (-b * |t|)
    rw [abs_of_nonpos ht]
    ring_nf
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0 ∪ Set.Iic 0) :=
    integrableOn_union.mpr ⟨h1, h2⟩
  rw [Set.Ioi_union_Iic] at h3
  exact integrableOn_univ.mp h3

/-- A fifth power is dominated by `exp (e |t|)` for every `e > 0`. -/
private lemma pow_five_le_exp519 (e : ℝ) (he : 0 < e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, (|t| + 4) ^ 5 ≤ K * Real.exp (e * |t|) := by
  refine ⟨120 * (1 / e) ^ 5 * Real.exp (4 * e), by positivity, fun t => ?_⟩
  have hv : (0 : ℝ) ≤ e * (|t| + 4) := by positivity
  have h1 : (e * (|t| + 4)) ^ 5 ≤ 120 * Real.exp (e * (|t| + 4)) := by
    have h := Real.pow_div_factorial_le_exp (x := e * (|t| + 4)) hv 5
    norm_num at h
    calc (e * (|t| + 4)) ^ 5 = (e * (|t| + 4)) ^ 5 / 120 * 120 := by ring
      _ ≤ Real.exp (e * (|t| + 4)) * 120 := by
          exact mul_le_mul_of_nonneg_right h (by norm_num)
      _ = 120 * Real.exp (e * (|t| + 4)) := by ring
  have h2 : (|t| + 4) ^ 5 = (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5 := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hExp : Real.exp (e * (|t| + 4)) = Real.exp (4 * e) * Real.exp (e * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2]
  calc (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5
      ≤ (1 / e) ^ 5 * (120 * Real.exp (e * (|t| + 4))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 120 * (1 / e) ^ 5 * Real.exp (4 * e) * Real.exp (e * |t|) := by
        rw [hExp]; ring

/-- The arithmetic weight of the outer kernel is integrable on the line. -/
private lemma outer_weight_integrable519 (N : ℕ) (hN : 2 ≤ N) :
    Integrable (fun t : ℝ => (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
      Real.exp (-(Real.arctan (1 / (4 * Real.pi * (N : ℝ))) * |t|))) := by
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hδpos : 0 < δ := delta519_pos N (by omega)
  obtain ⟨K, hK0, hK⟩ := pow_five_le_exp519 (δ / 2) (by linarith)
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNr
  have hbase : Integrable (fun t : ℝ => Real.exp (-(δ / 2) * |t|)) :=
    exp_neg_abs_integrable519 _ (by linarith)
  refine Integrable.mono' (hbase.const_mul (16 * (Real.log N ^ 3 + 1) * K)) ?_ ?_
  · have hcont : Continuous fun t : ℝ => (3 + |t|) *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ * |t|)) := by
      have harg : Continuous fun t : ℝ => (N : ℝ) * (|t| + 2) :=
        continuous_const.mul (continuous_abs.add continuous_const)
      have hlog : Continuous fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) :=
        harg.log (fun t => ne_of_gt (by positivity))
      have hexp : Continuous fun t : ℝ => Real.exp (-(δ * |t|)) :=
        Real.continuous_exp.comp (by fun_prop)
      exact ((continuous_const.add continuous_abs).mul (hlog.pow 3)).mul hexp
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    have hlogpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
        have h2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
        nlinarith [hNr, abs_nonneg t]
      have h3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
        Real.log_nonneg h1
      positivity
    have hsplit := log_cube_split519 N t hN
    have ht4 : (0 : ℝ) < |t| + 4 := by linarith [abs_nonneg t]
    have hlog2 : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := by
      have h1 : Real.log (|t| + 2) ≤ |t| + 4 :=
        (Real.log_le_self (by linarith [abs_nonneg t])).trans (by linarith)
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      exact pow_le_pow_left₀ h2 h1 3
    have h17 : (1 : ℝ) ≤ |t| + 4 := by linarith [abs_nonneg t]
    have hcube : (1 : ℝ) ≤ (|t| + 4) ^ 3 := by
      calc (1 : ℝ) = 1 ^ 3 := by ring
        _ ≤ (|t| + 4) ^ 3 := pow_le_pow_left₀ (by norm_num) h17 3
    have hkey : (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
        16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 := by
      have h3 : (0 : ℝ) ≤ 3 + |t| := by linarith [abs_nonneg t]
      have h4 : Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
          8 * (Real.log N ^ 3 + 1) * (1 + Real.log (|t| + 2) ^ 3) := by
        have h5 : 8 * Real.log N ^ 3 ≤ 8 * (Real.log N ^ 3 + 1) := by linarith
        have h6 : 8 * Real.log (|t| + 2) ^ 3 ≤
            8 * (Real.log N ^ 3 + 1) * Real.log (|t| + 2) ^ 3 := by
          have h7 : (1 : ℝ) ≤ Real.log N ^ 3 + 1 := by linarith [pow_nonneg hlogN 3]
          have h8 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
            have h9 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
            exact pow_nonneg (Real.log_nonneg h9) 3
          nlinarith [h7, h8]
        linarith [hsplit, h5, h6]
      have h11 : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := hlog2
      have h12 : (1 : ℝ) + Real.log (|t| + 2) ^ 3 ≤ 2 * (|t| + 4) ^ 3 := by linarith
      have hlog3nn : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
        have h9 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
        exact pow_nonneg (Real.log_nonneg h9) 3
      have h13 : (3 + |t|) * (1 + Real.log (|t| + 2) ^ 3) ≤
          2 * (|t| + 4) * (|t| + 4) ^ 3 := by
        have h14 : (3 + |t|) ≤ (|t| + 4) := by linarith [abs_nonneg t]
        calc (3 + |t|) * (1 + Real.log (|t| + 2) ^ 3)
            ≤ (|t| + 4) * (2 * (|t| + 4) ^ 3) :=
              mul_le_mul h14 h12
                (by linarith : (0 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3)
                (by linarith [abs_nonneg t] : (0 : ℝ) ≤ |t| + 4)
          _ = 2 * (|t| + 4) * (|t| + 4) ^ 3 := by ring
      have h15 : (0 : ℝ) ≤ 8 * (Real.log N ^ 3 + 1) := by positivity
      calc (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3
          ≤ (3 + |t|) * (8 * (Real.log N ^ 3 + 1) * (1 + Real.log (|t| + 2) ^ 3)) := by
            exact mul_le_mul_of_nonneg_left h4 h3
        _ = 8 * (Real.log N ^ 3 + 1) * ((3 + |t|) * (1 + Real.log (|t| + 2) ^ 3)) := by
            ring
        _ ≤ 8 * (Real.log N ^ 3 + 1) * (2 * (|t| + 4) * (|t| + 4) ^ 3) := by
            exact mul_le_mul_of_nonneg_left h13 h15
        _ = 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 := by ring
    have h16 : (|t| + 4) ^ 4 ≤ (|t| + 4) ^ 5 := by
      have h18 : (|t| + 4) ^ 4 * 1 ≤ (|t| + 4) ^ 4 * (|t| + 4) :=
        mul_le_mul_of_nonneg_left h17 (by positivity)
      calc (|t| + 4) ^ 4 = (|t| + 4) ^ 4 * 1 := by ring
        _ ≤ (|t| + 4) ^ 4 * (|t| + 4) := h18
        _ = (|t| + 4) ^ 5 := by ring
    have hexp1 : Real.exp (-(δ * |t|)) = Real.exp (-(δ / 2) * |t|) * Real.exp (-(δ / 2) * |t|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hC2 : (0 : ℝ) ≤ 16 * (Real.log N ^ 3 + 1) * K := by positivity
    have hexpbound : Real.exp (-(δ * |t|)) ≤ Real.exp (-(δ / 2) * |t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg t, hδpos]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith [abs_nonneg t]) hlogpos)
        (Real.exp_pos _).le)]
    calc (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ * |t|))
        ≤ 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 * Real.exp (-(δ * |t|)) := by
          apply mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ ≤ (16 * (Real.log N ^ 3 + 1) * K * Real.exp (δ / 2 * |t|)) * Real.exp (-(δ * |t|)) := by
          have hp : (0 : ℝ) ≤ Real.exp (-(δ * |t|)) := (Real.exp_pos _).le
          have hq : (|t| + 4) ^ 4 ≤ (|t| + 4) ^ 5 := h16
          have hr : (|t| + 4) ^ 5 ≤ K * Real.exp (δ / 2 * |t|) := hK t
          have hs : 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 ≤
              16 * (Real.log N ^ 3 + 1) * (K * Real.exp (δ / 2 * |t|)) := by
            have h0 : (0 : ℝ) ≤ 16 * (Real.log N ^ 3 + 1) := by positivity
            calc 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4
                ≤ 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 5 := by
                  exact mul_le_mul_of_nonneg_left hq h0
              _ ≤ 16 * (Real.log N ^ 3 + 1) * (K * Real.exp (δ / 2 * |t|)) := by
                  exact mul_le_mul_of_nonneg_left hr h0
          calc 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 * Real.exp (-(δ * |t|))
              ≤ 16 * (Real.log N ^ 3 + 1) * (K * Real.exp (δ / 2 * |t|)) *
                  Real.exp (-(δ * |t|)) := by
                exact mul_le_mul_of_nonneg_right hs hp
            _ = (16 * (Real.log N ^ 3 + 1) * K * Real.exp (δ / 2 * |t|)) *
                  Real.exp (-(δ * |t|)) := by ring
      _ = 16 * (Real.log N ^ 3 + 1) * K * Real.exp (-(δ / 2) * |t|) := by
          rw [mul_assoc (16 * (Real.log N ^ 3 + 1) * K), ← Real.exp_add]
          congr 1
          ring

/-- On the outer range up to two the Mellin transform is continuous in the outer
variable, by dominated convergence against the outer kernel majorant. -/
private lemma outer_continuousOn519 (N : ℕ) (hN : 3 ≤ N) (M : ℝ → ℂ) (hM : Continuous M)
    (B0 : ℝ) (hB0 : 0 ≤ B0)
    (hbound : ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :
    ContinuousOn (fun α => mellinU519 N M α) (Set.Icc (4 / (N : ℝ)) 2) := by
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hW := outer_weight_integrable519 N hN2
  simp only [← hδdef] at hW
  have hBint : Integrable (fun t : ℝ => B0 * (Real.exp 1 * Real.sqrt N *
      Real.sqrt (2 * Real.pi)) * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(δ * |t|)))) := by
    have := hW.const_mul (B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this
  have hmain : ContinuousOn (fun α => ∫ t : ℝ, mellinKernel519 N α t * M t)
      (Set.Icc (4 / (N : ℝ)) 2) := by
    refine MeasureTheory.continuousOn_of_dominated (μ := volume) ?_ ?_ hBint ?_
    · intro α _
      exact ((continuous_mellin_integrand519 N hN M hM).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro α hα
      filter_upwards with t
      have hk := outer_kernel_bound519 N hN α t hα.1 hα.2
      rw [norm_mul]
      have hlog3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
        have h5 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
          have h6 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
          have h7 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
          nlinarith [h6, h7, abs_nonneg t]
        exact pow_nonneg (Real.log_nonneg h5) 3
      have hstep := mul_le_mul hk (hbound t) (norm_nonneg (M t)) (by positivity)
      calc ‖mellinKernel519 N α t‖ * ‖M t‖
          ≤ (Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
              Real.exp (-(δ * |t|))) *
            (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := hstep
        _ = B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) *
              ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
                Real.exp (-(δ * |t|))) := by
            rw [hδdef]; ring
    · filter_upwards with t
      exact ((continuous_mellin_integrand519 N hN M hM).comp
        (continuous_id.prodMk continuous_const)).continuousOn
  have heq : (fun α => mellinU519 N M α) = fun α =>
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, mellinKernel519 N α t * M t := by
    funext α
    simp only [mellinU519, mellinKernel519]
  rw [heq]
  exact hmain.const_mul _

/-- LEAF. Integrability half of the outer interval.  For a positive line constant
B0, once N is large enough, and for every inverse radius R between one and the
two sevenths power of N, every continuous coefficient obeying the cubic
logarithmic line bound has square norm integrable over the outer interval from
four over N to one over R.  This is the first conjunct alone: it carries no
constant, no factor of N over R and no power of the logarithm, so it is strictly
weaker than the sealed estimate. -/
theorem outer_square_integrable519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
            (Set.Icc (4 / (N : ℝ)) (1 / R)) := by
  refine ⟨127, ?_⟩
  intro N hN R hR _ M hM
  have hN3 : 3 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hcont := outer_continuousOn519 N hN3 M hM.1 B0 hB0.le hM.2
  have hcont2 : ContinuousOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc (4 / (N : ℝ)) 2) := hcont.norm.pow 2
  have hint : IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc (4 / (N : ℝ)) 2) := hcont2.integrableOn_compact isCompact_Icc
  refine hint.mono_set ?_
  apply Set.Icc_subset_Icc le_rfl
  have hR1 : 1 / R ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < R)]
    exact hR
  linarith


/-- LEAF. Mass bound on the small inverse radius range, from one up to the seventh
root of N.  Here the outer interval is at least as long as the central one, so
this is the case of the estimate in which the inverse radius is short and the
interval reaches back to the central scale four over N.  It is one case of the
sealed mass bound, with the same conclusion and a restricted range of R, and it
says nothing about the complementary range nor about integrability. -/
theorem outer_square_small_R519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- LEAF. Mass bound on the large inverse radius range, from the seventh root of N
up to the two sevenths power of N.  Here the outer interval lies far from the
central scale, which is the case in which the double frequency calculation is
cut off only by the two sevenths power of N in the statement of Lemma 2.  It is
the complementary case of the sealed mass bound, again with the same conclusion
and a restricted range of R, and it carries no integrability claim. -/
theorem outer_square_large_R519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (1 / 7 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- The three leaves together give the outer square estimate: the square of the
Mellin transform is integrable on the outer interval, and its mass there is at
most the larger of the two range constants times N over R times the tenth power
of the logarithm of N. -/
theorem lemma2_outer_square519_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
            (Set.Icc (4 / (N : ℝ)) (1 / R)) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨Ni, hi⟩ := outer_square_integrable519 B0 hB0
  obtain ⟨C1, hC1, N1, h1⟩ := outer_square_small_R519 B0 hB0
  obtain ⟨C2, hC2, N2, h2⟩ := outer_square_large_R519 B0 hB0
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left C1 C2),
    max Ni (max N1 N2), ?_⟩
  intro N hN R hR hRN M hM
  have hNi : Ni < N := lt_of_le_of_lt (le_max_left Ni (max N1 N2)) hN
  have hN1 : N1 < N :=
    lt_of_le_of_lt ((le_max_left N1 N2).trans (le_max_right Ni (max N1 N2))) hN
  have hN2 : N2 < N :=
    lt_of_le_of_lt ((le_max_right N1 N2).trans (le_max_right Ni (max N1 N2))) hN
  refine ⟨hi N hNi R hR hRN M hM, ?_⟩
  have hRp : (0 : ℝ) < R := by linarith
  have hX : 0 ≤ (N : ℝ) / R * Real.log N ^ 10 := by
    have hNR : (0 : ℝ) ≤ (N : ℝ) / R := div_nonneg (Nat.cast_nonneg N) hRp.le
    have hlog : (0 : ℝ) ≤ Real.log N ^ 10 := by
      have he : Real.log N ^ 10 = (Real.log N ^ 5) ^ 2 := by ring
      rw [he]
      exact sq_nonneg _
    exact mul_nonneg hNR hlog
  rcases le_or_gt R ((N : ℝ) ^ (1 / 7 : ℝ)) with hs | hl
  · exact (h1 N hN1 R hR hs M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hX)
  · exact (h2 N hN2 R hR hl.le hRN M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hX)

end LeanLab.Linnik1951.Task519
