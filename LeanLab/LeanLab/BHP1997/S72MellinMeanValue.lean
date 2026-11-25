/-
P0069 Baker Harman Pintz 1997, proof of Lemma 29, page 44, the step "By a variant of [8],
Lemma 2", the mean value of a Mellin type integral over `y` in `[Y/2, 3Y]`.

This file proves the lab statement `S64LowExcCharNP.leaf_mellin_mean_value` as
`mellin_mean_value_of_leaves`, by the standard proof of Gallagher [8] Lemma 2 type bounds,
from steps that are now all PROVED:
* `leaf_mellin_exp_substitution`, PROVED: the substitution `y = e^u`, under which
  `y^(1/2+it) = e^(u/2) e^(iut)` and `dy = e^u du`, so the integrand becomes
  `e^(2u) |F(u)|^2 ≤ (3Y)^2 |F(u)|^2` with `F(u) = ∫_{-T}^{T} g(t) e^(iut) dt`, over an
  interval of length `log 6`;
* `gaussian_domination`, PROVED: the indicator of that interval is at most
  `e^((log 6 / 2)^2) e^(-(u-m)^2)`;
* `leaf_gaussian_fubini_identity`, PROVED by S130: Fubini and the Gaussian Fourier transform;
* `leaf_schur_gaussian`, PROVED: the Schur bound with `∫ e^(-v^2/4) = 2 sqrt π`;
* `leaf_local_fourier_l2` and `mellin_mean_value_of_leaves`, PROVED assemblies.
No Plancherel and no log factor are used.

The file imports only Mathlib so that the S64 file can import it without a cycle.
AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import Mathlib

namespace LeanLab.BHP1997.S72MellinMV
open Complex MeasureTheory

/-- Page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant, the substitution step,
PROVED. With `y = e^u`, `u` running over `[log (Y/2), log (Y/2) + log 6]`,
`y^(1/2+it) = e^(u/2) e^(iut)` and `dy = e^u du`; the integrand is
`e^(2u) |∫ g(t) e^(iut) dt|^2` and `e^(2u) ≤ (3Y)^2` on that range. -/
theorem leaf_mellin_exp_substitution :
    ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y),
          ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        (3 * Y) ^ 2 * ∫ u in (Real.log (Y / 2))..(Real.log (Y / 2) + Real.log 6),
          ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I)‖ ^ 2 := by
  intro Y hY T hT g hg
  set a := Real.log (Y / 2) with ha_def
  set F : ℝ → ℂ := fun u => ∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I) with hF
  have hFc : Continuous F := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have ha : Real.exp a = Y / 2 := Real.exp_log (by positivity)
  have hb : Real.exp (a + Real.log 6) = 3 * Y := by
    rw [Real.exp_add, ha, Real.exp_log (by norm_num)]; ring
  have hab : a ≤ a + Real.log 6 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6); linarith
  have key : ∀ u : ℝ,
      ‖∫ t in (-T)..T, g t * ((Real.exp u : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
        Real.exp u * ‖F u‖ ^ 2 := by
    intro u
    have hpt : ∀ t : ℝ, g t * ((Real.exp u : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
        cexp ((u : ℂ) / 2) * (g t * cexp ((u : ℂ) * (t : ℂ) * I)) := by
      intro t
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp,
        mul_left_comm, ← Complex.exp_add]
      congr 2; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, norm_mul, mul_pow, Complex.norm_exp]
    have : (((u : ℂ) / 2).re) = u / 2 := by simp
    rw [this, sq (Real.exp (u / 2)), ← Real.exp_add]
    ring_nf
    rfl
  set H : ℝ → ℝ := fun y =>
    ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 with hH
  have hcov : ∫ y in (Y / 2)..(3 * Y), H y =
      ∫ u in a..(a + Real.log 6), Real.exp u * (Real.exp u * ‖F u‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le hab,
      ← ha, ← hb, ← Real.image_exp_Ioc,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    simp only [smul_eq_mul, abs_of_pos (Real.exp_pos u), hH]
    rw [key u]
  show ∫ y in (Y / 2)..(3 * Y), H y ≤ _
  rw [hcov, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab
  · exact (by fun_prop : Continuous fun u => Real.exp u * (Real.exp u * ‖F u‖ ^ 2)
      ).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun u => (3 * Y) ^ 2 * ‖F u‖ ^ 2).intervalIntegrable _ _
  · intro u hu
    have h1 : Real.exp u ≤ 3 * Y := by rw [← hb]; exact Real.exp_le_exp.mpr hu.2
    have h0 := (Real.exp_pos u).le
    have : Real.exp u * Real.exp u ≤ (3 * Y) ^ 2 := by nlinarith
    have hF0 : 0 ≤ ‖F u‖ ^ 2 := by positivity
    calc Real.exp u * (Real.exp u * ‖F u‖ ^ 2) = (Real.exp u * Real.exp u) * ‖F u‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hF0

/-- Page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant: the Fourier integral
`F(u) = ∫_{-T}^{T} g(t) e^(iut) dt` is bounded by `∫_{-T}^{T} |g|`. PROVED. -/
theorem fourier_norm_le (T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ) (u : ℝ) :
    ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I)‖ ≤ ∫ t in (-T)..T, ‖g t‖ := by
  have hle : -T ≤ T := by linarith
  refine (intervalIntegral.norm_integral_le_integral_norm hle).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [norm_mul, show (u : ℂ) * (t : ℂ) * I = ((u * t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant, the Gaussian domination step:
on `[c, c + log 6]` with midpoint `m`, `(u-m)^2 ≤ (log 6 / 2)^2`, so the indicator is at most
`e^((log 6 / 2)^2) e^(-(u-m)^2)`. PROVED. -/
theorem gaussian_domination (c T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ) (hg : Continuous g) :
    ∫ u in c..(c + Real.log 6), ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I)‖ ^ 2 ≤
      Real.exp ((Real.log 6 / 2) ^ 2) *
        ∫ u, Real.exp (-(u - (c + Real.log 6 / 2)) ^ 2) *
          ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I)‖ ^ 2 := by
  set F : ℝ → ℂ := fun u => ∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I) with hF
  set m := c + Real.log 6 / 2
  set M := ∫ t in (-T)..T, ‖g t‖
  have hFc : Continuous F := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have hL : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hc : c ≤ c + Real.log 6 := by linarith
  have hG : Integrable (fun u => Real.exp (-(u - m) ^ 2) * ‖F u‖ ^ 2) := by
    have hgauss : Integrable (fun u => Real.exp (-1 * (u - m) ^ 2)) :=
      (integrable_exp_neg_mul_sq (b := 1) one_pos).comp_sub_right m
    refine (hgauss.mul_const (M ^ 2)).mono'
      (by fun_prop : Continuous fun u => Real.exp (-(u - m) ^ 2) * ‖F u‖ ^ 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 : ‖F u‖ ≤ M := fourier_norm_le T hT g u
    have h2 : ‖F u‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_one_mul]
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  rw [intervalIntegral.integral_of_le hc, ← integral_const_mul]
  calc ∫ u in Set.Ioc c (c + Real.log 6), ‖F u‖ ^ 2
      ≤ ∫ u in Set.Ioc c (c + Real.log 6),
          Real.exp ((Real.log 6 / 2) ^ 2) * (Real.exp (-(u - m) ^ 2) * ‖F u‖ ^ 2) := by
        refine setIntegral_mono_on ?_ ((hG.const_mul _).integrableOn) measurableSet_Ioc
          (fun u hu => ?_)
        · exact ((by fun_prop : Continuous fun u => ‖F u‖ ^ 2).integrableOn_Icc).mono_set
            Set.Ioc_subset_Icc_self
        · have hd : (u - m) ^ 2 ≤ (Real.log 6 / 2) ^ 2 := by
            have hm : m = c + Real.log 6 / 2 := rfl
            have := hu.1; have := hu.2
            exact sq_le_sq' (by linarith) (by linarith)
          have he : 1 ≤ Real.exp ((Real.log 6 / 2) ^ 2) * Real.exp (-(u - m) ^ 2) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
          have hF0 : 0 ≤ ‖F u‖ ^ 2 := by positivity
          calc ‖F u‖ ^ 2 = 1 * ‖F u‖ ^ 2 := by ring
            _ ≤ (Real.exp ((Real.log 6 / 2) ^ 2) * Real.exp (-(u - m) ^ 2)) * ‖F u‖ ^ 2 :=
              mul_le_mul_of_nonneg_right he hF0
            _ = _ := by ring
    _ ≤ ∫ u, Real.exp ((Real.log 6 / 2) ^ 2) * (Real.exp (-(u - m) ^ 2) * ‖F u‖ ^ 2) :=
        setIntegral_le_integral (hG.const_mul _)
          (Filter.Eventually.of_forall fun u => by positivity)

/-- Page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant, the Gaussian Fourier transform
used in the Fubini step, PROVED: `∫_ℝ e^(-(u-m)^2) e^(iuv) du = sqrt π e^(imv) e^(-v^2/4)`, from
Mathlib `integral_cexp_quadratic` with `b = -1`, `c = 2m + iv`, `d = -m^2`. -/
theorem gaussian_fourier_shift (m v : ℝ) :
    ∫ u : ℝ, ((Real.exp (-(u - m) ^ 2) : ℝ) : ℂ) * cexp ((u : ℂ) * (v : ℂ) * I) =
      ((Real.sqrt Real.pi : ℝ) : ℂ) * cexp ((m : ℂ) * (v : ℂ) * I) *
        ((Real.exp (-v ^ 2 / 4) : ℝ) : ℂ) := by
  have h : ∀ u : ℝ, ((Real.exp (-(u - m) ^ 2) : ℝ) : ℂ) * cexp ((u : ℂ) * (v : ℂ) * I) =
      cexp ((-1 : ℂ) * (u : ℂ) ^ 2 + (2 * (m : ℂ) + (v : ℂ) * I) * (u : ℂ) + (-(m : ℂ) ^ 2)) := by
    intro u
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [h]
  rw [integral_cexp_quadratic (by simp) _ _]
  have hpi : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [neg_neg, div_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast; ring_nf
  rw [hpi, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- LEAF: page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant, the Fubini expansion with
Gaussian kernel, class HARD. Writing `|F(u)|^2 = ∫∫ g(t) conj g(s) e^(iu(t-s)) dt ds`, Fubini,
and the Gaussian Fourier transform
`∫_ℝ e^(-(u-m)^2) e^(iuv) du = sqrt π e^(imv) e^(-v^2/4)`, available in Mathlib as
`integral_cexp_quadratic` or `fourierIntegral_gaussian`, give
`∫_ℝ e^(-(u-m)^2) |F(u)|^2 du = Re ∫∫ g(t) conj g(s) sqrt π e^(im(t-s)) e^(-(t-s)^2/4) dt ds`.
PROVED by CLOUD S130, burst-20261122: pointwise `|F(u)|^2 = F(u) conj F(u)` as a double
integral, two Fubini swaps by `intervalIntegral_integral_swap` with the integrable majorant
`|g(t)| |g(s)| e^(-(u-m)^2)`, then `gaussian_fourier_shift`. -/
theorem leaf_gaussian_fubini_identity (m T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ)
    (hg : Continuous g) :
    ∫ u, Real.exp (-(u - m) ^ 2) *
        ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I)‖ ^ 2 =
      (∫ t in (-T)..T, ∫ s in (-T)..T, g t * (starRingEnd ℂ) (g s) *
          (((Real.sqrt Real.pi : ℝ) : ℂ) * cexp ((m : ℂ) * ((t : ℂ) - (s : ℂ)) * I) *
            ((Real.exp (-(t - s) ^ 2 / 4) : ℝ) : ℂ))).re := by
  have hle : -T ≤ T := by linarith
  set w : ℝ → ℝ := fun u => Real.exp (-(u - m) ^ 2) with hw
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hwi : Integrable w := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).comp_sub_right m
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hw, neg_one_mul]
  set F : ℝ → ℂ := fun u => ∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I) with hF
  set E : ℝ → ℝ → ℝ → ℂ := fun u t s =>
    g t * (starRingEnd ℂ) (g s) * cexp ((u : ℂ) * ((t : ℂ) - (s : ℂ)) * I) with hE
  -- pointwise expansion of |F u|^2
  have hpt : ∀ u, ((w u * ‖F u‖ ^ 2 : ℝ) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T, (w u : ℂ) * E u t s := by
    intro u
    have hc : ∀ x : ℝ, (starRingEnd ℂ) (cexp ((u : ℂ) * (x : ℂ) * I)) =
        cexp ((u : ℂ) * (x : ℂ) * (-I)) := by
      intro x; rw [← Complex.exp_conj]; congr 1; simp [map_mul, Complex.conj_ofReal]
    have hconj : (starRingEnd ℂ) (F u) =
        ∫ s in (-T)..T, (starRingEnd ℂ) (g s) * cexp ((u : ℂ) * (s : ℂ) * (-I)) := by
      simp only [hF, intervalIntegral.integral_of_le hle]
      rw [← integral_conj]
      congr 1; ext s; rw [map_mul, hc]
    have hsq : ((‖F u‖ ^ 2 : ℝ) : ℂ) = F u * (starRingEnd ℂ) (F u) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.ofReal_mul, hsq, hconj]
    set C := ∫ s in (-T)..T, (starRingEnd ℂ) (g s) * cexp ((u : ℂ) * (s : ℂ) * (-I))
    have h1 : F u * C = ∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I) * C := by
      simp only [hF]; rw [intervalIntegral.integral_mul_const]
    rw [h1, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [C]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hE]
    rw [show (u : ℂ) * ((t : ℂ) - (s : ℂ)) * I = (u : ℂ) * (t : ℂ) * I + (u : ℂ) * (s : ℂ) * (-I)
      by ring, Complex.exp_add]
    ring
  have hgc : Continuous fun t => ‖g t‖ := hg.norm
  have hIoc : ∀ f : ℝ → ℝ, Continuous f → Integrable f (volume.restrict (Set.uIoc (-T) T)) := by
    intro f hf
    rw [Set.uIoc_of_le hle]
    exact (hf.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  set Cg := ∫ s in (-T)..T, ‖g s‖ with hCg
  have hEn : ∀ u t s, ‖(w u : ℂ) * E u t s‖ = ‖g t‖ * ‖g s‖ * w u := by
    intro u t s
    have e : (u : ℂ) * ((t : ℂ) - (s : ℂ)) * I = ((u * (t - s) : ℝ) : ℂ) * I := by
      push_cast; ring
    simp only [hE, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, e,
      Complex.norm_exp_ofReal_mul_I, hw, abs_of_pos (Real.exp_pos _)]
    ring
  -- first swap, u against t
  set Φ : ℝ → ℝ → ℂ := fun t u => ∫ s in (-T)..T, (w u : ℂ) * E u t s with hΦ
  have hΦc : Continuous (Function.uncurry Φ) := by
    show Continuous fun p : ℝ × ℝ => ∫ s in (-T)..T, (w p.2 : ℂ) * E p.2 p.1 s
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    simp only [hE, hw]; fun_prop
  have hΦb : ∀ t u, ‖Φ t u‖ ≤ (‖g t‖ * Cg) * w u := by
    intro t u
    refine (intervalIntegral.norm_integral_le_integral_norm hle).trans (le_of_eq ?_)
    simp_rw [hEn]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  have hΦi : Integrable (Function.uncurry Φ)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
    refine ((hIoc (fun t => ‖g t‖ * Cg) (hgc.mul continuous_const)).mul_prod hwi).mono'
      hΦc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    exact hΦb p.1 p.2
  -- second swap, u against s, for fixed t
  have hΨi : ∀ t, Integrable (Function.uncurry fun s u => (w u : ℂ) * E u t s)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
    intro t
    refine ((hIoc (fun s => ‖g t‖ * ‖g s‖) (continuous_const.mul hgc)).mul_prod hwi).mono'
      ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (by simp only [hE, hw]; fun_prop :
        Continuous fun p : ℝ × ℝ => (w p.2 : ℂ) * E p.2 t p.1).aestronglyMeasurable
    · exact le_of_eq (hEn p.2 t p.1)
  -- the Gaussian Fourier transform
  have hinner : ∀ t s, ∫ u, (w u : ℂ) * E u t s = g t * (starRingEnd ℂ) (g s) *
      (((Real.sqrt Real.pi : ℝ) : ℂ) * cexp ((m : ℂ) * ((t : ℂ) - (s : ℂ)) * I) *
        ((Real.exp (-(t - s) ^ 2 / 4) : ℝ) : ℂ)) := by
    intro t s
    calc ∫ u, (w u : ℂ) * E u t s = g t * (starRingEnd ℂ) (g s) *
          ∫ u : ℝ, ((Real.exp (-(u - m) ^ 2) : ℝ) : ℂ) * cexp ((u : ℂ) * ((t - s : ℝ) : ℂ) * I) := by
          rw [← integral_const_mul]; congr 1; ext u; simp only [hE, hw]; push_cast; ring
      _ = _ := by rw [gaussian_fourier_shift]; push_cast; ring
  have hmain : ((∫ u, w u * ‖F u‖ ^ 2 : ℝ) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T, g t * (starRingEnd ℂ) (g s) *
        (((Real.sqrt Real.pi : ℝ) : ℂ) * cexp ((m : ℂ) * ((t : ℂ) - (s : ℂ)) * I) *
          ((Real.exp (-(t - s) ^ 2 / 4) : ℝ) : ℂ)) := by
    have hcast : ∫ u, ((w u * ‖F u‖ ^ 2 : ℝ) : ℂ) = ((∫ u, w u * ‖F u‖ ^ 2 : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [← hcast]
    simp_rw [hpt]
    rw [← intervalIntegral_integral_swap hΦi]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hΦ]
    rw [← intervalIntegral_integral_swap (hΨi t)]
    exact intervalIntegral.integral_congr fun s _ => hinner t s
  have := congrArg Complex.re hmain
  rw [Complex.ofReal_re] at this
  exact this

/-- Page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant, the Schur bound for the
Gaussian kernel, PROVED. With `|g(t)| |g(s)| ≤ (|g(t)|^2 + |g(s)|^2)/2`, symmetry in
`t, s`, and `∫_ℝ e^(-v^2/4) dv = 2 sqrt π`, the double integral is at most
`sqrt π 2 sqrt π ∫ |g|^2 = 2π ∫_{-T}^{T} |g(t)|^2 dt`. -/
theorem leaf_schur_gaussian (m T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ) (hg : Continuous g) :
    ‖∫ t in (-T)..T, ∫ s in (-T)..T, g t * (starRingEnd ℂ) (g s) *
          (((Real.sqrt Real.pi : ℝ) : ℂ) * cexp ((m : ℂ) * ((t : ℂ) - (s : ℂ)) * I) *
            ((Real.exp (-(t - s) ^ 2 / 4) : ℝ) : ℂ))‖ ≤
      2 * Real.pi * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  have hle : -T ≤ T := by linarith
  set ps := Real.sqrt Real.pi with hps
  have hps0 : 0 ≤ ps := Real.sqrt_nonneg _
  set k : ℝ → ℝ → ℝ := fun t s => Real.exp (-(t - s) ^ 2 / 4) with hk
  have hkc : Continuous (Function.uncurry k) := by simp only [hk]; fun_prop
  have hgauss : ∫ x : ℝ, Real.exp (-(1 / 4) * x ^ 2) = 2 * ps := by
    rw [integral_gaussian, hps, show Real.pi / (1 / 4) = 2 ^ 2 * Real.pi by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hk_int : ∀ t, ∫ s in (-T)..T, k t s ≤ 2 * ps := by
    intro t
    have hint0 : Integrable (fun x : ℝ => Real.exp (-(1 / 4) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num)
    have hint : Integrable (fun s => k t s) := by
      refine (hint0.comp_sub_left t).congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [hk]; ring_nf
    rw [intervalIntegral.integral_of_le hle]
    calc _ ≤ ∫ s, k t s := setIntegral_le_integral hint
            (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le)
      _ = ∫ x : ℝ, Real.exp (-(1 / 4) * x ^ 2) := by
          rw [← integral_sub_left_eq_self (fun x : ℝ => Real.exp (-(1 / 4) * x ^ 2)) volume t]
          congr 1; ext s; simp only [hk]; ring_nf
      _ = 2 * ps := hgauss
  have hksymm : ∀ t s, k t s = k s t := by intro t s; simp only [hk]; ring_nf
  set a : ℝ → ℝ := fun t => ‖g t‖ with ha
  have hac : Continuous a := by simp only [ha]; fun_prop
  set K : ℝ → ℝ → ℂ := fun t s => g t * (starRingEnd ℂ) (g s) *
    (((ps : ℝ) : ℂ) * cexp ((m : ℂ) * ((t : ℂ) - (s : ℂ)) * I) * ((k t s : ℝ) : ℂ)) with hK
  show ‖∫ t in (-T)..T, ∫ s in (-T)..T, K t s‖ ≤ 2 * Real.pi * ∫ t in (-T)..T, a t ^ 2
  have hKc : Continuous (Function.uncurry K) := by
    simp only [hK, hk]; fun_prop
  have hnorm : ∀ t s, ‖K t s‖ = ps * (a t * a s * k t s) := by
    intro t s
    have e : (m : ℂ) * ((t : ℂ) - (s : ℂ)) * I = ((m * (t - s) : ℝ) : ℂ) * I := by
      push_cast; ring
    simp only [hK, ha, hk, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hps0, abs_of_pos (Real.exp_pos _), e, Complex.norm_exp_ofReal_mul_I]
    ring
  set A : ℝ → ℝ → ℝ := fun t s => ps / 2 * a t ^ 2 * k t s with hA
  set B : ℝ → ℝ → ℝ := fun t s => ps / 2 * a s ^ 2 * k t s with hB
  have hAc : Continuous (Function.uncurry A) := by simp only [hA, hk]; fun_prop
  have hBc : Continuous (Function.uncurry B) := by simp only [hB, hk]; fun_prop
  have hpt : ∀ t s, ‖K t s‖ ≤ A t s + B t s := by
    intro t s
    rw [hnorm]
    have hk0 : 0 ≤ k t s := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a t) (a s)) (mul_nonneg hps0 hk0)
    simp only [hA, hB]; nlinarith
  have cpar : ∀ F : ℝ → ℝ → ℝ, Continuous (Function.uncurry F) →
      Continuous fun t => ∫ s in (-T)..T, F t s := fun F hF =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _
  have hcont_row : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ t,
      Continuous fun s => F t s := fun F hF t => hF.comp (Continuous.prodMk_right t)
  -- first term
  have hAint : ∀ t, ∫ s in (-T)..T, A t s = ps / 2 * a t ^ 2 * ∫ s in (-T)..T, k t s := by
    intro t; simp only [hA]; rw [intervalIntegral.integral_const_mul]
  have hBint : ∀ s, ∫ t in (-T)..T, B t s = ps / 2 * a s ^ 2 * ∫ t in (-T)..T, k s t := by
    intro s; simp only [hB]; rw [intervalIntegral.integral_const_mul]
    congr 1; exact intervalIntegral.integral_congr fun t _ => hksymm t s
  have hpp : ps * ps = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hA_le : ∫ t in (-T)..T, ∫ s in (-T)..T, A t s ≤ Real.pi * ∫ t in (-T)..T, a t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hle ((cpar A hAc).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => Real.pi * a t ^ 2).intervalIntegrable _ _)
      (fun t _ => ?_)
    rw [hAint]
    have h0 : 0 ≤ ps / 2 * a t ^ 2 := by positivity
    calc ps / 2 * a t ^ 2 * ∫ s in (-T)..T, k t s ≤ ps / 2 * a t ^ 2 * (2 * ps) :=
          mul_le_mul_of_nonneg_left (hk_int t) h0
      _ = Real.pi * a t ^ 2 := by rw [← hpp]; ring
  have hswap : ∫ t in (-T)..T, ∫ s in (-T)..T, B t s =
      ∫ s in (-T)..T, ∫ t in (-T)..T, B t s := by
    simp only [intervalIntegral.integral_of_le hle]
    refine MeasureTheory.integral_integral_swap ?_
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hBc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hB_le : ∫ t in (-T)..T, ∫ s in (-T)..T, B t s ≤ Real.pi * ∫ t in (-T)..T, a t ^ 2 := by
    rw [hswap, ← intervalIntegral.integral_const_mul]
    have hBc' : Continuous fun s => ∫ t in (-T)..T, B t s := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hBc.comp continuous_swap
    refine intervalIntegral.integral_mono_on hle (hBc'.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => Real.pi * a t ^ 2).intervalIntegrable _ _)
      (fun s _ => ?_)
    rw [hBint]
    have h0 : 0 ≤ ps / 2 * a s ^ 2 := by positivity
    calc ps / 2 * a s ^ 2 * ∫ t in (-T)..T, k s t ≤ ps / 2 * a s ^ 2 * (2 * ps) :=
          mul_le_mul_of_nonneg_left (hk_int s) h0
      _ = Real.pi * a s ^ 2 := by rw [← hpp]; ring
  have hsplit : ∫ t in (-T)..T, ∫ s in (-T)..T, (A t s + B t s) =
      (∫ t in (-T)..T, ∫ s in (-T)..T, A t s) + ∫ t in (-T)..T, ∫ s in (-T)..T, B t s := by
    rw [← intervalIntegral.integral_add ((cpar A hAc).intervalIntegrable _ _)
      ((cpar B hBc).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    exact intervalIntegral.integral_add ((hcont_row A hAc t).intervalIntegrable _ _)
      ((hcont_row B hBc t).intervalIntegrable _ _)
  have hABc : Continuous (Function.uncurry fun t s => A t s + B t s) := hAc.add hBc
  have hKn : Continuous (Function.uncurry fun t s => ‖K t s‖) := hKc.norm
  calc ‖∫ t in (-T)..T, ∫ s in (-T)..T, K t s‖
      ≤ ∫ t in (-T)..T, ‖∫ s in (-T)..T, K t s‖ :=
        intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ ∫ t in (-T)..T, ∫ s in (-T)..T, (A t s + B t s) := by
        refine intervalIntegral.integral_mono_on hle
          ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hKc _ _
            ).norm.intervalIntegrable _ _)
          ((cpar _ hABc).intervalIntegrable _ _) (fun t _ => ?_)
        refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
        exact intervalIntegral.integral_mono_on hle
          ((hKc.comp (Continuous.prodMk_right t)).norm.intervalIntegrable _ _)
          ((hcont_row _ hABc t).intervalIntegrable _ _) (fun s _ => hpt t s)
    _ = _ := hsplit
    _ ≤ Real.pi * (∫ t in (-T)..T, a t ^ 2) + Real.pi * ∫ t in (-T)..T, a t ^ 2 :=
        add_le_add hA_le hB_le
    _ = 2 * Real.pi * ∫ t in (-T)..T, a t ^ 2 := by ring

/-- Page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant, the Gaussian weighted L2 bound:
for every centre `m`,
`∫_ℝ e^(-(u-m)^2) |∫_{-T}^{T} g(t) e^(iut) dt|^2 du ≤ 2π ∫_{-T}^{T} |g(t)|^2 dt`.
PROVED from the LEAF `leaf_gaussian_fubini_identity` and `leaf_schur_gaussian`, since the
real part is at most the norm. -/
theorem gaussian_weighted_l2 (m T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ) (hg : Continuous g) :
    ∫ u, Real.exp (-(u - m) ^ 2) *
        ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  rw [leaf_gaussian_fubini_identity m T hT g hg]
  exact (Complex.re_le_norm _).trans (leaf_schur_gaussian m T hT g hg)

/-- Page 44, proof of Lemma 29, Gallagher [8] Lemma 2 variant, the local L2 bound over an
interval of length `log 6`, with `K₀ = 2π e^((log 6 / 2)^2)`. PROVED from
`gaussian_domination` and `gaussian_weighted_l2`. -/
theorem leaf_local_fourier_l2 :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ c : ℝ, ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ u in c..(c + Real.log 6), ‖∫ t in (-T)..T, g t * cexp ((u : ℂ) * (t : ℂ) * I)‖ ^ 2 ≤
        K₀ * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  refine ⟨Real.exp ((Real.log 6 / 2) ^ 2) * (2 * Real.pi), by positivity,
    fun c T hT g hg => ?_⟩
  refine (gaussian_domination c T hT g hg).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (gaussian_weighted_l2 _ T hT g hg)
    (Real.exp_pos _).le

/-- Page 44, proof of Lemma 29, "By a variant of [8], Lemma 2". PROVED from the two steps
`leaf_mellin_exp_substitution` and `leaf_local_fourier_l2`, with `K = 9 K₀`. The statement is
exactly that of `S64LowExcCharNP.leaf_mellin_mean_value`. -/
theorem mellin_mean_value_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y),
          ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        K * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  obtain ⟨K₀, hK₀, hloc⟩ := leaf_local_fourier_l2
  refine ⟨9 * K₀, by positivity, fun Y hY T hT g hg => ?_⟩
  have h1 := leaf_mellin_exp_substitution Y hY T hT g hg
  have h2 := hloc (Real.log (Y / 2)) T hT g hg
  have hsq : (0 : ℝ) ≤ (3 * Y) ^ 2 := by positivity
  calc _ ≤ _ := h1
    _ ≤ (3 * Y) ^ 2 * (K₀ * ∫ t in (-T)..T, ‖g t‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hsq
    _ = 9 * K₀ * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by ring

end LeanLab.BHP1997.S72MellinMV
