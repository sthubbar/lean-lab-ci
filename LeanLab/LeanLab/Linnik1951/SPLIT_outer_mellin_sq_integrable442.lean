/-
Split of the square integrability leaf `outer_mellin_sq_integrable442` of
`SPLIT_abstract_outer_kernels442` into three steps.

The leaf asks that the squared Mellin integral of a coefficient satisfying the
line bound be interval integrable in the frequency over the outer range from
four over N to one over R. Two things are needed for that, and they are
separated here. First, the log weighted absolute kernel is controlled by one
integrable function of the single real variable t that does not depend on the
frequency, so on the outer range the kernel mass is at most the integral of
that dominating function; the line bound then converts the Mellin integral into
the kernel mass, which bounds the square pointwise. Second, the Mellin integral
is a measurable function of the frequency, so a measurable function bounded on
an interval of finite length is integrable there.

Nothing here changes the statement of `outer_mellin_sq_integrable442`; the
theorem `outer_mellin_sq_integrable442_split` restates it character for
character and proves it from the three leaves without using the original
theorem.
-/
import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

namespace LeanLab.Linnik1951

open MeasureTheory

open Filter
open scoped Topology

/- The block below, from `private lemma exp_neg_abs_le_inv_sq` to the end of
`private theorem continuous_mellinU442`, is carried verbatim from the proved
stack of `LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442` in this same
folder, which keeps it `private`, so it has to be restated here to be used.
It is not this chat's work. It gives the Gamma decay on the shifted line, the
integrability of the model weight, the power bound with the argument, and the
continuity of the kernel mass and of the Mellin integral in the frequency. -/

private lemma exp_neg_abs_le_inv_sq (c : ℝ) (hc : 0 < c) (t : ℝ) :
    Real.exp (-(c * |t|)) ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ := by
  have hc3 : (0 : ℝ) < c ^ 3 := by positivity
  rcases le_total |t| 1 with h1 | h1
  · have hL : Real.exp (-(c * |t|)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg t]
    have hR : (1 : ℝ) ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ := by
      have h2 : (2 : ℝ) ≤ 2 + 12 / c ^ 3 := by
        have hpos12 : (0 : ℝ) < 12 / c ^ 3 := by positivity
        linarith
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t, h1]
      have hinv : (1 / 2 : ℝ) ≤ (1 + t ^ 2)⁻¹ := by
        have hle : 1 + t ^ 2 ≤ 2 := by linarith
        calc (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
          _ ≤ (1 + t ^ 2)⁻¹ := inv_anti₀ (by nlinarith [sq_nonneg t]) hle
      calc (1 : ℝ) = 2 * (1 / 2) := by norm_num
        _ ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ :=
            mul_le_mul h2 hinv (by norm_num) (by linarith)
    linarith
  · have ht1 : (1 : ℝ) ≤ |t| := h1
    have hpos : (0 : ℝ) < c * |t| := by positivity
    have hfac := Real.pow_div_factorial_le_exp (x := c * |t|) hpos.le 3
    norm_num at hfac
    have h3 : (c * |t|) ^ 3 / 6 ≤ Real.exp (c * |t|) := hfac
    have hexp : Real.exp (-(c * |t|)) = (Real.exp (c * |t|))⁻¹ := by
      rw [← Real.exp_neg]
    rw [hexp]
    have hinv : (Real.exp (c * |t|))⁻¹ ≤ 6 / (c * |t|) ^ 3 := by
      have hcube : (0 : ℝ) < (c * |t|) ^ 3 := by positivity
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 6)] at h3
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      have h4 : (1 : ℝ) ≤ Real.exp (c * |t|) * 6 / (c * |t|) ^ 3 := (one_le_div hcube).mpr h3
      have he : 6 / (c * |t|) ^ 3 * Real.exp (c * |t|) =
          Real.exp (c * |t|) * 6 / (c * |t|) ^ 3 := by ring
      rw [he]
      exact h4
    have hbound : 6 / (c * |t|) ^ 3 ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ := by
      have ht3 : (1 : ℝ) ≤ |t| ^ 3 := by
        calc (1:ℝ) = 1 ^ 3 := by norm_num
          _ ≤ |t| ^ 3 := pow_le_pow_left₀ (by norm_num) ht1 3
      have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      have hden : (c * |t|) ^ 3 = c ^ 3 * |t| ^ 3 := by ring
      rw [hden, ht2]
      have hA : (0 : ℝ) < c ^ 3 * |t| ^ 3 := by positivity
      have hB : (0 : ℝ) < 1 + |t| ^ 2 := by positivity
      rw [div_le_iff₀ hA]
      have hpoly : 6 * (1 + |t| ^ 2) ≤ (2 + 12 / c ^ 3) * (c ^ 3 * |t| ^ 3) := by
        have e1 : (2 + 12 / c ^ 3) * (c ^ 3 * |t| ^ 3) =
            2 * c ^ 3 * |t| ^ 3 + 12 * |t| ^ 3 := by
          field_simp
        rw [e1]
        have h12 : 12 * |t| ^ 2 ≤ 12 * |t| ^ 3 := by nlinarith [ht3, sq_nonneg |t|, ht1]
        have hone : 1 + |t| ^ 2 ≤ 2 * |t| ^ 2 := by nlinarith [ht1]
        have hpos2 : (0 : ℝ) ≤ 2 * c ^ 3 * |t| ^ 3 := by positivity
        nlinarith [h12, hone, hpos2]
      have e : (2 + 12 / c ^ 3) * (1 + |t| ^ 2)⁻¹ * (c ^ 3 * |t| ^ 3) =
          (2 + 12 / c ^ 3) * (c ^ 3 * |t| ^ 3) / (1 + |t| ^ 2) := by
        rw [inv_eq_one_div]; ring
      rw [e]
      have e2 : (6 : ℝ) = 6 * (1 + |t| ^ 2) / (1 + |t| ^ 2) := by
        field_simp
      rw [e2]
      exact div_le_div_of_nonneg_right hpoly hB.le
    exact hinv.trans hbound

/-- `exp (-(c * |t|))` is integrable for `c > 0`. -/
private lemma integrable_exp_neg_abs_mul (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-(c * |t|))) := by
  have hdom : Integrable (fun t : ℝ =>
      (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hdom (by fun_prop) (Filter.Eventually.of_forall (fun t => ?_))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_abs_le_inv_sq c hc t

/-- `(s + 3) ^ k` is dominated by a half exponential. -/
private lemma poly_pow_le_exp (c : ℝ) (hc : 0 < c) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (s + 3) ^ k ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) := by
  have hpos : (0 : ℝ) ≤ 6 ^ k + (4 / c) ^ k * (k.factorial : ℝ) := by positivity
  rcases le_total s 3 with h3 | h3
  · have h6 : s + 3 ≤ 6 := by linarith
    have h0 : (0 : ℝ) ≤ s + 3 := by linarith
    have hp : (s + 3) ^ k ≤ 6 ^ k := pow_le_pow_left₀ h0 h6 k
    have he : (1 : ℝ) ≤ Real.exp (c * s / 2) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      positivity
    have hmul : (6 : ℝ) ^ k ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) *
        Real.exp (c * s / 2) := by
      have hle : (6 : ℝ) ^ k ≤ 6 ^ k + (4 / c) ^ k * (k.factorial : ℝ) := by
        have : (0 : ℝ) ≤ (4 / c) ^ k * (k.factorial : ℝ) := by positivity
        linarith
      calc (6 : ℝ) ^ k ≤ 6 ^ k + (4 / c) ^ k * (k.factorial : ℝ) := hle
        _ = (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * 1 := by ring
        _ ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) :=
            mul_le_mul_of_nonneg_left he hpos
    exact hp.trans hmul
  · have h2 : s + 3 ≤ 2 * s := by linarith
    have h0 : (0 : ℝ) ≤ s + 3 := by linarith
    have hp : (s + 3) ^ k ≤ (2 * s) ^ k := pow_le_pow_left₀ h0 h2 k
    have hx : (0 : ℝ) ≤ c * s / 2 := by positivity
    have hfac := Real.pow_div_factorial_le_exp (x := c * s / 2) hx k
    have hc2 : (0 : ℝ) < (c / 2) ^ k := by positivity
    have hkey : s ^ k ≤ (2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2) := by
      have hcalc : (c * s / 2) ^ k / (k.factorial : ℝ) = (c / 2) ^ k * s ^ k / (k.factorial : ℝ) := by
        ring
      rw [hcalc, div_le_iff₀ (by positivity : (0:ℝ) < (k.factorial : ℝ))] at hfac
      have hstep : s ^ k ≤ (Real.exp (c * s / 2) * (k.factorial : ℝ)) / ((c / 2) ^ k) := by
        rw [le_div_iff₀ hc2]
        linarith [hfac]
      have h4c : (2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2) =
          (Real.exp (c * s / 2) * (k.factorial : ℝ)) / ((c / 2) ^ k) := by
        rw [eq_div_iff (ne_of_gt hc2)]
        have hone : (2 / c) ^ k * (c / 2) ^ k = 1 := by
          rw [← mul_pow]
          have h1 : 2 / c * (c / 2) = 1 := by field_simp
          rw [h1, one_pow]
        calc (2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2) * (c / 2) ^ k
            = ((2 / c) ^ k * (c / 2) ^ k) * ((k.factorial : ℝ) * Real.exp (c * s / 2)) := by
              ring
          _ = (k.factorial : ℝ) * Real.exp (c * s / 2) := by rw [hone]; ring
          _ = Real.exp (c * s / 2) * (k.factorial : ℝ) := by ring
      rw [h4c]
      exact hstep
    have hp2 : (2 * s) ^ k = 2 ^ k * s ^ k := by ring
    have h26 : 2 ^ k * (2 / c) ^ k = (4 / c) ^ k := by
      have h24 : 2 * (2 / c) = 4 / c := by
        field_simp
        norm_num
      rw [← mul_pow, h24]
    calc (s + 3) ^ k ≤ (2 * s) ^ k := hp
      _ = 2 ^ k * s ^ k := hp2
      _ ≤ 2 ^ k * ((2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = ((4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) := by
          rw [show 2 ^ k * ((2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2)) =
              (2 ^ k * (2 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) from by ring, h26]
      _ ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have h6k : (0 : ℝ) ≤ 6 ^ k := by positivity
          have hnk : (0 : ℝ) ≤ (4 / c) ^ k * (k.factorial : ℝ) := by positivity
          linarith



open MeasureTheory

/-- Gamma decay on the shifted Mellin line (adapted from
`LeanLab.Linnik1951.Gamma442.gamma_mellin_line442`, restated here so that
this file needs only the Mathlib-clean `GammaBounds` module). -/
private theorem gamma_line_decay442 (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
    ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hNr)
  have hlog : 0 < Real.log N := by linarith
  have hinv : 1 / Real.log N ≤ 1 := (div_le_one hlog).mpr hl
  have hre : (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (mellinLine1622 N t).im = t := by
    simp only [mellinLine1622, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hinvpos : 0 < 1 / Real.log N := div_pos one_pos hlog
  have hlo : 1 / 2 ≤ (mellinLine1622 N t).re := by rw [hre]; linarith
  have hhi : (mellinLine1622 N t).re ≤ 3 / 2 := by rw [hre]; linarith
  have hnorm : ‖mellinLine1622 N t + 1‖ ≤ 3 + |t| := by
    have hh := Complex.norm_le_abs_re_add_abs_im (mellinLine1622 N t + 1)
    have hr : (mellinLine1622 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by simp [hre]
    have hi : (mellinLine1622 N t + 1).im = t := by simp [him]
    rw [hr, hi, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 + 1 / Real.log N + 1)] at hh
    linarith
  rcases lt_or_ge t 0 with ht | ht
  · have h2 := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL (s := star (mellinLine1622 N t))
      (by simpa using hlo) (by simpa using hhi)
    have hg : ‖Complex.Gamma (star (mellinLine1622 N t))‖ =
        ‖Complex.Gamma (mellinLine1622 N t)‖ := by
      simp only [Complex.star_def, Complex.Gamma_conj, Complex.norm_conj]
    have hn : ‖star (mellinLine1622 N t) + 1‖ = ‖mellinLine1622 N t + 1‖ := by
      simpa using norm_star (mellinLine1622 N t + 1)
    have hi2 : (star (mellinLine1622 N t)).im = -t := by simp [him]
    rw [hg, hn, hi2] at h2
    have h2' : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t + 1‖ *
          Real.exp (-(Real.pi * |t| / 2)) := by
      rw [abs_of_neg ht]; exact h2
    exact h2'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (by positivity)) (Real.exp_pos _).le)
  · have h := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL (s := mellinLine1622 N t) hlo hhi
    rw [him] at h
    have h' : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t + 1‖ *
          Real.exp (-(Real.pi * |t| / 2)) := by
      rw [abs_of_nonneg ht]; exact h
    exact h'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (by positivity)) (Real.exp_pos _).le)


/-- The absolute Mellin weight `(3 + |t|) * log (N (|t| + 2)) ^ m * exp (-c |t|)` is integrable. -/
private theorem integrable_weight_log (N : ℕ) (hN : 2 ≤ N) (c : ℝ) (hc : 0 < c) (m : ℕ) :
    Integrable (fun t : ℝ =>
      (3 + |t|) * Real.exp (-(c * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ m) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hC : (0 : ℝ) ≤ 6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ) := by positivity
  have hdom : Integrable (fun t : ℝ =>
      (N : ℝ) ^ m * (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
        Real.exp (-(c / 2 * |t|))) :=
    (integrable_exp_neg_abs_mul (c / 2) (by linarith)).const_mul _
  refine Integrable.mono' hdom (by fun_prop) (Filter.Eventually.of_forall (fun t => ?_))
  have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg
    have hm2 : (2 * 2 : ℝ) ≤ (N : ℝ) * (|t| + 2) :=
      mul_le_mul hNr (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2)
        (by norm_num) (by linarith : (0 : ℝ) ≤ (N : ℝ))
    linarith
  have h5 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ m := pow_nonneg hlog0 m
  have hnonneg : (0 : ℝ) ≤ (3 + |t|) * Real.exp (-(c * |t|)) *
      Real.log ((N : ℝ) * (|t| + 2)) ^ m :=
    mul_nonneg (mul_nonneg (by linarith [abs_nonneg t]) (Real.exp_pos _).le) h5
  rw [Real.norm_of_nonneg hnonneg]
  have hx : (0 : ℝ) < (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have h1 : Real.log ((N : ℝ) * (|t| + 2)) ≤ (N : ℝ) * (|t| + 2) := by
    have := Real.log_le_sub_one_of_pos hx
    linarith
  have h2 : Real.log ((N : ℝ) * (|t| + 2)) ^ m ≤ ((N : ℝ) * (|t| + 2)) ^ m :=
    pow_le_pow_left₀ hlog0 h1 m
  have h3 : ((N : ℝ) * (|t| + 2)) ^ m ≤ N ^ m * (|t| + 3) ^ m := by
    have hle : (N : ℝ) * (|t| + 2) ≤ N * (|t| + 3) := by nlinarith [abs_nonneg t]
    calc ((N : ℝ) * (|t| + 2)) ^ m ≤ (N * (|t| + 3)) ^ m := pow_le_pow_left₀ hx.le hle m
      _ = N ^ m * (|t| + 3) ^ m := by rw [mul_pow]
  have hpoly := poly_pow_le_exp c hc (m + 1) |t| (abs_nonneg t)
  have hexp : Real.exp (c * |t| / 2) * Real.exp (-(c * |t|)) = Real.exp (-(c / 2 * |t|)) := by
    rw [← Real.exp_add, show c * |t| / 2 + -(c * |t|) = -(c / 2 * |t|) from by ring]
  have hmain : (3 + |t|) * Real.exp (-(c * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ m ≤
      (3 + |t|) * Real.exp (-(c * |t|)) * (N ^ m * (|t| + 3) ^ m) := by
    exact mul_le_mul_of_nonneg_left (h2.trans h3)
      (mul_nonneg (by linarith [abs_nonneg t]) (Real.exp_pos _).le)
  have hstep : (3 + |t|) * Real.exp (-(c * |t|)) * (N ^ m * (|t| + 3) ^ m) ≤
      N ^ m * (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
        Real.exp (-(c / 2 * |t|)) := by
    have hq : (3 + |t|) * (|t| + 3) ^ m = (|t| + 3) ^ (m + 1) := by
      rw [pow_succ]
      ring
    calc (3 + |t|) * Real.exp (-(c * |t|)) * (N ^ m * (|t| + 3) ^ m)
        = N ^ m * ((|t| + 3) ^ (m + 1) * Real.exp (-(c * |t|))) := by rw [← hq]; ring
      _ ≤ N ^ m * ((6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
            Real.exp (c * |t| / 2) * Real.exp (-(c * |t|))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = N ^ m * (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
            Real.exp (-(c / 2 * |t|)) := by
          rw [show (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
              Real.exp (c * |t| / 2) * Real.exp (-(c * |t|)) =
              (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                (Real.exp (c * |t| / 2) * Real.exp (-(c * |t|))) from by ring, hexp]
          ring
  exact hmain.trans hstep

/-- The power factor of the kernel, with the absolute value of the argument. -/
private theorem cpow_line_bound_abs442 (N : ℕ) (hN : 2 ≤ N) (z : ℂ)
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

/-- The kernel weight is continuous in the line variable. -/
private theorem continuous_kernel_t442 (N : ℕ) (hN : 3 ≤ N) (z : ℂ)
    (hzre : z.re = 1 / (N : ℝ)) :
    Continuous (fun t : ℝ =>
      ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hNr1 : (1 : ℝ) < (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNr0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hNr1
  have hz0 : z ≠ 0 := by
    intro h0
    have hz : z.re = 0 := by rw [h0]; simp
    rw [hzre] at hz
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := div_pos one_pos hNr0
    linarith
  have hmc : Continuous (fun t : ℝ => mellinLine1622 N t) := by
    simp only [mellinLine1622]
    fun_prop
  have hmre : ∀ t : ℝ, (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine1622 N t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : ∀ m : ℕ, mellinLine1622 N t ≠ -m := by
      intro m hm
      have hrev := congr_arg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re, hmre] at hrev
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hinvpos : 0 < 1 / Real.log N := div_pos one_pos hlogN
      linarith
    exact ((Complex.differentiableAt_Gamma _ hne).continuousAt).comp hmc.continuousAt
  have hpow : Continuous (fun t : ℝ => z ^ (-(mellinLine1622 N t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hinner : Continuous (fun t : ℝ => -(mellinLine1622 N t)) := hmc.neg
    exact (continuousAt_const_cpow hz0).comp hinner.continuousAt
  apply Continuous.mul
  · exact (hpow.mul hGamma).norm
  · have h1 : Continuous (fun t : ℝ => (N : ℝ) * (|t| + 2)) := by fun_prop
    exact (h1.log (fun t => by positivity)).pow 3

/-- The absolute kernel mass is continuous in the frequency. -/
private theorem continuous_mass442 (N : ℕ) (hN : 3 ≤ N) (Z : ℝ → ℂ) (hZc : Continuous Z)
    (hZre : ∀ α, (Z α).re = 1 / (N : ℝ)) :
    Continuous (fun α : ℝ =>
      ∫ t : ℝ, ‖Z α ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hN2 : 2 ≤ N := by omega
  have hNr0 : (0 : ℝ) < (N : ℝ) := by
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h1N : (0 : ℝ) < 1 / (N : ℝ) := div_pos one_pos hNr0
  have hZslit : ∀ α, Z α ∈ Complex.slitPlane := fun α => Or.inl (by rw [hZre α]; exact h1N)
  rw [continuous_iff_continuousAt]
  intro α₀
  set a₀ : ℝ := |(Z α₀).arg| with ha₀
  have ha₀lt : a₀ < Real.pi / 2 := by
    rw [ha₀]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hZre α₀]; exact h1N))
  set δ₀ : ℝ := (Real.pi / 2 - a₀) / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; linarith
  have hargc : ContinuousAt (fun α => |(Z α).arg|) α₀ :=
    ((Complex.continuousAt_arg (hZslit α₀)).comp hZc.continuousAt).abs
  have hev : ∀ᶠ α in 𝓝 α₀, |(Z α).arg| ≤ a₀ + δ₀ := by
    have hlt : ∀ᶠ α in 𝓝 α₀, |(Z α).arg| < a₀ + δ₀ :=
      hargc.eventually_lt continuousAt_const (by linarith)
    filter_upwards [hlt] with α hα using hα.le
  have hboundint : Integrable (fun t : ℝ => Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) *
      ((3 + |t|) * Real.exp (-(δ₀ * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :=
    (integrable_weight_log N hN2 δ₀ hδ₀ 3).const_mul _
  refine continuousAt_of_dominated (F := fun α t =>
      ‖Z α ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3)
    (bound := fun t => Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) *
      ((3 + |t|) * Real.exp (-(δ₀ * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3))
    ?_ ?_ hboundint ?_
  · filter_upwards with α
    exact (continuous_kernel_t442 N hN (Z α) (hZre α)).aestronglyMeasurable
  · filter_upwards [hev] with α hα
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      have hm2 : (2 * 2 : ℝ) ≤ (N : ℝ) * (|t| + 2) :=
        mul_le_mul (by exact_mod_cast hN2) (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2)
          (by norm_num) (by linarith : (0 : ℝ) ≤ (N : ℝ))
      linarith
    have h5 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := pow_nonneg hlog0 3
    have hnonneg : (0 : ℝ) ≤ ‖Z α ^ (-(mellinLine1622 N t)) *
        Complex.Gamma (mellinLine1622 N t)‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
      mul_nonneg (norm_nonneg _) h5
    rw [Real.norm_of_nonneg hnonneg, norm_mul]
    have hb1 := cpow_line_bound_abs442 N hN2 (Z α) (hZre α) t
    have hb2 := gamma_line_decay442 N hN t
    have hp1 : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (N:ℝ) * Real.exp (|t| * |(Z α).arg|) :=
      by positivity
    have hprod := mul_le_mul hb1 hb2 (norm_nonneg _) hp1
    have hprod' := mul_le_mul_of_nonneg_right hprod h5
    have hkey : |(Z α).arg| - Real.pi / 2 ≤ -δ₀ := by
      rw [hδ₀def]; rw [ha₀] at hα; linarith
    have hexp : Real.exp (|t| * |(Z α).arg|) * Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.exp (-(δ₀ * |t|)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hkey (abs_nonneg t)
      nlinarith [hmul, abs_nonneg t, mul_nonneg (abs_nonneg t) (abs_nonneg (Z α).arg)]
    calc ‖Z α ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3
        ≤ (Real.exp 1 * Real.sqrt (N:ℝ) * Real.exp (|t| * |(Z α).arg|)) *
            (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := hprod'
      _ = Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) *
            (Real.exp (|t| * |(Z α).arg|) * Real.exp (-(Real.pi * |t| / 2))) *
              ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by ring
      _ ≤ Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) *
            Real.exp (-(δ₀ * |t|)) *
              ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
          have hK : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) := by positivity
          have hL : (0 : ℝ) ≤ (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
            mul_nonneg (by linarith [abs_nonneg t]) h5
          have h2 := mul_le_mul_of_nonneg_right hexp hL
          have h2' := mul_le_mul_of_nonneg_left h2 hK
          linarith [h2']
      _ = Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) *
            ((3 + |t|) * Real.exp (-(δ₀ * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by ring
  · filter_upwards with t
    have hct : ContinuousAt (fun α => Z α ^ (-(mellinLine1622 N t))) α₀ :=
      (continuousAt_cpow_const (hZslit α₀)).comp hZc.continuousAt
    exact ((hct.mul continuousAt_const).norm.mul continuousAt_const)

private theorem continuous_kernel_prod442 (N : ℕ) (hN : 3 ≤ N) (z : ℂ)
    (hzre : z.re = 1 / (N : ℝ)) :
    Continuous (fun t : ℝ => z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) := by
  have hNr1 : (1 : ℝ) < (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNr0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hNr1
  have hz0 : z ≠ 0 := by
    intro h0
    have hz : z.re = 0 := by rw [h0]; simp
    rw [hzre] at hz
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := div_pos one_pos hNr0
    linarith
  have hmc : Continuous (fun t : ℝ => mellinLine1622 N t) := by
    simp only [mellinLine1622]
    fun_prop
  have hmre : ∀ t : ℝ, (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine1622 N t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : ∀ m : ℕ, mellinLine1622 N t ≠ -m := by
      intro m hm
      have hrev := congr_arg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re, hmre] at hrev
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hinvpos : 0 < 1 / Real.log N := div_pos one_pos hlogN
      linarith
    exact ((Complex.differentiableAt_Gamma _ hne).continuousAt).comp hmc.continuousAt
  have hpow : Continuous (fun t : ℝ => z ^ (-(mellinLine1622 N t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hinner : Continuous (fun t : ℝ => -(mellinLine1622 N t)) := hmc.neg
    exact (continuousAt_const_cpow hz0).comp hinner.continuousAt
  exact hpow.mul hGamma

/-- The norm of the kernel is continuous in the line variable. -/
private theorem continuous_kernel_norm442 (N : ℕ) (hN : 3 ≤ N) (z : ℂ)
    (hzre : z.re = 1 / (N : ℝ)) :
    Continuous (fun t : ℝ => ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖) :=
  (continuous_kernel_prod442 N hN z hzre).norm

/-- The Mellin integral `U` is continuous in the frequency. -/
private theorem continuous_mellinU442 (N : ℕ) (hN : 3 ≤ N) (B0 : ℝ) (hB0 : 0 < B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) :
    Continuous (fun α : ℝ => mellinU1622 N M α) := by
  have hN2 : 2 ≤ N := by omega
  have hNr0 : (0 : ℝ) < (N : ℝ) := by
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h1N : (0 : ℝ) < 1 / (N : ℝ) := div_pos one_pos hNr0
  set Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hZ
  have hZc : Continuous Z := by rw [hZ]; fun_prop
  have hZre : ∀ α, (Z α).re = 1 / (N : ℝ) := fun α => by simp [hZ]
  have hZslit : ∀ α, Z α ∈ Complex.slitPlane := fun α => Or.inl (by rw [hZre α]; exact h1N)
  rw [continuous_iff_continuousAt]
  intro α₀
  set a₀ : ℝ := |(Z α₀).arg| with ha₀
  have ha₀lt : a₀ < Real.pi / 2 := by
    rw [ha₀]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hZre α₀]; exact h1N))
  set δ₀ : ℝ := (Real.pi / 2 - a₀) / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; linarith
  have hargc : ContinuousAt (fun α => |(Z α).arg|) α₀ :=
    ((Complex.continuousAt_arg (hZslit α₀)).comp hZc.continuousAt).abs
  have hev : ∀ᶠ α in 𝓝 α₀, |(Z α).arg| ≤ a₀ + δ₀ := by
    have hlt : ∀ᶠ α in 𝓝 α₀, |(Z α).arg| < a₀ + δ₀ :=
      hargc.eventually_lt continuousAt_const (by linarith)
    filter_upwards [hlt] with α hα using hα.le
  have hboundint : Integrable (fun t : ℝ => Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) * B0 *
      ((3 + |t|) * Real.exp (-(δ₀ * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :=
    (integrable_weight_log N hN2 δ₀ hδ₀ 3).const_mul _
  have hmeas : ∀ᶠ α in 𝓝 α₀, AEStronglyMeasurable (fun t : ℝ =>
      Z α ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t) * M t) volume := by
    filter_upwards with α
    exact (Continuous.mul (continuous_kernel_prod442 N hN (Z α) (hZre α)) hM.1).aestronglyMeasurable
  have hboundpt : ∀ᶠ α in 𝓝 α₀, ∀ᵐ t ∂volume,
      ‖Z α ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t) * M t‖ ≤
        Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) * B0 *
          ((3 + |t|) * Real.exp (-(δ₀ * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
    filter_upwards [hev] with α hα
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      have hm2 : (2 * 2 : ℝ) ≤ (N : ℝ) * (|t| + 2) :=
        mul_le_mul (by exact_mod_cast hN2) (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2)
          (by norm_num) (by linarith : (0 : ℝ) ≤ (N : ℝ))
      linarith
    have hL3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := pow_nonneg hlog0 3
    have h3 : (0 : ℝ) ≤ 3 + |t| := by linarith [abs_nonneg t]
    rw [norm_mul, norm_mul]
    have hb1 := cpow_line_bound_abs442 N hN2 (Z α) (hZre α) t
    have hb2 := gamma_line_decay442 N hN t
    have hb3 : ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := hM.2 t
    have hp1 : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (N:ℝ) * Real.exp (|t| * |(Z α).arg|) := by
      positivity
    have hp3 : (0 : ℝ) ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h0 : (0 : ℝ) ≤ B0 := hB0.le
      positivity
    have hs1 : ‖Z α ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        (Real.exp 1 * Real.sqrt (N:ℝ) * Real.exp (|t| * |(Z α).arg|)) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul hb1 hb2 (norm_nonneg _) hp1
    have hp12 : (0 : ℝ) ≤ (Real.exp 1 * Real.sqrt (N:ℝ) * Real.exp (|t| * |(Z α).arg|)) *
        (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) := by
      positivity
    have hs2 : ‖Z α ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ * ‖M t‖ ≤
        ((Real.exp 1 * Real.sqrt (N:ℝ) * Real.exp (|t| * |(Z α).arg|)) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)))) *
            (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mul_le_mul hs1 hb3 (norm_nonneg _) hp12
    have hkey : |(Z α).arg| - Real.pi / 2 ≤ -δ₀ := by
      rw [hδ₀def]
      rw [ha₀] at hα
      linarith
    have hexp : Real.exp (|t| * |(Z α).arg|) * Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.exp (-(δ₀ * |t|)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hkey (abs_nonneg t)
      nlinarith [hmul, abs_nonneg t]
    have hK : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2 * Real.pi) * B0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) hB0.le
    have hLcomb : (0 : ℝ) ≤ (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
      mul_nonneg h3 hL3
    calc ‖Z α ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ * ‖M t‖
        ≤ ((Real.exp 1 * Real.sqrt (N:ℝ) * Real.exp (|t| * |(Z α).arg|)) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)))) *
            (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := hs2
      _ = Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2 * Real.pi) * B0 *
            ((Real.exp (|t| * |(Z α).arg|) * Real.exp (-(Real.pi * |t| / 2))) *
              ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) := by ring
      _ ≤ Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2 * Real.pi) * B0 *
            (Real.exp (-(δ₀ * |t|)) * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) := by
          have h2 := mul_le_mul_of_nonneg_right hexp hLcomb
          exact mul_le_mul_of_nonneg_left h2 hK
      _ = Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2 * Real.pi) * B0 *
            ((3 + |t|) * Real.exp (-(δ₀ * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
          ring
  have hcontpt : ∀ᵐ t ∂volume, ContinuousAt (fun α =>
      Z α ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t) * M t) α₀ := by
    filter_upwards with t
    have hct : ContinuousAt (fun α => Z α ^ (-(mellinLine1622 N t))) α₀ :=
      (continuousAt_cpow_const (hZslit α₀)).comp hZc.continuousAt
    exact ((hct.mul continuousAt_const).mul continuousAt_const)
  have hmain := continuousAt_of_dominated (μ := volume) (x₀ := α₀)
    (F := fun α t => Z α ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t) * M t)
    (bound := fun t => Real.exp 1 * Real.sqrt (N:ℝ) * Real.sqrt (2*Real.pi) * B0 *
      ((3 + |t|) * Real.exp (-(δ₀ * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3))
    hmeas hboundpt hboundint hcontpt

  have hfin : ContinuousAt (fun α => ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t, Z α ^ (-(mellinLine1622 N t)) *
      Complex.Gamma (mellinLine1622 N t) * M t) α₀ := continuousAt_const.mul hmain
  simpa only [mellinU1622, hZ] using hfin

/-- LEAF. Step 1 of 3, the kernel layer. On the outer range the log weighted
absolute kernel mass is bounded by one positive constant that does not depend on
the frequency. The frequency enters the kernel only through the base one over N
plus two pi alpha i on the shifted line; the shifted real part is fixed and
positive there, so the complex power and the Gamma factor depend continuously on
the frequency, and a continuous real function is bounded on the closed interval.
No coefficient, no Mellin integral and no integral over the frequency occur. -/
theorem outer_kernel_mass_uniform442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Icc (4 / (N : ℝ)) (1 / R) →
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤ C := by
  have hZc : Continuous (fun α : ℝ =>
      ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by fun_prop
  have hZre : ∀ α : ℝ,
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).re = 1 / (N : ℝ) :=
    fun α => by simp
  have hmass : Continuous (fun α : ℝ => ∫ t : ℝ,
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
    continuous_mass442 N hN
      (fun α : ℝ => ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)
      hZc hZre
  by_cases hne : (Set.Icc (4 / (N : ℝ)) (1 / R)).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hx⟩ hmass.continuousOn
    refine ⟨max 1 (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * x₀ : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3), ?_,
      fun α hα => (hmax hα).trans (le_max_right _ _)⟩
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · exact ⟨1, one_pos, fun α hα => absurd ⟨α, hα⟩ hne⟩

/-- LEAF. Step 2 of 3, the coefficient layer. The line bound removes the
coefficient from the Mellin integral: the norm of the integral of the kernel
times the coefficient is at most B0 times the log weighted kernel mass. This is
the norm integral inequality together with the pointwise line bound, and it
carries no integrability of the square and no integral over the frequency. It
is not vacuous: the integrability hypothesis is met on the outer range by the
previous step. -/
theorem line_bound_norm_integral442 (N : ℕ) (B0 α : ℝ) (M : ℝ → ℂ)
    (hM : LineBound1622 N B0 M)
    (hI : Integrable (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :
    ‖∫ t : ℝ,
        ((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t‖ ≤
      B0 * ∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  have hb (t : ℝ) :
      ‖((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t‖ ≤
        B0 * (‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left (hM.2 t) (norm_nonneg _)).trans (le_of_eq ?_)
    ring
  have hnorm := norm_integral_le_of_norm_le (hI.const_mul B0)
    (Filter.Eventually.of_forall hb)
  refine hnorm.trans (le_of_eq ?_)
  rw [integral_const_mul]

/-- LEAF. Step 3 of 3, the measurable layer. For a coefficient continuous and
bounded by the line bound, the squared norm of the Mellin integral is a
strongly measurable function of the frequency, restricted to the outer range.
This is the measurability half of the conclusion and nothing about size. The
frequency enters only through the base one over N plus two pi alpha i on the
shifted line, where the complex power and the Gamma factor are continuous in
the line variable and dominated by one integrable weight, so the Mellin
integral is continuous and hence strongly measurable in the frequency. PROVED.
It is not vacuous: the coefficient identically one on a large N satisfies the
line bound. -/
theorem mellinU_sq_aemeasurable442 (N : ℕ) (hN : 3 ≤ N) (B0 : ℝ) (hB0 : 0 < B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) (R : ℝ) (hR : 1 ≤ R) :
    AEStronglyMeasurable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2)
      (volume.restrict (Set.uIoc (4 / (N : ℝ)) (1 / R))) :=
  ((continuous_mellinU442 N hN B0 hB0 M hM).norm.pow 2).aestronglyMeasurable.restrict

/-- Assembly of `outer_mellin_sq_integrable442` from the three leaves. The
uniform mass bound gives the pointwise bound on the square of the Mellin
integral through the norm integral inequality, and the measurability of the
Mellin integral together with the finiteness of the interval makes the square
integrable there. The original theorem is not used. -/
theorem outer_mellin_sq_integrable442_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) volume
          (4 / (N : ℝ)) (1 / R) := by
  refine ⟨8, ?_⟩
  intro N hN R hR1 hR2 M hM
  have h8 : 8 ≤ N := le_of_lt hN
  have h3 : 3 ≤ N := by omega
  obtain ⟨C, -, hCbound⟩ := outer_kernel_mass_uniform442 N h3 R hR1
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have h4R : 4 * R ≤ (N : ℝ) := by
    have hfour := four_rpow1622 N h8
    nlinarith [hfour, hR2]
  have hle : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNr hRp]
    simpa using h4R
  have hmono : Set.uIoc (4 / (N : ℝ)) (1 / R) ⊆ Set.Icc (4 / (N : ℝ)) (1 / R) := by
    rw [Set.uIoc_of_le hle]
    exact Set.Ioc_subset_Icc_self
  have hpt : ∀ α : ℝ, α ∈ Set.Icc (4 / (N : ℝ)) (1 / R) →
      ‖mellinU1622 N M α‖ ^ 2 ≤
        ((1 / (2 * Real.pi)) * (B0 * C)) ^ 2 := by
    intro α hα
    have hIα := outer_kernel_integrable442 N h3 R hR1 α hα
    have hL2 := line_bound_norm_integral442 N B0 α M hM hIα
    have hnU : ‖mellinU1622 N M α‖ =
        (1 / (2 * Real.pi)) * ‖∫ t : ℝ,
          ((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t‖ := by
      rw [show mellinU1622 N M α = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
            ((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t
          from rfl,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    have hstep1 : ‖mellinU1622 N M α‖ ≤ (1 / (2 * Real.pi)) *
        (B0 * ∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
      rw [hnU]
      exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    have hstep2 : (1 / (2 * Real.pi)) *
          (B0 * ∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
        (1 / (2 * Real.pi)) * (B0 * C) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hCbound α hα) hB0.le) (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) (hstep1.trans hstep2) 2
  have hs : volume (Set.uIoc (4 / (N : ℝ)) (1 / R)) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound hs ?_ (((1 / (2 * Real.pi)) * (B0 * C)) ^ 2) ?_
  · exact mellinU_sq_aemeasurable442 N h3 B0 hB0 M hM R hR1
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with α hα
    have hp := hpt α (hmono hα)
    rwa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]

#print axioms outer_mellin_sq_integrable442_split

end LeanLab.Linnik1951
