import LeanLab.LanguascoPintzZaccagnini2007.Decomp481c

/-!
Split of `gamma_pair_bound481` of `Decomp481c`.

The target bounds the norm of `gammaPair481 s t n` by `π * n` for `s, t` with real parts in
`[1/2, 1]` and `1 ≤ n`. `gammaPair481` is a product of two independent factors,

`gammaPair481 s t n = (Γ s * Γ t / Γ (s + t)) * (n : ℂ) ^ (s + t - 1)`,

so the norm is the product of the two factor norms and the two are estimated separately.

The first factor is the Beta quotient. The Beta integral is the modulus-majorant of the Gamma
quotient: replacing each exponent `s`, `t` by its real part can only enlarge the integral of the
modulus, and at real parts at least one half the Beta integral is largest at the smallest
parameters, where it equals `π`. Hence the quotient is at most `π` in this strip.

The second factor is a complex power of a positive integer base. Its norm is the real power
`n ^ ((s + t).re - 1)`, and since `(s + t).re ≤ 2` the exponent is at most `1`, while the base is
at least `1`, so that power is at most `n`.

`gamma_pair_bound481_split` below is proved from the five leaves with no `sorry`, and does not use
`gamma_pair_bound481`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

section beta_helpers

open MeasureTheory

private lemma lpz_norm_cpow_factor (u : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (u - 1)‖ = x ^ (u.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

private lemma lpz_integrand_norm (u v : ℂ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ =
      x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
  have h2 : ‖(1 - (x : ℂ)) ^ (v - 1)‖ = (1 - x) ^ (v.re - 1) := by
    have hc : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    exact lpz_norm_cpow_factor v (by linarith)
  rw [norm_mul, lpz_norm_cpow_factor u hx0, h2]

private lemma lpz_ae_ne_one : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 1 := by
  have h : (volume : Measure ℝ) ({1} : Set ℝ) = 0 := by simp
  exact MeasureTheory.ae_iff.mpr (by simp)

/-- The norm of the Beta integral is at most the integral of the modulus, and the modulus of the
integrand is exactly the real Beta integrand of the real parts. -/
private lemma lpz_beta_norm_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ ∫ x in (0 : ℝ)..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
  rw [Complex.betaIntegral]
  refine (intervalIntegral.norm_integral_le_integral_norm
    (f := fun x : ℝ => (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1))
    (a := 0) (b := 1) zero_le_one).trans_eq ?_
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [lpz_ae_ne_one] with x hx1 hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact lpz_integrand_norm u v hx.1 (lt_of_le_of_ne hx.2 hx1)

/-- For real parameters of positive real part the Beta integral is a nonnegative real number, and
its modulus is the real Beta integral. -/
private lemma lpz_beta_norm_eq (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) :
    ‖Complex.betaIntegral (a : ℂ) (b : ℂ)‖ =
      ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  have hcongr : (∫ x in (0 : ℝ)..1, (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1))
      = ∫ x in (0 : ℝ)..1, ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [lpz_ae_ne_one] with x hx1 hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : 0 < x := hx.1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have e1 : (x : ℂ) ^ ((a : ℂ) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) := by
      have he : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [he, ← Complex.ofReal_cpow hx0.le]
    have e2 : (1 - (x : ℂ)) ^ ((b : ℂ) - 1) = (((1 - x) ^ (b - 1) : ℝ) : ℂ) := by
      have hc : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
      have he : (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, he, ← Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - x)]
    rw [e1, e2, ← Complex.ofReal_mul]
  rw [Complex.betaIntegral, hcongr, intervalIntegral.integral_ofReal]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  refine intervalIntegral.integral_nonneg zero_le_one ?_
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (by linarith [hx.2]) _)

/-- The real Beta integrand of positive parameters is interval integrable on `[0,1]`. -/
private lemma lpz_intervalIntegrable_beta (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 := by
  have hc : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) volume 0 1 :=
    Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
      (by simpa using ha) (by simpa using hb)
  have hnorm : IntervalIntegrable
      (fun x : ℝ => ‖(x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)‖) volume 0 1 :=
    intervalIntegrable_iff.mpr hc.def'.norm
  refine hnorm.congr_ae ?_
  filter_upwards [lpz_ae_ne_one.filter_mono ae_restrict_le,
    self_mem_ae_restrict measurableSet_uIoc] with x hx1 hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact lpz_integrand_norm _ _ hx.1 (lt_of_le_of_ne hx.2 hx1)

/-- The symmetric Beta integral at one half is `π`. -/
private lemma lpz_beta_half : Complex.betaIntegral ((1 / 2 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ) =
    (Real.pi : ℂ) := by
  have hg : Complex.Gamma ((1 / 2 : ℝ) : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Complex.Gamma_ofReal, Real.Gamma_one_half_eq]
  have hsum : ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num), hsum, hg,
    Complex.Gamma_one, div_one, ← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]

end beta_helpers

/-- LEAF. First step: identify the modulus of the Gamma quotient with the modulus of the Beta
integral. In the strip of the target both real parts are positive, so the Beta integral exists and
the Gamma factors multiply to `Γ (s + t)` times it; dividing by the nonvanishing `Γ (s + t)` gives
the identity of norms. This is the reduction step, an identity and not an estimate. -/
theorem gamma_ratio_norm_eq_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ =
      ‖Complex.betaIntegral s t‖ := by
  rw [← Complex.betaIntegral_eq_Gamma_mul_div s t (by linarith) (by linarith)]

/-- LEAF. Second step: the Beta integral of the complex pair is dominated by the Beta integral of
its real parts. The integrand of the real-part Beta integral is the pointwise modulus of the
integrand of the complex one, so the norm of the integral is at most the integral of the modulus,
which is the real-part Beta integral. -/
theorem beta_norm_le_re_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.betaIntegral s t‖ ≤ ‖Complex.betaIntegral (s.re : ℂ) (t.re : ℂ)‖ := by
  have h1 := lpz_beta_norm_le s t
  have h2 := lpz_beta_norm_eq s.re t.re (by linarith) (by linarith)
  rw [h2]
  exact h1

/-- LEAF. Third step: the real-parameter Beta integral is at most `π` once both parameters are at
least one half. On `(0, 1)` the integrand decreases in each parameter, so the integral is largest at
the pair `(1/2, 1/2)`, where it equals the square of `Γ (1/2)` divided by `Γ 1`, that is `π`. -/
theorem beta_real_half_le_pi481 {a b : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    ‖Complex.betaIntegral (a : ℂ) (b : ℂ)‖ ≤ Real.pi := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [lpz_beta_norm_eq a b ha0 hb0]
  have hstep : (∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1))
      ≤ ∫ x in (0 : ℝ)..1, x ^ ((1 / 2 : ℝ) - 1) * (1 - x) ^ ((1 / 2 : ℝ) - 1) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo
      (f := fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
      (g := fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) * (1 - x) ^ ((1 / 2 : ℝ) - 1))
      (a := 0) (b := 1) zero_le_one (lpz_intervalIntegrable_beta a b ha0 hb0)
      (lpz_intervalIntegrable_beta _ _ (by norm_num) (by norm_num)) ?_
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have h1 : x ^ (a - 1) ≤ x ^ ((1 / 2 : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith)
    have h2 : (1 - x) ^ (b - 1) ≤ (1 - x) ^ ((1 / 2 : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hx0.le _)
  refine hstep.trans ?_
  rw [← lpz_beta_norm_eq (1 / 2) (1 / 2) (by norm_num) (by norm_num), lpz_beta_half]
  rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- LEAF. Fourth step: the norm of the power factor is the real power at the real part of the
exponent. The base is the positive integer `n`, so the norm of `n ^ w` is `n ^ w.re`. -/
theorem cpow_norm_eq481 {s t : ℂ} {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (s + t - 1)‖ = (n : ℝ) ^ ((s + t).re - 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : (s + t - (1 : ℂ)).re = (s + t).re - 1 := by simp
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0, hre]

/-- LEAF. Fifth step: a real power of a base at least one is at most the base itself when the
exponent is at most one. Here `σ = (s + t).re` is at most two, so the exponent `σ - 1` is at most
one, and the base `n` is at least one. -/
theorem rpow_sub_one_le_self481 {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : σ ≤ 2) :
    (n : ℝ) ^ (σ - 1) ≤ (n : ℝ) := by
  refine Real.rpow_le_self_of_one_le ?_ ?_
  · exact_mod_cast hn
  · linarith

/-- The target of `Decomp481c`, proved from the leaves above with no `sorry`: the Gamma quotient is
at most `π`, the power factor is at most `n`, and both are nonnegative, so their product is at most
`π * n`. -/
theorem gamma_pair_bound481_split {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re)
    (hs1 : s.re ≤ 1) (ht1 : t.re ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖gammaPair481 s t n‖ ≤ Real.pi * n := by
  have hA : ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ ≤ Real.pi := by
    rw [gamma_ratio_norm_eq_beta481 hs0 ht0]
    exact (beta_norm_le_re_beta481 hs0 ht0).trans (beta_real_half_le_pi481 hs0 ht0)
  have hB : ‖(n : ℂ) ^ (s + t - 1)‖ ≤ (n : ℝ) := by
    rw [cpow_norm_eq481 (s := s) (t := t) hn]
    refine rpow_sub_one_le_self481 hn ?_
    have hst : (s + t).re = s.re + t.re := Complex.add_re s t
    linarith
  rw [gammaPair481, norm_mul]
  exact mul_le_mul hA hB (norm_nonneg _) Real.pi_pos.le

#print axioms LeanLab.LPZ2007.gamma_pair_bound481_split

end

end LeanLab.LPZ2007
