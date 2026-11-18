import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
The reduction of the explicit formula on P0045 pages 5 and 6.
The odd radical argument is kept separate from the analytic family selection.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- LEAF. P0045 page 5, multiplicity sentence before Lemma 4.1.
Group an indexed zero family by its actual character and zero value.
The occurrence bound controls its length by the sum of analytic multiplicities. -/
theorem indexed_zero_count481 {K : ℕ}
    (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (hmult : ∀ w, (univ.filter (fun i => z i = w)).card ≤
      analyticOrderNatAt (Lfun481 w.2.1) w.2.2) :
    (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ) := by
  exact_mod_cast (show K ≤ ∑ w ∈ univ.image z, analyticOrderNatAt (Lfun481 w.2.1) w.2.2 from by
    simpa only [← card_eq_sum_card_image z univ, card_univ, Fintype.card_fin] using
      (sum_le_sum fun w (_ : w ∈ univ.image z) => hmult w))

/-! Helpers for `gamma_pair_bound481`. These are the proved steps of
`SPLIT_gamma_pair_bound481`, repeated here as private lemmas because that file imports this one.
Mathlib inputs: `Complex.betaIntegral_eq_Gamma_mul_div`, `Complex.betaIntegral_convergent`,
`Real.Gamma_one_half_eq`. -/

section gamma_pair_helpers

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


/-- First step: identify the modulus of the Gamma quotient with the modulus of the Beta
integral. In the strip of the target both real parts are positive, so the Beta integral exists and
the Gamma factors multiply to `Γ (s + t)` times it; dividing by the nonvanishing `Γ (s + t)` gives
the identity of norms. This is the reduction step, an identity and not an estimate. -/
private theorem lpz_gamma_ratio_norm_eq_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ =
      ‖Complex.betaIntegral s t‖ := by
  rw [← Complex.betaIntegral_eq_Gamma_mul_div s t (by linarith) (by linarith)]

/-- Second step: the Beta integral of the complex pair is dominated by the Beta integral of
its real parts. The integrand of the real-part Beta integral is the pointwise modulus of the
integrand of the complex one, so the norm of the integral is at most the integral of the modulus,
which is the real-part Beta integral. -/
private theorem lpz_beta_norm_le_re_beta481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re) :
    ‖Complex.betaIntegral s t‖ ≤ ‖Complex.betaIntegral (s.re : ℂ) (t.re : ℂ)‖ := by
  have h1 := lpz_beta_norm_le s t
  have h2 := lpz_beta_norm_eq s.re t.re (by linarith) (by linarith)
  rw [h2]
  exact h1

/-- Third step: the real-parameter Beta integral is at most `π` once both parameters are at
least one half. On `(0, 1)` the integrand decreases in each parameter, so the integral is largest at
the pair `(1/2, 1/2)`, where it equals the square of `Γ (1/2)` divided by `Γ 1`, that is `π`. -/
private theorem lpz_beta_real_half_le_pi481 {a b : ℝ}
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

/-- Fourth step: the norm of the power factor is the real power at the real part of the
exponent. The base is the positive integer `n`, so the norm of `n ^ w` is `n ^ w.re`. -/
private theorem lpz_cpow_norm_eq481 {s t : ℂ} {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (s + t - 1)‖ = (n : ℝ) ^ ((s + t).re - 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : (s + t - (1 : ℂ)).re = (s + t).re - 1 := by simp
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0, hre]

/-- Fifth step: a real power of a base at least one is at most the base itself when the
exponent is at most one. Here `σ = (s + t).re` is at most two, so the exponent `σ - 1` is at most
one, and the base `n` is at least one. -/
private theorem lpz_rpow_sub_one_le_self481 {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : σ ≤ 2) :
    (n : ℝ) ^ (σ - 1) ≤ (n : ℝ) := by
  refine Real.rpow_le_self_of_one_le ?_ ?_
  · exact_mod_cast hn
  · linarith

end gamma_pair_helpers

/-- LEAF. PROVED. P0045 page 5, Gamma pair in Lemma 4.1.
The beta integral bounds the Gamma quotient by pi in this strip.
The power of positive n is then bounded by n. This is a derived summand estimate. -/
theorem gamma_pair_bound481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re)
    (hs1 : s.re ≤ 1) (ht1 : t.re ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖gammaPair481 s t n‖ ≤ Real.pi * n := by
  have hA : ‖Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)‖ ≤ Real.pi := by
    rw [lpz_gamma_ratio_norm_eq_beta481 hs0 ht0]
    exact (lpz_beta_norm_le_re_beta481 hs0 ht0).trans (lpz_beta_real_half_le_pi481 hs0 ht0)
  have hB : ‖(n : ℂ) ^ (s + t - 1)‖ ≤ (n : ℝ) := by
    rw [lpz_cpow_norm_eq481 (s := s) (t := t) hn]
    refine lpz_rpow_sub_one_le_self481 hn ?_
    have hst : (s + t).re = s.re + t.re := Complex.add_re s t
    linarith
  rw [gammaPair481, norm_mul]
  exact mul_le_mul hA hB (norm_nonneg _) Real.pi_pos.le

/-- LEAF. OPEN. P0045 page 6, paragraph before Corollary 4.2 and display 9.
Choose H and T large, then epsilon small. Separate the pole pair in Lemma 4.1,
bound the other Gamma pairs and absorb the remainder using n in J and Sing n bounded below.
Jutila controls the indexed family with multiplicity. This leaf does not assert display 10. -/
theorem explicit_formula_reduction481
    (hexp : Lemma41Statement481) (hdensity : JutilaStatement481)
    (hcount : ∀ {K : ℕ} (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ w, (univ.filter (fun i => z i = w)).card ≤
        analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
      (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ))
    (hgamma : ∀ {s t : ℂ}, (1 / 2 : ℝ) ≤ s.re → (1 / 2 : ℝ) ≤ t.re →
      s.re ≤ 1 → t.re ≤ 1 → ∀ {n : ℕ}, 1 ≤ n →
        ‖gammaPair481 s t n‖ ≤ Real.pi * n)
    (η : ℝ) (hη : 0 < η) :
    ∃ (K₁ Cstar : ℕ) (A H T : ℝ), 0 < Cstar ∧ 0 ≤ A ∧ 1 ≤ H ∧ 1 ≤ T ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ E.card ≤ K₁ ∧
          (∀ r ∈ E, ∃ z ∈ zeroBox481 X H T P, z.1 = r) ∧
          (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
            |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
          (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  sorry

/-- P0045 page 6, display 10: combine the real and nonreal character cases.
The conclusion remains conditional on the explicit classification and zero region inputs. -/
theorem exceptional_radical481 (hclass : RealPrimitiveStatement481)
    (hzero : RealZeroStatement481) (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨cr, hcr, Xr, hr⟩ := real_exceptional_conductor481 hzero H T hH hT
  obtain ⟨cn, hcn, Xn, hn⟩ := nonreal_exceptional_radical481 hiw H T hH hT
  refine ⟨min (cr / 8) cn, lt_min (by positivity) hcn, max Xr Xn, ?_⟩
  intro X hX P hP z hz
  by_cases hreal : ∀ a, (z.2.1 a).im = 0
  · have hbound := real_radical_transfer481 (hclass _ hz.1 _ hz.2.2.1 hreal)
      (hr X ((le_max_left _ _).trans hX) P hP z hz hreal)
    have hm := mul_le_mul_of_nonneg_right (min_le_left (cr / 8) cn) (sq_nonneg (Lg X))
    nlinarith
  · exact (mul_le_mul_of_nonneg_right (min_le_right (cr / 8) cn)
      (sq_nonneg (Lg X))).trans
        (hn X ((le_max_right _ _).trans hX) P hP z hz (by simpa using hreal))

end
end LeanLab.LPZ2007
