/-
Hardy-Littlewood 1923, unit DecompJ1131: a non-real zero of the Riemann zeta function
exists.

Proof route (nothing cited; the one added import carries a sorry-free closure, see the
note at the end of this header): let `L(s) = pi^(-s/2) Gamma(s/2) zeta(s)` be the
completed zeta function and `xi(s) = s (s-1) L0(s)/2 + 1/2` the completed function with
the poles at `0` and `1` removed, so that `xi 0 = xi 1 = 1/2`, `xi(1-s) = xi(s)` and
`xi 2 = pi/6`. If every zero of `zeta` were real then `xi` would have no zero: away from
`0` and `1` its zeros are the zeros of `L = GammaR * zeta`; `GammaR` vanishes only at the
non-positive even integers, where `zeta` has its trivial zero, so a hypothetical zero of
`xi` there would be a zero of `zeta` at a point `z` with `z.re <= 0`, and `xi(z) = xi(1-z)`
with `(1-z).re > 1`, where `xi` does not vanish; and the real zeros of `zeta` are absent
on `(0,1)` (the lab's alternating-series sign result `riemannZeta_real_neg`), absent on
`(1,inf)` (Mathlib's `riemannZeta_ne_zero_of_one_le_re`) and, below `0`, reflected to
`1-s > 1`. A zero-free entire function whose logarithm grows faster than linearly but
like `C (1+|z|)^(3/2)` is the exponential of an affine map
(`exp_affine_of_order_two`: Borel-Caratheodory plus Cauchy's estimates kill every
Taylor coefficient of order at least `2` of the logarithm); the functional equation then
forces the linear part to vanish, so `xi` is constant, contradicting
`xi 0 = 1/2 != pi/6 = xi 2`.

Import note: `LeanLab.PNTPort.DirichletZF.SiegelSigns` is used only for the sign of
`zeta` on `(0,1)`. Its whole import closure (33 modules) contains no `sorry`, does not
reach this file, and its own `lake build` replays cleanly.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import LeanLab.PNTPort.DirichletZF.SiegelSigns

namespace LeanLab.HardyLittlewood1923.DecompJ1131

open Complex

/-- **A zero-free entire function of order `< 2` is the exponential of an affine map.**

This is the classical Hadamard step for genus `≤ 1`, proved with no factorisation
theory: Borel-Caratheodory bounds `φ` on discs, and Cauchy's estimates then show that
every Taylor coefficient of the logarithm of order at least `2` vanishes. -/
private theorem exp_affine_of_order_two {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0)
    (hgr : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, Real.log ‖f z‖ ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ) + C) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a + b * z) := by
  obtain ⟨C, hC0, hCz⟩ := hgr
  -- the logarithmic derivative is entire, so it has a primitive vanishing at `0`
  have hderiv : Differentiable ℂ (fun z => deriv f z) := by fun_prop
  have hF : Differentiable ℂ (fun z => deriv f z / f z) := hderiv.div hf hne
  obtain ⟨φ, hφ0, hφ⟩ := hF.isExactOn_univ.with_val_at (0 : ℂ) (0 : ℂ)
  have hφd : Differentiable ℂ φ := fun z => (hφ z (Set.mem_univ z)).differentiableAt
  have hφ' : ∀ z, HasDerivAt φ (deriv f z / f z) z := fun z => hφ z (Set.mem_univ z)
  -- the logarithmic derivative of `f * exp (-φ)` vanishes
  have hg : ∀ z, HasDerivAt (fun w => f w * Complex.exp (-(φ w))) 0 z := by
    intro z
    have h1 : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
    have h3 : HasDerivAt (fun w => -(φ w)) (-(deriv f z / f z)) z := (hφ' z).neg
    have h2 : HasDerivAt (fun w => Complex.exp (-(φ w)))
        (Complex.exp (-(φ z)) * (-(deriv f z / f z))) z :=
      (Complex.hasDerivAt_exp (-(φ z))).comp z h3
    have h4 := h1.mul h2
    convert h4 using 1
    have hfz : f z ≠ 0 := hne z
    field_simp
    ring
  -- hence `f z = f 0 * exp (φ z)`
  have hfeq : ∀ z, f z = f 0 * Complex.exp (φ z) := by
    intro z
    have h0 : f 0 * Complex.exp (-(φ 0)) = f 0 := by rw [hφ0]; simp
    have hconst := is_const_of_deriv_eq_zero (𝕜 := ℂ)
      (f := fun w => f w * Complex.exp (-(φ w)))
      (fun w => (hg w).differentiableAt) (fun w => (hg w).deriv) z 0
    rw [h0] at hconst
    have h2 : f z * Complex.exp (-(φ z)) * Complex.exp (φ z) = f 0 * Complex.exp (φ z) := by
      rw [hconst]
    rwa [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] at h2
  -- the real part of `φ` inherits the growth bound
  have hf0 : (0 : ℝ) < ‖f 0‖ := norm_pos_iff.mpr (hne 0)
  have hf0ne : ‖f 0‖ ≠ 0 := hf0.ne'
  have hre : ∀ z, (φ z).re ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ) + (C - Real.log ‖f 0‖) := by
    intro z
    have hnorm : ‖f z‖ = ‖f 0‖ * Real.exp ((φ z).re) := by
      rw [hfeq z, norm_mul, Complex.norm_exp]
    have hlog : Real.log ‖f z‖ = Real.log ‖f 0‖ + (φ z).re := by
      rw [hnorm, Real.log_mul hf0ne (Real.exp_ne_zero _), Real.log_exp]
    have := hCz z
    linarith
  set K : ℝ := |C - Real.log ‖f 0‖| + 1 with hKdef
  have hKpos : 0 < K := by positivity
  have hCsub : C - Real.log ‖f 0‖ ≤ K := by
    have h1 : C - Real.log ‖f 0‖ ≤ |C - Real.log ‖f 0‖| := le_abs_self _
    linarith
  -- Borel-Caratheodory on the ball of radius `R`
  have hBC : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ < R →
      ‖φ z‖ ≤ 2 * (C * (1 + R) ^ (3 / 2 : ℝ) + K) * ‖z‖ / (R - ‖z‖) := by
    intro R hR z hz
    have hMpos : 0 < C * (1 + R) ^ (3 / 2 : ℝ) + K := by
      have h1 : 0 ≤ C * (1 + R) ^ (3 / 2 : ℝ) := by positivity
      linarith
    have hmap : Set.MapsTo φ (Metric.ball 0 R) {z | z.re ≤ C * (1 + R) ^ (3 / 2 : ℝ) + K} := by
      intro w hw
      simp only [Set.mem_setOf_eq]
      have hw' : ‖w‖ < R := by simpa using hw
      have hmono : (1 + ‖w‖) ^ (3 / 2 : ℝ) ≤ (1 + R) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have hC' : C * (1 + ‖w‖) ^ (3 / 2 : ℝ) ≤ C * (1 + R) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hmono hC0
      have := hre w
      linarith
    have h := Complex.borelCaratheodory hMpos hφd.differentiableOn hmap hR
      (by simpa using hz)
    rw [hφ0, norm_zero, zero_mul, zero_div, add_zero] at h
    exact h
  -- the bound is monotone in `r`, so Cauchy's estimate applies at every radius
  have hCauchy : ∀ n : ℕ, ∀ r : ℝ, 0 < r →
      ‖iteratedDeriv n φ 0‖ ≤
        n.factorial * (2 * (C * (1 + 2 * r) ^ (3 / 2 : ℝ) + K)) / r ^ n := by
    intro n r hr0
    have hsup : ∀ z ∈ Metric.sphere (0 : ℂ) r,
        ‖φ z‖ ≤ 2 * (C * (1 + 2 * r) ^ (3 / 2 : ℝ) + K) := by
      intro z hz
      have hzr : ‖z‖ = r := by simpa using hz
      have h := hBC (2 * r) (by linarith) z (by rw [hzr]; linarith)
      rw [hzr] at h
      have he : 2 * (C * (1 + 2 * r) ^ (3 / 2 : ℝ) + K) * r / (2 * r - r) =
          2 * (C * (1 + 2 * r) ^ (3 / 2 : ℝ) + K) := by
        field_simp
        norm_num
      linarith [he ▸ h]
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr0
      hφd.diffContOnCl hsup
    simpa using this
  -- every Taylor coefficient of `φ` at `0` of order `≥ 2` vanishes
  have hrpow1 : Filter.Tendsto (fun r : ℝ => r ^ (-(1 / 2) : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hrpow2 : Filter.Tendsto (fun r : ℝ => r ^ (-(2 : ℝ))) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hzero : ∀ n : ℕ, 2 ≤ n → iteratedDeriv n φ 0 = 0 := by
    intro n hn
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    have key : ∀ r : ℝ, 1 ≤ r →
        ‖iteratedDeriv n φ 0‖ ≤
          ((n.factorial : ℝ) * 2 * C * 3 ^ (3 / 2 : ℝ)) * r ^ (-(1 / 2) : ℝ) +
            ((n.factorial : ℝ) * 2 * K) * r ^ (-(2 : ℝ)) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
      have hCa := hCauchy n r hr0
      refine hCa.trans ?_
      have h3 : (1 + 2 * r) ^ (3 / 2 : ℝ) ≤ 3 ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) := by
        have h13 : 1 + 2 * r ≤ 3 * r := by linarith
        calc (1 + 2 * r) ^ (3 / 2 : ℝ) ≤ (3 * r) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow (by positivity) h13 (by norm_num)
          _ = 3 ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hr0.le
      have hnum : 2 * (C * (1 + 2 * r) ^ (3 / 2 : ℝ) + K) ≤
          2 * (C * (3 ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) + K) := by
        have := mul_le_mul_of_nonneg_left h3 hC0
        linarith
      have hrn : (0 : ℝ) < r ^ n := pow_pos hr0 n
      have hdiv : (n.factorial : ℝ) * (2 * (C * (1 + 2 * r) ^ (3 / 2 : ℝ) + K)) / r ^ n ≤
          (n.factorial : ℝ) * (2 * (C * (3 ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) + K)) / r ^ n := by
        apply div_le_div_of_nonneg_right _ hrn.le
        exact mul_le_mul_of_nonneg_left hnum (by positivity)
      refine hdiv.trans ?_
      have hsplit : (n.factorial : ℝ) * (2 * (C * (3 ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) + K)) / r ^ n =
          ((n.factorial : ℝ) * 2 * C * 3 ^ (3 / 2 : ℝ)) * (r ^ (3 / 2 : ℝ) / r ^ n) +
            ((n.factorial : ℝ) * 2 * K) * (1 / r ^ n) := by
        field_simp
      rw [hsplit]
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have he1 : r ^ (3 / 2 : ℝ) / r ^ n ≤ r ^ (-(1 / 2) : ℝ) := by
        rw [show r ^ n = r ^ (n : ℝ) from (Real.rpow_natCast r n).symm,
          ← Real.rpow_sub hr0 (3 / 2 : ℝ) (n : ℝ)]
        apply Real.rpow_le_rpow_of_exponent_le hr
        push_cast
        linarith
      have he2 : 1 / r ^ n ≤ r ^ (-(2 : ℝ)) := by
        rw [one_div, show r ^ n = r ^ (n : ℝ) from (Real.rpow_natCast r n).symm,
          ← Real.rpow_neg hr0.le]
        apply Real.rpow_le_rpow_of_exponent_le hr
        push_cast
        linarith
      have hb1 : (0 : ℝ) ≤ (n.factorial : ℝ) * 2 * C * 3 ^ (3 / 2 : ℝ) := by positivity
      have hb2 : (0 : ℝ) ≤ (n.factorial : ℝ) * 2 * K := by positivity
      have g1 := mul_le_mul_of_nonneg_left he1 hb1
      have g2 := mul_le_mul_of_nonneg_left he2 hb2
      linarith
    have htend : Filter.Tendsto
        (fun r : ℝ => ((n.factorial : ℝ) * 2 * C * 3 ^ (3 / 2 : ℝ)) * r ^ (-(1 / 2) : ℝ) +
          ((n.factorial : ℝ) * 2 * K) * r ^ (-(2 : ℝ))) Filter.atTop (nhds 0) := by
      have h := (hrpow1.const_mul ((n.factorial : ℝ) * 2 * C * 3 ^ (3 / 2 : ℝ))).add
        (hrpow2.const_mul ((n.factorial : ℝ) * 2 * K))
      simpa using h
    have hneg : Filter.Tendsto
        (fun r : ℝ => -(((n.factorial : ℝ) * 2 * C * 3 ^ (3 / 2 : ℝ)) * r ^ (-(1 / 2) : ℝ) +
          ((n.factorial : ℝ) * 2 * K) * r ^ (-(2 : ℝ)))) Filter.atTop (nhds 0) := by
      simpa using htend.neg
    have hle : (0 : ℝ) ≤ -(‖iteratedDeriv n φ 0‖) := by
      refine le_of_tendsto hneg (Filter.eventually_atTop.mpr ⟨1, fun r hr => ?_⟩)
      have h1 := key r hr
      linarith
    linarith
  -- Taylor's formula then makes `φ` linear
  have hφlin : ∀ z : ℂ, φ z = deriv φ 0 * z := by
    intro z
    have htl := Complex.taylorSeries_eq_of_entire' hφd (c := (0 : ℂ)) (z := z)
    rw [tsum_eq_single (1 : ℕ) ?_] at htl
    · simpa using htl.symm
    · intro k hk
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · simp [iteratedDeriv_zero, hφ0]
        · exact absurd rfl hk
      · rw [hzero k hk2]
        simp
  refine ⟨Complex.log (f 0), deriv φ 0, fun z => ?_⟩
  rw [hfeq z, hφlin z, Complex.exp_add, Complex.exp_log (hne 0)]

/-- ζ is real and negative on the real segment `(0,1)`. -/
private theorem zeta_real_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta (σ : ℂ)).im = 0 ∧ (riemannZeta (σ : ℂ)).re < 0 :=
  LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg h0 h1

/-- The completed zeta function `xi s = s(s-1) Λ₀(s)/2 + 1/2`; it equals the classical
`s(s-1)Λ(s)/2` away from `0` and `1`, so it is entire with the poles removed. -/
private theorem xi_differentiable :
    Differentiable ℂ (fun z : ℂ => z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2) := by
  have h : Differentiable ℂ fun z : ℂ => z * (z - 1) * completedRiemannZeta₀ z / 2 :=
    (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
      differentiable_completedZeta₀).div_const 2)
  exact h.add_const (1 / 2)

/-- The functional equation of the completed zeta function. -/
private theorem xi_one_sub (z : ℂ) :
    (1 - z) * ((1 - z) - 1) * completedRiemannZeta₀ (1 - z) / 2 + 1 / 2 =
      z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2 := by
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- `Λ = Γℝ * ζ` at points where `Γℝ` does not vanish. -/
private theorem completedRiemannZeta_eq_mul {s : ℂ} (hs : s ≠ 0) (h : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

private theorem gammaR_two : Gammaℝ (2 : ℂ) = (Real.pi : ℂ)⁻¹ := by
  rw [Gammaℝ_def, show ((2 : ℂ) / 2) = 1 by norm_num, Complex.Gamma_one]
  rw [show (-(2 : ℂ) / 2) = -1 by ring, Complex.cpow_neg_one]
  simp

/-- `xi 2 = π/6`. -/
private theorem xi_two :
    (2 : ℂ) * (2 - 1) * completedRiemannZeta₀ 2 / 2 + 1 / 2 = (Real.pi : ℂ) / 6 := by
  have hG : Gammaℝ (2 : ℂ) ≠ 0 := by
    rw [gammaR_two]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h : completedRiemannZeta₀ 2 + 1 / 2 = completedRiemannZeta 2 := by
    rw [completedRiemannZeta_eq]
    ring
  rw [show (2 : ℂ) * (2 - 1) * completedRiemannZeta₀ 2 / 2 + 1 / 2 =
      completedRiemannZeta₀ 2 + 1 / 2 by ring, h,
    completedRiemannZeta_eq_mul (by norm_num) hG, riemannZeta_two, gammaR_two]
  field_simp



/-! ## 1. Growth of `Γ` -/

/-- Euler's integral gives `‖Γ w‖ ≤ Γ (re w)` on the right half-plane. -/
private theorem norm_Gamma_le_Gamma_re {w : ℂ} (h : 0 < w.re) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral h, Complex.GammaIntegral, Real.Gamma_eq_integral h]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp

private lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hfac : ((Nat.succ m).factorial : ℝ) = (m.factorial : ℝ) * ((m : ℝ) + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hm0 : (0 : ℝ) < (m.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos m
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [hfac, Real.log_mul hm0.ne' hm1.ne']
    have hcast : ((Nat.succ m : ℕ) : ℝ) = (m : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    have hstep : (m : ℝ) * Real.log (m : ℝ) ≤ (m : ℝ) * Real.log ((m : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        simp
      · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h
        exact mul_le_mul_of_nonneg_left (Real.log_le_log hmpos (by linarith)) hmpos.le
    linarith [ih, hstep]

private lemma mul_log_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * Real.log a ≤ b * Real.log b := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb1 : (1 : ℝ) ≤ b := le_trans ha hab
  have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have h1 : a * Real.log a ≤ a * Real.log b := mul_le_mul_of_nonneg_left hlog ha0.le
  have h2 : a * Real.log b ≤ b * Real.log b :=
    mul_le_mul_of_nonneg_right hab (Real.log_nonneg hb1)
  linarith

private lemma log_Gamma_nat_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Real.Gamma (n : ℝ)) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hG : Real.Gamma (((k + 1 : ℕ) : ℝ)) = (k.factorial : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial k
  rw [hG]
  push_cast
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    norm_num
  · calc Real.log (k.factorial : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := log_factorial_le k
      _ ≤ ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) := by
          apply mul_log_mono
          · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
            linarith
          · linarith

private lemma log_Gamma_nat_succ_le (n : ℕ) :
    Real.log (Real.Gamma ((n : ℝ) + 1)) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  have hG : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
  rw [hG]
  exact log_factorial_le n

/-- `log Γ x ≤ (1 + x) log (1 + x)` for `x ≥ 1`, by log-convexity of `Γ`. -/
private theorem log_Gamma_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ (1 + x) * Real.log (1 + x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set n : ℕ := ⌊x⌋₊ with hn
  have hle : (n : ℝ) ≤ x := by rw [hn]; exact Nat.floor_le (by linarith)
  have hlt : x < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one x
  have hn1 : 1 ≤ n := by
    rw [hn]
    apply Nat.le_floor
    simpa using hx
  have hmem1 : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hmem2 : ((n : ℝ) + 1) ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    linarith
  have ha : (0 : ℝ) ≤ (n : ℝ) + 1 - x := by linarith
  have hb : (0 : ℝ) ≤ x - (n : ℝ) := by linarith
  have hab : ((n : ℝ) + 1 - x) + (x - (n : ℝ)) = 1 := by ring
  have hconv := Real.convexOn_log_Gamma.2 hmem1 hmem2 ha hb hab
  have hpt : ((n : ℝ) + 1 - x) * (n : ℝ) + (x - (n : ℝ)) * ((n : ℝ) + 1) = x := by ring
  simp only [Function.comp_apply, smul_eq_mul, hpt] at hconv
  have hGn : Real.log (Real.Gamma (n : ℝ)) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    log_Gamma_nat_le n hn1
  have hGm : Real.log (Real.Gamma ((n : ℝ) + 1)) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    log_Gamma_nat_succ_le n
  have h1 : ((n : ℝ) + 1 - x) * Real.log (Real.Gamma (n : ℝ)) ≤
      ((n : ℝ) + 1 - x) * ((n : ℝ) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hGn ha
  have h2 : (x - (n : ℝ)) * Real.log (Real.Gamma ((n : ℝ) + 1)) ≤
      (x - (n : ℝ)) * ((n : ℝ) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hGm hb
  have hsum : ((n : ℝ) + 1 - x) * ((n : ℝ) * Real.log (n : ℝ)) +
      (x - (n : ℝ)) * ((n : ℝ) * Real.log (n : ℝ)) = (n : ℝ) * Real.log (n : ℝ) := by
    ring
  have hnn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hfac1 : (n : ℝ) * Real.log (n : ℝ) ≤ (1 + x) * Real.log (1 + x) :=
    mul_log_mono hnn1 (by linarith)
  linarith [hconv, h1, h2, hsum, hfac1]

/-- Uniform growth bound for `log Γ` on `[1/4, ∞)`. -/
private theorem log_Gamma_le_uniform {x : ℝ} (h : 1 / 4 ≤ x) :
    Real.log (Real.Gamma x) ≤ 2 * (1 + x) ^ (3 / 2 : ℝ) + 12 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  have hmain : 0 ≤ 2 * (1 + x) ^ (3 / 2 : ℝ) := by positivity
  by_cases h1 : x ≤ 1
  · -- small range: `Γ x = Γ (x+1) / x` and `x ≥ 1/4`
    have hGx : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx0.ne'
    have hpos1 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
    have hb1 : Real.log (Real.Gamma (x + 1)) ≤ 6 := by
      have h3 : 1 + (x + 1) ≤ 3 := by linarith
      have h4 : (1 : ℝ) ≤ 1 + (x + 1) := by linarith
      have h5 : Real.log (3 : ℝ) ≤ 2 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith
      calc Real.log (Real.Gamma (x + 1))
          ≤ (1 + (x + 1)) * Real.log (1 + (x + 1)) := log_Gamma_le (by linarith)
        _ ≤ 3 * Real.log 3 := mul_log_mono h4 h3
        _ ≤ 3 * 2 := mul_le_mul_of_nonneg_left h5 (by norm_num)
        _ = 6 := by norm_num
    have hExp : Real.Gamma (x + 1) ≤ Real.exp 6 := by
      rw [← Real.exp_log hpos1]
      exact Real.exp_le_exp.mpr hb1
    have hΓx : Real.Gamma x = Real.Gamma (x + 1) / x := by
      rw [hGx]
      field_simp
    have hdiv4 : Real.Gamma x ≤ 4 * Real.Gamma (x + 1) := by
      rw [hΓx, div_le_iff₀ hx0]
      have h4x : (1 : ℝ) ≤ 4 * x := by linarith
      nlinarith [hpos1, h4x]
    have hbound : Real.Gamma x ≤ Real.exp 12 := by
      have h4e : (4 : ℝ) ≤ Real.exp 6 := by
        have := Real.add_one_le_exp 6
        linarith
      calc Real.Gamma x ≤ 4 * Real.Gamma (x + 1) := hdiv4
        _ ≤ Real.exp 6 * Real.exp 6 :=
            mul_le_mul h4e hExp (le_of_lt hpos1) (by positivity)
        _ = Real.exp 12 := by
            rw [← Real.exp_add]
            norm_num
    have hlog : Real.log (Real.Gamma x) ≤ 12 := by
      have hpos12 : 0 < Real.exp (12 : ℝ) := Real.exp_pos _
      have h := Real.log_le_log hpos hbound
      rwa [Real.log_exp] at h
    have h12 : (12 : ℝ) ≤ 2 * (1 + x) ^ (3 / 2 : ℝ) + 12 := le_add_of_nonneg_left hmain
    exact hlog.trans h12
  · push_neg at h1
    have hb : Real.log (Real.Gamma x) ≤ (1 + x) * Real.log (1 + x) := log_Gamma_le h1.le
    have hlog : Real.log (1 + x) ≤ 2 * (1 + x) ^ (1 / 2 : ℝ) := by
      have h2 : (1 : ℝ) ≤ 1 + x := by linarith
      have hs : (0 : ℝ) < Real.sqrt (1 + x) := Real.sqrt_pos.mpr (by linarith)
      have hsq : Real.sqrt (1 + x) * Real.sqrt (1 + x) = 1 + x := Real.mul_self_sqrt (by linarith)
      have hlog2 : Real.log (1 + x) = 2 * Real.log (Real.sqrt (1 + x)) := by
        conv_lhs => rw [← hsq]
        rw [← sq, Real.log_pow]
        norm_num
      rw [hlog2]
      have h3 : Real.log (Real.sqrt (1 + x)) ≤ Real.sqrt (1 + x) - 1 :=
        Real.log_le_sub_one_of_pos hs
      have hrw : ((1 + x) ^ (1 / 2 : ℝ)) = Real.sqrt (1 + x) := (Real.sqrt_eq_rpow _).symm
      rw [hrw]
      linarith
    have hstep : (1 + x) * Real.log (1 + x) ≤ (1 + x) * (2 * (1 + x) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    have hone : (1 + x) * (2 * (1 + x) ^ (1 / 2 : ℝ)) = 2 * (1 + x) ^ (3 / 2 : ℝ) := by
      conv_rhs =>
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith),
          Real.rpow_one]
      ring
    linarith [hone ▸ hstep]

/-! ## 2. Bounds for `ζ` on the half-plane `re ≥ 1/2` -/

/-- The Euler–Maclaurin (alternative) formula bounds `ζ` by
`1 + 1/|s-1| + |s|/re s` for `re s > 0`. -/
private theorem norm_zeta_le_alt {w : ℂ} (h0 : 0 < w.re) (hne : w ≠ 1) :
    ‖riemannZeta w‖ ≤ 1 + 1 / ‖w - 1‖ + ‖w‖ / w.re := by
  rw [ZetaAltFormula h0 hne]
  have hre0 : w.re ≠ 0 := h0.ne'
  have hint : ‖∫ u in Set.Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ ≤ 1 / w.re := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    have hdom : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-w.re - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (a := -w.re - 1) (c := 1) (by linarith) zero_lt_one
    have hmono : ∀ u ∈ Set.Ioi (1 : ℝ),
        ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ ≤ u ^ (-w.re - 1) := by
      intro u hu
      have hu1 : (1 : ℝ) < u := hu
      have hu0 : (0 : ℝ) < u := by linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have hfract : |Int.fract u| ≤ 1 := by
        rw [abs_of_nonneg (Int.fract_nonneg u)]
        linarith [Int.fract_lt_one u]
      have hexp : (-w - 1).re = -w.re - 1 := by simp
      rw [hexp]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hu0.le _) hfract
    have hIntNorm : MeasureTheory.IntegrableOn
        (fun u : ℝ => ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖) (Set.Ioi 1) := by
      refine hdom.mono' ?_ ?_
      · exact (((Complex.measurable_ofReal.comp measurable_fract).mul
          (Complex.measurable_ofReal.pow_const _)).norm).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hmono u hu
    calc ∫ u in Set.Ioi (1 : ℝ), ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖
        ≤ ∫ u in Set.Ioi (1 : ℝ), u ^ (-w.re - 1) :=
          MeasureTheory.setIntegral_mono_on hIntNorm hdom measurableSet_Ioi hmono
      _ = 1 / w.re := by
          rw [integral_Ioi_rpow_of_lt (a := -w.re - 1) (c := 1) (by linarith) one_pos]
          have hexp : -w.re - 1 + 1 = -w.re := by ring
          rw [hexp, Real.one_rpow]
          field_simp
  have hsplit : riemannZeta1 w =
      1 + 1 / (w - 1) - w * ∫ u in Set.Ioi (1 : ℝ),
        (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1) := rfl
  rw [hsplit]
  have hA : ‖1 + 1 / (w - 1)‖ ≤ 1 + 1 / ‖w - 1‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_div, norm_one]
  have hB : ‖w * ∫ u in Set.Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ =
      ‖w‖ * ‖∫ u in Set.Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ := norm_mul _ _
  have hC : ‖1 + 1 / (w - 1) -
      w * ∫ u in Set.Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ ≤
      1 + 1 / ‖w - 1‖ + ‖w‖ * (1 / w.re) := by
    have hsub : ‖1 + 1 / (w - 1) -
        w * ∫ u in Set.Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ ≤
        ‖1 + 1 / (w - 1)‖ +
          ‖w * ∫ u in Set.Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ :=
      norm_sub_le _ _
    have hmul : ‖w‖ *
        ‖∫ u in Set.Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-w - 1)‖ ≤ ‖w‖ * (1 / w.re) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg w)
    rw [hB] at hsub
    linarith [hsub, hA, hmul]
  have hfin : 1 + 1 / ‖w - 1‖ + ‖w‖ * (1 / w.re) = 1 + 1 / ‖w - 1‖ + ‖w‖ / w.re := by
    ring
  linarith [hC, hfin]

private theorem norm_zeta_le_of_re_ge_half {w : ℂ} (hre : 1 / 2 ≤ w.re) (hw : 3 ≤ ‖w‖) :
    ‖riemannZeta w‖ ≤ 3 + 2 * ‖w‖ := by
  have h0 : 0 < w.re := by linarith
  have hne : w ≠ 1 := by
    intro h
    rw [h] at hw
    simp only [norm_one] at hw
    linarith
  have h := norm_zeta_le_alt h0 hne
  have hw1 : (1 : ℝ) ≤ ‖w - 1‖ := by
    have h1 : ‖w‖ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := by
      have h2 := norm_add_le (w - 1) (1 : ℂ)
      have h3 : w - 1 + 1 = w := by ring
      rw [h3] at h2
      simpa using h2
    simp only [norm_one] at h1
    linarith
  have hinv : 1 / ‖w - 1‖ ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h2 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    rw [div_le_iff₀ h0]
    nlinarith [norm_nonneg w]
  linarith

/-! ## 3. Growth of the completed zeta function, and the growth hypothesis for `xi` -/

private theorem gammaR_ne_zero_of_half_le_re {w : ℂ} (h : 1 / 2 ≤ w.re) : Complex.Gammaℝ w ≠ 0 := by
  intro hz
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hz
  have hre := congrArg Complex.re hn
  simp at hre
  linarith

private theorem norm_Gammaℝ_le {w : ℂ} (hre : 1 / 2 ≤ w.re) :
    ‖Complex.Gammaℝ w‖ ≤ Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 12) := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hexp : (-w / 2).re = -w.re / 2 := by simp
  rw [hexp]
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpi2 : Real.pi ^ (-w.re / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hpi1 (by linarith)
  have hw2 : (0 : ℝ) < (w / 2).re := by
    have hhalf : (w / 2).re = w.re / 2 := by simp
    rw [hhalf]
    linarith
  have hΓ : ‖Complex.Gamma (w / 2)‖ ≤ Real.Gamma (w.re / 2) := by
    have h := norm_Gamma_le_Gamma_re hw2
    simpa using h
  have hΓ2 : Real.Gamma (w.re / 2) ≤ Real.exp (2 * (1 + w.re / 2) ^ (3 / 2 : ℝ) + 12) := by
    rw [← Real.exp_log (Real.Gamma_pos_of_pos (by linarith))]
    exact Real.exp_le_exp.mpr (log_Gamma_le_uniform (by linarith))
  have hmono : (1 + w.re / 2) ^ (3 / 2 : ℝ) ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (x := 1 + w.re / 2) (y := 1 + ‖w‖) (z := 3 / 2)
      (by linarith) (by nlinarith [Complex.re_le_norm w]) (by norm_num)
  have hstep : Real.exp (2 * (1 + w.re / 2) ^ (3 / 2 : ℝ) + 12) ≤
      Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 12) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  calc Real.pi ^ (-w.re / 2) * ‖Complex.Gamma (w / 2)‖
      ≤ 1 * Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 12) :=
        mul_le_mul hpi2 (hΓ.trans (hΓ2.trans hstep)) (norm_nonneg _) (by norm_num)
    _ = Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 12) := one_mul _

private theorem norm_completedRiemannZeta_le {w : ℂ} (hre : 1 / 2 ≤ w.re) (hw : 3 ≤ ‖w‖) :
    ‖completedRiemannZeta w‖ ≤ Real.exp (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  rw [completedRiemannZeta_eq_mul hw0 (gammaR_ne_zero_of_half_le_re hre), norm_mul]
  have hζ := norm_zeta_le_of_re_ge_half hre hw
  have hΓ := norm_Gammaℝ_le (w := w) hre
  have hpoly : 3 + 2 * ‖w‖ ≤ Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ)) := by
    have h2 : (2 + 2 * ‖w‖) + 1 ≤ Real.exp (2 + 2 * ‖w‖) := Real.add_one_le_exp _
    have honep : (1 : ℝ) + ‖w‖ ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) := by
      calc (1 : ℝ) + ‖w‖ = (1 + ‖w‖) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le
              (by linarith [norm_nonneg w] : (1 : ℝ) ≤ 1 + ‖w‖) (by norm_num)
    have h3 : 2 + 2 * ‖w‖ ≤ 2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) := by linarith
    linarith [Real.exp_le_exp.mpr h3]
  have hfirst : ‖riemannZeta w‖ * ‖Complex.Gammaℝ w‖ ≤
      (3 + 2 * ‖w‖) * Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 12) :=
    mul_le_mul hζ hΓ (norm_nonneg _) (by positivity)
  have hsecond : (3 + 2 * ‖w‖) * Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 12) ≤
      Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ)) *
        Real.exp (2 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 12) :=
    mul_le_mul_of_nonneg_right hpoly (by positivity)
  refine hfirst.trans (hsecond.trans ?_)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  linarith

private theorem norm_completedRiemannZeta₀_le {w : ℂ} (hre : 1 / 2 ≤ w.re) (hw : 3 ≤ ‖w‖) :
    ‖completedRiemannZeta₀ w‖ ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by
  have hEq : completedRiemannZeta₀ w = completedRiemannZeta w + 1 / w + 1 / (1 - w) := by
    rw [completedRiemannZeta_eq]
    ring
  have hb1 : ‖1 / w‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  have hb2 : ‖1 / (1 - w)‖ ≤ 1 := by
    have h1w : (2 : ℝ) ≤ ‖1 - w‖ := by
      have h2 : ‖w‖ ≤ ‖w - 1‖ + 1 := by
        have h3 := norm_add_le (w - 1) (1 : ℂ)
        have h4 : w - 1 + 1 = w := by ring
        rw [h4] at h3
        simpa using h3
      have h5 : ‖1 - w‖ = ‖w - 1‖ := by
        rw [show (1 : ℂ) - w = -(w - 1) by ring, norm_neg]
      rw [h5]
      linarith
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  rw [hEq]
  have hΛ := norm_completedRiemannZeta_le hre hw
  have htri : ‖completedRiemannZeta w + 1 / w + 1 / (1 - w)‖ ≤
      ‖completedRiemannZeta w‖ + 1 + 1 := by
    have h2 : ‖completedRiemannZeta w + 1 / w‖ ≤ ‖completedRiemannZeta w‖ + ‖1 / w‖ :=
      norm_add_le _ _
    have h3 : ‖completedRiemannZeta w + 1 / w + 1 / (1 - w)‖ ≤
        ‖completedRiemannZeta w + 1 / w‖ + ‖1 / (1 - w)‖ := norm_add_le _ _
    linarith
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hexp2 : (2 : ℝ) ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by
    have h1 : (0 : ℝ) ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) := by positivity
    have h3 : (2 : ℝ) ≤ Real.exp 20 := by
      have := Real.add_one_le_exp 20
      linarith
    calc (2 : ℝ) ≤ Real.exp 20 := h3
      _ ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by
          refine Real.exp_le_exp.mpr ?_
          linarith
  calc ‖completedRiemannZeta w + 1 / w + 1 / (1 - w)‖
      ≤ Real.exp (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14) +
          Real.exp (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14) := by
        have hlow : Real.exp (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14) ≥ 2 := by
          have h1 : (0 : ℝ) ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) := by positivity
          have h2 : Real.exp (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14) ≥ Real.exp 14 := by
            refine Real.exp_le_exp.mpr ?_
            linarith
          have h3 : (2 : ℝ) ≤ Real.exp 14 := by
            have := Real.add_one_le_exp 14
            linarith
          linarith
        linarith
    _ = 2 * Real.exp (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14) := by ring
    _ ≤ Real.exp 1 * Real.exp (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14) :=
        mul_le_mul_of_nonneg_right h2e (by positivity)
    _ = Real.exp (1 + (4 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 14)) := (Real.exp_add 1 _).symm
    _ ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (1 : ℝ) ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) := by
          calc (1 : ℝ) = 1 ^ (3 / 2 : ℝ) := by norm_num
            _ ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) :=
                Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
        linarith

/-- `xi z = z (z-1) Λ z / 2` away from the two points `0` and `1`. -/
private theorem xi_eq_mul {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2 =
      z * (z - 1) * completedRiemannZeta z / 2 := by
  have h2 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [completedRiemannZeta_eq]
  field_simp
  ring

/-- Away from the compact disk of radius `4`, `xi` is bounded by
`exp (40 (1 + ‖z‖)^(3/2) + 40)`. -/
private theorem norm_xi_le_of_four_le {z : ℂ} (hz : 4 ≤ ‖z‖) :
    ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ ≤
      Real.exp (40 * (1 + ‖z‖) ^ (3 / 2 : ℝ) + 40) := by
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg z
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hr
    simp at hr
    linarith
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hr
    simp at hr
    linarith
  rw [xi_eq_mul hz0 hz1]
  set w : ℂ := if (1 / 2 : ℝ) ≤ z.re then z else 1 - z with hw
  have hwre : 1 / 2 ≤ w.re := by
    by_cases hc : (1 / 2 : ℝ) ≤ z.re
    · rw [hw, if_pos hc]
      exact hc
    · rw [hw, if_neg hc]
      simp only [sub_re, one_re]
      linarith
  have hzn : ‖z‖ = r := hr.symm
  have hwnorm : 3 ≤ ‖w‖ := by
    have h1 : ‖z‖ ≤ ‖z - 1‖ + 1 := by
      have h3 := norm_add_le (z - 1) (1 : ℂ)
      have h4 : z - 1 + 1 = z := by ring
      rw [h4] at h3
      simpa using h3
    by_cases hc : (1 / 2 : ℝ) ≤ z.re
    · rw [hw, if_pos hc]
      linarith
    · rw [hw, if_neg hc]
      have h5 : ‖1 - z‖ = ‖z - 1‖ := by
        rw [show (1 : ℂ) - z = -(z - 1) by ring, norm_neg]
      rw [h5]
      linarith
  have hΛ₀ : completedRiemannZeta₀ z = completedRiemannZeta₀ w := by
    by_cases hc : (1 / 2 : ℝ) ≤ z.re
    · rw [hw, if_pos hc]
    · rw [hw, if_neg hc]
      exact (completedRiemannZeta₀_one_sub z).symm
  have hΛz : ‖completedRiemannZeta z‖ ≤ ‖completedRiemannZeta₀ w‖ + 2 := by
    have hE : completedRiemannZeta z = completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
      completedRiemannZeta_eq z
    rw [hE, hΛ₀]
    have hb1 : ‖1 / z‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]
      linarith
    have hb2 : ‖1 / (1 - z)‖ ≤ 1 := by
      have h1z : (3 : ℝ) ≤ ‖1 - z‖ := by
        have h5 : ‖1 - z‖ = ‖z - 1‖ := by
          rw [show (1 : ℂ) - z = -(z - 1) by ring, norm_neg]
        have h6 : ‖z‖ ≤ ‖z - 1‖ + 1 := by
          have h3 := norm_add_le (z - 1) (1 : ℂ)
          have h4 : z - 1 + 1 = z := by ring
          rw [h4] at h3
          simpa using h3
        rw [h5]
        linarith
      rw [norm_div, norm_one, div_le_one (by linarith)]
      linarith
    have h3 := norm_sub_le (completedRiemannZeta₀ w - 1 / z) (1 / (1 - z))
    have h4 := norm_sub_le (completedRiemannZeta₀ w) (1 / z)
    linarith
  have hΛ₀w := norm_completedRiemannZeta₀_le hwre hwnorm
  have hexp2 : (2 : ℝ) ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by
    have h1 : (0 : ℝ) ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) := by positivity
    have h3 : (2 : ℝ) ≤ Real.exp 20 := by
      have := Real.add_one_le_exp 20
      linarith
    calc (2 : ℝ) ≤ Real.exp 20 := h3
      _ ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by
          refine Real.exp_le_exp.mpr ?_
          linarith
  have hbounded : ‖completedRiemannZeta₀ w‖ + 2 ≤
      Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 21) := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    calc ‖completedRiemannZeta₀ w‖ + 2
        ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) +
            Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by linarith
      _ = 2 * Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) := by ring
      _ ≤ Real.exp 1 * Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20) :=
          mul_le_mul_of_nonneg_right h2e (by positivity)
      _ = Real.exp (1 + (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 20)) := (Real.exp_add 1 _).symm
      _ ≤ Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 21) := by
          refine Real.exp_le_exp.mpr ?_
          ring_nf
          linarith
  have hnorm : ‖z * (z - 1) * completedRiemannZeta z / 2‖ ≤
      (1 + r) ^ 2 * Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 21) := by
    have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_div, norm_mul, norm_mul, h2n]
    have hz1n : ‖z - 1‖ ≤ r + 1 := by
      have h := norm_sub_le z (1 : ℂ)
      simp only [norm_one] at h
      rw [hr]
      exact h
    have h1 : ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta z‖ / 2 ≤
        r * (r + 1) * (‖completedRiemannZeta₀ w‖ + 2) / 2 := by
      have h6 : ‖z‖ * ‖z - 1‖ ≤ r * (r + 1) := by
        rw [hzn]
        exact mul_le_mul (le_refl _) hz1n (norm_nonneg _) hr0
      have h5 : ‖completedRiemannZeta z‖ / 2 ≤ (‖completedRiemannZeta₀ w‖ + 2) / 2 := by
        linarith
      calc ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta z‖ / 2
          = (‖z‖ * ‖z - 1‖) * (‖completedRiemannZeta z‖ / 2) := by ring
        _ ≤ (r * (r + 1)) * ((‖completedRiemannZeta₀ w‖ + 2) / 2) :=
            mul_le_mul h6 h5 (by positivity) (by positivity)
        _ = r * (r + 1) * (‖completedRiemannZeta₀ w‖ + 2) / 2 := by ring
    have h7 : r * (r + 1) * (‖completedRiemannZeta₀ w‖ + 2) / 2 ≤
        (1 + r) ^ 2 * Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 21) := by
      have h8 : r * (r + 1) / 2 ≤ (1 + r) ^ 2 := by nlinarith
      calc r * (r + 1) * (‖completedRiemannZeta₀ w‖ + 2) / 2
          = (r * (r + 1) / 2) * (‖completedRiemannZeta₀ w‖ + 2) := by ring
        _ ≤ (1 + r) ^ 2 * Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 21) :=
            mul_le_mul h8 hbounded (by positivity) (by positivity)
    linarith
  have hwle : 1 + ‖w‖ ≤ 2 * (1 + r) := by
    have hwn : ‖w‖ ≤ r + 1 := by
      by_cases hc : (1 / 2 : ℝ) ≤ z.re
      · rw [hw, if_pos hc]
        linarith
      · rw [hw, if_neg hc]
        have h5 : ‖1 - z‖ ≤ ‖z‖ + 1 := by
          have h3 := norm_sub_le (1 : ℂ) z
          simp only [norm_one] at h3
          linarith
        linarith
    linarith
  have hexpmono : Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 21) ≤
      Real.exp (15 * (1 + r) ^ (3 / 2 : ℝ) + 21) := by
    refine Real.exp_le_exp.mpr ?_
    have hpos : (0 : ℝ) ≤ 1 + r := by linarith
    have h1 : (1 + ‖w‖) ^ (3 / 2 : ℝ) ≤ (2 * (1 + r)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hwle (by norm_num)
    have h2 : (2 * (1 + r)) ^ (3 / 2 : ℝ) = 2 ^ (3 / 2 : ℝ) * (1 + r) ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) hpos
    have h3 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
      have h4 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
      rw [h4]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    rw [h2] at h1
    have e1 : 5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) ≤
        5 * (2 ^ (3 / 2 : ℝ) * (1 + r) ^ (3 / 2 : ℝ)) := by linarith
    have e2 : 5 * (2 ^ (3 / 2 : ℝ) * (1 + r) ^ (3 / 2 : ℝ)) ≤
        5 * (3 * (1 + r) ^ (3 / 2 : ℝ)) := by
      have hR0 : (0 : ℝ) ≤ (1 + r) ^ (3 / 2 : ℝ) := by positivity
      nlinarith
    linarith
  have hpoly : (1 + r) ^ 2 ≤ Real.exp (25 * (1 + r) ^ (3 / 2 : ℝ)) := by
    have hpos : (0 : ℝ) < 1 + r := by linarith
    have hlog1 : Real.log (1 + r) ≤ 1 + r := by
      have h := Real.log_le_sub_one_of_pos hpos
      linarith
    have h2log : Real.log ((1 + r) ^ 2) = 2 * Real.log (1 + r) := by
      rw [Real.log_pow]
      norm_num
    have hsplit : (1 + r) ^ (3 / 2 : ℝ) = (1 + r) * (1 + r) ^ (1 / 2 : ℝ) := by
      conv_lhs =>
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith),
          Real.rpow_one]
    have hhalf : (1 : ℝ) ≤ (1 + r) ^ (1 / 2 : ℝ) := by
      calc (1 : ℝ) = 1 ^ (1 / 2 : ℝ) := by norm_num
        _ ≤ (1 + r) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    have hR' : (1 + r) ≤ (1 + r) ^ (3 / 2 : ℝ) := by
      rw [hsplit]
      nlinarith [hr0, hhalf]
    have h3 : Real.log ((1 + r) ^ 2) ≤ 25 * (1 + r) ^ (3 / 2 : ℝ) := by
      rw [h2log]
      nlinarith
    calc (1 + r) ^ 2 = Real.exp (Real.log ((1 + r) ^ 2)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (25 * (1 + r) ^ (3 / 2 : ℝ)) := Real.exp_le_exp.mpr h3
  refine hnorm.trans ?_
  calc (1 + r) ^ 2 * Real.exp (5 * (1 + ‖w‖) ^ (3 / 2 : ℝ) + 21)
      ≤ Real.exp (25 * (1 + r) ^ (3 / 2 : ℝ)) *
          Real.exp (15 * (1 + r) ^ (3 / 2 : ℝ) + 21) :=
        mul_le_mul hpoly hexpmono (by positivity) (by positivity)
    _ = Real.exp (25 * (1 + r) ^ (3 / 2 : ℝ) + (15 * (1 + r) ^ (3 / 2 : ℝ) + 21)) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (40 * (1 + r) ^ (3 / 2 : ℝ) + 40) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (1 : ℝ) ≤ (1 + r) ^ (3 / 2 : ℝ) := by
          calc (1 : ℝ) = 1 ^ (3 / 2 : ℝ) := by norm_num
            _ ≤ (1 + r) ^ (3 / 2 : ℝ) :=
                Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
        nlinarith

private theorem exists_xi_growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
    Real.log ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖
      ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ) + C := by
  have hcont : Continuous (fun z : ℂ => z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2) := by
    have h : Differentiable ℂ (fun z : ℂ => z * (z - 1) * completedRiemannZeta₀ z / 2) :=
      (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
        differentiable_completedZeta₀).div_const 2)
    exact (h.add_const (1 / 2)).continuous
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_isMaxOn
    ⟨0, by simp⟩ hcont.norm.continuousOn
  refine ⟨max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)),
    ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 60 := by norm_num
    exact le_trans h1 (le_max_left _ _)
  · intro z
    have hR1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
      calc (1 : ℝ) = 1 ^ (3 / 2 : ℝ) := by norm_num
        _ ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith [norm_nonneg z]) (by norm_num)
    by_cases hsmall : ‖z‖ ≤ 4
    · have hzmem : z ∈ Metric.closedBall (0 : ℂ) 4 := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact hsmall
      have hb : ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ ≤
          ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ := hmax hzmem
      have hlog : Real.log ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ ≤
          max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)) := by
        by_cases hzero : ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ = 0
        · rw [hzero, Real.log_zero]
          have h1 : (0 : ℝ) ≤ 60 := by norm_num
          exact le_trans h1 (le_max_left _ _)
        · have hpos : 0 < ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ :=
            lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
          have h2 : Real.log ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ ≤
              Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ :=
            Real.log_le_log hpos hb
          have h3 : Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1 ≤
              max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1) :=
            le_max_right _ _
          have h4 : max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1) ≤
              max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)) :=
            le_max_right _ _
          linarith
      have h0c : (0 : ℝ) ≤
          max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)) := by
        have h1 : (0 : ℝ) ≤ 60 := by norm_num
        exact le_trans h1 (le_max_left _ _)
      have hconst :
          max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)) ≤
          max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)) *
            (1 + ‖z‖) ^ (3 / 2 : ℝ) +
          max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)) := by
        nlinarith [hR1, h0c]
      linarith
    · push_neg at hsmall
      have hb := norm_xi_le_of_four_le (z := z) hsmall.le
      have hlog : Real.log ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ ≤
          40 * (1 + ‖z‖) ^ (3 / 2 : ℝ) + 40 := by
        by_cases hzero : ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ = 0
        · rw [hzero, Real.log_zero]
          positivity
        · have hpos : 0 < ‖z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2‖ :=
            lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
          have hpos2 : 0 < Real.exp (40 * (1 + ‖z‖) ^ (3 / 2 : ℝ) + 40) := Real.exp_pos _
          have hlogexp := Real.log_le_log hpos hb
          rwa [Real.log_exp] at hlogexp
      have hC60 : (40 : ℝ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) + 40 ≤
          60 * (1 + ‖z‖) ^ (3 / 2 : ℝ) + 60 := by nlinarith [hR1]
      have hcle : (60 : ℝ) ≤
          max 60 (max 1 (Real.log ‖z₀ * (z₀ - 1) * completedRiemannZeta₀ z₀ / 2 + 1 / 2‖ + 1)) :=
        le_max_left _ _
      nlinarith [hlog, hC60, hcle, hR1]

/-! ## 4. `xi` has no zeros when every zero of `ζ` is real -/

private theorem xi_real_gt_one_ne_zero {t : ℝ} (h : 1 < t) :
    (t : ℂ) * ((t : ℂ) - 1) * completedRiemannZeta₀ (t : ℂ) / 2 + 1 / 2 ≠ 0 := by
  intro hzero
  have ht1 : (1 : ℝ) < ((t : ℂ)).re := by simpa using h
  have ht0 : (t : ℂ) ≠ 0 := by
    intro hh
    have := congrArg Complex.re hh
    simp at this
    linarith
  have ht1' : (t : ℂ) ≠ 1 := by
    intro hh
    have := congrArg Complex.re hh
    simp at this
    linarith
  have hΛ : completedRiemannZeta (t : ℂ) = 0 := by
    have heq := xi_eq_mul ht0 ht1'
    have h2 : (t : ℂ) * ((t : ℂ) - 1) * completedRiemannZeta (t : ℂ) / 2 = 0 := by
      rw [← heq]
      exact hzero
    have h2' : ((t : ℂ) * ((t : ℂ) - 1) / 2) * completedRiemannZeta (t : ℂ) = 0 := by
      rw [← h2]
      ring
    have hne : ((t : ℂ) * ((t : ℂ) - 1) / 2) ≠ 0 := by
      refine div_ne_zero (mul_ne_zero ht0 ?_) two_ne_zero
      exact sub_ne_zero.mpr ht1'
    rcases mul_eq_zero.mp h2' with hh | hh
    · exact absurd hh hne
    · exact hh
  have hΓ : Complex.Gammaℝ (t : ℂ) ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hz
    have hre := congrArg Complex.re hn
    simp at hre
    linarith
  have hmul := completedRiemannZeta_eq_mul (s := (t : ℂ)) ht0 hΓ
  rw [hmul] at hΛ
  have hζ : riemannZeta ((t : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt ht1)
  rcases mul_eq_zero.mp hΛ with hh | hh
  · exact hζ hh
  · exact hΓ hh

private theorem xi_ne_zero_of_all_zeros_real
    (H : ∀ z : ℂ, riemannZeta z = 0 → z.im = 0) :
    ∀ z : ℂ, z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2 ≠ 0 := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hΛ : completedRiemannZeta z = 0 := by
    have heq := xi_eq_mul hz0 hz1
    have h2 : z * (z - 1) * completedRiemannZeta z / 2 = 0 := by
      rw [← heq]
      exact hz
    have h2' : (z * (z - 1) / 2) * completedRiemannZeta z = 0 := by
      rw [← h2]
      ring
    have hne : (z * (z - 1) / 2) ≠ 0 := by
      refine div_ne_zero (mul_ne_zero hz0 ?_) two_ne_zero
      exact sub_ne_zero.mpr hz1
    rcases mul_eq_zero.mp h2' with hh | hh
    · exact absurd hh hne
    · exact hh
  by_cases hΓ : Complex.Gammaℝ z = 0
  · obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hΓ
    have hrez : z.re = -(2 * (n : ℝ)) := by
      have hre := congrArg Complex.re hn
      simpa using hre
    have himz : z.im = 0 := by
      have him := congrArg Complex.im hn
      simpa using him
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      have hzero : z = 0 := by simpa using hn
      exact hz0 hzero
    · have hgt : 1 < (1 - z).re := by
        simp only [sub_re, one_re, hrez]
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        linarith
      have hreal : (1 - z).im = 0 := by simp [himz]
      have hcast : (1 : ℂ) - z = (((1 - z).re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hreal]
      have hxi := xi_real_gt_one_ne_zero hgt
      have hfe : z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2 =
          (1 - z) * ((1 - z) - 1) * completedRiemannZeta₀ (1 - z) / 2 + 1 / 2 :=
        (xi_one_sub z).symm
      rw [hfe, hcast] at hz
      exact hxi hz
  · have hmul := completedRiemannZeta_eq_mul (s := z) hz0 hΓ
    rw [hmul] at hΛ
    have hζz : riemannZeta z = 0 := by
      rcases mul_eq_zero.mp hΛ with hh | hh
      · exact hh
      · exact absurd hh hΓ
    have hzim : z.im = 0 := H z hζz
    have hcast : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hzim]
    rw [hcast] at hz hζz
    rcases lt_trichotomy z.re 1 with hlt | heq | hgt
    · rcases lt_trichotomy z.re 0 with hlt0 | heq0 | hgt0
      · have hgt' : 1 < (1 - (((z.re : ℝ)) : ℂ)).re := by
          simp only [sub_re, one_re, ofReal_re]
          linarith
        have hreal : (1 - (((z.re : ℝ)) : ℂ)).im = 0 := by simp
        have hcast2 : (1 : ℂ) - (((z.re : ℝ)) : ℂ) =
            ((((1 - (((z.re : ℝ)) : ℂ)).re : ℝ)) : ℂ) := by
          apply Complex.ext
          · simp
          · simp [hreal]
        have hxi := xi_real_gt_one_ne_zero hgt'
        have hfe : (((z.re : ℝ)) : ℂ) * ((((z.re : ℝ)) : ℂ) - 1) *
            completedRiemannZeta₀ (((z.re : ℝ)) : ℂ) / 2 + 1 / 2 =
            (1 - (((z.re : ℝ)) : ℂ)) * ((1 - (((z.re : ℝ)) : ℂ)) - 1) *
              completedRiemannZeta₀ (1 - (((z.re : ℝ)) : ℂ)) / 2 + 1 / 2 :=
          (xi_one_sub _).symm
        rw [hfe, hcast2] at hz
        exact hxi hz
      · exact hz0 (by rw [hcast, heq0]; norm_num)
      · have hneg := zeta_real_neg hgt0 hlt
        rw [hζz] at hneg
        exact absurd hneg.2 (by norm_num)
    · exact hz1 (by rw [hcast, heq]; norm_num)
    · exact xi_real_gt_one_ne_zero hgt hz

/-! ## 5. Assembly -/

/-- LEAF. The non-trivial zero of the Riemann zeta function is a complex number.
Textbook argument: Standard analytic number theory. -/
theorem zeta_has_complex_zero : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.im ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, hC0, hCg⟩ := exists_xi_growth
  obtain ⟨a, b, hab⟩ :=
    exp_affine_of_order_two xi_differentiable (xi_ne_zero_of_all_zeros_real hcon)
      ⟨C, hC0, hCg⟩
  have hb : b = 0 := by
    by_contra hb0
    have h1 : ∀ z : ℂ, Complex.exp (a + b - b * z) = Complex.exp (a + b * z) := by
      intro z
      have h2 : (1 - z) * ((1 - z) - 1) * completedRiemannZeta₀ (1 - z) / 2 + 1 / 2 =
          z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2 := xi_one_sub z
      rw [hab (1 - z), hab z] at h2
      have h3 : a + b * (1 - z) = a + b - b * z := by ring
      rwa [h3] at h2
    have h2 : ∀ z : ℂ, Complex.exp (b - 2 * b * z) = 1 := by
      intro z
      have h3 : Complex.exp (a + b - b * z) / Complex.exp (a + b * z) = 1 := by
        rw [h1 z]
        exact div_self (Complex.exp_ne_zero _)
      rw [← Complex.exp_sub] at h3
      convert h3 using 2
      ring
    have harith : ∀ z : ℂ, b * (1 - 2 * z) = b - 2 * b * z := by
      intro z
      ring
    have hexp1 : ∀ u : ℂ, Complex.exp u = 1 := by
      intro u
      have hz : b * (1 - 2 * ((1 - u / b) / 2)) = u := by
        field_simp
        ring
      rw [← hz]
      rw [harith]
      exact h2 _
    have hone : Complex.exp (1 : ℂ) = 1 := hexp1 1
    have h1e : Complex.exp (1 : ℂ) = ((Real.exp 1 : ℝ) : ℂ) := by
      have h : Complex.exp ((1 : ℝ) : ℂ) = ((Real.exp 1 : ℝ) : ℂ) :=
        (Complex.ofReal_exp 1).symm
      simpa using h
    rw [h1e] at hone
    have hre := congrArg Complex.re hone
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    have hgt : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    linarith
  have hxi0 : (0 : ℂ) * ((0 : ℂ) - 1) * completedRiemannZeta₀ 0 / 2 + 1 / 2 = 1 / 2 := by
    norm_num
  have key : ∀ z : ℂ, z * (z - 1) * completedRiemannZeta₀ z / 2 + 1 / 2 = Complex.exp a := by
    intro z
    rw [hab z, hb]
    ring
  have h1 : (Real.pi : ℂ) / 6 = 1 / 2 := by
    rw [← xi_two, key 2, ← key 0, hxi0]
  have hpi : Real.pi = 3 := by
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  linarith [Real.pi_gt_three]

/-- LEAF. The classical existence input to its functional equation argument.
Textbook argument: Landau Handbuch page 489 and the classical theory of zeta zeros. -/
theorem zeta_has_complex_zero_sym : ∃ ρ : ℂ, ρ.im ≠ 0 ∧ riemannZeta ρ = 0 := by
  obtain ⟨ρ, h1, h2⟩ := zeta_has_complex_zero
  exact ⟨ρ, h2, h1⟩

/-- The classical existence input to its functional equation argument.
Textbook argument: Landau Handbuch page 489 and the classical theory of zeta zeros. -/
theorem exists_nonreal_zeta_zero :
    ∃ ρ : ℂ, ρ.im ≠ 0 ∧ riemannZeta ρ = 0 := by
  exact zeta_has_complex_zero_sym

end LeanLab.HardyLittlewood1923.DecompJ1131
