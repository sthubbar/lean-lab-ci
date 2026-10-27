import Mathlib
import LeanLab.RamareSaouter2003.Theorem3Smooth
import LeanLab.RamareSaouter2003.MuStarUpper

/-!
# Ramare-Saouter 2003, the zero terms of display (13) to (15)

Unit U-1531, run 20261026T0004Z-24325, DECOMPOSE. AI wrote this Lean code, Claude, checked only
by the Lean kernel. Binary Goldbach is OPEN.

The open analytic input of Table 1 row one is `JLower15Lit`, display (15) on p. 20 with
`delta = m u`. Its proof in the paper applies the explicit formula Lemma 4 to `J`, then bounds
every zero term. This file splits the per-zero bookkeeping into LEAF lemmas:

* zeros with `|gamma| <= T`, where `beta = 1/2` by the RH height hypothesis: the bounds on p. 19
  `|(e^(u rho) - 1)/rho| <= u e^(u/2) <= u (1 + delta)^(1/2)` and
  `|int (1 + delta t)^rho f| <= (1 + delta)^(1/2) ||f||_1`;
* zeros with `|gamma| > T`: the `m` integrations by parts on p. 19 and the bound (14) on p. 20.

Assemblies, with real proofs and no sorry of their own, CONDITIONAL ON the leaves:
`bound14`, display (14); `far_zero_term_le`, one zero term of (15) with `|gamma| > T`;
`near_zero_term_le`, one zero term with `beta = 1/2`.
-/

namespace LeanLab.RamareSaouter2003.Decomp1531a

open LeanLab.RamareSaouter2003.Smooth Set

/-- LEAF. Unit U-1531. For `Re rho = 1/2` and `u >= 0`, the norm of `(e^(u rho) - 1)/rho` is at
most `u e^(u/2)`, since it is the integral of `e^(x rho)` over `[0, u]`; p. 19, the display
after (12). -/
theorem norm_exp_sub_one_div_crit {ρ : ℂ} (hρ : ρ.re = 1 / 2) {u : ℝ} (hu : 0 ≤ u) :
    ‖(Complex.exp (u * ρ) - 1) / ρ‖ ≤ u * Real.exp (u / 2) := by
  have hne : ρ ≠ 0 := by
    intro hh
    rw [hh] at hρ
    norm_num at hρ
  have hi := integral_exp_mul_complex (a := (0 : ℝ)) (b := u) hne
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hi
  have hb : ‖∫ x in (0 : ℝ)..u, Complex.exp (ρ * x)‖ ≤ Real.exp (u / 2) * |u - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hu] at hx
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hρ]
    linarith [hx.2]
  rw [hi] at hb
  simpa only [sub_zero, abs_of_nonneg hu, mul_comm] using hb

/-- LEAF. Unit U-1531. For `m >= 2` and `0 <= u <= 10^-4`, `e^u <= 1 + m u`, which gives
`e^(u/2) <= (1 + delta)^(1/2)` with `delta = m u`; p. 19, the display after (12). -/
theorem exp_le_one_add_mul {m : ℕ} (hm : 2 ≤ m) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 0.0001) :
    Real.exp u ≤ 1 + m * u := by
  have hsmall : u < 1 := by linarith
  have h := Real.exp_bound_div_one_sub_of_interval hu0 hsmall
  have hden : 0 < 1 - u := by linarith
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hu2 : u ^ 2 ≤ u / 2 := by nlinarith
  have hq : 1 / (1 - u) ≤ 1 + 2 * u := by
    rw [div_le_iff₀ hden]
    nlinarith
  exact h.trans (hq.trans (by nlinarith))

/-- LEAF. Unit U-1531. For `Re rho = 1/2`, `delta >= 0` and `f` continuous and nonnegative on
`[0, 1]`, the norm of the integral of `(1 + delta t)^rho f(t)` over `[0, 1]` is at most
`(1 + delta)^(1/2)` times the integral of `f`; p. 19, the display after (12). -/
theorem norm_integral_cpow_crit {ρ : ℂ} (hρ : ρ.re = 1 / 2) {δ : ℝ} (hδ : 0 ≤ δ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) :
    ‖∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ ρ) * (f t : ℂ)‖ ≤
      √(1 + δ) * ∫ t in (0 : ℝ)..1, f t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
  · apply Filter.Eventually.of_forall
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hpos : 0 < 1 + δ * t := by nlinarith [ht'.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hρ, ← Real.sqrt_eq_rpow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 t ht')]
    apply mul_le_mul_of_nonneg_right _ (hf0 t ht')
    apply Real.sqrt_le_sqrt
    nlinarith [ht'.2]
  · exact (hf.const_mul _).intervalIntegrable_of_Icc (by norm_num)

/-- LEAF. Unit U-1531. For `0 <= Re rho <= 1`, `Im rho` nonzero and `u >= 0`, the norm of
`(e^(u rho) - 1)/rho` is at most `(e^u + 1)/|Im rho|`; p. 20, the step from (14) to (15). -/
theorem norm_exp_sub_one_div_far {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (hγ : ρ.im ≠ 0)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖(Complex.exp (u * ρ) - 1) / ρ‖ ≤ (Real.exp u + 1) / |ρ.im| := by
  have hγ0 : 0 < |ρ.im| := abs_pos.mpr hγ
  have hn : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have he : ‖Complex.exp (u * ρ)‖ ≤ Real.exp u := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith
  rw [norm_div]
  calc
    ‖Complex.exp (u * ρ) - 1‖ / ‖ρ‖ ≤ (Real.exp u + 1) / ‖ρ‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      simpa using (norm_sub_le (Complex.exp (u * ρ)) 1).trans (by simpa using add_le_add_right he 1)
    _ ≤ (Real.exp u + 1) / |ρ.im| := by
      exact div_le_div_of_nonneg_left (by positivity) hγ0 hn

/-- LEAF. Unit U-1531. The product of the norms of `rho + j` for `j = 1, ..., m` is at least
`|Im rho|^m`, since each factor has the same imaginary part as `rho`; p. 20, (14). -/
theorem prod_norm_add_ge (ρ : ℂ) (m : ℕ) :
    |ρ.im| ^ m ≤ ∏ j ∈ Finset.range m, ‖ρ + ((j : ℂ) + 1)‖ := by
  calc
    |ρ.im| ^ m = ∏ j ∈ Finset.range m, |ρ.im| := by simp
    _ ≤ ∏ j ∈ Finset.range m, ‖ρ + ((j : ℂ) + 1)‖ := by
      apply Finset.prod_le_prod₀
      · intro j _; exact abs_nonneg _
      · intro j _
        simpa using Complex.abs_im_le_norm (ρ + ((j : ℂ) + 1))

/-- LEAF. Unit U-1531. For `0 <= Re rho <= 1`, `delta >= 0` and `t` in `[0, 1]`, the norm of
`(1 + delta t)^(rho + m)` is at most `(1 + delta)^(m + 1)`; p. 20, (14). -/
theorem norm_cpow_shift_le {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    ‖((1 + δ * t : ℝ) : ℂ) ^ (ρ + m)‖ ≤ (1 + δ) ^ (m + 1) := by
  have hb : 1 ≤ 1 + δ * t := by nlinarith [ht.1]
  have hB : 1 + δ * t ≤ 1 + δ := by nlinarith [ht.2]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + δ * t)]
  simp only [Complex.add_re, Complex.natCast_re]
  calc
    (1 + δ * t) ^ (ρ.re + m) ≤ (1 + δ * t) ^ ((m + 1 : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hb
      push_cast
      linarith
    _ = (1 + δ * t) ^ (m + 1) := Real.rpow_natCast _ _
    _ ≤ (1 + δ) ^ (m + 1) := pow_le_pow_left₀ (by linarith) hB _

/-- LEAF. Unit U-1531. One integration by parts: for `s` not `-1`, `delta > 0` and `g` with a
continuous derivative `g'` vanishing at `0` and `1`, the integral of `(1 + delta t)^s g` over
`[0, 1]` equals `-1/((s + 1) delta)` times the integral of `(1 + delta t)^(s + 1) g'`; p. 19, the
display before (14). -/
theorem ibp_cpow_step {s : ℂ} (hs : s ≠ -1) {δ : ℝ} (hδ : 0 < δ) {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g') (h0 : g 0 = 0) (h1 : g 1 = 0) :
    ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ s) * (g t : ℂ) =
      -(1 / ((s + 1) * δ)) * ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ (s + 1)) * (g' t : ℂ) := by
  let U : ℝ → ℂ := fun t => ((1 + δ * t : ℝ) : ℂ) ^ (s + 1) / (s + 1) / (δ : ℂ)
  have hbase (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1 + δ * t := by
    nlinarith [ht.1]
  have hc (r : ℂ) : ContinuousOn (fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ r) (Icc 0 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact (Complex.continuousAt_ofReal_cpow_const (1 + δ * t) r (Or.inr (hbase t ht).ne')).comp_of_eq (by fun_prop : ContinuousAt (fun x : ℝ => 1 + δ * x) t) rfl
  have hdu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt U (((1 + δ * t : ℝ) : ℂ) ^ s) t := by
    have hi : HasDerivAt (fun x : ℝ => 1 + δ * x) δ t := by
      simpa using ((hasDerivAt_id t).const_mul δ).const_add 1
    have hd := ((hasDerivAt_ofReal_cpow_const' (hbase t ht).ne' hs).scomp t hi).div_const (δ : ℂ)
    have hd' : HasDerivAt U (δ • (((1 + δ * t : ℝ) : ℂ) ^ s) / (δ : ℂ)) t := by
      simpa only [U, Function.comp_apply] using hd
    convert hd' using 1
    change _ = (δ : ℂ) * _ / (δ : ℂ)
    field_simp [Complex.ofReal_ne_zero.mpr hδ.ne']
  have hgcont : Continuous (fun t => (g t : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt)
  have hg'cont : Continuous (fun t => (g' t : ℂ)) := Complex.continuous_ofReal.comp hg'
  have hUcont : ContinuousOn U (Icc 0 1) := fun t ht => (hdu t ht).continuousAt.continuousWithinAt
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t => (g t : ℂ)) (v := U)
    (u' := fun t => (g' t : ℂ)) (v' := fun t => ((1 + δ * t : ℝ) : ℂ) ^ s)
    hgcont.continuousOn
    (by simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hUcont)
    (fun t _ => (hg t).ofReal_comp)
    (fun t ht => hdu t ⟨by simpa using ht.1.le, by simpa using ht.2.le⟩)
    (hg'cont.intervalIntegrable _ _)
    ((hc s).intervalIntegrable_of_Icc (by norm_num))
  simp only [h0, h1, Complex.ofReal_zero, zero_mul, sub_self, zero_sub] at hp
  calc
    (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (g t : ℂ)) =
        ∫ t in (0 : ℝ)..1, (g t : ℂ) * ((1 + δ * t : ℝ) : ℂ) ^ s := by
          congr 1; funext t; ring
    _ = -(∫ t in (0 : ℝ)..1, (g' t : ℂ) * U t) := hp
    _ = -(1 / ((s + 1) * δ)) * ∫ t in (0 : ℝ)..1,
        (((1 + δ * t : ℝ) : ℂ) ^ (s + 1)) * (g' t : ℂ) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      congr 1
      funext t
      dsimp [U]
      have hs1 : s + 1 ≠ 0 := by
        intro h
        apply hs
        linear_combination h
      field_simp [hs1, Complex.ofReal_ne_zero.mpr hδ.ne']

/-- LEAF. Unit U-1531. For `k < m` the `k`-th derivative of `f_m(t) = (4t(1 - t))^m` vanishes
at `0` and at `1`, condition (2) of m-admissibility on p. 17 for `f_m` of (19). -/
theorem iteratedDeriv_fm_boundary {m k : ℕ} (hk : k < m) :
    iteratedDeriv k (fm m) 0 = 0 ∧ iteratedDeriv k (fm m) 1 = 0 := by
  have heq : fm m = fun x => (MuStarUpper.F m).eval x := by
    funext x
    exact (MuStarUpper.F_eval m x).symm
  rw [heq, MuStarUpper.iteratedDeriv_eval]
  exact ⟨MuStarUpper.iter_eval_zero hk 0 (Or.inl rfl),
    MuStarUpper.iter_eval_zero hk 1 (Or.inr rfl)⟩

/-- LEAF. Unit U-1531. The identity of the `m` integrations by parts on p. 19 for `f = f_m`:
for `Re rho >= 0` and `delta > 0`, the integral of `(1 + delta t)^rho f_m(t)` over `[0, 1]`
equals `(-1)^m / ((rho + 1) ... (rho + m) delta^m)` times the integral of
`(1 + delta t)^(rho + m) f_m^(m)(t)`. -/
theorem integral_fm_ibp {ρ : ℂ} (h0 : 0 ≤ ρ.re) {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ ρ) * (fm m t : ℂ) =
      (-1) ^ m / ((∏ j ∈ Finset.range m, (ρ + ((j : ℂ) + 1))) * (δ : ℂ) ^ m) *
        ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ (ρ + m)) * ((iteratedDeriv m (fm m) t : ℝ) : ℂ) := by
  have heq (k : ℕ) : iteratedDeriv k (fm m) =
      fun x => (Polynomial.derivative^[k] (MuStarUpper.F m)).eval x := by
    have hh : fm m = fun x => (MuStarUpper.F m).eval x := by
      funext x; exact (MuStarUpper.F_eval m x).symm
    rw [hh, MuStarUpper.iteratedDeriv_eval]
  have hd (k : ℕ) (t : ℝ) : HasDerivAt (iteratedDeriv k (fm m))
      (iteratedDeriv (k + 1) (fm m) t) t := by
    rw [heq k, heq (k + 1), Function.iterate_succ_apply']
    exact (Polynomial.derivative^[k] (MuStarUpper.F m)).hasDerivAt t
  have hc (k : ℕ) : Continuous (iteratedDeriv k (fm m)) := by
    exact continuous_iff_continuousAt.mpr fun t => (hd k t).continuousAt
  have hi : ∀ k : ℕ, k ≤ m →
      (∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ ρ) * (fm m t : ℂ)) =
        (-1) ^ k / ((∏ j ∈ Finset.range k, (ρ + ((j : ℂ) + 1))) * (δ : ℂ) ^ k) *
          ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ (ρ + k)) *
            ((iteratedDeriv k (fm m) t : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < m := by omega
      have hs : ρ + k ≠ -1 := by
        intro hh
        have hr := congrArg Complex.re hh
        simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re, Complex.one_re] at hr
        have : (0 : ℝ) ≤ k := by positivity
        linarith
      have hb := iteratedDeriv_fm_boundary hk'
      have hstep := ibp_cpow_step hs hδ (hd k) (hc (k + 1)) hb.1 hb.2
      rw [ih (by omega), hstep]
      simp only [Finset.prod_range_succ, pow_succ, Nat.cast_add, Nat.cast_one]
      rw [show ρ + (k : ℂ) + 1 = ρ + ((k : ℂ) + 1) by ring]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  exact hi m le_rfl

/-- LEAF. Unit U-1531. The zero term of Lemma 4 applied to `J`: for `X > 0` and `delta >= 0`,
the integral over `[0, 1]` of `((e^u (1 + delta t) X)^rho - ((1 + delta t) X)^rho)/rho f(t)`
equals `(e^(u rho) - 1)/rho X^rho` times the integral of `(1 + delta t)^rho f(t)`; p. 19, (13). -/
theorem zero_term_factor (ρ : ℂ) {X : ℝ} (hX : 0 < X) {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ)
    (f : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1,
        ((((Real.exp u * (1 + δ * t) * X : ℝ) : ℂ) ^ ρ - (((1 + δ * t) * X : ℝ) : ℂ) ^ ρ) / ρ) *
          (f t : ℂ) =
      (Complex.exp (u * ρ) - 1) / ρ * (X : ℂ) ^ ρ *
        ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ ρ) * (f t : ℂ) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
  have hb : 0 ≤ 1 + δ * t := by nlinarith [ht.1]
  have he : ((Real.exp u : ℝ) : ℂ) ^ ρ = Complex.exp (u * ρ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  dsimp only
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg (Real.exp_pos u).le hb) hX.le,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos u).le hb,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hb hX.le, he]
  ring

/-! ### Assemblies -/

lemma contDiff_fm (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fm m) := by
  unfold fm
  fun_prop

lemma continuous_iteratedDeriv_fm (m : ℕ) : Continuous (iteratedDeriv m (fm m)) :=
  (contDiff_fm m).continuous_iteratedDeriv m (by exact_mod_cast le_top)

/-- **Display (14), p. 20.** For `0 <= Re rho <= 1`, `Im rho` nonzero and `delta > 0`,
`|int (1 + delta t)^rho f_m| <= (1 + delta)^(m+1)/(|gamma|^m delta^m) ||f_m^(m)||_1`.
PROVED CONDITIONAL ON the leaves `integral_fm_ibp`, `prod_norm_add_ge`, `norm_cpow_shift_le`. -/
theorem bound14 {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (hγ : ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) :
    ‖∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ ρ) * (fm m t : ℂ)‖ ≤
      (1 + δ) ^ (m + 1) / (|ρ.im| ^ m * δ ^ m) *
        ∫ t in (0 : ℝ)..1, |iteratedDeriv m (fm m) t| := by
  rw [integral_fm_ibp h0 hδ m, norm_mul]
  have hP := prod_norm_add_ge ρ m
  have hγpos : 0 < |ρ.im| ^ m := pow_pos (abs_pos.mpr hγ) m
  have hA : ‖((-1 : ℂ) ^ m / ((∏ j ∈ Finset.range m, (ρ + ((j : ℂ) + 1))) * (δ : ℂ) ^ m))‖ ≤
      1 / (|ρ.im| ^ m * δ ^ m) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, norm_prod, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right hP (by positivity)
  have hI : ‖∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ (ρ + m)) *
        ((iteratedDeriv m (fm m) t : ℝ) : ℂ)‖ ≤
      ∫ t in (0 : ℝ)..1, (1 + δ) ^ (m + 1) * |iteratedDeriv m (fm m) t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (norm_cpow_shift_le h0 h1 hδ.le ⟨ht.1.le, ht.2⟩ m) (abs_nonneg _)
    · exact (continuous_const.mul (continuous_iteratedDeriv_fm m).abs).intervalIntegrable 0 1
  rw [intervalIntegral.integral_const_mul] at hI
  calc _ ≤ 1 / (|ρ.im| ^ m * δ ^ m) *
        ((1 + δ) ^ (m + 1) * ∫ t in (0 : ℝ)..1, |iteratedDeriv m (fm m) t|) :=
        mul_le_mul hA hI (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma integral_fm_pos (m : ℕ) : 0 < ∫ t in (0 : ℝ)..1, fm m t := by
  rw [norm_fm]; positivity

lemma fm_nonneg' (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ fm m t := by
  unfold fm
  have : 0 ≤ 4 * t * (1 - t) := by nlinarith [ht.1, ht.2]
  positivity

/-- **One zero term of (15), `|gamma| > T`.** For `0 <= beta <= 1`, `gamma` nonzero, `u >= 0`,
`delta > 0` and `X > 0`, the zero term `(e^(u rho) - 1)/rho X^rho int (1 + delta t)^rho f_m`
has norm at most `(e^u + 1)(1 + delta)^(m+1) mu*_m ||f_m||_1 / delta^m` times
`X^beta/|gamma|^(m+1)`. PROVED CONDITIONAL ON the leaves through `bound14` and
`norm_exp_sub_one_div_far`. -/
theorem far_zero_term_le {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (hγ : ρ.im ≠ 0) {u : ℝ}
    (hu : 0 ≤ u) {δ : ℝ} (hδ : 0 < δ) {X : ℝ} (hX : 0 < X) (m : ℕ) :
    ‖(Complex.exp (u * ρ) - 1) / ρ * (X : ℂ) ^ ρ *
        ∫ t in (0 : ℝ)..1, (((1 + δ * t : ℝ) : ℂ) ^ ρ) * (fm m t : ℂ)‖ ≤
      (Real.exp u + 1) * (1 + δ) ^ (m + 1) * muStar m * (∫ t in (0 : ℝ)..1, fm m t) / δ ^ m *
        (X ^ ρ.re / |ρ.im| ^ (m + 1)) := by
  have hF := integral_fm_pos m
  have hmu : (∫ t in (0 : ℝ)..1, |iteratedDeriv m (fm m) t|) =
      muStar m * ∫ t in (0 : ℝ)..1, fm m t := by
    unfold muStar; field_simp
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  have hE := norm_exp_sub_one_div_far h0 h1 hγ hu
  have hB := bound14 h0 h1 hγ hδ m
  rw [hmu] at hB
  have hg : 0 < |ρ.im| := abs_pos.mpr hγ
  have hXr : 0 ≤ X ^ ρ.re := Real.rpow_nonneg hX.le _
  have hmuS : 0 ≤ muStar m := by
    unfold muStar
    apply div_nonneg _ hF.le
    exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
  calc _ ≤ (Real.exp u + 1) / |ρ.im| * X ^ ρ.re *
        ((1 + δ) ^ (m + 1) / (|ρ.im| ^ m * δ ^ m) * (muStar m * ∫ t in (0 : ℝ)..1, fm m t)) := by
        apply mul_le_mul _ hB (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hE hXr
    _ = _ := by field_simp; ring

/-- **One zero term of (13), `|gamma| <= T`, under RH there.** For `Re rho = 1/2`, `m >= 2`,
`0 <= u <= 10^-4` and `X > 0`, with `delta = m u`, the zero term has norm at most
`u (1 + delta) √X ||f_m||_1`, so the `2N(T)` such zeros give the second term of (15).
PROVED CONDITIONAL ON the leaves `norm_exp_sub_one_div_crit`, `exp_le_one_add_mul`,
`norm_integral_cpow_crit`. -/
theorem near_zero_term_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) {m : ℕ} (hm : 2 ≤ m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 0.0001) {X : ℝ} (hX : 0 < X) :
    ‖(Complex.exp (u * ρ) - 1) / ρ * (X : ℂ) ^ ρ *
        ∫ t in (0 : ℝ)..1, (((1 + (m * u) * t : ℝ) : ℂ) ^ ρ) * (fm m t : ℂ)‖ ≤
      u * (1 + m * u) * √X * ∫ t in (0 : ℝ)..1, fm m t := by
  have hδ : 0 ≤ (m : ℝ) * u := by positivity
  have hF := integral_fm_pos m
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hρ, ← Real.sqrt_eq_rpow]
  have hE := norm_exp_sub_one_div_crit hρ hu0
  have hI := norm_integral_cpow_crit hρ hδ (f := fm m) (continuous_fm m).continuousOn
    (fun t ht => fm_nonneg' m ht)
  have hexp : Real.exp (u / 2) ≤ √(1 + m * u) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (u / 2) = u := by push_cast; ring
    rw [this]
    exact exp_le_one_add_mul hm hu0 hu
  have hs : √(1 + m * u) * √(1 + m * u) = 1 + m * u := Real.mul_self_sqrt (by positivity)
  calc _ ≤ u * √(1 + m * u) * √X * (√(1 + m * u) * ∫ t in (0 : ℝ)..1, fm m t) := by
        apply mul_le_mul _ hI (norm_nonneg _) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact hE.trans (mul_le_mul_of_nonneg_left hexp hu0)
    _ = u * (√(1 + m * u) * √(1 + m * u)) * √X * ∫ t in (0 : ℝ)..1, fm m t := by ring
    _ = _ := by rw [hs]

end LeanLab.RamareSaouter2003.Decomp1531a
