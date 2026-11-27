import LeanLab.HelfgottMajor.SPLIT_stieltjes_positive_zero_sum_parts

/-!
Faithful Stieltjes split of `positive_mass_norm_sum_integral` in
`LeanLab.HelfgottMajor.SPLIT_positive_sampling_raw`, following the proof of book Lemma 16.9,
display 16.20 and 16.21 on book pages 431 and 432 of P0014 Part IV, as applied in the proof of
Lemma 16.10 on book pages 433 and 434 with `y = 1` and `f t = |G_δ (1/2 + i t)|` on `[1, T]`.

Notation used in the doc comments, all spelled out in the Lean statements:
* `G t` is the norm of `gaussianMellin δ` at `1/2 + i t`;
* `N t` is the multiplicity weighted count of zeros of `L(s, χ)` with `0 < re < 1` and
  `0 < im ≤ t`;
* `M t = t / (2 π) * log (q t / (2 π e))` is the main term of the zero counting function;
* `g t = 0.15 log (q t) + 3.389` is the explicit error bound of display 16.21.

The three leaves are: the integration by parts identity of the proof of Lemma 16.9, the zero
counting bound of book display 3.95 in the per sign form used through display 16.21, and the
estimate of the error integral by `∫ |f'| g`.

IMPORTANT, a QUESTION for a reviewer. Integration by parts on `[1, T]` produces a boundary
term `G T * R T` at the top height `T`, where `R = N + c - M`.  The book removes it by
truncating `f` to zero above `T0` and applying Lemma 16.9 on `[1, ∞)`; but that truncated `f` is
not continuous, Lemma 16.9 assumes continuity, and the jump at `T0` contributes
`|G_δ (1/2 + i T0)| g(T0)` to `∫ |f'| g`, which display 16.26 then drops when it replaces
`|f'|` by `|G_δ'|`.  The statement `positive_mass_norm_sum_integral` follows display 16.26 and
has no term at height `T`.  So the faithful assembly below proves the parent bound PLUS the
endpoint term `G T * g T`, and does not close the parent.  The parent is not wired.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: proof of book Lemma 16.9, pages 431 and 432, the Stieltjes integration by parts
`∑_{1 < γ ≤ T} f(γ) = ∫_{1+}^{T} f dN` with `N = M + R - c`, followed by the second integration
by parts that turns `∫ f dM` into `(1 / 2 π) ∫ f(t) log (q t / 2 π) dt`, since
`M'(t) = (1 / 2 π) log (q t / 2 π)`.  Here `f t = G t = |G_δ (1/2 + i t)|` as in the proof of
Lemma 16.10, page 433, but kept continuous on `[1, T]`, so the boundary terms at `1` and at `T`
both remain.  The constant shift `c` is arbitrary because `G T - G 1 = ∫ G'`.  Under `hzeros`
every summand `‖gaussianMellin δ ρ‖` equals `G (im ρ)`.  `G` is Lipschitz on `[1, T]` as the norm
of a holomorphic function on a compact segment, so the fundamental theorem of calculus holds with
`deriv`.  Class HARD. -/
theorem stieltjes_positive_zero_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T c : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
          T / (2 * π) * log ((q : ℝ) * T / (2 * π * exp 1))) -
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
        ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ (1 : ℝ)},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
          (1 : ℝ) / (2 * π) * log ((q : ℝ) * (1 : ℝ) / (2 * π * exp 1))) -
      (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
            t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) := by
  obtain ⟨hI1, hI2, hI3⟩ := stieltjes_integrability q χ δ T hT
  rw [stieltjes_sum_by_parts_N q χ δ T hT hzeros]
  have hsplit :
      (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
            t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) =
      (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))) +
        c * (∫ t in (1 : ℝ)..T,
          deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t) -
        (∫ t in (1 : ℝ)..T,
          deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
            (t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1
      (hI2.const_mul c), ← intervalIntegral.integral_sub (hI1.add (hI2.const_mul c)) hI3]
    congr 1
    funext t
    ring
  rw [hsplit, norm_gaussianMellin_ftc δ T hT, main_term_by_parts q δ T hT]
  ring

/-- LEAF: the zero counting bound of book display 3.95, section 3.7.3.3, in the per sign form
`N(t, χ) = (t / 2 π) log (q t / 2 π e) + O*(g_χ(t))` with `g_χ(t) = 0.15 log q t + 3.389`,
display 16.21 page 431, used for every `t ≥ y = 1` in the proof of Lemma 16.9 and at `t = 1` in
the proof of Lemma 16.10, page 433.  The book's `N(t, χ)` counts zeros with `0 ≤ im ≤ t` and
gives half weight to zeros of height exactly `0` and `t`; here the count is over `0 < im ≤ t`
with full weight at `t`, so the half weight of the zeros at height `0` is the constant `c`, and
full weight at `t` follows from the half weight form by right continuity, since the bound is a
closed inequality with continuous right side.  Class HARD, a cited explicit zero counting
result. -/
theorem zero_count_error_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
        t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))| ≤
        0.15 * log ((q : ℝ) * t) + 3.389 := by
  sorry

open MeasureTheory Filter Asymptotics Set
open scoped Topology

private lemma gm_f_norm (δ t : ℝ) :
    ‖(exp (-t ^ 2 / 2) : ℂ) * e (δ * t)‖ = exp (-t ^ 2 / 2) := by
  have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
  rw [norm_mul, he0 (δ * t), mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

private lemma gm_bigO_top (δ : ℝ) :
    (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) =O[atTop]
      (fun t : ℝ => t ^ (-(1 : ℝ))) := by
  rw [← isBigO_norm_left]
  simp_rw [gm_f_norm]
  have hexp : (fun t : ℝ => exp (-t)) =O[atTop] (fun t : ℝ => t ^ (-1 : ℝ)) := by
    simpa only [one_mul, neg_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-1)).isBigO
  have hh := (exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)).isBigO.trans hexp
  simpa only [one_mul, neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using hh

private lemma gm_bigO_zero (δ : ℝ) :
    (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  apply isBigO_iff.mpr
  refine ⟨1, Eventually.of_forall fun t => ?_⟩
  simp only [gm_f_norm, neg_zero, rpow_zero, norm_one, mul_one]
  exact exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])

private lemma gm_continuous (δ : ℝ) :
    Continuous (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) := by
  unfold e
  fun_prop

private theorem gm_hasDerivAt (δ : ℝ) {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    HasDerivAt (gaussianMellin δ)
      (mellin (fun t : ℝ => log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) s) s := by
  let f : ℝ → ℂ := fun t => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  exact (mellin_hasDerivAt_of_isBigO_rpow
    ((gm_continuous δ).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (gm_bigO_top δ) hs1 (gm_bigO_zero δ) hs).2

private lemma gm_log_continuousOn (δ : ℝ) :
    ContinuousOn (fun t : ℝ => log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) (Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => log t) (Ioi 0) :=
    continuousOn_log.mono (subset_compl_singleton_iff.mpr self_notMem_Ioi)
  exact h1.smul (gm_continuous δ).continuousOn

private theorem gm_deriv_hasDerivAt (δ : ℝ) {s : ℂ} (hs : (1 / 4 : ℝ) < s.re)
    (hs1 : s.re < 3 / 4) :
    HasDerivAt (mellin (fun t : ℝ => log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))))
      (mellin (fun t : ℝ => log t •
        (log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t)))) s) s := by
  refine (mellin_hasDerivAt_of_isBigO_rpow
    ((gm_log_continuousOn δ).locallyIntegrableOn measurableSet_Ioi) ?_ hs1 ?_ hs).2
  · have h := isBigO_rpow_top_log_smul (E := ℂ) (show (3 / 4 : ℝ) < 1 by norm_num)
      (gm_bigO_top δ)
    simpa only [neg_mul] using h
  · have h := isBigO_rpow_zero_log_smul (E := ℂ) (show (0 : ℝ) < 1 / 4 by norm_num)
      (gm_bigO_zero δ)
    simpa only [neg_mul] using h

private lemma gm_differentiableAt (δ : ℝ) {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    DifferentiableAt ℂ (gaussianMellin δ) s :=
  (gm_hasDerivAt δ hs hs1).differentiableAt

private lemma gm_differentiableAt_deriv (δ : ℝ) {s : ℂ} (hs : (1 / 4 : ℝ) < s.re)
    (hs1 : s.re < 3 / 4) :
    DifferentiableAt ℂ (deriv (gaussianMellin δ)) s := by
  have h2 : DifferentiableAt ℂ
      (mellin (fun t : ℝ => log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t)))) s :=
    (gm_deriv_hasDerivAt δ (s := s) hs hs1).differentiableAt
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).and
      (isOpen_lt Complex.continuous_re continuous_const)
  have hcongr : deriv (gaussianMellin δ) =ᶠ[𝓝 s]
      mellin (fun t : ℝ => log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) := by
    filter_upwards [hopen.mem_nhds
      (show s ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} from ⟨by linarith, by linarith⟩)]
      with z hz
    exact (gm_hasDerivAt δ hz.1 hz.2).deriv
  exact h2.congr_of_eventuallyEq hcongr

private lemma gm_deriv_continuousAt (δ : ℝ) (t : ℝ) :
    ContinuousAt (fun u : ℝ => deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)) t := by
  have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by simp
  have hd : DifferentiableAt ℂ (deriv (gaussianMellin δ))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) :=
    gm_differentiableAt_deriv δ (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  have h1 : Tendsto (fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) (𝓝 t)
      (𝓝 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto t).mul_const Complex.I).const_add _
  exact hd.continuousAt.tendsto.comp h1

private lemma gm_deriv_continuous (δ : ℝ) :
    Continuous (fun u : ℝ => deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)) :=
  continuous_iff_continuousAt.mpr (gm_deriv_continuousAt δ)

private lemma deriv_norm_le (δ t : ℝ) :
    |deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t| ≤
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I with hsdef
  set γ : ℝ → ℂ := fun u => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) with hγdef
  set F : ℝ → ℝ := fun u => ‖γ u‖ with hFdef
  have hsre : s.re = (1 / 2 : ℝ) := by simp [hsdef]
  have hGd : DifferentiableAt ℂ (gaussianMellin δ) s :=
    gm_differentiableAt δ (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
  have hγd : HasDerivAt γ (Complex.I • deriv (gaussianMellin δ) s) t := by
    have h0 : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
    have hlin : HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) Complex.I t := by
      have h := (h0.mul_const Complex.I).const_add (1 / 2 : ℂ)
      simpa using h
    exact hGd.hasDerivAt.scomp t hlin
  by_cases hd : DifferentiableAt ℝ F t
  · have hFd : HasDerivAt F (deriv F t) t := hd.hasDerivAt
    have h1 : Tendsto (fun h : ℝ => |h⁻¹ • (F (t + h) - F t)|) (𝓝[≠] 0) (𝓝 |deriv F t|) :=
      hFd.tendsto_slope_zero.abs
    have h2 : Tendsto (fun h : ℝ => ‖h⁻¹ • (γ (t + h) - γ t)‖) (𝓝[≠] 0)
        (𝓝 ‖Complex.I • deriv (gaussianMellin δ) s‖) := hγd.tendsto_slope_zero.norm
    have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h⁻¹ • (F (t + h) - F t)| ≤ ‖h⁻¹ • (γ (t + h) - γ t)‖ := by
      filter_upwards with h
      have hb : |F (t + h) - F t| ≤ ‖γ (t + h) - γ t‖ := by
        have hbl := abs_norm_sub_norm_le (γ (t + h)) (γ t)
        simpa only [hFdef] using hbl
      have hnorm : ‖h⁻¹ • (γ (t + h) - γ t)‖ = |h|⁻¹ * ‖γ (t + h) - γ t‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv]
      calc |h⁻¹ • (F (t + h) - F t)| = |h|⁻¹ * |F (t + h) - F t| := by
            simp only [smul_eq_mul, abs_mul, abs_inv]
        _ ≤ |h|⁻¹ * ‖γ (t + h) - γ t‖ := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ‖h⁻¹ • (γ (t + h) - γ t)‖ := hnorm.symm
    have key : |deriv F t| ≤ ‖Complex.I • deriv (gaussianMellin δ) s‖ :=
      le_of_tendsto_of_tendsto h1 h2 hev
    simpa only [norm_smul, Complex.norm_I, one_mul] using key
  · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
    exact norm_nonneg _

private lemma book_error_nonneg (q : ℕ) [NeZero q] {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ 0.15 * log ((q : ℝ) * t) + 3.389 := by
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqt : (1 : ℝ) ≤ (q : ℝ) * t := by nlinarith
  have hl : 0 ≤ log ((q : ℝ) * t) := log_nonneg hqt
  nlinarith

/-- LEAF: the error integral step of the proof of Lemma 16.9, page 431, the bound
`∫ f'(T) (N(T, χ) - main) dT = O*(∫ |f'(T)| g_χ(T) dT)`, together with `|f'| ≤ |G_δ'|` used in
display 16.26, page 434: for `f t = |G_δ (1/2 + i t)|` one has `|f'(t)| ≤ |G_δ'(1/2 + i t)|`
wherever `f` is differentiable, and `deriv f t = 0` elsewhere.  The hypothesis is the bound of
display 3.95 on `[1, T]`.  Class MEDIUM. -/
theorem error_integral_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T c : ℝ) (hT : 1 ≤ T)
    (hR : ∀ t ∈ Set.Icc (1 : ℝ) T,
      |(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
        t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))| ≤
        0.15 * log ((q : ℝ) * t) + 3.389) :
    -(∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
            t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) ≤
      ∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389) := by
  set F : ℝ → ℝ := fun u => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖ with hF
  set G : ℝ → ℝ := fun t => 0.15 * log ((q : ℝ) * t) + 3.389 with hG
  set N : ℝ → ℝ := fun t => (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
      t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)) with hN
  set K : ℝ → ℝ := fun t => ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ * G t
    with hK
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hGnn : ∀ t ∈ Set.Icc (1 : ℝ) T, 0 ≤ G t := by
    intro t ht
    have := book_error_nonneg q ht.1
    simpa only [hG] using this
  have hKint : IntervalIntegrable K volume (1 : ℝ) T := by
    have h1 : Continuous
        (fun t : ℝ => ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖) :=
      (gm_deriv_continuous δ).norm
    have h2 : ContinuousOn G (Set.uIcc (1 : ℝ) T) := by
      have hlog : ContinuousOn (fun t : ℝ => log ((q : ℝ) * t)) (Set.uIcc (1 : ℝ) T) :=
        ContinuousOn.log (by fun_prop) (by
          intro t ht
          have ht1 : (1 : ℝ) ≤ t := (Set.uIcc_of_le hT ▸ ht : t ∈ Set.Icc (1:ℝ) T).1
          have hqt : (q : ℝ) * t ≠ 0 := by
            have : (1 : ℝ) ≤ (q : ℝ) * t := by nlinarith
            linarith
          exact hqt)
      have hm : ContinuousOn (fun t : ℝ => 0.15 * log ((q : ℝ) * t)) (Set.uIcc (1 : ℝ) T) :=
        ContinuousOn.congr (continuousOn_const.mul hlog) (fun t _ => rfl)
      have hsum : ContinuousOn (fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389)
          (Set.uIcc (1 : ℝ) T) :=
        ContinuousOn.congr (hm.add continuousOn_const) (fun t _ => rfl)
      simpa only [hG] using hsum
    have hKc : ContinuousOn
        (fun t : ℝ => ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ * G t)
        (Set.uIcc (1 : ℝ) T) := h1.continuousOn.mul h2
    simpa only [hK] using hKc.intervalIntegrable
  have hle : ∀ t ∈ Set.Icc (1 : ℝ) T, |deriv F t * N t| ≤ K t := by
    intro t ht
    have h1 : |deriv F t| ≤
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ := by
      simpa only [hF] using deriv_norm_le δ t
    have h2 : |N t| ≤ G t := by simpa only [hN, hG] using hR t ht
    have h3 : (0 : ℝ) ≤ ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ :=
      norm_nonneg _
    have := mul_le_mul h1 h2 (abs_nonneg _) h3
    simpa only [hK, abs_mul] using this
  by_cases hint : IntervalIntegrable (fun t : ℝ => deriv F t * N t) volume (1 : ℝ) T
  · have habs : IntervalIntegrable (fun t : ℝ => |deriv F t * N t|) volume (1 : ℝ) T :=
      hint.abs
    calc -(∫ t in (1 : ℝ)..T, deriv F t * N t)
        ≤ |∫ t in (1 : ℝ)..T, deriv F t * N t| := by
          simpa using le_abs_self (-(∫ t in (1 : ℝ)..T, deriv F t * N t))
      _ ≤ ∫ t in (1 : ℝ)..T, |deriv F t * N t| :=
          intervalIntegral.abs_integral_le_integral_abs hT
      _ ≤ ∫ t in (1 : ℝ)..T, K t := intervalIntegral.integral_mono_on hT habs hKint hle
  · rw [intervalIntegral.integral_undef hint, neg_zero]
    exact intervalIntegral.integral_nonneg hT
      (fun t ht => mul_nonneg (norm_nonneg _) (hGnn t ht))

/-- The faithful assembly of the three leaves: the bound of `positive_mass_norm_sum_integral`
plus the boundary term at height `T`, namely `G T * g T`, which integration by parts on `[1, T]`
leaves and which the parent statement omits; see the module doc.  Sorry free given the leaves. -/
theorem positive_mass_norm_sum_integral_endpoint_of_leaves (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
  obtain ⟨c, hc⟩ := zero_count_error_bound q χ hχ
  rw [stieltjes_positive_zero_sum q χ δ T c hT hzeros]
  have hE := error_integral_le q χ δ T c hT (fun t ht => hc t ht.1)
  have hTb := abs_le.mp (hc T hT)
  have h1b := abs_le.mp (hc 1 le_rfl)
  have hGT : 0 ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ := norm_nonneg _
  have hG1eq : ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ := by
    simp only [Complex.ofReal_one, one_mul]
  have hG1 : 0 ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ := norm_nonneg _
  rw [hG1eq]
  simp only [mul_one] at h1b ⊢
  nlinarith [mul_le_mul_of_nonneg_left hTb.2 hGT, mul_le_mul_of_nonneg_left h1b.1 hG1]

end LeanLab.HelfgottMajor.Decomp431a
