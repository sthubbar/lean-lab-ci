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

/-- The exponential `e` has norm one. -/
private lemma norm_e_one (x : ℝ) : ‖e x‖ = 1 := by
  rw [LeanLab.HelfgottArcs.e, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The norm of the Gaussian kernel defining `gaussianMellin`. -/
private lemma gaussianKernel_norm (δ t : ℝ) :
    ‖(exp (-t ^ 2 / 2) : ℂ) * e (δ * t)‖ = exp (-t ^ 2 / 2) := by
  rw [norm_mul, norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]

/-- The Gaussian kernel defining `gaussianMellin` is continuous. -/
private lemma gaussianKernel_continuous (δ : ℝ) :
    Continuous fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t) := by
  have h1 : Continuous fun t : ℝ => ((exp (-t ^ 2 / 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
  have h2 : Continuous fun t : ℝ => e (δ * t) := by
    unfold LeanLab.HelfgottArcs.e
    fun_prop
  exact h1.mul h2

/-- `gaussianMellin δ` is complex differentiable on the half plane `re s > 0`. -/
private lemma gaussianMellin_differentiableAt (δ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (gaussianMellin δ) s := by
  have hfc : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t))
      (Set.Ioi 0) :=
    (gaussianKernel_continuous δ).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) =O[Filter.atTop]
      (fun t : ℝ => Real.exp (-1 * t)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
    rw [gaussianKernel_norm, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, one_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbot : (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with t
    rw [gaussianKernel_norm]
    have hpow : ‖t ^ (-(0 : ℝ))‖ = 1 := by simp
    rw [hpow, mul_one]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  exact mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := 0) one_pos
    hfc htop hbot (by simpa using hs)

/-- `gaussianMellin δ` is complex differentiable on the half plane `re s > 0`, as a set. -/
private lemma differentiableOn_gaussianMellin (δ : ℝ) :
    DifferentiableOn ℂ (gaussianMellin δ) {z : ℂ | 0 < z.re} :=
  fun _ hz => (gaussianMellin_differentiableAt δ hz).differentiableWithinAt

/-- The derivative of `gaussianMellin δ` is continuous on the half plane `re s > 0`. -/
private lemma continuousOn_deriv_gaussianMellin (δ : ℝ) :
    ContinuousOn (deriv (gaussianMellin δ)) {z : ℂ | 0 < z.re} :=
  ((differentiableOn_gaussianMellin δ).deriv
    (isOpen_lt continuous_const Complex.continuous_re)).continuousOn

/-- The norm of a differentiable curve has derivative bounded by the norm of the derivative of
the curve. -/
private lemma abs_deriv_norm_le {G : ℝ → ℂ} {g' : ℂ} {t : ℝ} (hG : HasDerivAt G g' t) :
    |deriv (fun u : ℝ => ‖G u‖) t| ≤ ‖g'‖ := by
  by_cases h0 : G t = 0
  · have hmin : IsLocalMin (fun u : ℝ => ‖G u‖) t := by
      filter_upwards with u
      rw [h0, norm_zero]
      exact norm_nonneg _
    rw [hmin.deriv_eq_zero, abs_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖G t‖ := norm_pos_iff.mpr h0
    have hne : ‖G t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
    have hsq : HasDerivAt (fun u : ℝ => ‖G u‖ ^ 2) (2 * inner ℝ (G t) g') t := hG.norm_sq
    have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (‖G u‖ ^ 2))
        ((1 / (2 * Real.sqrt (‖G t‖ ^ 2))) * (2 * inner ℝ (G t) g')) t :=
      (Real.hasDerivAt_sqrt hne).comp t hsq
    have hfun : (fun u : ℝ => Real.sqrt (‖G u‖ ^ 2)) = fun u : ℝ => ‖G u‖ := by
      funext u
      exact Real.sqrt_sq (norm_nonneg _)
    have hsv : Real.sqrt (‖G t‖ ^ 2) = ‖G t‖ := Real.sqrt_sq (norm_nonneg _)
    have hderiv : deriv (fun u : ℝ => ‖G u‖) t = inner ℝ (G t) g' / ‖G t‖ := by
      rw [← hfun, hsqrt.deriv, hsv]
      field_simp
    rw [hderiv, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |inner ℝ (G t) g'| ≤ ‖G t‖ * ‖g'‖ := abs_real_inner_le_norm _ _
      _ = ‖g'‖ * ‖G t‖ := by ring

/-- The derivative along the vertical line of `gaussianMellin δ`. -/
private lemma hasDerivAt_gaussianMellin_line (δ : ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I))
      (deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) * Complex.I) t := by
  have hz : 0 < ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re := by
    simp
  have hF : DifferentiableAt ℂ (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) :=
    gaussianMellin_differentiableAt δ hz
  have hγ : HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) Complex.I t := by
    have h1 : HasDerivAt (Complex.ofRealCLM : ℝ → ℂ) (Complex.ofRealCLM 1) t :=
      Complex.ofRealCLM.hasDerivAt
    have h2 := h1.mul_const Complex.I
    simpa [Complex.ofRealCLM_apply, one_mul] using h2.const_add (1 / 2 : ℂ)
  have hcomp := hF.hasDerivAt.scomp (x := t)
    (h := fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) hγ
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using hcomp

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
  set g : ℝ → ℝ := fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389 with hg
  set h : ℝ → ℝ := fun t : ℝ => ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
    with hh
  set f : ℝ → ℝ := fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖ with hf
  set Rf : ℝ → ℝ := fun t : ℝ => (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
    t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)) with hRf
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq
  have hg_nonneg : ∀ t ∈ Set.Icc (1 : ℝ) T, 0 ≤ g t := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have hqt : (1 : ℝ) ≤ (q : ℝ) * t := by nlinarith
    have hlog : 0 ≤ log ((q : ℝ) * t) := Real.log_nonneg hqt
    simp only [hg]
    nlinarith
  have hcont_g : ContinuousOn g (Set.Icc (1 : ℝ) T) := by
    have hlog : ContinuousOn (fun t : ℝ => log ((q : ℝ) * t)) (Set.Icc (1 : ℝ) T) := by
      apply ContinuousOn.log (by fun_prop)
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1
      have hpos : (0 : ℝ) < (q : ℝ) * t := by nlinarith
      exact ne_of_gt hpos
    simp only [hg]
    exact (continuous_const.continuousOn.mul hlog).add continuous_const.continuousOn
  have hcont_h : ContinuousOn h (Set.Icc (1 : ℝ) T) := by
    have hmaps : Set.MapsTo (fun t : ℝ => (1 / 2 : ℂ) + (t : ℝ) * Complex.I)
        (Set.Icc (1 : ℝ) T) {z : ℂ | 0 < z.re} := by
      intro t ht
      simp
    have hc : ContinuousOn
        (fun t : ℝ => deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I))
        (Set.Icc (1 : ℝ) T) :=
      (continuousOn_deriv_gaussianMellin δ).comp (by fun_prop) hmaps
    simp only [hh]
    exact hc.norm
  have hbound : ∀ t ∈ Set.Icc (1 : ℝ) T, |deriv f t| ≤ h t := by
    intro t _
    have hGd := hasDerivAt_gaussianMellin_line δ t
    have hle := abs_deriv_norm_le hGd
    have hnorm : ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) * Complex.I‖
        = h t := by
      simp only [hh, norm_mul, Complex.norm_I, mul_one]
    rw [hnorm] at hle
    simpa only [hf] using hle
  by_cases hint : IntervalIntegrable (fun t : ℝ => deriv f t * Rf t) MeasureTheory.volume 1 T
  · have hle : ∀ t ∈ Set.Icc (1 : ℝ) T, |deriv f t * Rf t| ≤ h t * g t := by
      intro t ht
      have h1 : |deriv f t| ≤ h t := hbound t ht
      have h2 : |Rf t| ≤ g t := hR t ht
      have hh0 : 0 ≤ h t := norm_nonneg _
      have hmul : |deriv f t| * |Rf t| ≤ h t * g t := mul_le_mul h1 h2 (abs_nonneg _) hh0
      simpa only [abs_mul] using hmul
    have hIntK : IntervalIntegrable (fun t : ℝ => h t * g t) MeasureTheory.volume 1 T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT]
      exact hcont_h.mul hcont_g
    have key : -(∫ t in (1 : ℝ)..T, deriv f t * Rf t) ≤ ∫ t in (1 : ℝ)..T, h t * g t :=
      calc -(∫ t in (1 : ℝ)..T, deriv f t * Rf t)
          ≤ |∫ t in (1 : ℝ)..T, deriv f t * Rf t| := neg_le_abs _
        _ ≤ ∫ t in (1 : ℝ)..T, |deriv f t * Rf t| :=
            intervalIntegral.abs_integral_le_integral_abs hT
        _ ≤ ∫ t in (1 : ℝ)..T, h t * g t :=
            intervalIntegral.integral_mono_on hT hint.abs hIntK hle
    simpa only [hh, hg] using key
  · have hzero : (∫ t in (1 : ℝ)..T, deriv f t * Rf t) = 0 :=
      intervalIntegral.integral_undef hint
    rw [hzero, neg_zero]
    exact intervalIntegral.integral_nonneg hT
      (fun t ht => mul_nonneg (norm_nonneg _) (hg_nonneg t ht))


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
