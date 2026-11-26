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

/-- PROVED, a helper for `error_integral_le`: the derivative of `t ↦ ‖G_δ (1/2 + i t)‖` is at most
`‖G_δ' (1/2 + i t)‖` in absolute value, display 16.26, page 434.  AI wrote this proof. -/
theorem errint_deriv_norm_le (δ t : ℝ) :
    |deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t| ≤
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ := by
  set z : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I with hz
  have han : AnalyticAt ℂ (gaussianMellin δ) z :=
    Decomp389b.gaussian_mellin_analyticAt δ _ (by simp [z]) (by simp [z]; norm_num)
  have hlin : HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I) Complex.I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (1 / 2 : ℂ)
  have hc : HasDerivAt (fun w : ℂ => gaussianMellin δ ((1 / 2 : ℂ) + w * Complex.I))
      (deriv (gaussianMellin δ) z * Complex.I) (t : ℂ) :=
    han.differentiableAt.hasDerivAt.comp (t : ℂ) hlin
  have hh : HasDerivAt (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℂ) * Complex.I))
      (deriv (gaussianMellin δ) z * Complex.I) t := hc.comp_ofReal
  have hb : ‖deriv (gaussianMellin δ) z * Complex.I‖ = ‖deriv (gaussianMellin δ) z‖ := by
    simp
  rw [← Real.norm_eq_abs, ← hb]
  apply le_of_forall_pos_le_add
  intro ε hε
  apply norm_deriv_le_of_lip' (by positivity)
  have ho := (hasDerivAt_iff_isLittleO.mp hh).def hε
  filter_upwards [ho] with x hx
  have h1 : |‖gaussianMellin δ ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)‖ -
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖| ≤
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (x : ℂ) * Complex.I) -
        gaussianMellin δ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := abs_norm_sub_norm_le _ _
  have h2 : ‖gaussianMellin δ ((1 / 2 : ℂ) + (x : ℂ) * Complex.I) -
        gaussianMellin δ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖(x - t) • (deriv (gaussianMellin δ) z * Complex.I)‖ + ε * ‖x - t‖ := by
    set A := gaussianMellin δ ((1 / 2 : ℂ) + (x : ℂ) * Complex.I) -
        gaussianMellin δ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
    set B := (x - t) • (deriv (gaussianMellin δ) z * Complex.I)
    calc ‖A‖ = ‖(A - B) + B‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
      _ ≤ ‖B‖ + ε * ‖x - t‖ := by linarith
  rw [norm_smul] at h2
  rw [Real.norm_eq_abs]
  simp only [Real.norm_eq_abs] at h2 ⊢
  nlinarith [abs_nonneg (x - t)]

/-- PROVED, a helper for `error_integral_le`: the error integral bound of the proof of Lemma 16.9,
page 431, for any error function `R` bounded by display 16.21 on `[1, T]`.  AI wrote this proof. -/
theorem errint_general_le (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) (R : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (1 : ℝ) T, |R t| ≤ 0.15 * log ((q : ℝ) * t) + 3.389) :
    -(∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t * R t) ≤
      ∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hcontD : Continuous (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖) := by
    have hpath : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℝ) * Complex.I) := by fun_prop
    apply Continuous.norm
    apply continuous_iff_continuousAt.mpr
    intro t
    have han : AnalyticAt ℂ (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) :=
      Decomp389b.gaussian_mellin_analyticAt δ _ (by simp) (by simp; norm_num)
    exact ContinuousAt.comp (f := fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I)
      (g := deriv (gaussianMellin δ)) han.deriv.continuousAt hpath.continuousAt
  have hcontB : ContinuousOn (fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389)
      (Set.uIcc 1 T) := by
    rw [Set.uIcc_of_le hT]
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    have : (0 : ℝ) < x := by linarith [hx.1]
    positivity
  have hint : IntervalIntegrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * t) + 3.389)) MeasureTheory.volume 1 T :=
    (hcontD.continuousOn.mul hcontB).intervalIntegrable
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hT
    (f := fun t => deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t * R t)
    (Filter.Eventually.of_forall (fun t ht => by
      have hRt := hR t ⟨ht.1.le, ht.2⟩
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (errint_deriv_norm_le δ t) hRt (abs_nonneg _) (norm_nonneg _)))
    hint
  rw [Real.norm_eq_abs] at hbound
  exact (neg_le_abs _).trans hbound

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
          (0.15 * log ((q : ℝ) * t) + 3.389) :=
  errint_general_le q δ T hT _ hR

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
