import LeanLab.HelfgottMajor.Lemma43Zeros123

/-!
Route burst 2026-11-12, step gaussian_explicit_estimate p4, leaf tail_mass_of_corollary.
P0014 Helfgott, Major arcs for Goldbach's problem, Lemma 4.3 pages 37 and 38, Lemma 4.5 pages 40
to 42, and the tail terms of display 4.43 on page 43.

This file gives the CORRECTED TRUE FORM of the zero sum step of Lemma 4.5, displays 4.33 to 4.35,
in closed form. It evaluates the two sided Stieltjes bound of Lemma43Zeros123 by the integration
by parts of displays 4.27 and 4.28 on page 38, keeping the boundary term f(y) g(y) that the
remark after 4.28 drops. The result is

  sum over zeros with abs Im above T of abs F_δ(ρ)
    ≤ 4.226 (2 I_exp + 2 I_gauss + (log(qT) + 35.4)(e^(-0.1598 T) + e^(-0.1065 (T/(π abs δ))²)))

where I_exp and I_gauss are exactly the integrals of display 4.35, bounded in 4.36 and 4.41.
The printed Lemma 4.5 has 1 I_exp + 1 I_gauss and no boundary term. Three QUESTIONs, recorded in
research/burst-20261112c, explain the difference:
1. Page 38, remark after 4.28: f(y) g(y) minus the integral of f' g equals 2 f(y) g(y) plus the
   integral of f g', not 0.5 times the integral of f(T)/T.
2. Page 38, third line of the first display: N⁺ = N/2 holds for real χ only.
3. Page 41, display 4.33: the pairing of ρ with 1 − ρ holds for real χ only.
Nothing here closes SplitGaussian123.tail_mass_of_corollary, which keeps its printed statement.
CONDITIONAL ON the shared lab leaf ZeroCount1623.book_zero_count, and on Corollary 3.2 either as
the hypothesis hcor or as the open leaf SplitGaussian123.corollary_3_2_k0.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.TailMass123Corrected
open Real MeasureTheory Set Filter Topology
open LeanLab.HelfgottMajor.SplitGaussian123 LeanLab.HelfgottMajor.Lemma43Zeros123
open LeanLab.HelfgottMajor.TailIntegral123

/-! ## The count bound of display 4.26 and its derivative, twice the density of display 4.35 -/

/-- PROVED. P0014 page 38, display 4.28: the derivative in t of the bound that display 4.26
gives for N(t) − N(T) is (1/π) log(qt/2π) + 0.5/t, twice the density of display 4.35. -/
theorem countBound_hasDerivAt (q : ℕ) [NeZero q] (T t : ℝ) (ht : 0 < t) :
    HasDerivAt (countBound q T) (2 * countDensity q t) t := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h1 : HasDerivAt (fun s : ℝ => (q : ℝ) * s / (2 * π * exp 1))
      ((q : ℝ) / (2 * π * exp 1)) t := by
    simpa using ((hasDerivAt_id t).const_mul (q : ℝ)).div_const (2 * π * exp 1)
  have h2 : HasDerivAt (fun s : ℝ => log ((q : ℝ) * s / (2 * π * exp 1)))
      ((q : ℝ) / (2 * π * exp 1) / ((q : ℝ) * t / (2 * π * exp 1))) t :=
    h1.log (by positivity)
  have h3 : HasDerivAt (fun s : ℝ => s / π) (1 / π) t := by
    simpa using (hasDerivAt_id t).div_const π
  have h4 : HasDerivAt (fun s : ℝ => s / π * log ((q : ℝ) * s / (2 * π * exp 1)))
      (1 / π * log ((q : ℝ) * t / (2 * π * exp 1)) +
        t / π * ((q : ℝ) / (2 * π * exp 1) / ((q : ℝ) * t / (2 * π * exp 1)))) t :=
    h3.mul h2
  have h5 : HasDerivAt (fun s : ℝ => (q : ℝ) * s) (q : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (q : ℝ)
  have h6 : HasDerivAt (fun s : ℝ => 0.5 * log ((q : ℝ) * s) + 17.7)
      (0.5 * ((q : ℝ) / ((q : ℝ) * t))) t :=
    ((h5.log (by positivity)).const_mul (0.5 : ℝ)).add_const 17.7
  have h7 : HasDerivAt (fun s : ℝ => s / π * log ((q : ℝ) * s / (2 * π * exp 1)) +
      (0.5 * log ((q : ℝ) * s) + 17.7) -
      (T / π * log (q * T / (2 * π * exp 1)) - (0.5 * log (q * T) + 17.7)))
      (1 / π * log ((q : ℝ) * t / (2 * π * exp 1)) +
        t / π * ((q : ℝ) / (2 * π * exp 1) / ((q : ℝ) * t / (2 * π * exp 1))) +
        0.5 * ((q : ℝ) / ((q : ℝ) * t))) t :=
    (h4.add h6).sub_const _
  have hlog : log ((q : ℝ) * t / (2 * π * exp 1)) = log ((q : ℝ) * t / (2 * π)) - 1 := by
    rw [show (q : ℝ) * t / (2 * π * exp 1) = (q : ℝ) * t / (2 * π) / exp 1 by field_simp,
      Real.log_div (by positivity) (exp_ne_zero 1), Real.log_exp]
  have h8 : HasDerivAt (countBound q T) _ t := h7
  convert h8 using 1
  unfold countDensity
  rw [hlog]
  field_simp
  ring

/-- PROVED. At t = T the count bound is twice the error term g of display 4.25, page 37. -/
theorem countBound_self (q : ℕ) (T : ℝ) : countBound q T T = log (q * T) + 35.4 := by
  unfold countBound
  ring

/-- PROVED. The density of display 4.35 grows at most quadratically. -/
lemma countDensity_abs_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t) :
    |countDensity q t| ≤ ((q : ℝ) + 8) * (1 + t ^ 2) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hpi := pi_gt_three
  have hpi4 := pi_lt_four
  have hqt : 1 ≤ (q : ℝ) * t := by nlinarith
  have hx : 0 < (q : ℝ) * t / (2 * π) := by positivity
  have hl := abs_log_le _ hx
  have h1 : (q : ℝ) * t / (2 * π) ≤ q * t := div_le_self (by linarith) (by linarith)
  have h2 : ((q : ℝ) * t / (2 * π))⁻¹ ≤ 8 := by
    rw [inv_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hl' : |log ((q : ℝ) * t / (2 * π))| ≤ q * t + 8 := by linarith
  have h3 : |1 / (2 * π) * log ((q : ℝ) * t / (2 * π))| ≤ q * t + 8 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    have h2pi : 1 / (2 * π) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc 1 / (2 * π) * |log ((q : ℝ) * t / (2 * π))| ≤ 1 * |log ((q : ℝ) * t / (2 * π))| :=
          mul_le_mul_of_nonneg_right h2pi (abs_nonneg _)
      _ ≤ _ := by linarith
  have h4 : |1 / (4 * t)| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one (by positivity)]
    linarith
  unfold countDensity
  refine (abs_add_le _ _).trans ?_
  nlinarith [sq_nonneg (t - 1), mul_nonneg (by linarith : (0 : ℝ) ≤ q) (sq_nonneg (t - 1))]

/-! ## Integrability and decay against a weight exp(−b t^p) -/

/-- PROVED. A measurable function of at most quadratic growth is integrable on (T, ∞) against
exp(−b t^p). Used for the two branches of display 4.34 against the density of display 4.35. -/
lemma weight_mul_integrable (p b T K : ℝ) (hp : 0 < p) (hb : 0 < b) (hT : 0 ≤ T)
    (h : ℝ → ℝ) (hm : Measurable h) (hK : ∀ t, T < t → |h t| ≤ K * (1 + t ^ 2)) :
    IntegrableOn (fun t => exp (-b * t ^ p) * h t) (Ioi T) := by
  have h0 := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := p) (b := b) (by norm_num)
    hp hb).mono_set (Ioi_subset_Ioi hT)
  have h2 := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := p) (b := b) (by norm_num)
    hp hb).mono_set (Ioi_subset_Ioi hT)
  have hmaj := (h0.add h2).const_mul K
  apply hmaj.mono'
  · have hm' : Measurable (fun t : ℝ => exp (-b * t ^ p) * h t) :=
      (Real.measurable_exp.comp ((measurable_id.pow_const p).const_mul (-b))).mul hm
    exact hm'.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change T < t at ht
    have hb' := hK t ht
    simp only [Pi.add_apply, Real.rpow_zero, Real.rpow_two, one_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    calc exp (-b * t ^ p) * |h t| ≤ exp (-b * t ^ p) * (K * (1 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left hb' (exp_pos _).le
      _ = K * (exp (-b * t ^ p) + t ^ 2 * exp (-b * t ^ p)) := by ring

/-- PROVED. The boundary term at infinity in the partial summation of page 38 vanishes: the count
bound of display 4.26 times a function of exponential decay tends to 0. -/
lemma count_mul_tendsto (q : ℕ) [NeZero q] (T : ℝ) (hT : 1 ≤ T) (f : ℝ → ℝ) (b : ℝ)
    (hb : 0 < b) (hfb : ∀ᶠ t in atTop, |f t| ≤ exp (-b * t)) :
    Tendsto (fun t => countBound q T t * f t) atTop (𝓝 0) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 b hb
  have hg : Tendsto (fun t : ℝ => countConst q T *
      (t ^ (0 : ℝ) * exp (-b * t) + t ^ (2 : ℝ) * exp (-b * t))) atTop (𝓝 0) := by
    simpa using (h0.add h2).const_mul (countConst q T)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hfb, eventually_ge_atTop T] with t hft htT
  have hcb := countBound_abs_le q T t hT htT
  have hnn : 0 ≤ countConst q T * (1 + t ^ 2) := (abs_nonneg _).trans hcb
  rw [Real.norm_eq_abs, abs_mul, Real.rpow_zero, Real.rpow_two, one_mul]
  calc |countBound q T t| * |f t| ≤ countConst q T * (1 + t ^ 2) * exp (-b * t) :=
        mul_le_mul hcb hft (abs_nonneg _) hnn
    _ = _ := by ring

/-! ## Lemma 4.3 by parts, with the boundary term kept -/

/-- PROVED. P0014 page 38, displays 4.27 and 4.28 with the boundary term kept: if f has
derivative −φ and decays, then the integral of φ against the bound of N(t) − N(T) from display
4.26 equals twice the integral of f against the density of display 4.35 plus the boundary term
2 f(T) g(T), where g(T) = 0.5 log(qT) + 17.7 is display 4.25. The remark after 4.28 on page 38
omits this boundary term; see the QUESTION in the note. -/
theorem count_by_parts (q : ℕ) [NeZero q] (T : ℝ) (hT : 1 ≤ T) (f φ : ℝ → ℝ)
    (hf : ∀ t, T ≤ t → HasDerivAt f (-φ t) t)
    (hint1 : IntegrableOn (fun t => φ t * countBound q T t) (Ioi T))
    (hint2 : IntegrableOn (fun t => f t * countDensity q t) (Ioi T))
    (hlim : Tendsto (fun t => countBound q T t * f t) atTop (𝓝 0)) :
    ∫ t in Ioi T, φ t * countBound q T t =
      2 * (∫ t in Ioi T, f t * countDensity q t) + f T * (log (q * T) + 35.4) := by
  have hT0 : 0 < T := by linarith
  have hu : ∀ x ∈ Ioi T, HasDerivAt (countBound q T) ((fun t => 2 * countDensity q t) x) x :=
    fun x hx => countBound_hasDerivAt q T x (hT0.trans hx)
  have hv : ∀ x ∈ Ioi T, HasDerivAt (fun t => -f t) (φ x) x := by
    intro x hx
    have h := (hf x (le_of_lt hx)).neg
    rw [neg_neg] at h
    exact h
  have huv' : IntegrableOn (countBound q T * φ) (Ioi T) := by
    refine hint1.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [mul_comm]
  have hu'v : IntegrableOn ((fun t => 2 * countDensity q t) * fun t => -f t) (Ioi T) := by
    have h2 : IntegrableOn (fun t => -2 * (f t * countDensity q t)) (Ioi T) :=
      hint2.const_mul (-2)
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have hzero : Tendsto (countBound q T * fun t => -f t) (𝓝[>] T)
      (𝓝 (countBound q T T * -f T)) := by
    have hc1 : ContinuousAt (countBound q T) T := (countBound_hasDerivAt q T T hT0).continuousAt
    have hc2 : ContinuousAt (fun t => -f t) T := (hf T le_rfl).continuousAt.neg
    exact (hc1.mul hc2).tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (countBound q T * fun t => -f t) atTop (𝓝 0) := by
    have := hlim.neg
    simp only [neg_zero] at this
    refine this.congr (fun t => ?_)
    simp only [Pi.mul_apply]
    ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
  have e1 : (∫ t in Ioi T, φ t * countBound q T t) = ∫ t in Ioi T, countBound q T t * φ t := by
    congr 1; ext t; ring
  have e2 : (∫ t in Ioi T, (fun t => 2 * countDensity q t) t * (fun t => -f t) t) =
      -(2 * ∫ t in Ioi T, f t * countDensity q t) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1; ext t; ring
  rw [e1, key, e2, countBound_self]
  ring

/-- PROVED. The exponential branch of display 4.34 through Lemma 4.3 with the boundary term:
the integral of c e^(−ct) against the count bound equals twice the integral of display 4.35 for
e^(−ct), plus e^(−cT)(log(qT) + 35.4). -/
theorem exp_count_integral_eq (q : ℕ) [NeZero q] (c T : ℝ) (hc : 0 < c) (hT : 1 ≤ T) :
    ∫ t in Ioi T, c * exp (-c * t) * countBound q T t =
      2 * (∫ t in Ioi T, exp (-c * t) * countDensity q t) +
        exp (-c * T) * (log (q * T) + 35.4) := by
  apply count_by_parts q T hT (fun t => exp (-c * t)) (fun t => c * exp (-c * t))
  · intro t _
    have h1 : HasDerivAt (fun s : ℝ => -c * s) (-c) t := by
      simpa using (hasDerivAt_id t).const_mul (-c)
    convert h1.exp using 1
    ring
  · exact exp_count_integrable q c T hc hT
  · have h := weight_mul_integrable 1 c T ((q : ℝ) + 8) one_pos hc (by linarith)
      (fun t => countDensity q t) (by unfold countDensity; fun_prop)
      (fun t ht => countDensity_abs_le q t (hT.trans ht.le))
    simpa only [Real.rpow_one] using h
  · apply count_mul_tendsto q T hT _ c hc
    filter_upwards with t
    rw [abs_of_pos (exp_pos _)]

/-- PROVED. The Gaussian branch of display 4.34 through Lemma 4.3 with the boundary term. -/
theorem gauss_count_integral_eq (q : ℕ) [NeZero q] (k D T : ℝ) (hk : 0 < k) (hD : 0 < D)
    (hT : 1 ≤ T) :
    ∫ t in Ioi T, gaussDensity k D t * countBound q T t =
      2 * (∫ t in Ioi T, exp (-k * (t / D) ^ 2) * countDensity q t) +
        exp (-k * (T / D) ^ 2) * (log (q * T) + 35.4) := by
  have hb : 0 < k / D ^ 2 := by positivity
  have hexp : ∀ t : ℝ, exp (-k * (t / D) ^ 2) = exp (-(k / D ^ 2) * t ^ (2 : ℝ)) := by
    intro t
    rw [Real.rpow_two, div_pow]
    congr 1
    field_simp
  apply count_by_parts q T hT (fun t => exp (-k * (t / D) ^ 2)) (gaussDensity k D)
  · intro x _
    have h1 : HasDerivAt (fun t => -k * (t / D) ^ 2) (-k * (2 * (x / D) * (1 / D))) x := by
      have := ((hasDerivAt_id x).div_const D).pow 2
      simpa using this.const_mul (-k)
    convert h1.exp using 1
    unfold gaussDensity
    field_simp
  · exact gauss_count_integrable q k D T hk hD hT
  · have h := weight_mul_integrable 2 (k / D ^ 2) T ((q : ℝ) + 8) two_pos hb (by linarith)
      (fun t => countDensity q t) (by unfold countDensity; fun_prop)
      (fun t ht => countDensity_abs_le q t (hT.trans ht.le))
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hexp]
  · apply count_mul_tendsto q T hT _ (k / D ^ 2) hb
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have h1 : -k * (t / D) ^ 2 = -(k / D ^ 2) * t ^ 2 := by
      rw [div_pow]; field_simp
    rw [h1]
    have : t ≤ t ^ 2 := by nlinarith
    nlinarith

/-! ## The corrected Lemma 4.5 and the corrected tail of display 4.43 -/

/-- The boundary term of Lemma 4.3 for the function f of display 4.34 without its constant 4.226:
(log(qT) + 35.4) times the two branches at T, that is 2 g(T) of display 4.25 times the envelope.
The Gaussian branch is absent at zero shift. P0014 page 38, the term f(y) g(y) of display 4.27. -/
noncomputable def boundaryTerm (q : ℕ) (δ T : ℝ) : ℝ :=
  (log (q * T) + 35.4) *
    (exp (-0.1598 * T) + if δ = 0 then 0 else exp (-0.1065 * (T / (π * |δ|)) ^ 2))

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count and on hcor, the k = 0 case of
Corollary 3.2. The corrected true form of P0014 Lemma 4.5, page 41, displays 4.33 to 4.35: the
Mellin mass of the zeros with abs Im above T is summable and at most 4.226 times twice the two
integrals of display 4.35 plus the boundary term. The factor 2 replaces the pairing of display
4.33, which holds for real χ only, and the boundary term is the one the remark after display
4.28 on page 38 drops. Compare SplitGaussian123.tail_mass_of_corollary, the printed form. -/
theorem tail_mass_corrected {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : HighIdx χ T => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : HighIdx χ T, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (2 * expTailIntegral q T + 2 * gaussianTailIntegral q δ T +
        boundaryTerm q δ T) := by
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  obtain ⟨hs, hb⟩ := tail_mass_two_sided χ hχ δ T hT hcor
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  rw [exp_count_integral_eq q 0.1598 T (by norm_num) hT1]
  unfold expTailIntegral gaussianTailIntegral boundaryTerm
  by_cases hδ : δ = 0
  · simp only [hδ, ite_true]
    ring
  · have hD : 0 < π * |δ| := mul_pos pi_pos (abs_pos.mpr hδ)
    simp only [hδ, ite_false]
    rw [gauss_count_integral_eq q 0.1065 (π * |δ|) T (by norm_num) hD hT1]
    ring

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count and on hcor. The corrected Lemma 4.5 in
closed form, with the integral bounds of displays 4.36 and 4.41 on pages 41 and 42:
the Mellin mass above T is at most
log(qT/2π)(8.657 e^(−0.1598 T) + 1.588 abs δ e^(−0.1065 (T/(π abs δ))²)) plus 4.226 times the
boundary term. The printed Lemma 4.5 has 4.329 and 0.802 and no boundary term. -/
theorem tail_mass_corrected_closed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : HighIdx χ T => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : HighIdx χ T, mellinMassTerm χ δ ρ.val) ≤
      log (q * T / (2 * π)) *
        (8.657 * exp (-0.1598 * T) +
          1.588 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
      4.226 * boundaryTerm q δ T := by
  obtain ⟨hs, hm⟩ := tail_mass_corrected χ hχ δ T hT hcor
  refine ⟨hs, hm.trans ?_⟩
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have he := exp_integral_bound q T hT100
  have hg : gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
    by_cases hδ : δ = 0
    · simp [hδ, gaussianTailIntegral]
    · exact gaussian_integral_bound q δ T hδ hT
  have hlog : 0 ≤ log ((q : ℝ) * T / (2 * π)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pi_lt_four]
  nlinarith [mul_nonneg hlog (exp_pos (-0.1598 * T)).le,
    mul_nonneg hlog (mul_nonneg (abs_nonneg δ)
      (exp_pos (-0.1065 * (T / (π * |δ|)) ^ 2)).le)]

/-- PROVED, CONDITIONAL ON the open leaves SplitGaussian123.corollary_3_2_k0 and
ZeroCount1623.book_zero_count only. The corrected true form of the tail terms of display 4.43,
P0014 page 43, proof of Proposition 4.6: the zeros above T contribute at most
(log(qT/2π)(8.657 e^(−0.1598 T) + 1.588 abs δ e^(−0.1065 (T/(π abs δ))²)) + 4.226 boundary) x.
It does not use SplitGaussian123.tail_mass_of_corollary. Compare SplitGaussian123.high_zero_bound,
the printed form with 4.329 and 0.802 and no boundary term. -/
theorem high_zero_bound_corrected (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ‖highZeros χ δ x T‖ ≤
      (log (q * T / (2 * π)) *
        (8.657 * exp (-0.1598 * T) +
          1.588 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
      4.226 * boundaryTerm q δ T) * x := by
  obtain ⟨hs, hb⟩ := tail_mass_corrected_closed χ hχ δ T hT
    (fun s h0 h1 hτ => corollary_3_2_k0 δ s h0 h1 hτ)
  exact high_zero_bound_of_mass χ δ x T _ hx hs hb

end LeanLab.HelfgottMajor.TailMass123Corrected
