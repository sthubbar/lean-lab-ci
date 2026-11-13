import LeanLab.HelfgottMajor.SplitGaussian123

/-!
Route burst session 8, 2026-11-12, step gaussian_explicit_estimate p3.
P0014 Helfgott, Major arcs for Goldbach's problem, Lemma 4.3, pages 37 and 38, and Lemma 4.5,
pages 40 and 41: a correct two sided form of the Stieltjes summation of a decreasing function
over the zeros above height T, against the zero count 4.26.

The proof of Lemma 4.3 on page 38 writes the sum of f over zeros above y as minus the integral
of f' against the count N. Here f is written as the integral of φ = −f' from the height to
infinity, and the sum over the zeros with abs Im above T is bounded by the integral of φ against
the upper bound of N(t) − N(T) that display 4.26 gives. No pairing of ρ with 1 − ρ is used and no
cancellation of the error term g is used, so neither QUESTION recorded on display 4.33 and on
page 38 enters. CONDITIONAL ON the shared lab leaf ZeroCount1623.book_zero_count through
ZeroCount1623.arxiv_zero_count, and for the zero shift tail on the hypothesis hcor, the k = 0
case of Corollary 3.2, which is the open leaf SplitGaussian123.corollary_3_2_k0.
The bound obtained is NOT the printed bound of Lemma 4.5: its main term is twice the density of
display 4.35 and it keeps the boundary term. It does not close SplitGaussian123.
tail_mass_of_corollary, whose statement is kept as a QUESTION.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Lemma43Zeros123
open Real MeasureTheory Set Filter
open LeanLab.HelfgottMajor.SplitGaussian123

/-- PROVED. P0014 page 38, first display of the proof of Lemma 4.3, in layer cake form: if each
weight w_i sits at a height a_i above T and f(a) is the integral of φ ≥ 0 over (a, ∞), then the
weighted sum of f(a_i) is at most the integral over (T, ∞) of φ times any upper bound A(t) for
the total weight at heights below t. -/
theorem sum_le_integral_count {ι : Type*} (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (T : ℝ)
    (ha : ∀ i, T < a i) (φ A : ℝ → ℝ) (hφ : ∀ t, T < t → 0 ≤ φ t)
    (hφint : IntegrableOn φ (Ioi T)) (hint : IntegrableOn (fun t => φ t * A t) (Ioi T))
    (hcount : ∀ t, T < t → ∀ S : Finset ι, ∑ i ∈ S.filter (fun i => a i < t), w i ≤ A t) :
    Summable (fun i => w i * ∫ t in Ioi (a i), φ t) ∧
      (∑' i, w i * ∫ t in Ioi (a i), φ t) ≤ ∫ t in Ioi T, φ t * A t := by
  classical
  have hnn : 0 ≤ fun i => w i * ∫ t in Ioi (a i), φ t := by
    intro i
    apply mul_nonneg (hw i)
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact hφ t ((ha i).trans ht)
  have hfin : ∀ S : Finset ι, ∑ i ∈ S, w i * ∫ t in Ioi (a i), φ t ≤
      ∫ t in Ioi T, φ t * A t := by
    intro S
    have hrw : ∀ i ∈ S, w i * ∫ t in Ioi (a i), φ t =
        ∫ t in Ioi T, w i * (Ioi (a i)).indicator φ t := by
      intro i _
      rw [integral_const_mul, setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Ioi_subset_Ioi (ha i).le)]
    have hint_i : ∀ i ∈ S, IntegrableOn (fun t => w i * (Ioi (a i)).indicator φ t) (Ioi T) := by
      intro i _
      exact (hφint.indicator measurableSet_Ioi).const_mul (w i)
    rw [Finset.sum_congr rfl hrw, ← integral_finset_sum S hint_i]
    apply setIntegral_mono_on (integrable_finset_sum S hint_i) hint measurableSet_Ioi
    intro t ht
    have hpt : ∀ i ∈ S, w i * (Ioi (a i)).indicator φ t =
        if a i < t then w i * φ t else 0 := by
      intro i _
      by_cases h : a i < t
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter, ← Finset.sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcount t ht S) (hφ t ht)
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

/-- The zeros in the open strip with abs Im above T, the index of SplitGaussian123.highZeros. -/
abbrev HighIdx {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Type :=
  {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}

/-- The upper bound for N(t) − N(T) given by display 4.26 on page 38, read at t and at T. -/
noncomputable def countBound (q : ℕ) (T t : ℝ) : ℝ :=
  (t / π * log (q * t / (2 * π * exp 1)) + (0.5 * log (q * t) + 17.7)) -
    (T / π * log (q * T / (2 * π * exp 1)) - (0.5 * log (q * T) + 17.7))

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count. P0014 display 4.26, page 38, read at
t and at T: the zeros with T < abs Im below t, with multiplicity, number at most countBound. -/
theorem high_count_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (T t : ℝ) (hT : 1 ≤ T) (ht : T < t) (S : Finset (HighIdx χ T)) :
    ∑ ρ ∈ S.filter (fun ρ => |ρ.val.im| < t),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) ≤ countBound q T t := by
  classical
  set U := (ZeroCount1623.stripZeros_finite χ t).toFinset with hU
  set V := (ZeroCount1623.stripZeros_finite χ T).toFinset with hV
  have hVU : V ⊆ U := by
    intro z hz
    rw [hV, Set.Finite.mem_toFinset] at hz
    rw [hU, Set.Finite.mem_toFinset]
    exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans ht.le⟩
  have hmap : ∑ ρ ∈ S.filter (fun ρ => |ρ.val.im| < t),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) =
      ∑ z ∈ (S.filter (fun ρ => |ρ.val.im| < t)).map (Function.Embedding.subtype _),
        (ZeroCount1623.mult χ z : ℝ) := by
    rw [Finset.sum_map]; rfl
  have hsub : (S.filter (fun ρ => |ρ.val.im| < t)).map (Function.Embedding.subtype _) ⊆
      U \ V := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    rw [Finset.mem_filter] at hρ
    rw [Finset.mem_sdiff, hU, hV, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    refine ⟨⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2.1, hρ.2.le⟩, ?_⟩
    intro h
    have := h.2.2.2
    have := ρ.property.2.2.2
    simp only [Function.Embedding.subtype_apply] at *
    linarith
  have hle : ∑ z ∈ (S.filter (fun ρ => |ρ.val.im| < t)).map (Function.Embedding.subtype _),
      (ZeroCount1623.mult χ z : ℝ) ≤ ∑ z ∈ U \ V, (ZeroCount1623.mult χ z : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have hsd : ∑ z ∈ U \ V, (ZeroCount1623.mult χ z : ℝ) =
      ∑ z ∈ U, (ZeroCount1623.mult χ z : ℝ) - ∑ z ∈ V, (ZeroCount1623.mult χ z : ℝ) := by
    rw [← Finset.sum_sdiff hVU]; ring
  have h1 := (abs_le.mp (ZeroCount1623.arxiv_zero_count χ hχ (hT.trans ht.le))).2
  have h2 := (abs_le.mp (ZeroCount1623.arxiv_zero_count χ hχ hT)).1
  rw [hmap]
  refine hle.trans (le_of_eq_of_le hsd ?_)
  unfold countBound
  rw [← hU] at h1
  rw [← hV] at h2
  linarith

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count. P0014 Lemma 4.3, page 38, two sided
and in inequality form: for φ ≥ 0 on (T, ∞), the sum over the zeros with abs Im above T of the
multiplicity times the integral of φ above abs Im is summable and at most the integral of φ
against countBound. -/
theorem high_zero_sum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (T : ℝ) (hT : 1 ≤ T) (φ : ℝ → ℝ) (hφ : ∀ t, T < t → 0 ≤ φ t)
    (hφint : IntegrableOn φ (Ioi T))
    (hint : IntegrableOn (fun t => φ t * countBound q T t) (Ioi T)) :
    Summable (fun ρ : HighIdx χ T =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ∫ t in Ioi |ρ.val.im|, φ t) ∧
    (∑' ρ : HighIdx χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ∫ t in Ioi |ρ.val.im|, φ t) ≤ ∫ t in Ioi T, φ t * countBound q T t :=
  sum_le_integral_count (fun ρ : HighIdx χ T => |ρ.val.im|)
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))
    (fun _ => Nat.cast_nonneg _) T (fun ρ => ρ.property.2.2.2) φ (countBound q T) hφ hφint hint
    (fun t ht S => high_count_le χ hχ T t hT ht S)

/-! ## The exponential branch of display 4.34 -/

/-- PROVED. exp(−cτ) is the integral of c exp(−ct) over (τ, ∞). -/
lemma exp_eq_integral (c τ : ℝ) (hc : 0 < c) :
    exp (-c * τ) = ∫ t in Ioi τ, c * exp (-c * t) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c < 0)]
  field_simp

lemma abs_log_le (x : ℝ) (hx : 0 < x) : |log x| ≤ x + x⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h2
  rw [abs_le]; constructor <;> linarith [inv_pos.mpr hx]

/-- A constant bounding countBound by a quadratic. -/
noncomputable def countConst (q : ℕ) (T : ℝ) : ℝ :=
  2 * q + 37 + |T / π * log (q * T / (2 * π * exp 1))| + |0.5 * log (q * T)| + 17.7

/-- PROVED. countBound grows at most quadratically. -/
lemma countBound_abs_le (q : ℕ) [NeZero q] (T t : ℝ) (hT : 1 ≤ T) (ht : T ≤ t) :
    |countBound q T t| ≤ countConst q T * (1 + t ^ 2) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have ht1 : 1 ≤ t := hT.trans ht
  have hqt : 1 ≤ (q : ℝ) * t := by nlinarith
  have hpi := pi_gt_three
  have hpi2 := pi_lt_d2
  have he := exp_one_lt_d9
  have he1 := exp_one_gt_d9
  have hK : (1 : ℝ) ≤ 2 * π * exp 1 := by nlinarith
  have hK18 : 2 * π * exp 1 ≤ 18 := by nlinarith
  set x1 := (q : ℝ) * t / (2 * π * exp 1) with hx1
  have hx1pos : 0 < x1 := by positivity
  have hx1le : x1 ≤ q * t := div_le_self (by linarith) hK
  have hx1inv : x1⁻¹ ≤ 18 := by
    rw [hx1, inv_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hl1 : |log x1| ≤ q * t + 18 := (abs_log_le x1 hx1pos).trans (by linarith)
  have hl2 : |log ((q : ℝ) * t)| ≤ q * t + 1 := by
    refine (abs_log_le _ (by linarith)).trans ?_
    have : ((q : ℝ) * t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hqt
    linarith
  have hA : |t / π * log x1| ≤ t * (q * t + 18) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < t / π)]
    have htp : t / π ≤ t := div_le_self (by linarith) (by linarith)
    calc t / π * |log x1| ≤ t * |log x1| :=
          mul_le_mul_of_nonneg_right htp (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hl1 (by linarith)
  have hC1 := abs_nonneg (T / π * log (q * T / (2 * π * exp 1)))
  have hC2 := abs_nonneg (0.5 * log ((q : ℝ) * T))
  have eA := abs_le.mp hA
  have eB := abs_le.mp hl2
  have eC1 := abs_le.mp (le_refl |T / π * log (q * T / (2 * π * exp 1))|)
  have eC2 := abs_le.mp (le_refl |0.5 * log ((q : ℝ) * T)|)
  have key : t * (q * t + 18) + 0.5 * (q * t + 1) + 35.4 ≤
      (2 * q + 37 + 17.7) * (1 + t ^ 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q) (sq_nonneg (t - 1)), sq_nonneg (t - 1)]
  have k1 : |T / π * log (q * T / (2 * π * exp 1))| ≤
      |T / π * log (q * T / (2 * π * exp 1))| * (1 + t ^ 2) := by
    nlinarith [mul_nonneg hC1 (sq_nonneg t)]
  have k2 : |0.5 * log ((q : ℝ) * T)| ≤ |0.5 * log ((q : ℝ) * T)| * (1 + t ^ 2) := by
    nlinarith [mul_nonneg hC2 (sq_nonneg t)]
  unfold countBound countConst
  rw [← hx1, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- PROVED. c exp(−ct) times countBound is integrable on (T, ∞). -/
lemma exp_count_integrable (q : ℕ) [NeZero q] (c T : ℝ) (hc : 0 < c) (hT : 1 ≤ T) :
    IntegrableOn (fun t => c * exp (-c * t) * countBound q T t) (Ioi T) := by
  have h1 := integrableOn_exp_mul_Ioi (a := -c) (by linarith) T
  have h2 := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (b := c) (by norm_num)
    (by norm_num) hc).mono_set (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ T))
  have hmaj := (h1.add h2).const_mul (c * countConst q T)
  apply hmaj.mono'
  · have hm : Measurable (fun t => c * exp (-c * t) * countBound q T t) := by
      unfold countBound; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change T < t at ht
    have hb := countBound_abs_le q T t hT ht.le
    have ht0 : 0 ≤ t := by linarith
    simp only [Pi.add_apply, Real.rpow_one, Real.rpow_two]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hc, abs_of_pos (exp_pos _)]
    have hep := exp_pos (-c * t)
    calc c * exp (-c * t) * |countBound q T t| ≤
        c * exp (-c * t) * (countConst q T * (1 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = c * countConst q T * (exp (-c * t) + t ^ 2 * exp (-c * t)) := by ring

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count. Lemma 4.3 applied to the exponential
branch of display 4.34: the sum over the zeros with abs Im above T of the multiplicity times
exp(−c abs Im) converges and is at most the integral of c exp(−ct) against countBound. -/
theorem high_zero_exp_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (c T : ℝ) (hc : 0 < c) (hT : 1 ≤ T) :
    Summable (fun ρ : HighIdx χ T =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * exp (-c * |ρ.val.im|)) ∧
    (∑' ρ : HighIdx χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        exp (-c * |ρ.val.im|)) ≤ ∫ t in Ioi T, c * exp (-c * t) * countBound q T t := by
  have h := high_zero_sum_le χ hχ T hT (fun t => c * exp (-c * t))
    (fun t _ => by positivity) ((integrableOn_exp_mul_Ioi (by linarith) T).const_mul c)
    (exp_count_integrable q c T hc hT)
  have he : ∀ τ : ℝ, (∫ t in Ioi τ, c * exp (-c * t)) = exp (-c * τ) :=
    fun τ => (exp_eq_integral c τ hc).symm
  simp only [he] at h
  exact h

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count and on hcor, the k = 0 case of
Corollary 3.2 at zero shift, the open leaf SplitGaussian123.corollary_3_2_k0 at δ = 0.
P0014 Lemma 4.5, pages 40 and 41, at δ = 0, proved WITHOUT the pairing of display 4.33: the
Mellin mass of the zeros with abs Im above T is summable and at most 4.226 times the integral
of 0.1598 exp(−0.1598 t) against countBound. -/
theorem tail_mass_zero_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |(0 : ℝ)|) ≤ |s.im| →
      ‖gaussianMellin 0 s‖ + ‖gaussianMellin 0 (1 - s)‖ ≤ 4.226 * corEnvelope 0 s.im) :
    Summable (fun ρ : HighIdx χ T => mellinMassTerm χ 0 ρ.val) ∧
    (∑' ρ : HighIdx χ T, mellinMassTerm χ 0 ρ.val) ≤
      4.226 * ∫ t in Ioi T, 0.1598 * exp (-0.1598 * t) * countBound q T t := by
  obtain ⟨hs, hb⟩ := high_zero_exp_sum χ hχ 0.1598 T (by norm_num) (by linarith)
  have hT' : max (4 * π ^ 2 * |(0 : ℝ)|) 100 ≤ T := by simp; linarith
  have hpt : ∀ ρ : HighIdx χ T, mellinMassTerm χ 0 ρ.val ≤
      4.226 * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        exp (-0.1598 * |ρ.val.im|)) := by
    intro ρ
    have h1 := zero_mass_le_envelope χ 0 T hT' hcor ρ
    have h2 := corEnvelope_le 0 ρ.val.im
    rw [if_pos rfl, add_zero] at h2
    have hm : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
      Nat.cast_nonneg _
    calc mellinMassTerm χ 0 ρ.val ≤ _ := h1
      _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (4.226 * exp (-0.1598 * |ρ.val.im|)) :=
          mul_le_mul_of_nonneg_left (by linarith) hm
      _ = _ := by ring
  have hnn : ∀ ρ : HighIdx χ T, 0 ≤ mellinMassTerm χ 0 ρ.val := fun ρ =>
    mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hs' := hs.mul_left 4.226
  refine ⟨hs'.of_nonneg_of_le hnn hpt, ?_⟩
  calc _ ≤ ∑' ρ : HighIdx χ T, 4.226 * ((analyticOrderNatAt (DirichletCharacter.LFunction χ)
        ρ.val : ℝ) * exp (-0.1598 * |ρ.val.im|)) :=
        (hs'.of_nonneg_of_le hnn hpt).tsum_le_tsum hpt hs'
    _ = _ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

/-! ## The Gaussian branch of display 4.34 -/

/-- The density whose integral from τ to infinity is the Gaussian branch exp(−k (τ/D)²). -/
noncomputable def gaussDensity (k D t : ℝ) : ℝ := 2 * k / D ^ 2 * t * exp (-k * (t / D) ^ 2)

lemma gaussDensity_eq (k D t : ℝ) :
    gaussDensity k D t = 2 * k / D ^ 2 * (t ^ (1 : ℝ) * exp (-(k / D ^ 2) * t ^ (2 : ℝ))) := by
  unfold gaussDensity
  rw [Real.rpow_one, Real.rpow_two, div_pow]
  ring_nf

lemma gaussDensity_integrable (k D τ : ℝ) (hk : 0 < k) (hD : 0 < D) (hτ : 0 ≤ τ) :
    IntegrableOn (gaussDensity k D) (Ioi τ) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 2) (b := k / D ^ 2)
    (by norm_num) (by norm_num) (by positivity)).mono_set (Ioi_subset_Ioi hτ)
  have h' := h.const_mul (2 * k / D ^ 2)
  exact IntegrableOn.congr_fun h' (fun t _ => (gaussDensity_eq k D t).symm) measurableSet_Ioi

/-- PROVED. exp(−k (τ/D)²) is the integral of gaussDensity over (τ, ∞), for τ ≥ 0. -/
lemma gauss_eq_integral (k D τ : ℝ) (hk : 0 < k) (hD : 0 < D) (hτ : 0 ≤ τ) :
    exp (-k * (τ / D) ^ 2) = ∫ t in Ioi τ, gaussDensity k D t := by
  have hderiv : ∀ x ∈ Ici τ, HasDerivAt (fun t => -exp (-k * (t / D) ^ 2))
      (gaussDensity k D x) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -k * (t / D) ^ 2) (-k * (2 * (x / D) * (1 / D))) x := by
      have := ((hasDerivAt_id x).div_const D).pow 2
      simpa using this.const_mul (-k)
    have h2 := (h1.exp).neg
    convert h2 using 1
    unfold gaussDensity
    field_simp
  have hlim : Tendsto (fun t => -exp (-k * (t / D) ^ 2)) atTop (nhds 0) := by
    have hsq : Tendsto (fun t : ℝ => (t / D) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp (tendsto_id.atTop_div_const hD)
    have hneg : Tendsto (fun t : ℝ => -k * (t / D) ^ 2) atTop atBot := by
      have := tendsto_neg_atTop_atBot.comp (hsq.const_mul_atTop hk)
      refine this.congr (fun t => ?_)
      simp [Function.comp, neg_mul]
    simpa using (Real.tendsto_exp_atBot.comp hneg).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (gaussDensity_integrable k D τ hk hD hτ) hlim]
  ring

/-- PROVED. gaussDensity times countBound is integrable on (T, ∞). -/
lemma gauss_count_integrable (q : ℕ) [NeZero q] (k D T : ℝ) (hk : 0 < k) (hD : 0 < D)
    (hT : 1 ≤ T) :
    IntegrableOn (fun t => gaussDensity k D t * countBound q T t) (Ioi T) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have h1 := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 2) (b := k / D ^ 2)
    (by norm_num) (by norm_num) (by positivity)).mono_set (Ioi_subset_Ioi hT0)
  have h3 := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 3) (p := 2) (b := k / D ^ 2)
    (by norm_num) (by norm_num) (by positivity)).mono_set (Ioi_subset_Ioi hT0)
  have hmaj := (h1.add h3).const_mul (2 * k / D ^ 2 * countConst q T)
  apply hmaj.mono'
  · have hm : Measurable (fun t => gaussDensity k D t * countBound q T t) := by
      unfold countBound gaussDensity; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change T < t at ht
    have hb := countBound_abs_le q T t hT ht.le
    have ht0 : 0 ≤ t := by linarith
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul, gaussDensity_eq, abs_mul, abs_of_pos (by positivity :
      (0 : ℝ) < 2 * k / D ^ 2), abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ t ^ (1 : ℝ) * exp (-(k / D ^ 2) * t ^ (2 : ℝ)))]
    have hr3 : t ^ (3 : ℝ) = t ^ (1 : ℝ) * t ^ 2 := by
      rw [Real.rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [hr3]
    have hpos : 0 ≤ t ^ (1 : ℝ) * exp (-(k / D ^ 2) * t ^ (2 : ℝ)) := by positivity
    calc 2 * k / D ^ 2 * (t ^ (1 : ℝ) * exp (-(k / D ^ 2) * t ^ (2 : ℝ))) *
          |countBound q T t| ≤ 2 * k / D ^ 2 * (t ^ (1 : ℝ) * exp (-(k / D ^ 2) * t ^ (2 : ℝ))) *
          (countConst q T * (1 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count. Lemma 4.3 applied to the Gaussian
branch of display 4.34, with D = π abs δ. -/
theorem high_zero_gauss_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (k D T : ℝ) (hk : 0 < k) (hD : 0 < D) (hT : 1 ≤ T) :
    Summable (fun ρ : HighIdx χ T =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        exp (-k * (|ρ.val.im| / D) ^ 2)) ∧
    (∑' ρ : HighIdx χ T, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        exp (-k * (|ρ.val.im| / D) ^ 2)) ≤
      ∫ t in Ioi T, gaussDensity k D t * countBound q T t := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have h := high_zero_sum_le χ hχ T hT (gaussDensity k D)
    (fun t ht => by unfold gaussDensity; have : 0 ≤ t := by linarith
                    positivity)
    (gaussDensity_integrable k D T hk hD hT0) (gauss_count_integrable q k D T hk hD hT)
  have he : ∀ ρ : HighIdx χ T, (∫ t in Ioi |ρ.val.im|, gaussDensity k D t) =
      exp (-k * (|ρ.val.im| / D) ^ 2) :=
    fun ρ => (gauss_eq_integral k D _ hk hD (abs_nonneg _)).symm
  simp only [he] at h
  exact h

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count and on hcor, the k = 0 case of
Corollary 3.2, the open leaf SplitGaussian123.corollary_3_2_k0. P0014 Lemma 4.5, pages 40 and
41, for every shift δ, proved WITHOUT the pairing of display 4.33 and without the cancellation
on page 38: the Mellin mass of the zeros with abs Im above T is summable and at most 4.226 times
the integrals of the two branches of display 4.34 against countBound, the Gaussian branch being
absent at zero shift. -/
theorem tail_mass_two_sided {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : HighIdx χ T => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : HighIdx χ T, mellinMassTerm χ δ ρ.val) ≤
      4.226 * ((∫ t in Ioi T, 0.1598 * exp (-0.1598 * t) * countBound q T t) +
        if δ = 0 then 0 else ∫ t in Ioi T, gaussDensity 0.1065 (π * |δ|) t * countBound q T t) := by
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  obtain ⟨hs1, hb1⟩ := high_zero_exp_sum χ hχ 0.1598 T (by norm_num) (by linarith)
  set w := fun ρ : HighIdx χ T =>
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) with hw
  set g : HighIdx χ T → ℝ := fun ρ => if δ = 0 then 0 else
    w ρ * exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2) with hg
  have hgs : Summable g ∧ ∑' ρ, g ρ ≤
      if δ = 0 then 0 else ∫ t in Ioi T, gaussDensity 0.1065 (π * |δ|) t * countBound q T t := by
    by_cases hδ : δ = 0
    · simp [hg, hδ]
    · have hD : 0 < π * |δ| := mul_pos pi_pos (abs_pos.mpr hδ)
      obtain ⟨hs2, hb2⟩ := high_zero_gauss_sum χ hχ 0.1065 (π * |δ|) T (by norm_num) hD
        (by linarith)
      simp only [hg, hδ, ite_false]
      exact ⟨hs2, hb2⟩
  obtain ⟨hs2, hb2⟩ := hgs
  have hpt : ∀ ρ : HighIdx χ T, mellinMassTerm χ δ ρ.val ≤
      4.226 * (w ρ * exp (-0.1598 * |ρ.val.im|) + g ρ) := by
    intro ρ
    have h1 := zero_mass_le_envelope χ δ T hT hcor ρ
    have h2 := corEnvelope_le δ ρ.val.im
    have hm : 0 ≤ w ρ := Nat.cast_nonneg _
    have h3 : w ρ * (exp (-0.1598 * |ρ.val.im|) +
        if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) =
        w ρ * exp (-0.1598 * |ρ.val.im|) + g ρ := by
      simp only [hg]; split_ifs <;> ring
    calc mellinMassTerm χ δ ρ.val ≤ w ρ * (4.226 * corEnvelope δ ρ.val.im) := h1
      _ ≤ w ρ * (4.226 * (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :=
          mul_le_mul_of_nonneg_left (by linarith) hm
      _ = 4.226 * (w ρ * (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by ring
      _ = _ := by rw [h3]
  have hnn : ∀ ρ : HighIdx χ T, 0 ≤ mellinMassTerm χ δ ρ.val := fun ρ =>
    mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hs' := (hs1.add hs2).mul_left 4.226
  have hsum := hs'.of_nonneg_of_le hnn hpt
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' ρ : HighIdx χ T, 4.226 * (w ρ * exp (-0.1598 * |ρ.val.im|) + g ρ) :=
        hsum.tsum_le_tsum hpt hs'
    _ = 4.226 * ((∑' ρ : HighIdx χ T, w ρ * exp (-0.1598 * |ρ.val.im|)) + ∑' ρ, g ρ) := by
        rw [tsum_mul_left, hs1.tsum_add hs2]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by norm_num)

/-- PROVED, CONDITIONAL ON the open leaves SplitGaussian123.corollary_3_2_k0 and
ZeroCount1623.book_zero_count. P0014 page 43, proof of Proposition 4.6, with Lemma 4.5 in the
two sided form above: the zeros above T contribute at most 4.226 times the two branch integrals
against countBound, times x. This is the corrected counterpart of SplitGaussian123.
high_zero_bound, whose printed constants rest on the two QUESTIONs of the note. -/
theorem high_zero_bound_two_sided (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ‖highZeros χ δ x T‖ ≤
      4.226 * ((∫ t in Ioi T, 0.1598 * exp (-0.1598 * t) * countBound q T t) +
        if δ = 0 then 0 else ∫ t in Ioi T, gaussDensity 0.1065 (π * |δ|) t * countBound q T t) *
        x := by
  obtain ⟨hs, hb⟩ := tail_mass_two_sided χ hχ δ T hT
    (fun s h0 h1 hτ => corollary_3_2_k0 δ s h0 h1 hτ)
  exact high_zero_bound_of_mass χ δ x T _ hx hs hb

end LeanLab.HelfgottMajor.Lemma43Zeros123
