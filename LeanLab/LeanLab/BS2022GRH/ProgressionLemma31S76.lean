/-
AI wrote this Lean code, Claude, ROUTE BURST S76, burst-20261122, unit lemma31_split.
Proof of the LEAF `ProgressionEPS70.lemma31`, Ernvall-Hytonen and Palojarvi,
arXiv 2003.01925v4, Lemma 31 pp. 40 to 42, along the paper's displays (40) to (46):
* `disp41`, `disp42`, `disp43`, `disp44`, `disp45`, `disp46`: one PROVED result for each integral
  of the proof, each the bound the paper writes for that piece of the integral of
  `|S(t)| / (t log² t)` once (40) is inserted; (43) to (45) through `split_bound`, the
  split at `√x` with both cases `√x ≥ 2` and `√x < 2` as on p. 41.
* `lemma31_S76`, fully PROVED: the triangle inequality, the bound (40) taken
  from the hypothesis `hS`, linearity of the integral, and the final combination with
  `φ(q) ≥ 2`, `π < 3.1416`, `log 2 > 0.6931471803` and `log log 2 > -0.36652`.
  The constant 0.534 is tight: it needs the term `-2A√2` of (42), margin about 0.0008.
Displays (47) to (49) belong to Lemma 32, not Lemma 31, so they are not used here.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.ProgressionEPS70

namespace LeanLab.BS2022GRH.ProgressionLemma31S76
open Real Finset ProgressionEPS70 MeasureTheory
noncomputable section

/-- PROVED: a function continuous at every point of `[2, x]` is interval integrable. -/
theorem ii {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) (hf : ∀ z, 2 ≤ z → ContinuousAt f z) :
    IntervalIntegrable f volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  rw [Set.uIcc_of_le hx] at hz
  exact (hf z hz.1).continuousWithinAt

/-- PROVED: a continuity helper for the pieces of the integrand on `[2, x]`. -/
theorem pieces_ok (z : ℝ) (hz : 2 ≤ z) :
    z ≠ 0 ∧ log z ≠ 0 ∧ log z ^ 2 ≠ 0 ∧ z * log z ^ 2 ≠ 0 := by
  have h1 : z ≠ 0 := by positivity
  have h2 : 0 < log z := Real.log_pos (by linarith)
  exact ⟨h1, h2.ne', by positivity, by positivity⟩

/-- PROVED: EP2022 display (41) p. 41, `∫₂ˣ dt / (t log² t) = 1/log 2 - 1/log x`. -/
theorem disp41 (x : ℝ) (hx : 3 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / (t * log t ^ 2) = 1 / log 2 - 1 / log x := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(log t)⁻¹)]
  · ring
  · intro t ht
    rw [Set.uIcc_of_le hx2] at ht
    have h1 : t ≠ 0 := by linarith [ht.1]
    have h2 : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    convert ((Real.hasDerivAt_log h1).inv h2).neg using 1
    field_simp
  · exact ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)

/-- PROVED: EP2022 display (42) p. 41, the first term, `∫₂ˣ dt / √t = 2 (√x - √2)`. -/
theorem disp42 (x : ℝ) (hx : 3 ≤ x) :
    ∫ t in (2 : ℝ)..x, √t * log t ^ 2 / (t * log t ^ 2) ≤ 2 * (√x - √2) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2 * √t)]
  · linarith
  · intro t ht
    rw [Set.uIcc_of_le hx2] at ht
    have h1 : t ≠ 0 := by linarith [ht.1]
    have h2 : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have h3 : 0 < √t := Real.sqrt_pos.mpr (by linarith [ht.1])
    convert (Real.hasDerivAt_sqrt h1).const_mul 2 using 1
    have h5 : √t * √t = t := Real.mul_self_sqrt (by linarith [ht.1])
    have h6 : √t * log t ^ 2 / (t * log t ^ 2) = √t / t := by field_simp
    rw [h6]
    field_simp
    nlinarith [h5]
  · exact ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)

/-- PROVED: interval integrability on `[a, b]` with `a, b > 1` of a function continuous at
every point above 1. -/
theorem ii1 {g : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (hg : ∀ z, 1 < z → ContinuousAt g z) :
    IntervalIntegrable g volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  have : 1 < z := by
    rcases Set.mem_uIcc.mp hz with h | h <;> linarith [h.1]
  exact (hg z this).continuousWithinAt

/-- PROVED: `∫ₐᵇ √t / t dt = 2 √b - 2 √a` for `a, b > 1`. -/
theorem int_sqrt_div (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, √t / t = 2 * √b - 2 * √a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2 * √t)]
  · intro t ht
    have h1 : 1 < t := by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    have h0 : t ≠ 0 := by linarith
    have h3 : 0 < √t := Real.sqrt_pos.mpr (by linarith)
    convert (Real.hasDerivAt_sqrt h0).const_mul 2 using 1
    have h5 : √t * √t = t := Real.mul_self_sqrt (by linarith)
    field_simp
    nlinarith [h5]
  · exact ii1 ha hb fun z hz => by
      have : z ≠ 0 := by linarith
      fun_prop (disch := assumption)

/-- PROVED: the splitting at `√x` used in displays (43) to (45) p. 42: for a nonnegative
`f`, the part over `[2, √x]` is at most `x^(1/4) ∫₂^√x f`, in both cases `√x ≥ 2` and
`√x < 2` as the paper remarks on p. 41, and on `[√x, x]` a pointwise bound
`√t f(t) ≤ c √t / t` integrates to `c (2√x - 2x^(1/4))`. -/
theorem split_bound (x : ℝ) (hx : 3 ≤ x) (f : ℝ → ℝ) (hf : ∀ z, 1 < z → ContinuousAt f z)
    (hf0 : ∀ t, 1 < t → 0 ≤ f t) (c : ℝ)
    (hc : ∀ t, √x ≤ t → t ≤ x → √t * f t ≤ c * (√t / t)) :
    ∫ t in (2 : ℝ)..x, √t * f t
      ≤ x ^ ((1 : ℝ) / 4) * (∫ t in (2 : ℝ)..√x, f t)
        + c * (2 * √x - 2 * x ^ ((1 : ℝ) / 4)) := by
  have hy1 : 1 < √x := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hyx : √x ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hx1 : 1 < x := by linarith
  have h14 : x ^ ((1 : ℝ) / 4) = √(√x) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]; norm_num
  have hcf : ∀ z, 1 < z → ContinuousAt (fun t => √t * f t) z := fun z hz => by
    have := hf z hz; fun_prop
  have hcg : ∀ z, 1 < z → ContinuousAt (fun t => √t / t) z := fun z hz => by
    have : z ≠ 0 := by linarith
    fun_prop (disch := assumption)
  have hadd : (∫ t in (2 : ℝ)..√x, √t * f t) + (∫ t in √x..x, √t * f t)
      = ∫ t in (2 : ℝ)..x, √t * f t :=
    intervalIntegral.integral_add_adjacent_intervals (ii1 (by norm_num) hy1 hcf) (ii1 hy1 hx1 hcf)
  have p2 : ∫ t in √x..x, √t * f t ≤ c * (2 * √x - 2 * x ^ ((1 : ℝ) / 4)) := by
    calc ∫ t in √x..x, √t * f t ≤ ∫ t in √x..x, c * (√t / t) :=
          intervalIntegral.integral_mono_on hyx (ii1 hy1 hx1 hcf)
            ((ii1 hy1 hx1 hcg).const_mul c) fun t ht => hc t ht.1 ht.2
      _ = c * (2 * √x - 2 * x ^ ((1 : ℝ) / 4)) := by
          rw [intervalIntegral.integral_const_mul, int_sqrt_div _ _ hy1 hx1, h14]
  have hcy : ∀ z, 1 < z → ContinuousAt (fun t => √(√x) * f t) z := fun z hz => by
    have := hf z hz; fun_prop
  have p1 : ∫ t in (2 : ℝ)..√x, √t * f t ≤ x ^ ((1 : ℝ) / 4) * ∫ t in (2 : ℝ)..√x, f t := by
    rw [h14, ← intervalIntegral.integral_const_mul]
    rcases le_or_gt 2 (√x) with h | h
    · apply intervalIntegral.integral_mono_on h (ii1 (by norm_num) hy1 hcf)
        (ii1 (by norm_num) hy1 hcy)
      intro t ht
      apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2) (hf0 t (by linarith [ht.1]))
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_symm (√x)]
      apply neg_le_neg
      apply intervalIntegral.integral_mono_on h.le (ii1 hy1 (by norm_num) hcy)
        (ii1 hy1 (by norm_num) hcf)
      intro t ht
      apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.1) (hf0 t (by linarith [ht.1]))
  rw [← hadd]
  exact add_le_add p1 p2

/-- PROVED: `∫₂ᵇ dt / (t log t) = log log b - log log 2` for `b > 1`. -/
theorem ftc_loglog (b : ℝ) (hb : 1 < b) :
    ∫ t in (2 : ℝ)..b, log t / (t * log t ^ 2) = log (log b) - log (log 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => log (log t))]
  · intro t ht
    have h1' : 1 < t := by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    have h1 : t ≠ 0 := by linarith
    have h2 : log t ≠ 0 := (Real.log_pos h1').ne'
    convert (Real.hasDerivAt_log h1).log h2 using 1
    field_simp
  · exact ii1 (by norm_num) hb fun z hz => by
      have h1 : z ≠ 0 := by linarith
      have h2 : log z ≠ 0 := (Real.log_pos hz).ne'
      have h4 : z * log z ^ 2 ≠ 0 := by positivity
      fun_prop (disch := assumption)

/-- PROVED: `∫₂ᵇ dt / (t log² t) = 1/log 2 - 1/log b` for `b > 1`. -/
theorem ftc_inv_log (b : ℝ) (hb : 1 < b) :
    ∫ t in (2 : ℝ)..b, 1 / (t * log t ^ 2) = 1 / log 2 - 1 / log b := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(log t)⁻¹)]
  · ring
  · intro t ht
    have h1' : 1 < t := by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    have h1 : t ≠ 0 := by linarith
    have h2 : log t ≠ 0 := (Real.log_pos h1').ne'
    convert ((Real.hasDerivAt_log h1).inv h2).neg using 1
    field_simp
  · exact ii1 (by norm_num) hb fun z hz => by
      have h1 : z ≠ 0 := by linarith
      have h4 : z * log z ^ 2 ≠ 0 := by have := Real.log_pos hz; positivity
      fun_prop (disch := assumption)

/-- PROVED: `∫₂ᵇ dt / (t log³ t) = 1/(2 log² 2) - 1/(2 log² b)` for `b > 1`. -/
theorem ftc_inv_log2 (b : ℝ) (hb : 1 < b) :
    ∫ t in (2 : ℝ)..b, 1 / log t / (t * log t ^ 2)
      = 1 / (2 * log 2 ^ 2) - 1 / (2 * log b ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(2 * log t ^ 2)⁻¹)]
  · ring
  · intro t ht
    have h1' : 1 < t := by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    have h1 : t ≠ 0 := by linarith
    have h2 : log t ≠ 0 := (Real.log_pos h1').ne'
    have h3 : 2 * log t ^ 2 ≠ 0 := by positivity
    convert ((((Real.hasDerivAt_log h1).pow 2).const_mul 2).inv h3).neg using 1
    simp only [Pi.pow_apply]
    field_simp
    ring
  · exact ii1 (by norm_num) hb fun z hz => by
      have h1 : z ≠ 0 := by linarith
      have h2 : log z ≠ 0 := (Real.log_pos hz).ne'
      have h4 : z * log z ^ 2 ≠ 0 := by positivity
      fun_prop (disch := assumption)

/-- PROVED: EP2022 display (43) p. 42, the second term, split at `√x`. -/
theorem disp43 (x : ℝ) (hx : 3 ≤ x) :
    ∫ t in (2 : ℝ)..x, √t * log t / (t * log t ^ 2)
      ≤ x ^ ((1 : ℝ) / 4) * (log (log √x) - log (log 2))
        + 2 / log x * (2 * √x - 2 * x ^ ((1 : ℝ) / 4)) := by
  set F : ℝ → ℝ := fun t => log t / (t * log t ^ 2) with hFdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hL : 0 < log x := Real.log_pos (by linarith)
  have hy1 : 1 < √x := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hcont : ∀ z : ℝ, 1 < z → ContinuousAt (fun t => F t) z := fun z hz => by
    have h1 : z ≠ 0 := by linarith
    have h2 : log z ≠ 0 := (Real.log_pos hz).ne'
    have h4 : z * log z ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have hnn : ∀ t : ℝ, 1 < t → 0 ≤ F t := fun t ht => by
    have := Real.log_pos ht
    have : 0 < t := by linarith
    positivity
  have hlt : ∀ t : ℝ, √x ≤ t → log x ≤ 2 * log t ∧ 0 < log t := fun t ht => by
    have h0 : 0 < √x := by linarith
    have := Real.log_le_log h0 ht
    rw [Real.log_sqrt hx0] at this
    exact ⟨by linarith, Real.log_pos (by linarith)⟩
  have heq : (∫ t in (2 : ℝ)..x, √t * log t / (t * log t ^ 2))
      = ∫ t in (2 : ℝ)..x, √t * F t := by
    congr 1; funext t; simp only [hFdef]; ring
  rw [heq]
  refine (split_bound x hx F hcont hnn (2 / log x) fun t ht1 ht2 => ?_).trans ?_
  · obtain ⟨h1, h2⟩ := hlt t ht1
    have ht0 : 0 < t := by linarith [hy1]
    have hst : 0 ≤ √t / t := by positivity
    have e : √t * F t = √t / t * (1 / log t) := by simp only [hFdef]; field_simp
    rw [e, mul_comm (2 / log x)]
    apply mul_le_mul_of_nonneg_left _ hst
    rw [div_le_div_iff₀ h2 hL]; linarith
  · rw [hFdef, ftc_loglog _ hy1]

/-- PROVED: EP2022 display (44) p. 42, the third term, split at `√x`. -/
theorem disp44 (x : ℝ) (hx : 3 ≤ x) :
    ∫ t in (2 : ℝ)..x, √t / (t * log t ^ 2)
      ≤ 8 * √x / log x ^ 2 + x ^ ((1 : ℝ) / 4) / log 2 - 2 * x ^ ((1 : ℝ) / 4) / log x
        - 8 * x ^ ((1 : ℝ) / 4) / log x ^ 2 := by
  set F : ℝ → ℝ := fun t => 1 / (t * log t ^ 2) with hFdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hL : 0 < log x := Real.log_pos (by linarith)
  have hy1 : 1 < √x := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hcont : ∀ z : ℝ, 1 < z → ContinuousAt (fun t => F t) z := fun z hz => by
    have h1 : z ≠ 0 := by linarith
    have h2 : log z ≠ 0 := (Real.log_pos hz).ne'
    have h4 : z * log z ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have hnn : ∀ t : ℝ, 1 < t → 0 ≤ F t := fun t ht => by
    have := Real.log_pos ht
    have : 0 < t := by linarith
    positivity
  have hlt : ∀ t : ℝ, √x ≤ t → log x ≤ 2 * log t ∧ 0 < log t := fun t ht => by
    have h0 : 0 < √x := by linarith
    have := Real.log_le_log h0 ht
    rw [Real.log_sqrt hx0] at this
    exact ⟨by linarith, Real.log_pos (by linarith)⟩
  have heq : (∫ t in (2 : ℝ)..x, √t / (t * log t ^ 2))
      = ∫ t in (2 : ℝ)..x, √t * F t := by
    congr 1; funext t; simp only [hFdef]; ring
  rw [heq]
  refine (split_bound x hx F hcont hnn (4 / log x ^ 2) fun t ht1 ht2 => ?_).trans ?_
  · obtain ⟨h1, h2⟩ := hlt t ht1
    have ht0 : 0 < t := by linarith [hy1]
    have hst : 0 ≤ √t / t := by positivity
    have e : √t * F t = √t / t * (1 / log t ^ 2) := by simp only [hFdef]; field_simp
    rw [e, mul_comm (4 / log x ^ 2)]
    apply mul_le_mul_of_nonneg_left _ hst
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · rw [hFdef, ftc_inv_log _ hy1, Real.log_sqrt hx0]
    apply le_of_eq
    field_simp
    ring

/-- PROVED: EP2022 display (45) p. 42, the fourth term, split at `√x`. -/
theorem disp45 (x : ℝ) (hx : 3 ≤ x) :
    ∫ t in (2 : ℝ)..x, √t / log t / (t * log t ^ 2)
      ≤ 16 * √x / log x ^ 3 + x ^ ((1 : ℝ) / 4) / (2 * log 2 ^ 2)
        - 2 * x ^ ((1 : ℝ) / 4) / log x ^ 2 - 16 * x ^ ((1 : ℝ) / 4) / log x ^ 3 := by
  set F : ℝ → ℝ := fun t => 1 / log t / (t * log t ^ 2) with hFdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hL : 0 < log x := Real.log_pos (by linarith)
  have hy1 : 1 < √x := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hcont : ∀ z : ℝ, 1 < z → ContinuousAt (fun t => F t) z := fun z hz => by
    have h1 : z ≠ 0 := by linarith
    have h2 : log z ≠ 0 := (Real.log_pos hz).ne'
    have h4 : z * log z ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have hnn : ∀ t : ℝ, 1 < t → 0 ≤ F t := fun t ht => by
    have := Real.log_pos ht
    have : 0 < t := by linarith
    positivity
  have hlt : ∀ t : ℝ, √x ≤ t → log x ≤ 2 * log t ∧ 0 < log t := fun t ht => by
    have h0 : 0 < √x := by linarith
    have := Real.log_le_log h0 ht
    rw [Real.log_sqrt hx0] at this
    exact ⟨by linarith, Real.log_pos (by linarith)⟩
  have heq : (∫ t in (2 : ℝ)..x, √t / log t / (t * log t ^ 2))
      = ∫ t in (2 : ℝ)..x, √t * F t := by
    congr 1; funext t; simp only [hFdef]; ring
  rw [heq]
  refine (split_bound x hx F hcont hnn (8 / log x ^ 3) fun t ht1 ht2 => ?_).trans ?_
  · obtain ⟨h1, h2⟩ := hlt t ht1
    have ht0 : 0 < t := by linarith [hy1]
    have hst : 0 ≤ √t / t := by positivity
    have e : √t * F t = √t / t * (1 / log t ^ 3) := by simp only [hFdef]; field_simp
    rw [e, mul_comm (8 / log x ^ 3)]
    apply mul_le_mul_of_nonneg_left _ hst
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : log x ^ 3 ≤ (2 * log t) ^ 3 := pow_le_pow_left₀ hL.le h1 3
    nlinarith
  · rw [hFdef, ftc_inv_log2 _ hy1, Real.log_sqrt hx0]
    apply le_of_eq
    field_simp
    ring

/-- PROVED: EP2022 display (46) p. 42, the fifth term,
`∫₂ˣ dt / (t log t) = log log x - log log 2`. -/
theorem disp46 (x : ℝ) (hx : 3 ≤ x) :
    ∫ t in (2 : ℝ)..x, log t / (t * log t ^ 2) ≤ log (log x) - log (log 2) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => log (log t))]
  · intro t ht
    rw [Set.uIcc_of_le hx2] at ht
    have h1 : t ≠ 0 := by linarith [ht.1]
    have h2 : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    convert (Real.hasDerivAt_log h1).log h2 using 1
    field_simp
  · exact ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)

/-- PROVED: `log (log 2) > -0.36652`, from six terms of the exponential series. -/
theorem loglog2_gt : (-0.36652 : ℝ) < log (log 2) := by
  have h2 := Real.log_two_gt_d9
  have hs := Real.sum_le_exp_of_nonneg (x := (0.36652 : ℝ)) (by norm_num) 6
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hs
  norm_num at hs
  have hpos : (0 : ℝ) < log 2 := by linarith
  rw [Real.lt_log_iff_exp_lt hpos]
  have he : exp (-0.36652) * exp 0.36652 = 1 := by rw [← Real.exp_add]; norm_num
  have hp := Real.exp_pos (-0.36652 : ℝ)
  nlinarith

/-- PROVED: `1 / log 2 ≤ 1.4426950415`. -/
theorem inv_log2_le : 1 / log 2 ≤ (1.4426950415 : ℝ) := by
  have h2 := Real.log_two_gt_d9
  rw [div_le_iff₀ (by linarith)]; nlinarith

/-- PROVED: the bounds on `A = 1/(8πφ) + 1/(6π)` used at the end of the proof, for `φ ≥ 2`. -/
theorem A_bounds (φ : ℝ) (hφ : 2 ≤ φ) :
    2 * (1 / (8 * π * φ) + 1 / (6 * π)) ≤ 0.146 ∧
    (0.15002 : ℝ) ≤ 2 * (1 / (8 * π * φ) + 1 / (6 * π)) * √2 ∧
    0 ≤ 1 / (8 * π * φ) + 1 / (6 * π) := by
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hsq2 : (1.414 : ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h0 : 0 ≤ 1 / (8 * π * φ) := by
    have : 0 < φ := by linarith
    positivity
  have h1 : 1 / (8 * π * φ) ≤ 1 / (16 * π) := by
    apply one_div_le_one_div_of_le (by positivity); nlinarith
  have h2 : 1 / (16 * π) ≤ 0.01990 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h3 : 1 / (6 * π) ≤ 0.05306 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h4 : 0.05305 ≤ 1 / (6 * π) := by rw [le_div_iff₀ (by positivity)]; nlinarith
  refine ⟨by linarith, ?_, by positivity⟩
  have hA : (0.1061 : ℝ) ≤ 2 * (1 / (8 * π * φ) + 1 / (6 * π)) := by linarith
  have := mul_le_mul hA hsq2 (by norm_num) (by positivity)
  linarith

/-- PROVED: the coefficient of `x^(1/4)` in the final combination is nonnegative. -/
theorem num_c2 (lq u v : ℝ) (hlq : 0 ≤ lq) (hu0 : 0 ≤ u) (hu1 : u ≤ 1.4426950415)
    (hv : -0.36652 < v) :
    0 ≤ (5.254 * lq ^ 2 + 121.765 * lq + 937.202) - (5.314 * lq + 124.318) * u
      - (5.048 * lq ^ 2 + 109.573 * lq + 725.316) * (u ^ 2 / 2) + (0.184 * lq + 8.250) * v := by
  have hu2 : u ^ 2 ≤ 1.4426950415 ^ 2 := by nlinarith
  have k1 : 0 ≤ lq ^ 2 * (5.254 - 5.048 * (u ^ 2 / 2)) := by
    apply mul_nonneg (by positivity); nlinarith
  have k2 : 0 ≤ lq * (121.765 - 5.314 * u - 109.573 * (u ^ 2 / 2) + 0.184 * v) := by
    apply mul_nonneg hlq; nlinarith
  have k3 : 0 ≤ 937.202 - 124.318 * u - 725.316 * (u ^ 2 / 2) + 8.250 * v := by
    nlinarith
  nlinarith

/-- PROVED: the constant term in the final combination is nonnegative. -/
theorem num_c3 (lq v w : ℝ) (hlq : 0 ≤ lq) (hv : -0.36652 < v) (hw : 0.15002 ≤ w) :
    0 ≤ (2.754 * lq + 0.534) - (2.015 * lq + 0.5) + (2.015 * lq + 0.5) * v + w := by
  have k2 : 0 ≤ lq * (0.739 + 2.015 * v) := by
    apply mul_nonneg hlq; nlinarith
  nlinarith

/-- PROVED: linearity, the right side of (40) divided by `t log² t`, integrated piece by
piece. -/
theorem integral_split (q : ℕ) (x : ℝ) (hx2 : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, thm3RHS q t / (t * log t ^ 2) =
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π))
        * (∫ t in (2 : ℝ)..x, √t * log t ^ 2 / (t * log t ^ 2))
      + (0.184 * log q + 8.250) * (∫ t in (2 : ℝ)..x, √t * log t / (t * log t ^ 2))
      + (5.314 * log q + 124.318) * (∫ t in (2 : ℝ)..x, √t / (t * log t ^ 2))
      + (5.048 * log q ^ 2 + 109.573 * log q + 725.316)
        * (∫ t in (2 : ℝ)..x, √t / log t / (t * log t ^ 2))
      + (2.015 * log q + 0.5) * (∫ t in (2 : ℝ)..x, log t / (t * log t ^ 2))
      + R1 q * (∫ t in (2 : ℝ)..x, 1 / (t * log t ^ 2)) := by
  have iA : IntervalIntegrable (fun t => √t * log t ^ 2 / (t * log t ^ 2)) volume 2 x :=
    ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)
  have iB : IntervalIntegrable (fun t => √t * log t / (t * log t ^ 2)) volume 2 x :=
    ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)
  have iC : IntervalIntegrable (fun t => √t / (t * log t ^ 2)) volume 2 x :=
    ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)
  have iD : IntervalIntegrable (fun t => √t / log t / (t * log t ^ 2)) volume 2 x :=
    ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)
  have iE : IntervalIntegrable (fun t => log t / (t * log t ^ 2)) volume 2 x :=
    ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)
  have iR : IntervalIntegrable (fun t => 1 / (t * log t ^ 2)) volume 2 x :=
    ii hx2 fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
      fun_prop (disch := assumption)
  have hg : (fun t => thm3RHS q t / (t * log t ^ 2)) =
      fun t => (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π))
          * (√t * log t ^ 2 / (t * log t ^ 2))
        + (0.184 * log q + 8.250) * (√t * log t / (t * log t ^ 2))
        + (5.314 * log q + 124.318) * (√t / (t * log t ^ 2))
        + (5.048 * log q ^ 2 + 109.573 * log q + 725.316) * (√t / log t / (t * log t ^ 2))
        + (2.015 * log q + 0.5) * (log t / (t * log t ^ 2)) + R1 q * (1 / (t * log t ^ 2)) := by
    funext t; simp only [thm3RHS]; ring
  rw [hg]
  rw [intervalIntegral.integral_add (((((iA.const_mul _).add (iB.const_mul _)).add
      (iC.const_mul _)).add (iD.const_mul _)).add (iE.const_mul _)) (iR.const_mul _),
    intervalIntegral.integral_add ((((iA.const_mul _).add (iB.const_mul _)).add
      (iC.const_mul _)).add (iD.const_mul _)) (iE.const_mul _),
    intervalIntegral.integral_add (((iA.const_mul _).add (iB.const_mul _)).add
      (iC.const_mul _)) (iD.const_mul _),
    intervalIntegral.integral_add ((iA.const_mul _).add (iB.const_mul _)) (iC.const_mul _),
    intervalIntegral.integral_add (iA.const_mul _) (iB.const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

/-- PROVED: the right side of (40) is interval integrable against `1/(t log² t)`. -/
theorem integrable_rhs (q : ℕ) (x : ℝ) (hx2 : 2 ≤ x) :
    IntervalIntegrable (fun t => thm3RHS q t / (t * log t ^ 2)) volume 2 x :=
  ii hx2 fun z hz => by
    obtain ⟨h1, h2, h3, h4⟩ := pieces_ok z hz
    simp only [thm3RHS]
    fun_prop (disch := assumption)

/-- PROVED: `thm3RHS q x / log x` expanded. -/
theorem first_term (q : ℕ) (x : ℝ) (hL : 0 < log x) :
    thm3RHS q x / log x = (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.250) * √x + (5.314 * log q + 124.318) * √x / log x
      + (5.048 * log q ^ 2 + 109.573 * log q + 725.316) * √x / log x ^ 2
      + (2.015 * log q + 0.5) + R1 q / log x := by
  simp only [thm3RHS]
  field_simp

/-- PROVED: the final combination, from the lemmas for displays (41) to (46), `φ(q) ≥ 2` and the
numerical constants: the right side of (40) over `log x` plus its integral against
`1/(t log² t)` is at most the right side of Lemma 31. -/
theorem final_combination (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx3 : 3 ≤ x) :
    thm3RHS q x / log x + ∫ t in (2 : ℝ)..x, thm3RHS q t / (t * log t ^ 2)
      ≤ lemma31RHS q x := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hL : 0 < log x := Real.log_pos (by linarith)
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 ≤ log (q : ℝ) := Real.log_nonneg (by linarith)
  have hphi : (2 : ℝ) ≤ (q.totient : ℝ) := by
    have he := Nat.totient_even (n := q) (by omega)
    have hp : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    obtain ⟨k, hk⟩ := he
    exact_mod_cast (by omega : 2 ≤ q.totient)
  obtain ⟨hA1, hA2, hA0⟩ := A_bounds _ hphi
  rw [integral_split q x hx2, first_term q x hL]
  unfold lemma31RHS
  rw [div_eq_mul_one_div (R1 q) (log 2)]
  have b42 := mul_le_mul_of_nonneg_left (disp42 x hx3) hA0
  have b43 := mul_le_mul_of_nonneg_left (disp43 x hx3)
    (by positivity : (0 : ℝ) ≤ 0.184 * log q + 8.250)
  have b44 := mul_le_mul_of_nonneg_left (disp44 x hx3)
    (by positivity : (0 : ℝ) ≤ 5.314 * log q + 124.318)
  have b45 := mul_le_mul_of_nonneg_left (disp45 x hx3)
    (by positivity : (0 : ℝ) ≤ 5.048 * log q ^ 2 + 109.573 * log q + 725.316)
  have b46 := mul_le_mul_of_nonneg_left (disp46 x hx3)
    (by positivity : (0 : ℝ) ≤ 2.015 * log q + 0.5)
  rw [disp41 x hx3]
  generalize ∫ t in (2 : ℝ)..x, √t * log t ^ 2 / (t * log t ^ 2) = I1 at *
  generalize ∫ t in (2 : ℝ)..x, √t * log t / (t * log t ^ 2) = I2 at *
  generalize ∫ t in (2 : ℝ)..x, √t / (t * log t ^ 2) = I3 at *
  generalize ∫ t in (2 : ℝ)..x, √t / log t / (t * log t ^ 2) = I4 at *
  generalize ∫ t in (2 : ℝ)..x, log t / (t * log t ^ 2) = I5 at *
  have hu0 : (0 : ℝ) ≤ 1 / log 2 := by
    have := Real.log_two_gt_d9; positivity
  have hc2 := num_c2 (log q) (1 / log 2) (log (log 2)) hlq hu0 inv_log2_le loglog2_gt
  have hc3 := num_c3 (log q) (log (log 2)) _ hlq loglog2_gt hA2
  have h4 : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := by positivity
  have hc2' := mul_nonneg hc2 h4
  have hc1 : 0 ≤ (0.146 - 2 * (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π))) * √x :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg x)
  have h44 : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = √x := by
    rw [← Real.rpow_add (by linarith), Real.sqrt_eq_rpow]; norm_num
  linear_combination b42 + b43 + b44 + b45 + b46 + hc1 + hc2' + hc3
    - (5.048 * log q ^ 2 + 109.573 * log q + 725.316) * 16 / log x ^ 3 * h44

/-- PROVED from the lemmas for displays (41) to (46): EP2022 Lemma 31 pp. 40 to 42, the exact statement
of `ProgressionEPS70.lemma31`. The triangle inequality, the pointwise bound (40) from `hS`
inside the integral, and `final_combination`. -/
theorem lemma31_S76 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x)
    (hS : ∀ t : ℝ, 2 ≤ t → t ≤ x → |psiAP q a t - t / (q.totient : ℝ)| < thm3RHS q t) :
    |(psiAP q a x - x / (q.totient : ℝ)) / log x
      + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)|
      < lemma31RHS q x := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hx3 : 3 ≤ x := le_trans hq3 hx
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hL : 0 < log x := Real.log_pos (by linarith)
  have hI : |∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)|
      ≤ ∫ t in (2 : ℝ)..x, thm3RHS q t / (t * log t ^ 2) := by
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun t => (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)) hx2
      (Filter.Eventually.of_forall fun t ht => by
        have h4 : 0 < t * log t ^ 2 := by
          have : 0 < log t := Real.log_pos (by linarith [ht.1])
          have : 0 < t := by linarith [ht.1]
          positivity
        rw [Real.norm_eq_abs, abs_div, abs_of_pos h4]
        exact div_le_div_of_nonneg_right (hS t ht.1.le ht.2).le h4.le)
      (integrable_rhs q x hx2)
    simpa [Real.norm_eq_abs] using this
  have hSx : |psiAP q a x - x / (q.totient : ℝ)| / log x < thm3RHS q x / log x :=
    div_lt_div_of_pos_right (hS x hx2 le_rfl) hL
  have htri := abs_add_le ((psiAP q a x - x / (q.totient : ℝ)) / log x)
    (∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2))
  rw [abs_div, abs_of_pos hL] at htri
  have hfin := final_combination q x hq hx3
  linarith

end

#print axioms LeanLab.BS2022GRH.ProgressionLemma31S76.final_combination
#print axioms LeanLab.BS2022GRH.ProgressionLemma31S76.lemma31_S76
#print axioms LeanLab.BS2022GRH.ProgressionLemma31S76.loglog2_gt
#print axioms LeanLab.BS2022GRH.ProgressionLemma31S76.integral_split

end LeanLab.BS2022GRH.ProgressionLemma31S76
