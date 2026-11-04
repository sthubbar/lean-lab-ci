import LeanLab.ChenDoubleSieve.Decomp275b

/-!
Elementary closed forms needed for the first six Section 10 integrals.
Source: https://arxiv.org/pdf/0705.1652, page 6 equation 2.6 and page 39 equation 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task275
open Wu04Functional (IsLinearSieve)

/-- The upper linear sieve function has its initial formula through three.
CONDITIONAL ON IsLinearSieve. -/
theorem linear_upper_three {F f : ℝ → ℝ} (h : IsLinearSieve F f)
    {u : ℝ} (hu0 : 0 < u) (hu3 : u ≤ 3) : F u = 2 * exp eulerMascheroniConstant / u := by
  by_cases hu2 : u ≤ 2
  · exact (h.2.2.1 u hu0 hu2).1
  have hu2' : 2 ≤ u := (lt_of_not_ge hu2).le
  have hc : ContinuousOn (fun v : ℝ => v * F v) (Icc 2 u) :=
    continuousOn_id.mul (h.1.mono (fun t ht => by change 0 < t; linarith [ht.1]))
  have hd : ∀ t ∈ Ioo (2 : ℝ) u, HasDerivAt (fun v => v * F v) 0 t := by
    intro t ht
    have hz := (h.2.2.1 (t - 1) (by linarith [ht.1]) (by linarith [ht.2])).2
    simpa only [hz] using (h.2.2.2 t ht.1).1
  have he := integral_eq_sub_of_hasDerivAt_of_le hu2' hc hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 2 u)
  have hb := (h.2.2.1 2 (by norm_num) (by norm_num)).1
  rw [hb] at he
  norm_num at he
  apply (eq_div_iff hu0.ne').2
  nlinarith

/-- The lower linear sieve function has its elementary logarithmic formula through four.
CONDITIONAL ON IsLinearSieve. -/
theorem linear_lower_four {F f : ℝ → ℝ} (h : IsLinearSieve F f)
    {u : ℝ} (hu : u ∈ Icc 2 4) :
    f u = 2 * exp eulerMascheroniConstant * log (u - 1) / u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hc : ContinuousOn (fun v : ℝ => v * f v) (Icc 2 u) :=
    continuousOn_id.mul (h.2.1.mono (fun t ht => by change 0 < t; linarith [ht.1]))
  have hd : ∀ t ∈ Ioo (2 : ℝ) u,
      HasDerivAt (fun v => v * f v) (2 * exp eulerMascheroniConstant / (t - 1)) t := by
    intro t ht
    have hf := linear_upper_three h (by linarith [ht.1] : 0 < t - 1)
      (by linarith [ht.2, hu.2] : t - 1 ≤ 3)
    simpa only [hf] using (h.2.2.2 t ht.1).2
  have hi : IntervalIntegrable
      (fun t : ℝ => 2 * exp eulerMascheroniConstant / (t - 1)) volume 2 u := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hu.1]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    linarith [ht.1]
  have he := integral_eq_sub_of_hasDerivAt_of_le hu.1 hc hd hi
  have hI : (∫ t in (2 : ℝ)..u, 2 * exp eulerMascheroniConstant / (t - 1)) =
      2 * exp eulerMascheroniConstant * log (u - 1) := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul,
      integral_comp_sub_right (fun t : ℝ => t⁻¹),
      integral_inv_of_pos (by norm_num) (by linarith [hu.1])]
    norm_num
  have hb := (h.2.2.1 2 (by norm_num) (by norm_num)).2
  rw [hI, hb] at he
  apply (eq_div_iff hu0.ne').2
  nlinarith

/-- The F4 arguments stay inside the elementary lower sieve interval. -/
theorem F4_argument_range (t u : ℝ) (ht : t ∈ Icc kappa1 kappa2)
    (hu : u ∈ Icc t kappa2) : (1 / 2 - t - u) / kappa1 ∈ Icc (2 : ℝ) 4 := by
  norm_num [kappa1, kappa2, mem_Icc] at *
  constructor <;> linarith

/-- The F5 arguments stay inside the same elementary lower sieve interval. -/
theorem F5_argument_range (t u : ℝ) (ht : t ∈ Icc kappa1 kappa2)
    (hu : u ∈ Icc kappa2 (1 / 2 - 2 * kappa1 - t)) :
    (1 / 2 - t - u) / kappa1 ∈ Icc (2 : ℝ) 4 := by
  norm_num [kappa1, kappa2, mem_Icc] at *
  constructor <;> linarith

/-- The next upper sieve interval is an explicit logarithmic integral.
CONDITIONAL ON IsLinearSieve. -/
theorem linear_upper_five {F f : ℝ → ℝ} (h : IsLinearSieve F f)
    {u : ℝ} (hu : u ∈ Icc 3 5) :
    F u = (2 * exp eulerMascheroniConstant) *
      (1 + ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) / u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hc : ContinuousOn (fun v : ℝ => v * F v) (Icc 3 u) :=
    continuousOn_id.mul (h.1.mono (fun t ht => by change 0 < t; linarith [ht.1]))
  have hd : ∀ t ∈ Ioo (3 : ℝ) u,
      HasDerivAt (fun v => v * F v)
        (2 * exp eulerMascheroniConstant * log ((t - 1) - 1) / (t - 1)) t := by
    intro t ht
    have hf := linear_lower_four h
      (show t - 1 ∈ Icc (2 : ℝ) 4 from ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩)
    simpa only [hf] using (h.2.2.2 t (by linarith [ht.1])).1
  have hi : IntervalIntegrable
      (fun t : ℝ => 2 * exp eulerMascheroniConstant * log ((t - 1) - 1) / (t - 1)) volume 3 u := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hu.1]
    apply ContinuousOn.div
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (by fun_prop)
      intro t ht
      linarith [ht.1]
    · fun_prop
    · intro t ht
      linarith [ht.1]
  have he := integral_eq_sub_of_hasDerivAt_of_le hu.1 hc hd hi
  have hI : (∫ t in (3 : ℝ)..u,
      2 * exp eulerMascheroniConstant * log ((t - 1) - 1) / (t - 1)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t := by
    have hf : (fun t : ℝ => 2 * exp eulerMascheroniConstant * log ((t - 1) - 1) / (t - 1)) =
        fun t => (2 * exp eulerMascheroniConstant) *
          ((fun x : ℝ => log (x - 1) / x) (t - 1)) := by funext t; ring
    rw [hf, intervalIntegral.integral_const_mul,
      integral_comp_sub_right (fun x : ℝ => log (x - 1) / x)]
    norm_num
  have hb := linear_upper_three h (u := 3) (by norm_num) (by norm_num)
  rw [hI, hb] at he
  apply (eq_div_iff hu0.ne').2
  nlinarith

/-- The value needed for F0 is reduced to a nested integral of elementary logarithms.
CONDITIONAL ON IsLinearSieve. -/
theorem linear_lower_six {F f : ℝ → ℝ} (h : IsLinearSieve F f) :
    f 6 = (2 * exp eulerMascheroniConstant) *
      (log 3 + ∫ t in (4 : ℝ)..6,
        (1 + ∫ x in (2 : ℝ)..((t - 1) - 1), log (x - 1) / x) / (t - 1)) / 6 := by
  have hc : ContinuousOn (fun v : ℝ => v * f v) (Icc 4 6) :=
    continuousOn_id.mul (h.2.1.mono (fun t ht => by change 0 < t; linarith [ht.1]))
  have hd : ∀ t ∈ Ioo (4 : ℝ) 6, HasDerivAt (fun v => v * f v) (F (t - 1)) t :=
    fun t ht => (h.2.2.2 t (by linarith [ht.1])).2
  have hi : IntervalIntegrable (fun t : ℝ => F (t - 1)) volume 4 6 := by
    apply ContinuousOn.intervalIntegrable
    apply h.1.comp (by fun_prop)
    intro t ht
    rw [uIcc_of_le (by norm_num : (4 : ℝ) ≤ 6)] at ht
    change 0 < t - 1
    linarith [ht.1]
  have he := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (4 : ℝ) ≤ 6) hc hd hi
  have hI : (∫ t in (4 : ℝ)..6, F (t - 1)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in (4 : ℝ)..6,
        (1 + ∫ x in (2 : ℝ)..((t - 1) - 1), log (x - 1) / x) / (t - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (4 : ℝ) ≤ 6)] at ht
    have hf := linear_upper_five h
      (show t - 1 ∈ Icc (3 : ℝ) 5 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simpa only [mul_div_assoc] using hf
  have hb := linear_lower_four h (u := 4) (by constructor <;> norm_num)
  rw [hI, hb] at he
  norm_num at he
  apply (eq_div_iff (by norm_num : (6 : ℝ) ≠ 0)).2
  nlinarith

end LeanLab.ChenDoubleSieve.Task275
