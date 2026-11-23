/-
ROUTE BURST burst-20261122, session S81. Inputs to the LEAF outer_square_bound of
KernelSumSplit1122, P0088 Kumchev and Liu 2007, page 7, the display before 27.
* f2_integral_le: the integral part of f2Weight z0 u is at most 1/log z0 when
  e at most z0 at most sqrt u.
* f2Weight_le_two, f2Weight_nonneg, abs_f2Weight_le_two: then 0 at most f2Weight z0 u at most 2.
* square_gap_window: two squares m^2 < m'^2 with s at most m that lie in a window of
  length H satisfy (m' - m) 2s < H, the square counting input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelSumPieces1122

namespace LeanLab.KumchevLiu2007.KernelSumF2Bound1122

open Real LeanLab.KumchevLiu2007 Task556a

/-- PROVED. For e at most z0 at most sqrt u, the integral of 1/(t log t log(u/t)) over
[z0, sqrt u] is at most 1/log z0. -/
theorem f2_integral_le (z0 u : ℝ) (hz : Real.exp 1 ≤ z0) (hzu : z0 ≤ Real.sqrt u) :
    ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) ≤ 1 / Real.log z0 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hz0 : 0 < z0 := lt_of_lt_of_le he hz
  have hL : 1 ≤ Real.log z0 := by
    have := Real.log_le_log he hz; rwa [Real.log_exp] at this
  have hsu : 0 < Real.sqrt u := lt_of_lt_of_le hz0 hzu
  have hu : 0 < u := Real.sqrt_pos.mp hsu
  have hM : Real.log z0 ≤ Real.log (Real.sqrt u) := Real.log_le_log hz0 hzu
  set L := Real.log z0
  set M := Real.log (Real.sqrt u)
  have hLM : 0 < L * M := by nlinarith
  have hpt : ∀ t ∈ Set.Icc z0 (Real.sqrt u),
      1 / (t * Real.log t * Real.log (u / t)) ≤ 1 / (L * M) * (1 / t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hz0 ht.1
    have h1 : L ≤ Real.log t := Real.log_le_log hz0 ht.1
    have hut : Real.sqrt u ≤ u / t := by
      rw [le_div_iff₀ ht0]
      have hs := Real.mul_self_sqrt hu.le
      nlinarith [ht.2]
    have h2 : M ≤ Real.log (u / t) := Real.log_le_log hsu hut
    have hk : t * L * M ≤ t * Real.log t * Real.log (u / t) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 ht0.le) h2 (by linarith)
        (mul_nonneg ht0.le (by linarith))
    calc 1 / (t * Real.log t * Real.log (u / t)) ≤ 1 / (t * L * M) :=
          one_div_le_one_div_of_le (mul_pos (mul_pos ht0 (by linarith)) (by linarith)) hk
      _ = 1 / (L * M) * (1 / t) := by field_simp
  have hg : IntervalIntegrable (fun t : ℝ => 1 / (L * M) * (1 / t)) MeasureTheory.volume
      z0 (Real.sqrt u) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_const.div continuousOn_id ?_)
    intro x hx
    rw [Set.uIcc_of_le hzu] at hx
    exact ne_of_gt (lt_of_lt_of_le hz0 hx.1)
  have hint : ∫ t in z0..Real.sqrt u, 1 / (L * M) * (1 / t) ≤ 1 / L := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hz0 hsu,
      Real.log_div hsu.ne' hz0.ne']
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hLM (by linarith)]
    nlinarith
  by_cases hf : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t * Real.log (u / t)))
      MeasureTheory.volume z0 (Real.sqrt u)
  · exact (intervalIntegral.integral_mono_on hzu hf hg hpt).trans hint
  · rw [intervalIntegral.integral_undef hf]
    exact div_nonneg zero_le_one (by linarith)

/-- PROVED. For e at most z0 at most sqrt u, f2Weight z0 u is at most 2. -/
theorem f2Weight_le_two (z0 u : ℝ) (hz : Real.exp 1 ≤ z0) (hzu : z0 ≤ Real.sqrt u) :
    f2Weight z0 u ≤ 2 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hz0 : 0 < z0 := lt_of_lt_of_le he hz
  have hL : 1 ≤ Real.log z0 := by
    have := Real.log_le_log he hz; rwa [Real.log_exp] at this
  have hsu : 0 < Real.sqrt u := lt_of_lt_of_le hz0 hzu
  have hu : 0 < u := Real.sqrt_pos.mp hsu
  have hM : Real.log z0 ≤ Real.log (Real.sqrt u) := Real.log_le_log hz0 hzu
  have hlu : 1 ≤ Real.log u := by
    rw [Real.log_sqrt hu.le] at hM; linarith
  have h1 : 1 / Real.log u ≤ 1 := by rw [div_le_one (by linarith)]; exact hlu
  have h2 : 1 / Real.log z0 ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
  have h3 := f2_integral_le z0 u hz hzu
  unfold f2Weight
  linarith

/-- PROVED. For e at most z0 at most sqrt u, f2Weight z0 u is nonnegative. -/
theorem f2Weight_nonneg (z0 u : ℝ) (hz : Real.exp 1 ≤ z0) (hzu : z0 ≤ Real.sqrt u) :
    0 ≤ f2Weight z0 u := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hz0 : 0 < z0 := lt_of_lt_of_le he hz
  have hL : 1 ≤ Real.log z0 := by
    have := Real.log_le_log he hz; rwa [Real.log_exp] at this
  have hsu : 0 < Real.sqrt u := lt_of_lt_of_le hz0 hzu
  have hu : 0 < u := Real.sqrt_pos.mp hsu
  have hM : Real.log z0 ≤ Real.log (Real.sqrt u) := Real.log_le_log hz0 hzu
  have hlu : 1 ≤ Real.log u := by
    rw [Real.log_sqrt hu.le] at hM; linarith
  unfold f2Weight
  refine add_nonneg (div_nonneg zero_le_one (by linarith)) ?_
  refine intervalIntegral.integral_nonneg hzu (fun t ht => ?_)
  have ht0 : 0 < t := lt_of_lt_of_le hz0 ht.1
  have h1 : 1 ≤ Real.log t := hL.trans (Real.log_le_log hz0 ht.1)
  have hut : Real.sqrt u ≤ u / t := by
    rw [le_div_iff₀ ht0]
    have hs := Real.mul_self_sqrt hu.le
    nlinarith [ht.2]
  have h2 : 1 ≤ Real.log (u / t) := (hL.trans hM).trans (Real.log_le_log hsu hut)
  exact div_nonneg zero_le_one (mul_nonneg (mul_nonneg ht0.le (by linarith)) (by linarith))

/-- PROVED. |f2Weight z0 u| at most 2 for e at most z0 at most sqrt u. -/
theorem abs_f2Weight_le_two (z0 u : ℝ) (hz : Real.exp 1 ≤ z0) (hzu : z0 ≤ Real.sqrt u) :
    |f2Weight z0 u| ≤ 2 := by
  rw [abs_of_nonneg (f2Weight_nonneg z0 u hz hzu)]
  exact f2Weight_le_two z0 u hz hzu

/-- PROVED. Square counting: if s at most m < m' and m^2, m'^2 lie in [A, A + H), then
(m' - m) 2s < H. -/
theorem square_gap_window (s A H : ℝ) (m m' : ℕ) (hs : s ≤ m) (hmm : m ≤ m')
    (hA : A ≤ (m : ℝ) ^ 2) (hH : (m' : ℝ) ^ 2 < A + H) :
    ((m' : ℝ) - m) * (2 * s) < H := by
  have h := KernelSumPieces1122.sq_gap m m' hmm
  have h' : (m : ℝ) ≤ m' := by exact_mod_cast hmm
  have h3 : ((m' : ℝ) - m) * (2 * s) ≤ ((m' : ℝ) - m) * (2 * m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

end LeanLab.KumchevLiu2007.KernelSumF2Bound1122

#print axioms LeanLab.KumchevLiu2007.KernelSumF2Bound1122.f2_integral_le
#print axioms LeanLab.KumchevLiu2007.KernelSumF2Bound1122.f2Weight_le_two
#print axioms LeanLab.KumchevLiu2007.KernelSumF2Bound1122.f2Weight_nonneg
#print axioms LeanLab.KumchevLiu2007.KernelSumF2Bound1122.abs_f2Weight_le_two
#print axioms LeanLab.KumchevLiu2007.KernelSumF2Bound1122.square_gap_window
