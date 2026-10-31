/-
P0044, Cai 2002: the constant of (4.14), `8/(2θ-1) ∫_{2.29}^{10} log(2.29 - 3.29/(t+1))/t dt ≤ 6.8086`
at θ = 0.95. Proof: substitute s = 1/(t+1), bound log(2.29 - 3.29 s) above by a degree 10
polynomial from Mathlib's Taylor remainder for log around 1.64, split the weight
1/s + 1/(1-s), integrate the polynomial exactly and bound the two logs by series.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Cai2002.Statements

open Finset Real intervalIntegral Set

namespace LeanLab.Cai2002

lemma negLog_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -Real.log (1 - x) ≤ (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  linarith

lemma negLog_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ -Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).2
  linarith

lemma log164_le : Real.log 1.64 ≤ 0.4946963 := by
  have h := negLog_le (x := 64 / 164) (by norm_num) (by norm_num) 20
  have e : Real.log (1 - 64 / 164) = -Real.log 1.64 := by
    rw [show (1 : ℝ) - 64 / 164 = (1.64)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma log_ba_le : Real.log (1100 / 329) ≤ 1.2070078 := by
  have h := negLog_ge (x := 216 / 1316) (by norm_num) (by norm_num) 14
  have e : Real.log (1 - 216 / 1316) = -Real.log (1316 / 1100) := by
    rw [show (1 : ℝ) - 216 / 1316 = (1316 / 1100)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  have e2 : Real.log (1100 / 329) = 2 * Real.log 2 - Real.log (1316 / 1100) := by
    rw [show (1100 : ℝ) / 329 = 2 ^ 2 / (1316 / 1100) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [e2]
  have h2 := Real.log_two_lt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

lemma log_r2_le : Real.log (3290 / 2519) ≤ 0.26702557 := by
  have h := negLog_le (x := 771 / 3290) (by norm_num) (by norm_num) 16
  have e : Real.log (1 - 771 / 3290) = -Real.log (3290 / 2519) := by
    rw [show (1 : ℝ) - 771 / 3290 = (3290 / 2519)⁻¹ by norm_num, Real.log_inv]
  rw [e, neg_neg] at h
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `v = y/1.64 - 1` for `y = 2.29 - 3.29 s`. -/
noncomputable def vf (s : ℝ) : ℝ := (2.29 - 3.29 * s) / 1.64 - 1

/-- Upper polynomial for `log(1.64 (1 + v))`, `|v| ≤ 0.214`. -/
noncomputable def Qv (v : ℝ) : ℝ :=
  0.4946963 + (v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5 - v ^ 6 / 6 + v ^ 7 / 7
    - v ^ 8 / 8 + v ^ 9 / 9) + v ^ 10 / 0.785

lemma log_le_Qv {s : ℝ} (hs : s ∈ Icc (1 / 11 : ℝ) (100 / 329)) :
    Real.log (2.29 - 3.29 * s) ≤ Qv (vf s) := by
  obtain ⟨h1, h2⟩ := hs
  set v := vf s with hv
  have hvu : v ≤ 0.214 := by rw [hv, vf]; norm_num; linarith
  have hvl : -0.214 ≤ v := by rw [hv, vf]; norm_num; linarith
  have habs : |v| ≤ 0.214 := abs_le.mpr ⟨hvl, hvu⟩
  have hy : 2.29 - 3.29 * s = 1.64 * (1 + v) := by rw [hv, vf]; ring
  rw [hy, Real.log_mul (by norm_num) (by linarith)]
  have hx : |(-v)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 9
  rw [abs_neg, sub_neg_eq_add] at h
  have hup := (abs_le.mp h).2
  have hrem : |v| ^ (9 + 1) / (1 - |v|) ≤ v ^ 10 / 0.785 := by
    rw [show |v| ^ (9 + 1) = v ^ 10 by
      rw [pow_abs]; exact abs_of_nonneg (Even.pow_nonneg (by decide) v)]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have e : ∑ i ∈ Finset.range 9, (-v) ^ (i + 1) / ((i : ℝ) + 1) =
      -(v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4 + v ^ 5 / 5 - v ^ 6 / 6 + v ^ 7 / 7
        - v ^ 8 / 8 + v ^ 9 / 9) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring
  rw [e] at hup
  have hc := log164_le
  unfold Qv
  linarith [hup, hrem, hc]

/-- Coefficients of the polynomial part. -/
noncomputable def rC (k : ℕ) : ℝ := [(-6026612435960914997034258101 : ℝ) / 49718801479094350939422720, (-6070558979162810155127187461 : ℝ) / 49718801479094350939422720, (-6218909949228013960508979701 : ℝ) / 49718801479094350939422720, (-5395221724670437236057034631 : ℝ) / 49718801479094350939422720, (-2153027326319995427114579935 : ℝ) / 9943760295818870187884544, (2294602804682544820864801541 : ℝ) / 9943760295818870187884544, (-10567510373167235112372857851 : ℝ) / 9943760295818870187884544, (6814200457794138266011164703 : ℝ) / 4971880147909435093942272, (-371448824387500495323930025 : ℝ) / 276215563772746394107904].getD k 0

noncomputable def Rp (s : ℝ) : ℝ := ∑ k ∈ range 9, rC k * s ^ k

lemma split_Q {s : ℝ} (h0 : s ≠ 0) (h1 : 1 - s ≠ 0) :
    Qv (vf s) * (1 / s + 1 / (1 - s)) = Rp s + Qv (vf 0) * s⁻¹ + Qv (vf 1) * (1 - s)⁻¹ := by
  simp only [Rp, rC, Qv, vf, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  field_simp
  ring

lemma integral_Rp : ∫ s in (1 / 11 : ℝ)..(100 / 329), Rp s =
    ∑ k ∈ range 9, rC k * (((100 / 329 : ℝ) ^ (k + 1) - (1 / 11 : ℝ) ^ (k + 1)) / (k + 1)) := by
  unfold Rp
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    all_goals norm_num
  · intro k _
    exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _

/-- The weight `1/s + 1/(1-s)` is continuous on `[1/11, 100/329]`. -/
lemma weight_cont : ContinuousOn (fun s : ℝ => 1 / s + 1 / (1 - s)) (Icc (1 / 11) (100 / 329)) := by
  apply ContinuousOn.add
  · apply ContinuousOn.div continuousOn_const continuousOn_id
    intro s hs; have : (1 / 11 : ℝ) ≤ s := hs.1; show s ≠ 0; intro h'; linarith
  · apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro s hs; have : s ≤ (100 / 329 : ℝ) := hs.2; show 1 - s ≠ 0; intro h'; linarith

lemma h_cont : ContinuousOn (fun s : ℝ => Real.log (2.29 - 3.29 * s) * (1 / s + 1 / (1 - s)))
    (Icc (1 / 11) (100 / 329)) := by
  apply ContinuousOn.mul _ weight_cont
  apply ContinuousOn.log (by fun_prop)
  intro s hs; have : s ≤ (100 / 329 : ℝ) := hs.2; intro h'; norm_num at h'; linarith

lemma change_var : ∫ t in (2.29 : ℝ)..10, Real.log (2.29 - 3.29 / (t + 1)) / t =
    ∫ s in (1 / 11 : ℝ)..(100 / 329), Real.log (2.29 - 3.29 * s) * (1 / s + 1 / (1 - s)) := by
  set h : ℝ → ℝ := fun s => Real.log (2.29 - 3.29 * s) * (1 / s + 1 / (1 - s)) with hh
  have hf : ∀ x ∈ uIcc (2.29 : ℝ) 10, HasDerivAt (fun t => 1 / (t + 1)) (-1 / (x + 1) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hx1 : x + 1 ≠ 0 := by have := hx.1; intro h'; linarith
    have := ((hasDerivAt_id x).add_const 1).inv hx1
    simp only [one_div]
    convert this using 1 <;> first | (funext t; simp) | simp
  have hf' : ContinuousOn (fun x : ℝ => -1 / (x + 1) ^ 2) (uIcc (2.29 : ℝ) 10) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; rw [Set.uIcc_of_le (by norm_num)] at hx; have := hx.1; positivity
  have himg : (fun t : ℝ => 1 / (t + 1)) '' uIcc (2.29 : ℝ) 10 ⊆ Icc (1 / 11) (100 / 329) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le (by norm_num)] at ht
    obtain ⟨ht1, ht2⟩ := ht
    constructor
    · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hg : ContinuousOn (fun s => -h s) ((fun t : ℝ => 1 / (t + 1)) '' uIcc (2.29 : ℝ) 10) :=
    (h_cont.neg).mono himg
  have key := intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  have lhs : ∫ t in (2.29 : ℝ)..10, Real.log (2.29 - 3.29 / (t + 1)) / t =
      ∫ t in (2.29 : ℝ)..10, ((fun s => -h s) ∘ (fun t => 1 / (t + 1))) t * (-1 / (t + 1) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht0 : t ≠ 0 := by have := ht.1; intro h'; linarith
    have ht1 : t + 1 ≠ 0 := by have := ht.1; intro h'; linarith
    simp only [Function.comp, hh]
    have e1 : 1 - 1 / (t + 1) = t / (t + 1) := by field_simp; ring
    rw [e1, show 3.29 * (1 / (t + 1)) = 3.29 / (t + 1) by ring]
    field_simp
  rw [lhs, key]
  rw [show (1 : ℝ) / (2.29 + 1) = 100 / 329 by norm_num, show (1 : ℝ) / (10 + 1) = 1 / 11 by norm_num]
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_neg, neg_neg]

lemma Q_cont : ContinuousOn (fun s : ℝ => Qv (vf s) * (1 / s + 1 / (1 - s)))
    (Icc (1 / 11) (100 / 329)) := by
  apply ContinuousOn.mul _ weight_cont
  apply Continuous.continuousOn; unfold Qv vf; fun_prop

lemma inv_cont : ContinuousOn (fun s : ℝ => s⁻¹) (Icc (1 / 11) (100 / 329)) := by
  apply ContinuousOn.inv₀ continuousOn_id
  intro s hs; have : (1 / 11 : ℝ) ≤ s := hs.1; show s ≠ 0; intro h'; linarith

lemma inv1_cont : ContinuousOn (fun s : ℝ => (1 - s)⁻¹) (Icc (1 / 11) (100 / 329)) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro s hs; have : s ≤ (100 / 329 : ℝ) := hs.2; intro h'; linarith

/-- (4.14) at θ = 0.95. The bound reached is 6.80845; the true value is 6.80844. -/
theorem eq414 : Eq414Const := by
  unfold Eq414Const
  simp only
  rw [change_var]
  have hab : (1 / 11 : ℝ) ≤ 100 / 329 := by norm_num
  have hmono : ∫ s in (1 / 11 : ℝ)..(100 / 329), Real.log (2.29 - 3.29 * s) * (1 / s + 1 / (1 - s))
      ≤ ∫ s in (1 / 11 : ℝ)..(100 / 329), Qv (vf s) * (1 / s + 1 / (1 - s)) := by
    apply intervalIntegral.integral_mono_on hab (h_cont.intervalIntegrable_of_Icc hab)
      (Q_cont.intervalIntegrable_of_Icc hab)
    intro s hs
    have hw : 0 ≤ 1 / s + 1 / (1 - s) := by
      have h1 : (1 / 11 : ℝ) ≤ s := hs.1
      have h2 : s ≤ (100 / 329 : ℝ) := hs.2
      have : 0 < 1 - s := by linarith
      have : 0 < s := by linarith
      positivity
    exact mul_le_mul_of_nonneg_right (log_le_Qv hs) hw
  have hsplit : ∫ s in (1 / 11 : ℝ)..(100 / 329), Qv (vf s) * (1 / s + 1 / (1 - s)) =
      (∫ s in (1 / 11 : ℝ)..(100 / 329), Rp s) + Qv (vf 0) * (∫ s in (1 / 11 : ℝ)..(100 / 329), s⁻¹)
        + Qv (vf 1) * (∫ s in (1 / 11 : ℝ)..(100 / 329), (1 - s)⁻¹) := by
    have hc : ∫ s in (1 / 11 : ℝ)..(100 / 329), Qv (vf s) * (1 / s + 1 / (1 - s)) =
        ∫ s in (1 / 11 : ℝ)..(100 / 329), (Rp s + Qv (vf 0) * s⁻¹ + Qv (vf 1) * (1 - s)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      have h1 : (1 / 11 : ℝ) ≤ s := hs.1
      have h2 : s ≤ (100 / 329 : ℝ) := hs.2
      exact split_Q (by intro h'; linarith) (by intro h'; linarith)
    rw [hc]
    have iR : IntervalIntegrable Rp MeasureTheory.volume (1 / 11 : ℝ) (100 / 329) := by
      apply Continuous.intervalIntegrable; unfold Rp; fun_prop
    have i1 := (inv_cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab).const_mul (Qv (vf 0))
    have i2 := (inv1_cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab).const_mul (Qv (vf 1))
    rw [intervalIntegral.integral_add (iR.add i1) i2, intervalIntegral.integral_add iR i1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hinv : ∫ s in (1 / 11 : ℝ)..(100 / 329), s⁻¹ = Real.log (1100 / 329) := by
    rw [integral_inv_of_pos (by norm_num) (by norm_num)]; norm_num
  have hinv1 : ∫ s in (1 / 11 : ℝ)..(100 / 329), (1 - s)⁻¹ = Real.log (3290 / 2519) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) (1 : ℝ),
      integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  rw [hsplit, hinv, hinv1, integral_Rp] at hmono
  have hQ0 : 0 < Qv (vf 0) := by unfold Qv vf; norm_num
  have hQ1 : 0 < Qv (vf 1) := by unfold Qv vf; norm_num
  have l1 := mul_le_mul_of_nonneg_left log_ba_le hQ0.le
  have l2 := mul_le_mul_of_nonneg_left log_r2_le hQ1.le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rC] at hmono
  norm_num [Qv, vf] at hmono l1 l2
  norm_num
  linarith

end LeanLab.Cai2002
