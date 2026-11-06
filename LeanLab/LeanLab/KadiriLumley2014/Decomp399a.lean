/-
P0059 arXiv 1407.7902v1 page 7 Lemma 2.5.
Written derivation: arXiv 1310.6374 pages 8 to 10, Section 2.3.
Five independent weighted zero estimates replace the combined proof task.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259
import LeanLab.KadiriLumley2014.DensityBound399
import LeanLab.KadiriLumley2014.EndpointIntegral399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory
open Task259


/-! ### Private helpers for the three Rosser leaves

The Rosser count bound is used through a strict/inclusive Abel summation on the
window `(U, V]`.  All the estimates below are elementary: the derivative of the
count main term is `log (t / 2π) / 2π`, the derivative of the Rosser remainder is
`0.137 / t + 0.443 / (t * log t)`, and the two agree at `T = 1132491` after
multiplication by `countQ`. -/

private lemma two_pi_pos : (0 : ℝ) < 2 * π := by positivity

private lemma log_two_pi_pos : 0 < Real.log (2 * π) := by
  apply Real.log_pos
  linarith [Real.pi_gt_three]

/-- The count main term has derivative `log (t / 2π) / 2π`. -/
private lemma hasDerivAt_countMain {t : ℝ} (ht : 0 < t) :
    HasDerivAt countMain ((1 / (2 * π)) * Real.log (t / (2 * π))) t := by
  have h2π : (0 : ℝ) < 2 * π := two_pi_pos
  have hne : t / (2 * π) ≠ 0 := (div_pos ht h2π).ne'
  have hu : HasDerivAt (fun x : ℝ => x / (2 * π)) (1 / (2 * π)) t := by
    simpa using (hasDerivAt_id t).div_const (2 * π)
  have hl : HasDerivAt (fun x : ℝ => Real.log (x / (2 * π))) (1 / t) t := by
    have h := hu.log hne
    convert h using 1
    field_simp
  have hmul : HasDerivAt (fun x : ℝ => x / (2 * π) * Real.log (x / (2 * π)))
      ((1 / (2 * π)) * Real.log (t / (2 * π)) + 1 / (2 * π)) t := by
    have h := hu.mul hl
    convert h using 1
    field_simp
  have hfin : HasDerivAt (fun x : ℝ => x / (2 * π) * Real.log (x / (2 * π)) - x / (2 * π)
      + 7 / 8) ((1 / (2 * π)) * Real.log (t / (2 * π))) t := by
    have h := (hmul.sub hu).add_const (7 / 8)
    convert h using 1
    ring
  convert hfin using 1
  ext x
  simp only [countMain]

/-- The Rosser remainder has derivative `0.137 / t + 0.443 / (t * log t)`. -/
private lemma hasDerivAt_countRemainder {t : ℝ} (ht : 1 < t) :
    HasDerivAt countRemainder (0.137 / t + 0.443 / (t * Real.log t)) t := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht
  have h1 : HasDerivAt (fun x : ℝ => Real.log x) (1 / t) t := by
    simpa using Real.hasDerivAt_log ht0.ne'
  have h2 : HasDerivAt (fun x : ℝ => Real.log (Real.log x)) (1 / (t * Real.log t)) t := by
    have h := (Real.hasDerivAt_log hlog.ne').comp t h1
    convert h using 1
    · rfl
    · rw [div_eq_mul_inv, mul_comm]
      ring
  have hfin : HasDerivAt (fun x : ℝ => 0.137 * Real.log x + 0.443 * Real.log (Real.log x))
      (0.137 / t + 0.443 / (t * Real.log t)) t := by
    have h := (h1.const_mul 0.137).add (h2.const_mul 0.443)
    convert h using 1
    ring
  convert hfin.add_const 1.588 using 1
  ext x
  simp only [countRemainder]

/-- The Rosser `q` correction, multiplied by `log (T / 2π)`, is the derivative of
the Rosser remainder at `T`. -/
private lemma countQ_mul_log {T : ℝ} (hT : 1132491 ≤ T) :
    countQ T * Real.log (T / (2 * π)) = 0.137 / T + 0.443 / (T * Real.log T) := by
  have h2π : (0 : ℝ) < 2 * π := two_pi_pos
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hpi := Real.pi_lt_four
  have hshift : 0 < Real.log (T / (2 * π)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ h2π]
    linarith
  have hTne : T ≠ 0 := hT0.ne'
  have hlT : Real.log T ≠ 0 := hlogT.ne'
  have hsT : Real.log (T / (2 * π)) ≠ 0 := hshift.ne'
  unfold countQ
  field_simp

/-- At every ordinate above the lower bound the Rosser remainder derivative is
dominated by `countQ U * log (t / 2π)`. -/
private lemma countRemainder_deriv_le {U t : ℝ} (hU : 1132491 ≤ U) (ht : U ≤ t) :
    0.137 / t + 0.443 / (t * Real.log t) ≤ countQ U * Real.log (t / (2 * π)) := by
  have h2π : (0 : ℝ) < 2 * π := two_pi_pos
  have hU0 : 0 < U := by linarith
  have htpos : 0 < t := hU0.trans_le ht
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith : (1 : ℝ) < U)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith : (1 : ℝ) < t)
  have hlogUt : Real.log U ≤ Real.log t := Real.log_le_log hU0 ht
  have hpi := Real.pi_lt_four
  have hshiftU : 0 < Real.log (U / (2 * π)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ h2π]
    linarith
  have hshift : Real.log (U / (2 * π)) ≤ Real.log (t / (2 * π)) := by
    apply Real.log_le_log (div_pos hU0 h2π)
    exact div_le_div_of_nonneg_right ht h2π.le
  have hqpos : 0 < countQ U := by
    have h := countQ_mul_log hU
    have hpos : 0 < 0.137 / U + 0.443 / (U * Real.log U) := by positivity
    have hqdef : countQ U =
        (0.137 / U + 0.443 / (U * Real.log U)) / Real.log (U / (2 * π)) := by
      rw [← h]
      field_simp
    rw [hqdef]
    positivity
  have h1 : countQ U * Real.log (U / (2 * π)) ≤ countQ U * Real.log (t / (2 * π)) := by
    exact mul_le_mul_of_nonneg_left hshift hqpos.le
  rw [countQ_mul_log hU] at h1
  have h2 : 0.137 / t ≤ 0.137 / U := by
    apply div_le_div_of_nonneg_left (by norm_num) hU0 ht
  have h3 : 0.443 / (t * Real.log t) ≤ 0.443 / (U * Real.log U) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 0.443)
    · positivity
    · exact mul_le_mul ht hlogUt hlogU.le htpos.le
  linarith

/-! ### Finite logarithmic integrals -/

/-- The derivative of `log (t / c)` at a positive point. -/
private lemma hasDerivAt_log_div {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => Real.log (x / c)) (1 / t) t := by
  have hu : HasDerivAt (fun x : ℝ => x / c) (1 / c) t := by
    simpa using (hasDerivAt_id t).div_const c
  have h := hu.log (div_ne_zero ht.ne' hc.ne')
  convert h using 1
  field_simp

/-- The reciprocal logarithm integrates to half the difference of squared logarithms. -/
private lemma integral_log_div_reciprocal {c U V : ℝ} (hc : 0 < c) (hU : 0 < U)
    (hUV : U ≤ V) :
    (∫ t in U..V, Real.log (t / c) / t) =
      ((Real.log (V / c)) ^ 2 - (Real.log (U / c)) ^ 2) / 2 := by
  have hd : ∀ t ∈ Icc U V, HasDerivAt (fun x : ℝ => (Real.log (x / c)) ^ 2 / 2)
      (Real.log (t / c) / t) t := by
    intro t ht
    have ht0 : 0 < t := hU.trans_le ht.1
    have h := (hasDerivAt_log_div hc ht0).pow 2 |>.div_const 2
    convert h using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t / c) / t) (Icc U V) := by
    fun_prop (disch := intro t ht; positivity [hU.trans_le ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (t / c) / t) volume U V :=
    hcont.intervalIntegrable_of_Icc hUV
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (Real.log (x / c)) ^ 2 / 2)
    (f' := fun t : ℝ => Real.log (t / c) / t)
    (fun t ht => hd t (by simpa only [uIcc_of_le hUV] using ht)) hi
  rw [he]
  ring

/-- The logarithmic power primitive of order `m` on the cited page 9 of the source. -/
private lemma hasDerivAt_logPowerPrimitive {m : ℕ} (hm : 0 < m) {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (1 + (m : ℝ) * Real.log (x / c)) / ((m : ℝ) ^ 2 * x ^ m))
      (-Real.log (t / c) / t ^ (m + 1)) t := by
  rcases m with _ | n
  · omega
  have hnum := ((hasDerivAt_log_div hc ht).const_mul ((n : ℝ) + 1)).const_add 1
  have hden := ((hasDerivAt_id t).pow (n + 1)).const_mul (((n : ℝ) + 1) ^ 2)
  have h := hnum.div hden (mul_ne_zero (by positivity) (pow_ne_zero _ ht.ne'))
  convert h using 1
  · ext x
    simp only [Nat.cast_add, Nat.cast_one, Pi.div_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.pow_apply, id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    simp only [pow_succ]
    field_simp
    ; ring

/-- The finite logarithmic reciprocal-power integral is the exact primitive difference. -/
private lemma integral_log_div_power {m : ℕ} (hm : 0 < m) {c U V : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hUV : U ≤ V) :
    (∫ t in U..V, Real.log (t / c) / t ^ (m + 1)) =
      (1 + (m : ℝ) * Real.log (U / c)) / ((m : ℝ) ^ 2 * U ^ m) -
        (1 + (m : ℝ) * Real.log (V / c)) / ((m : ℝ) ^ 2 * V ^ m) := by
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t / c) / t ^ (m + 1)) (Icc U V) := by
    fun_prop (disch := intro t ht; positivity [hU.trans_le ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (t / c) / t ^ (m + 1)) volume U V :=
    hcont.intervalIntegrable_of_Icc hUV
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => -((1 + (m : ℝ) * Real.log (x / c)) / ((m : ℝ) ^ 2 * x ^ m)))
    (f' := fun t : ℝ => Real.log (t / c) / t ^ (m + 1))
    (fun t ht => by
      rw [uIcc_of_le hUV] at ht
      convert (hasDerivAt_logPowerPrimitive hm hc (hU.trans_le ht.1)).neg using 1
      ring) hi
  linarith [he]

/-- The difference of squared endpoint logarithms equals the product printed for S1. -/
private lemma log_square_difference_eq {c U V : ℝ} (hc : 0 < c) (hU : 0 < U) (hV : 0 < V) :
    ((Real.log (V / c)) ^ 2 - (Real.log (U / c)) ^ 2) / 2 =
      Real.log (V / U) * Real.log (Real.sqrt (V * U) / c) := by
  have hs : 0 < Real.sqrt (V * U) := Real.sqrt_pos.mpr (mul_pos hV hU)
  rw [Real.log_div hV.ne' hc.ne', Real.log_div hU.ne' hc.ne',
    Real.log_div hV.ne' hU.ne', Real.log_div hs.ne' hc.ne',
    Real.log_sqrt (mul_nonneg hV.le hU.le), Real.log_mul hV.ne' hU.ne']
  ring

/-! ### Abel summation on the window `(U, V]` -/

/-- The `(U, V]` zero window, integrated against the derivative, with inclusive counts
at both endpoints. -/
private theorem window_summation {U V : ℝ} (hUV : U ≤ V)
    {φ φ' : ℝ → ℝ} (hd : ∀ t ∈ Icc U V, HasDerivAt φ (φ' t) t)
    (hi : IntervalIntegrable φ' volume U V)
    (hBin : IntervalIntegrable (fun t => inclusiveCount t * φ' t) volume U V) :
    positiveZeroSum (fun ρ => if U < ρ.im ∧ ρ.im ≤ V then φ ρ.im else 0) =
      φ V * inclusiveCount V - φ U * inclusiveCount U -
        ∫ t in U..V, inclusiveCount t * φ' t := by
  classical
  set s := (positiveZerosBelow (V + 1)).filter
    (fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
      U < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V) with hs
  have hsum : positiveZeroSum (fun z : ℂ => if U < z.im ∧ z.im ≤ V then φ z.im else 0)
      = ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * φ (ρ : ℂ).im := by
    have hcut : ∀ ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
        V + 1 ≤ (ρ : ℂ).im →
          (if U < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V then φ (ρ : ℂ).im else 0) = 0 := by
      intro ρ hV
      have h : ¬ ((ρ : ℂ).im ≤ V) := by linarith
      rw [ite_eq_right (by tauto : ¬ (U < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V))]
    rw [positiveZeroSum_eq_finite (V + 1) _ hcut, hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases h : U < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V
    · simp [h]
    · simp [h]
  have hzero : ∀ t : ℝ, t ≤ V → zeroCount t =
      ∑ ρ ∈ positiveZerosBelow (V + 1), (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if (ρ : ℂ).im < t then 1 else 0) := by
    intro t ht
    have hcut : ∀ ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
        V + 1 ≤ (ρ : ℂ).im → (if (ρ : ℂ).im < t then (1 : ℝ) else 0) = 0 := by
      intro ρ hV
      have h : ¬ ((ρ : ℂ).im < t) := by linarith
      rw [ite_eq_right h]
    rw [show zeroCount t = positiveZeroSum (fun z : ℂ => if z.im < t then 1 else 0) from rfl,
      positiveZeroSum_eq_finite (V + 1) _ hcut]
  have hincl : ∀ t : ℝ, t ≤ V → inclusiveCount t =
      ∑ ρ ∈ positiveZerosBelow (V + 1), (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if (ρ : ℂ).im ≤ t then 1 else 0) := by
    intro t ht
    have hcut : ∀ ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
        V + 1 ≤ (ρ : ℂ).im → (if (ρ : ℂ).im ≤ t then (1 : ℝ) else 0) = 0 := by
      intro ρ hV
      have h : ¬ ((ρ : ℂ).im ≤ t) := by linarith
      rw [ite_eq_right h]
    rw [show inclusiveCount t = positiveZeroSum (fun z : ℂ => if z.im ≤ t then 1 else 0) from rfl,
      positiveZeroSum_eq_finite (V + 1) _ hcut]
  have key : ∀ (w : ℝ) (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) (t : ℝ),
      U < t → t ≤ V →
      (if U < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V then (if (ρ : ℂ).im < t then w else 0) else 0)
        = (if (ρ : ℂ).im < t then w else 0) - (if (ρ : ℂ).im ≤ U then w else 0) := by
    intro w ρ t hUt htV
    by_cases h1 : U < (ρ : ℂ).im
    · by_cases h2 : (ρ : ℂ).im ≤ V
      · have h4 : ¬ ((ρ : ℂ).im ≤ U) := not_le.mpr h1
        simp [h1, h2, h4]
      · have h5 : ¬ ((ρ : ℂ).im < t) := by
          intro hc
          exact h2 (le_of_lt (lt_of_lt_of_le hc htV))
        simp [h1, h2, h5]
    · have h2 : (ρ : ℂ).im ≤ U := le_of_not_gt h1
      have h3 : (ρ : ℂ).im < t := lt_of_le_of_lt h2 hUt
      simp [h1, h2, h3]
  have htotal : ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) =
      inclusiveCount V - inclusiveCount U := by
    rw [hs, Finset.sum_filter, hincl V le_rfl, hincl U hUV, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases h1 : U < (ρ : ℂ).im
    · by_cases h2 : (ρ : ℂ).im ≤ V
      · have h4 : ¬ ((ρ : ℂ).im ≤ U) := not_le.mpr h1
        simp [h1, h2, h4]
      · have h4 : ¬ ((ρ : ℂ).im ≤ U) := not_le.mpr h1
        simp [h1, h2, h4]
    · have h2 : (ρ : ℂ).im ≤ U := le_of_not_gt h1
      have h5 : ((ρ : ℂ).im ≤ V) := h2.trans hUV
      simp [h1, h2, h5]
  have hcount : ∀ t : ℝ, U < t → t ≤ V →
      ∑ ρ ∈ s, (if (ρ : ℂ).im < t then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) =
        zeroCount t - inclusiveCount U := by
    intro t hUt htV
    rw [hs, Finset.sum_filter, hzero t htV, hincl U hUV, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [key ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) ρ t hUt htV]
    by_cases h : (ρ : ℂ).im ≤ U <;> simp [h]
  have hγ : ∀ ρ ∈ s, (ρ : ℂ).im ∈ Icc U V := by
    intro ρ hρ
    rw [hs, Finset.mem_filter] at hρ
    exact ⟨hρ.2.1.le, hρ.2.2⟩
  have hfin := finite_partial_summation s (fun ρ => (ρ : ℂ).im)
    (fun ρ => (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) hγ hd hi
  have hint : (∫ t in U..V, (∑ ρ ∈ s,
      if (ρ : ℂ).im < t then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) * φ' t)
      = ∫ t in U..V, (zeroCount t - inclusiveCount U) * φ' t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t htt
    rw [Set.uIoc_of_le hUV] at htt
    rw [hcount t htt.1 htt.2]
  have hint2 : (∫ t in U..V, (zeroCount t - inclusiveCount U) * φ' t)
      = ∫ t in U..V, (inclusiveCount t - inclusiveCount U) * φ' t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [inclusiveCount_ae_eq_zeroCount] with t ht _
    rw [← ht]
  have hsplit : (∫ t in U..V, (inclusiveCount t - inclusiveCount U) * φ' t)
      = (∫ t in U..V, inclusiveCount t * φ' t) - inclusiveCount U * (φ V - φ U) := by
    have h1 : (fun t => (inclusiveCount t - inclusiveCount U) * φ' t)
        = (fun t => inclusiveCount t * φ' t - inclusiveCount U * φ' t) := by
      funext t
      ring
    rw [h1, intervalIntegral.integral_sub hBin (hi.const_mul (inclusiveCount U)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := φ) (f' := φ') (fun t ht => hd t (by
          rw [uIcc_of_le hUV] at ht
          exact ht)) hi]
  rw [hsum, hfin, htotal, hint, hint2, hsplit]
  ring

/-! ### The Rosser count-error transfer -/

/-- The Rosser count bound transfers the weighted `(U, V]` zero window to the exact
logarithmic integral, with the Rosser error at the lower endpoint retained. -/
private theorem rosser_window_bound {U V : ℝ} (hU : 1132491 ≤ U) (hUV : U ≤ V)
    {φ φ' : ℝ → ℝ} (hcont : ContinuousOn φ (Icc U V))
    (hd : ∀ t ∈ Icc U V, HasDerivAt φ (φ' t) t)
    (hi : IntervalIntegrable φ' volume U V)
    (hφnn : ∀ t ∈ Icc U V, 0 ≤ φ t)
    (hφ'np : ∀ t ∈ Icc U V, φ' t ≤ 0)
    (hCount : RosserCountBound) :
    positiveZeroSum (fun ρ => if U < ρ.im ∧ ρ.im ≤ V then φ ρ.im else 0) ≤
      (1 / (2 * π) + countQ U) * (∫ t in U..V, Real.log (t / (2 * π)) * φ t) +
        2 * countRemainder U * φ U := by
  classical
  have hU2 : (2 : ℝ) ≤ U := by linarith
  have hU1 : (1 : ℝ) < U := by linarith
  have hU0 : (0 : ℝ) < U := by linarith
  have hV2 : (2 : ℝ) ≤ V := hU2.trans hUV
  have hφVnn : 0 ≤ φ V := hφnn V ⟨hUV, le_rfl⟩
  have hφUnn : 0 ≤ φ U := hφnn U ⟨le_rfl, hUV⟩
  have hRUnn : 0 ≤ countRemainder U := by
    have he : Real.exp 1 < U := Real.exp_one_lt_three.trans_le (by linarith : (3 : ℝ) ≤ U)
    have h1 : 1 < Real.log U := (Real.lt_log_iff_exp_lt hU0).mpr he
    have h2 : 0 < Real.log (Real.log U) := Real.log_pos h1
    unfold countRemainder
    positivity
  have hBV : inclusiveCount V ≤ countMain V + countRemainder V := by
    have h := inclusive_rosser_bound hCount hV2
    linarith [(abs_le.mp h).2]
  have hBU : countMain U - countRemainder U ≤ inclusiveCount U := by
    have h := inclusive_rosser_bound hCount hU2
    linarith [(abs_le.mp h).1]
  have hK : ∀ t ∈ Icc U V, inclusiveCount t ≤ countMain t + countRemainder t := by
    intro t ht
    have h := inclusive_rosser_bound hCount (by linarith [ht.1] : (2 : ℝ) ≤ t)
    linarith [(abs_le.mp h).2]
  -- integrability of the inclusive count against `φ'`
  have hBint : IntervalIntegrable (fun t => inclusiveCount t * φ' t) volume U V := by
    have h1 : IntervalIntegrable (fun t => zeroCount t * φ' t) volume U V := by
      simpa only [zeroCount_eq_densityCount_zero] using
        densityCount_mul_integrable (σ := 0) hUV hi
    refine h1.congr_ae ?_
    filter_upwards [inclusiveCount_ae_eq_zeroCount.filter_mono
      (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)] with t ht
    rw [ht]
  have hW := window_summation hUV hd hi hBint
  -- continuity and integrability of the two count pieces
  have hMcont : ContinuousOn countMain (Icc U V) :=
    fun t ht => (hasDerivAt_countMain (hU0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hRcont : ContinuousOn countRemainder (Icc U V) :=
    fun t ht => (hasDerivAt_countRemainder (hU1.trans_le ht.1)).continuousAt.continuousWithinAt
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log (t / (2 * π))) (Icc U V) := by
    apply ContinuousOn.log
    · fun_prop
    · intro t ht
      exact (div_pos (hU0.trans_le ht.1) two_pi_pos).ne'
  have hR'cont : ContinuousOn (fun t : ℝ => 0.137 / t + 0.443 / (t * Real.log t)) (Icc U V) := by
    have hdiv1 : ContinuousOn (fun t : ℝ => 0.137 / t) (Icc U V) := by
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro t ht
      exact (hU0.trans_le ht.1).ne'
    have hdiv2 : ContinuousOn (fun t : ℝ => 0.443 / (t * Real.log t)) (Icc U V) := by
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_id.mul (Real.continuousOn_log.mono (fun t ht => (hU0.trans_le ht.1).ne'))
      · intro t ht
        have ht1 : (0 : ℝ) < t := hU0.trans_le ht.1
        have ht2 : 0 < Real.log t := Real.log_pos (hU1.trans_le ht.1)
        positivity
    exact hdiv1.add hdiv2
  have hM'int : IntervalIntegrable (fun t : ℝ => (1 / (2 * π)) * Real.log (t / (2 * π)))
      volume U V := (hlogcont.const_mul _).intervalIntegrable_of_Icc hUV
  have hR'int : IntervalIntegrable (fun t : ℝ => 0.137 / t + 0.443 / (t * Real.log t))
      volume U V := hR'cont.intervalIntegrable_of_Icc hUV
  have hΦint : IntervalIntegrable (fun t : ℝ => Real.log (t / (2 * π)) * φ t) volume U V :=
    (hlogcont.mul hcont).intervalIntegrable_of_Icc hUV
  have hΨint : IntervalIntegrable
      (fun t : ℝ => (0.137 / t + 0.443 / (t * Real.log t)) * φ t) volume U V :=
    (hR'cont.mul hcont).intervalIntegrable_of_Icc hUV
  have hMKint : IntervalIntegrable (fun t : ℝ => countMain t * φ' t) volume U V := by
    have h := hi.mul_continuousOn (show ContinuousOn countMain (uIcc U V) from by
      rw [uIcc_of_le hUV]
      exact hMcont)
    simpa only [mul_comm] using h
  have hRKint : IntervalIntegrable (fun t : ℝ => countRemainder t * φ' t) volume U V := by
    have h := hi.mul_continuousOn (show ContinuousOn countRemainder (uIcc U V) from by
      rw [uIcc_of_le hUV]
      exact hRcont)
    simpa only [mul_comm] using h
  have hKint : IntervalIntegrable
      (fun t : ℝ => (countMain t + countRemainder t) * φ' t) volume U V := by
    have h := hMKint.add hRKint
    simpa only [add_mul] using h
  set IM : ℝ := ∫ t in U..V, countMain t * φ' t with hIM
  set IR : ℝ := ∫ t in U..V, countRemainder t * φ' t with hIR
  set Ilog : ℝ := ∫ t in U..V, Real.log (t / (2 * π)) * φ t with hIlog
  set IB : ℝ := ∫ t in U..V, inclusiveCount t * φ' t with hIB
  -- integration by parts for the two count pieces
  have hd' : ∀ t ∈ uIcc U V, HasDerivAt φ (φ' t) t :=
    fun t ht => hd t (by simpa only [uIcc_of_le hUV] using ht)
  have hIBPM := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := U) (b := V)
    (u := countMain) (u' := fun t : ℝ => (1 / (2 * π)) * Real.log (t / (2 * π)))
    (v := φ) (v' := φ')
    (fun t ht => hasDerivAt_countMain (hU0.trans_le (by
      rw [uIcc_of_le hUV] at ht
      exact ht.1))) hd' hM'int hi
  have hIBPR := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := U) (b := V)
    (u := countRemainder) (u' := fun t : ℝ => 0.137 / t + 0.443 / (t * Real.log t))
    (v := φ) (v' := φ')
    (fun t ht => hasDerivAt_countRemainder (hU1.trans_le (by
      rw [uIcc_of_le hUV] at ht
      exact ht.1))) hd' hR'int hi
  have hIPhi : (∫ t in U..V, ((1 / (2 * π)) * Real.log (t / (2 * π))) * φ t)
      = (1 / (2 * π)) * Ilog := by
    have h1 : (∫ t in U..V, ((1 / (2 * π)) * Real.log (t / (2 * π))) * φ t)
        = ∫ t in U..V, (1 / (2 * π)) * (Real.log (t / (2 * π)) * φ t) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [h1, intervalIntegral.integral_const_mul, hIlog]
  have hKsplit : (∫ t in U..V, (countMain t + countRemainder t) * φ' t) = IM + IR := by
    rw [hIM, hIR, ← intervalIntegral.integral_add hMKint hRKint]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hmono : (∫ t in U..V, (countMain t + countRemainder t) * φ' t)
      ≤ ∫ t in U..V, inclusiveCount t * φ' t := by
    apply intervalIntegral.integral_mono_on hUV hKint hBint
    intro t ht
    have h1 := hK t ht
    have h2 := hφ'np t ht
    nlinarith
  -- the derivative comparison for the Rosser remainder
  have hcmp : (∫ t in U..V, (0.137 / t + 0.443 / (t * Real.log t)) * φ t)
      ≤ countQ U * Ilog := by
    have h2 : (∫ t in U..V, (0.137 / t + 0.443 / (t * Real.log t)) * φ t)
        ≤ ∫ t in U..V, countQ U * (Real.log (t / (2 * π)) * φ t) := by
      apply intervalIntegral.integral_mono_on hUV hΨint (hΦint.const_mul _)
      intro t ht
      have h1 := countRemainder_deriv_le (U := U) hU ht.1
      have h2 := hφnn t ht
      nlinarith
    rw [intervalIntegral.integral_const_mul, ← hIlog] at h2
    exact h2
  have hstep : positiveZeroSum (fun ρ => if U < ρ.im ∧ ρ.im ≤ V then φ ρ.im else 0) ≤
      φ V * (countMain V + countRemainder V) - φ U * (countMain U - countRemainder U)
        - (IM + IR) := by
    rw [hW]
    have h1 : φ V * inclusiveCount V ≤ φ V * (countMain V + countRemainder V) :=
      mul_le_mul_of_nonneg_left hBV hφVnn
    have h2 : φ U * (countMain U - countRemainder U) ≤ φ U * inclusiveCount U :=
      mul_le_mul_of_nonneg_left hBU hφUnn
    have h3 : IM + IR ≤ IB := by
      rw [← hKsplit]
      exact hmono
    linarith
  -- assemble
  have hA : φ V * countMain V - φ U * countMain U - IM = (1 / (2 * π)) * Ilog := by
    rw [hIM, hIBPM, hIPhi]
    ring
  have hB : φ V * countRemainder V - φ U * countRemainder U - IR
      = ∫ t in U..V, (0.137 / t + 0.443 / (t * Real.log t)) * φ t := by
    rw [hIR, hIBPR]
    ring
  have hexp : φ V * (countMain V + countRemainder V) - φ U * (countMain U - countRemainder U)
      - (IM + IR) =
      (1 / (2 * π)) * Ilog +
        (∫ t in U..V, (0.137 / t + 0.443 / (t * Real.log t)) * φ t) + 2 * countRemainder U * φ U := by
    rw [← hA, ← hB]
    ring
  have hq : 0 ≤ countQ U := by
    have hshift : 0 < Real.log (U / (2 * π)) := by
      apply Real.log_pos
      rw [lt_div_iff₀ two_pi_pos]
      linarith [Real.pi_lt_four]
    have h1 : 0 < Real.log U := Real.log_pos (by linarith)
    have hpos : 0 < 0.137 / U + 0.443 / (U * Real.log U) := by positivity
    have key := countQ_mul_log hU
    have hqdef : countQ U =
        (0.137 / U + 0.443 / (U * Real.log U)) / Real.log (U / (2 * π)) := by
      rw [← key]
      field_simp
    rw [hqdef]
    positivity
  have hlast : (1 / (2 * π)) * Ilog +
      (∫ t in U..V, (0.137 / t + 0.443 / (t * Real.log t)) * φ t) + 2 * countRemainder U * φ U ≤
      (1 / (2 * π) + countQ U) * Ilog + 2 * countRemainder U * φ U := by
    have h1 : (1 / (2 * π)) * Ilog + countQ U * Ilog = (1 / (2 * π) + countQ U) * Ilog := by
      ring
    have h2 := hcmp
    linarith
  calc positiveZeroSum (fun ρ => if U < ρ.im ∧ ρ.im ≤ V then φ ρ.im else 0)
      ≤ φ V * (countMain V + countRemainder V) - φ U * (countMain U - countRemainder U)
          - (IM + IR) := hstep
    _ = (1 / (2 * π)) * Ilog +
        (∫ t in U..V, (0.137 / t + 0.443 / (t * Real.log t)) * φ t) + 2 * countRemainder U * φ U :=
        hexp
    _ ≤ (1 / (2 * π) + countQ U) * Ilog + 2 * countRemainder U * φ U := hlast



/-- LEAF. Page 7 display 2.45. Source 4, arXiv 1310.6374 pages 8 and 9,
Corollary 2.6 and display 2.22, applies the Rosser count bound to the reciprocal
ordinate on the finite interval. Only the Rosser input is needed. -/
theorem reciprocal_interval {T1 : ℝ}
    (hT0 : 1132491 ≤ T1) (hCount : RosserCountBound) :
    positiveZeroSum (fun ρ => if 1132491 < ρ.im ∧ ρ.im ≤ T1 then 1 / ρ.im else 0) ≤
      zeroS1 T1 := by
  have hT1 : (0 : ℝ) < T1 := by linarith
  have hU0 : (0 : ℝ) < 1132491 := by norm_num
  have hcont : ContinuousOn (fun t : ℝ => 1 / t) (Icc (1132491 : ℝ) T1) := by
    fun_prop (disch := intro t ht; positivity [hU0.trans_le ht.1])
  have hcont' : ContinuousOn (fun t : ℝ => -1 / t ^ 2) (Icc (1132491 : ℝ) T1) := by
    fun_prop (disch := intro t ht; positivity [hU0.trans_le ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => -1 / t ^ 2) volume (1132491 : ℝ) T1 :=
    hcont'.intervalIntegrable_of_Icc hT0
  have hderiv : ∀ t ∈ Icc (1132491 : ℝ) T1,
      HasDerivAt (fun t : ℝ => 1 / t) (-1 / t ^ 2) t := by
    intro t ht
    have ht0 : 0 < t := hU0.trans_le ht.1
    have h := reciprocal_power_derivative 0 ht0
    simpa using h
  have hmaster := rosser_window_bound (U := 1132491) (V := T1)
    (φ := fun t : ℝ => 1 / t) (φ' := fun t : ℝ => -1 / t ^ 2) (by norm_num) hT0
    hcont hderiv hi
    (fun t ht => by
      have h : (0 : ℝ) < t := by linarith [ht.1]
      positivity) (fun t ht => by
      have h : (0 : ℝ) < t := by linarith [ht.1]
      have h2 : (0 : ℝ) < t ^ 2 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) h2.le) hCount
  have hint : (∫ t in (1132491 : ℝ)..T1, Real.log (t / (2 * π)) * (1 / t)) =
      ((Real.log (T1 / (2 * π))) ^ 2 - (Real.log ((1132491 : ℝ) / (2 * π))) ^ 2) / 2 := by
    have h := integral_log_div_reciprocal (c := 2 * π) (U := 1132491) (V := T1)
      two_pi_pos (by norm_num) hT0
    rw [← h]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hS1 : zeroS1 T1 = (1 / (2 * π) + countQ 1132491) *
      (∫ t in (1132491 : ℝ)..T1, Real.log (t / (2 * π)) * (1 / t)) +
        2 * countRemainder 1132491 / 1132491 := by
    rw [hint]
    unfold zeroS1
    rw [mul_assoc, ← log_square_difference_eq (c := 2 * π) (U := 1132491) (V := T1)
      two_pi_pos (by norm_num) hT1]
  rw [hS1]
  simpa only [mul_one_div] using hmaster

/-- LEAF. Page 7 display 2.46. Source 4, arXiv 1310.6374 pages 8 and 9,
Corollary 2.6 and display 2.23, applies the Rosser count bound to the reciprocal
power on the finite interval. No verified RH height or density input is needed. -/
theorem power_interval {m : ℕ} {T1 : ℝ}
    (hm : 2 ≤ m) (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000)
    (hCount : RosserCountBound) :
    positiveZeroSum (fun ρ => if T1 < ρ.im ∧ ρ.im ≤ 30610000000 then
      1 / ρ.im ^ (m + 1) else 0) ≤ zeroS2 m T1 := by
  have hm1 : 0 < m := by omega
  have hT1 : (0 : ℝ) < T1 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ (m + 1)) (Icc T1 30610000000) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.pow (m + 1)
    · intro t ht
      exact pow_ne_zero _ (hT1.trans_le ht.1).ne'
  have hcont' : ContinuousOn (fun t : ℝ => -((m : ℝ) + 1) / t ^ (m + 2))
      (Icc T1 30610000000) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.pow (m + 2)
    · intro t ht
      exact pow_ne_zero _ (hT1.trans_le ht.1).ne'
  have hi : IntervalIntegrable (fun t : ℝ => -((m : ℝ) + 1) / t ^ (m + 2))
      volume T1 30610000000 := hcont'.intervalIntegrable_of_Icc hTH
  have hderiv : ∀ t ∈ Icc T1 30610000000,
      HasDerivAt (fun t : ℝ => 1 / t ^ (m + 1)) (-((m : ℝ) + 1) / t ^ (m + 2)) t :=
    fun t ht => reciprocal_power_derivative m (hT1.trans_le ht.1)
  have hnn : ∀ t ∈ Icc T1 30610000000, 0 ≤ 1 / t ^ (m + 1) := by
    intro t ht
    have h : (0 : ℝ) < t := hT1.trans_le ht.1
    positivity
  have hnp : ∀ t ∈ Icc T1 30610000000, -((m : ℝ) + 1) / t ^ (m + 2) ≤ 0 := by
    intro t ht
    have h : (0 : ℝ) < t := hT1.trans_le ht.1
    have h2 : (0 : ℝ) < t ^ (m + 2) := by positivity
    have h3 : (-((m : ℝ) + 1)) ≤ 0 := by
      have : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    exact div_nonpos_of_nonpos_of_nonneg h3 h2.le
  have hmaster := rosser_window_bound (U := T1) (V := 30610000000)
    (φ := fun t : ℝ => 1 / t ^ (m + 1)) (φ' := fun t : ℝ => -((m : ℝ) + 1) / t ^ (m + 2))
    hT0 hTH hcont hderiv hi hnn hnp hCount
  have hint : (∫ t in T1..(30610000000 : ℝ), Real.log (t / (2 * π)) * (1 / t ^ (m + 1))) =
      (1 + (m : ℝ) * Real.log (T1 / (2 * π))) / ((m : ℝ) ^ 2 * T1 ^ m) -
        (1 + (m : ℝ) * Real.log ((30610000000 : ℝ) / (2 * π))) /
          ((m : ℝ) ^ 2 * (30610000000 : ℝ) ^ m) := by
    have h := integral_log_div_power hm1 (c := 2 * π) (U := T1) (V := 30610000000)
      two_pi_pos hT1 hTH
    rw [← h]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hS2 : zeroS2 m T1 = (1 / (2 * π) + countQ T1) *
      (∫ t in T1..(30610000000 : ℝ), Real.log (t / (2 * π)) * (1 / t ^ (m + 1))) +
        2 * countRemainder T1 / T1 ^ (m + 1) := by
    rw [hint]
    unfold zeroS2
    ring
  rw [hS2]
  simpa only [mul_one_div] using hmaster

set_option maxHeartbeats 1000000 in
/-- LEAF. Page 7 display 2.47. Source 4, arXiv 1310.6374 pages 8 and 9,
Corollary 2.6 and display 2.24, sends the upper endpoint of the reciprocal power
estimate to infinity. Only the Rosser count input is needed. -/
theorem power_tail {m : ℕ} (hm : 2 ≤ m) (hCount : RosserCountBound) :
    positiveZeroSum (fun ρ => if 30610000000 < ρ.im then
      1 / ρ.im ^ (m + 1) else 0) ≤ zeroS3 m := by
  have hm1 : 0 < m := by omega
  have hH0 : (0 : ℝ) < 30610000000 := by norm_num
  have hHbig : (1132491 : ℝ) ≤ 30610000000 := by norm_num
  have hHlog : 0 < Real.log (30610000000 : ℝ) := Real.log_pos (by norm_num)
  have hHshift : 0 < Real.log ((30610000000 : ℝ) / (2 * π)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ two_pi_pos]
    linarith [Real.pi_lt_four]
  have hqH : 0 ≤ 1 / (2 * π) + countQ 30610000000 := by
    have hq : 0 ≤ countQ 30610000000 := by
      have hn : 0 < 0.137 / (30610000000 : ℝ) +
          0.443 / ((30610000000 : ℝ) * Real.log (30610000000 : ℝ)) := by positivity
      have key := countQ_mul_log hHbig
      have hqdef : countQ 30610000000 =
          (0.137 / (30610000000 : ℝ) +
            0.443 / ((30610000000 : ℝ) * Real.log (30610000000 : ℝ))) /
            Real.log ((30610000000 : ℝ) / (2 * π)) := by
        rw [← key]
        field_simp
      rw [hqdef]
      positivity
    have h2 : (0 : ℝ) < 1 / (2 * π) := by positivity
    linarith
  have hPH : 0 ≤ (1 + (m : ℝ) * Real.log ((30610000000 : ℝ) / (2 * π))) /
      ((m : ℝ) ^ 2 * (30610000000 : ℝ) ^ m) := by
    have h1 : (0 : ℝ) < 1 + (m : ℝ) * Real.log ((30610000000 : ℝ) / (2 * π)) := by
      have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      nlinarith
    have h2 : (0 : ℝ) < (m : ℝ) ^ 2 * (30610000000 : ℝ) ^ m := by positivity
    exact div_nonneg h1.le h2.le
  have hS3nn : 0 ≤ zeroS3 m := by
    unfold zeroS3
    have h3 : 0 ≤ 2 * countRemainder 30610000000 / (30610000000 : ℝ) ^ (m + 1) :=
      div_nonneg (by
        have h1 : 1 < Real.log (30610000000 : ℝ) :=
          (Real.lt_log_iff_exp_lt hH0).mpr
            (Real.exp_one_lt_three.trans_le (by norm_num : (3 : ℝ) ≤ 30610000000))
        have h2 : 0 < Real.log (Real.log (30610000000 : ℝ)) := Real.log_pos h1
        unfold countRemainder
        positivity) (by positivity)
    have h4 : 0 ≤ (1 / (2 * π) + countQ 30610000000) *
        ((1 + (m : ℝ) * Real.log ((30610000000 : ℝ) / (2 * π))) /
          ((m : ℝ) ^ 2 * (30610000000 : ℝ) ^ m)) := mul_nonneg hqH hPH
    linarith
  have hstep : ∀ V : ℝ, (30610000000 : ℝ) ≤ V →
      positiveZeroSum (fun ρ => if (30610000000 : ℝ) < ρ.im ∧ ρ.im ≤ V then
        1 / ρ.im ^ (m + 1) else 0) ≤ zeroS3 m := by
    intro V hHV
    have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ (m + 1)) (Icc (30610000000 : ℝ) V) := by
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_id.pow (m + 1)
      · intro t ht
        exact pow_ne_zero _ (hH0.trans_le ht.1).ne'
    have hcont' : ContinuousOn (fun t : ℝ => -((m : ℝ) + 1) / t ^ (m + 2))
        (Icc (30610000000 : ℝ) V) := by
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_id.pow (m + 2)
      · intro t ht
        exact pow_ne_zero _ (hH0.trans_le ht.1).ne'
    have hi : IntervalIntegrable (fun t : ℝ => -((m : ℝ) + 1) / t ^ (m + 2))
        volume (30610000000 : ℝ) V := hcont'.intervalIntegrable_of_Icc hHV
    have hderiv : ∀ t ∈ Icc (30610000000 : ℝ) V,
        HasDerivAt (fun t : ℝ => 1 / t ^ (m + 1)) (-((m : ℝ) + 1) / t ^ (m + 2)) t :=
      fun t ht => reciprocal_power_derivative m (hH0.trans_le ht.1)
    have hnn : ∀ t ∈ Icc (30610000000 : ℝ) V, 0 ≤ 1 / t ^ (m + 1) := by
      intro t ht
      have h : (0 : ℝ) < t := hH0.trans_le ht.1
      positivity
    have hnp : ∀ t ∈ Icc (30610000000 : ℝ) V, -((m : ℝ) + 1) / t ^ (m + 2) ≤ 0 := by
      intro t ht
      have h : (0 : ℝ) < t := hH0.trans_le ht.1
      have h2 : (0 : ℝ) < t ^ (m + 2) := by positivity
      have h3 : (-((m : ℝ) + 1)) ≤ 0 := by
        have : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith
      exact div_nonpos_of_nonpos_of_nonneg h3 h2.le
    have hmaster := rosser_window_bound (U := 30610000000) (V := V)
      (φ := fun t : ℝ => 1 / t ^ (m + 1)) (φ' := fun t : ℝ => -((m : ℝ) + 1) / t ^ (m + 2))
      hHbig hHV hcont hderiv hi hnn hnp hCount
    have hint : (∫ t in (30610000000 : ℝ)..V, Real.log (t / (2 * π)) * (1 / t ^ (m + 1))) =
        (1 + (m : ℝ) * Real.log ((30610000000 : ℝ) / (2 * π))) /
            ((m : ℝ) ^ 2 * (30610000000 : ℝ) ^ m) -
          (1 + (m : ℝ) * Real.log (V / (2 * π))) / ((m : ℝ) ^ 2 * V ^ m) := by
      have h := integral_log_div_power hm1 (c := 2 * π) (U := 30610000000) (V := V)
        two_pi_pos hH0 hHV
      rw [← h]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    have hPVnn : 0 ≤ (1 + (m : ℝ) * Real.log (V / (2 * π))) / ((m : ℝ) ^ 2 * V ^ m) := by
      have hVshift : 0 < Real.log (V / (2 * π)) := by
        apply Real.log_pos
        rw [lt_div_iff₀ two_pi_pos]
        linarith [Real.pi_lt_four]
      have h1 : (0 : ℝ) < 1 + (m : ℝ) * Real.log (V / (2 * π)) := by
        have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
        nlinarith
      have hV0 : (0 : ℝ) < V := hH0.trans_le hHV
      have h2 : (0 : ℝ) < (m : ℝ) ^ 2 * V ^ m := by positivity
      exact div_nonneg h1.le h2.le
    rw [hint, mul_one_div] at hmaster
    unfold zeroS3
    have hmul : (1 / (2 * π) + countQ 30610000000) *
        ((1 + (m : ℝ) * Real.log ((30610000000 : ℝ) / (2 * π))) /
            ((m : ℝ) ^ 2 * (30610000000 : ℝ) ^ m) -
          (1 + (m : ℝ) * Real.log (V / (2 * π))) / ((m : ℝ) ^ 2 * V ^ m)) ≤
        (1 / (2 * π) + countQ 30610000000) *
          ((1 + (m : ℝ) * Real.log ((30610000000 : ℝ) / (2 * π))) /
            ((m : ℝ) ^ 2 * (30610000000 : ℝ) ^ m)) :=
      mul_le_mul_of_nonneg_left (by linarith) hqH
    linarith
  have hmain : ∀ ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
      0 ≤ (if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if (30610000000 : ℝ) < (ρ : ℂ).im then 1 / (ρ : ℂ).im ^ (m + 1) else 0) else 0) := by
    intro ρ
    split_ifs <;> positivity
  change ∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
      (if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if (30610000000 : ℝ) < (ρ : ℂ).im then 1 / (ρ : ℂ).im ^ (m + 1) else 0) else 0) ≤
    zeroS3 m
  have hfin_bound : ∀ s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
      ∑ ρ ∈ s, (if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (if (30610000000 : ℝ) < (ρ : ℂ).im then 1 / (ρ : ℂ).im ^ (m + 1) else 0) else 0) ≤
        zeroS3 m := by
    intro s
    set V : ℝ := (30610000000 : ℝ) + ∑ ρ ∈ s, |(ρ : ℂ).im| + 1 with hVdef
    have hVH : (30610000000 : ℝ) ≤ V := by
      have h := Finset.sum_nonneg (s := s)
        (f := fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} => |(ρ : ℂ).im|)
        (fun i _ => abs_nonneg _)
      rw [hVdef]
      linarith
    have hmemV : ∀ ρ ∈ s, (ρ : ℂ).im ≤ V := by
      intro ρ hρ
      have h1 : |(ρ : ℂ).im| ≤ ∑ ρ ∈ s, |(ρ : ℂ).im| := Finset.single_le_sum (s := s)
        (f := fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} => |(ρ : ℂ).im|)
        (fun i _ => abs_nonneg _) hρ
      have h2 : (ρ : ℂ).im ≤ |(ρ : ℂ).im| := le_abs_self _
      rw [hVdef]
      linarith
    calc ∑ ρ ∈ s, (if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
          (if (30610000000 : ℝ) < (ρ : ℂ).im then 1 / (ρ : ℂ).im ^ (m + 1) else 0) else 0)
        = ∑ ρ ∈ s, (if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
            (if (30610000000 : ℝ) < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V then
              1 / (ρ : ℂ).im ^ (m + 1) else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro ρ hρ
          by_cases hp : 0 < (ρ : ℂ).im
          · by_cases hw : (30610000000 : ℝ) < (ρ : ℂ).im
            · rw [if_pos hp, if_pos hp, if_pos hw, if_pos ⟨hw, hmemV ρ hρ⟩]
            · rw [if_pos hp, if_pos hp, if_neg hw,
                ite_eq_right (by tauto : ¬ ((30610000000 : ℝ) < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V)),
                mul_zero]
          · rw [if_neg hp, if_neg hp]
      _ ≤ ∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
            (if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
              (if (30610000000 : ℝ) < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ V then
                1 / (ρ : ℂ).im ^ (m + 1) else 0) else 0) := by
          apply Summable.sum_le_tsum
          · intro ρ _
            split_ifs <;> positivity
          · exact summable_bounded_positive_zero_family V
              (fun ρ : ℂ =>
                if (30610000000 : ℝ) < ρ.im ∧ ρ.im ≤ V then 1 / ρ.im ^ (m + 1) else 0)
              (fun ρ hρ => ite_eq_right (by intro h; linarith [h.2]))
      _ ≤ zeroS3 m := hstep V hVH
  exact Real.tsum_le_of_sum_le hmain hfin_bound

/-- LEAF. Page 7 display 2.48. Source 4, arXiv 1310.6374 page 9,
Lemma 2.7 and display 2.25. Integrate the density count against the derivative
of the reciprocal power. Verified RH height removes the lower boundary count. -/
theorem density_power_tail {m : ℕ} {σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    positiveZeroSum (fun ρ => if 30610000000 < ρ.im ∧ σ < ρ.re then
      1 / ρ.im ^ (m + 1) else 0) ≤ zeroS4 m c1 c2 c3 := by
  have h := density_power_tail_bound (m := m) (by omega)
    (by norm_num : (0 : ℝ) < 30610000000) (by linarith : (1 / 2 : ℝ) < σ)
    hRH hDensity hc1 hc2
  apply h.trans_eq
  unfold densityPrimitive zeroS4
  rw [pow_succ]
  field_simp
  <;> ring

/-- LEAF. Page 7 display 2.49. Source 4, arXiv 1310.6374 pages 9 and 10,
Lemma 2.7 and displays 2.26 to 2.30. Integrate the density count against the
weighted reciprocal power, then bound its remaining integral as in display 2.29.
The zero-free region motivates the weight but is not needed to estimate this sum. -/
theorem density_weighted_tail {m : ℕ} {X σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hX : 10 < X) (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hlog : Real.log X < 5.69693 * m * (Real.log 30610000000) ^ 2) :
    positiveZeroSum (fun ρ => if 30610000000 < ρ.im ∧ σ < ρ.re then
      X ^ (-1 / (5.69693 * Real.log ρ.im)) / ρ.im ^ (m + 1) else 0) ≤
      zeroS5 X m c1 c2 c3 * X ^ (-1 / (5.69693 * Real.log 30610000000)) := by
  sorry

/-- Page 7 Lemma 2.5. Exact statement of Task259.lemma2_5_positive assembled
from its five strictly smaller estimates. CONDITIONAL ON the five OPEN leaves. -/
theorem lemma2_5_positive (m : ℕ) {T1 X σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hX : 10 < X) (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000)
    (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000) (hLow : LowZeroData 1132491 2001052 11.637732363)
    (hZF : ZeroFreeRegion 5.69693) (hCount : RosserCountBound)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hlog : Real.log X < 5.69693 * m * (Real.log 30610000000) ^ 2) :
    Lemma25Bounds m T1 X σ c1 c2 c3 := by
  exact ⟨reciprocal_interval hT0 hCount,
    power_interval hm hT0 hTH hCount,
    power_tail hm hCount,
    density_power_tail hm hσ hσ1 hRH hDensity hc1 hc2,
    density_weighted_tail hm hX hσ hσ1 hRH hDensity hc1 hc2 hlog⟩

end LeanLab.KadiriLumley2014.Task399
