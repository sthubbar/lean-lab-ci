import LeanLab.HelfgottMajor.Landau309

/-!
The disk geometry for the off center Landau estimate on P0014 page 36 display 4.16.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.LandauDisk309
open Complex Metric Set Filter
open scoped Topology ComplexConjugate

/-- The disk change of center used for the off center form of display 4.16, page 36. -/
noncomputable def diskMove (a z : ℂ) : ℂ := (z + a) / (1 + conj a * z)

/-- The norm identity showing that diskMove preserves the unit disk.
This is the elementary disk geometry in the proof of display 4.16 on page 36.
-/
theorem diskMove_norm_identity (a z : ℂ) :
    ‖1 + conj a * z‖ ^ 2 - ‖z + a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp [Complex.sq_norm, normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The disk change of center maps the open unit disk into itself.
Source P0014 page 36 display 4.16, elementary disk geometry.
-/
theorem diskMove_mem (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskMove a z‖ < 1 := by
  have ha' : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz' : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hsq := diskMove_norm_identity a z
  have hlt : ‖z + a‖ < ‖1 + conj a * z‖ := by
    nlinarith [mul_pos ha' hz', norm_nonneg (z + a), norm_nonneg (1 + conj a * z)]
  have hden : 0 < ‖1 + conj a * z‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  rw [diskMove, norm_div]
  exact (div_lt_one hden).mpr hlt

/-- The disk change of center has real positive derivative one minus norm a squared at zero.
Source P0014 page 36 display 4.16, elementary disk geometry.
-/
theorem diskMove_derivative (a : ℂ) :
    HasDerivAt (diskMove a) ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) 0 := by
  have hnum := (hasDerivAt_id (0 : ℂ)).add_const a
  have hden := ((hasDerivAt_id (0 : ℂ)).const_mul (conj a)).const_add 1
  have h := hnum.div hden (by simp)
  have hconj : a * conj a = (‖a‖ ^ 2 : ℝ) := by
    rw [mul_conj, ← Complex.sq_norm]
  convert h using 1 <;> simp [diskMove, hconj]
  funext z
  rfl

/-- The center derivative bound also holds for a nonnegative real part budget.
Source P0014 page 36 display 4.16. The zero budget follows by positive approximation.
-/
theorem normalized_derivative_bound_nonneg (g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hM : 0 ≤ M) (hg : DifferentiableOn ℂ g (ball 0 R)) (hg0 : g 0 = 0)
    (hgre : ∀ z ∈ ball 0 R, (g z).re ≤ M) :
    ‖deriv g 0‖ ≤ 2 * M / R := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hMp : 0 < M + ε * R / 2 := by positivity
  have h := Landau309.normalized_derivative_bound g R (M + ε * R / 2) hR hMp hg hg0
    (fun z hz => (hgre z hz).trans (by linarith [mul_pos hε hR]))
  convert h using 1 <;> field_simp <;> ring

/-- The off center Borel Caratheodory derivative estimate used by Landau.
Source P0014 page 36 display 4.16, before substituting an analytic logarithm.
-/
theorem normalized_derivative_bound_at (g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hg0 : g 0 = 0)
    (hgre : ∀ z ∈ ball 0 R, (g z).re ≤ M) (z : ℂ) (hz : ‖z‖ < R) :
    ‖deriv g z‖ ≤ 2 * M * R / (R - ‖z‖) ^ 2 := by
  let a : ℂ := z / (R : ℂ)
  have ha : ‖a‖ < 1 := by
    dsimp [a]
    rw [norm_div, norm_real, Real.norm_of_nonneg hR.le]
    exact (div_lt_one hR).mpr hz
  let φ : ℂ → ℂ := fun s => (R : ℂ) * diskMove a s
  have hφ0 : φ 0 = z := by
    dsimp [φ, diskMove, a]
    simp only [zero_add, mul_zero, add_zero, div_one]
    field_simp [ofReal_ne_zero.mpr hR.ne']
  have hmaps : MapsTo φ (ball 0 1) (ball 0 R) := by
    intro s hs
    rw [mem_ball_zero_iff] at hs ⊢
    dsimp [φ]
    rw [norm_mul, norm_real, Real.norm_of_nonneg hR.le]
    nlinarith [diskMove_mem a s ha hs]
  have hden : ∀ s ∈ ball (0 : ℂ) 1, 1 + conj a * s ≠ 0 := by
    intro s hs he
    have hs' := mem_ball_zero_iff.mp hs
    have hsq := diskMove_norm_identity a s
    rw [he, norm_zero, zero_pow (by decide)] at hsq
    have ha' : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have hs'' : 0 < 1 - ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
    nlinarith [mul_pos ha' hs'', sq_nonneg ‖s + a‖]
  have hφd : DifferentiableOn ℂ φ (ball 0 1) := by
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.div (by fun_prop) (by fun_prop) hden
  have hcomp : DifferentiableOn ℂ (fun s => g (φ s) - g z) (ball 0 1) :=
    (hg.comp hφd hmaps).sub_const _
  have hcomp0 : g (φ 0) - g z = 0 := by rw [hφ0]; simp
  have hbudget : 0 ≤ M - (g z).re := by linarith [hgre z (mem_ball_zero_iff.mpr hz)]
  have hcompRe : ∀ s ∈ ball (0 : ℂ) 1, (g (φ s) - g z).re ≤ M - (g z).re := by
    intro s hs
    simp only [sub_re]
    linarith [hgre (φ s) (hmaps hs)]
  have hb := normalized_derivative_bound_nonneg _ 1 (M - (g z).re) (by norm_num)
    hbudget hcomp hcomp0 hcompRe
  have hφder := (diskMove_derivative a).const_mul (R : ℂ)
  have hgder := (hg.differentiableAt (isOpen_ball.mem_nhds
    (mem_ball_zero_iff.mpr hz))).hasDerivAt
  have hgder' : HasDerivAt g (deriv g z) (φ (0 : ℂ)) := by
    rw [hφ0]
    exact hgder
  have hchain : HasDerivAt (fun s : ℂ => g (φ s) - g z)
      (deriv g z * ((R : ℂ) * ((1 - ‖a‖ ^ 2 : ℝ) : ℂ))) 0 := by
    simpa only [Function.comp_apply] using (hgder'.comp (0 : ℂ) hφder).sub_const (g z)
  have hkn : 0 ≤ R * (1 - ‖a‖ ^ 2) := by
    have h := norm_nonneg a
    have h' : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith
    positivity
  have hnorm : ‖deriv (fun s => g (φ s) - g z) 0‖ =
      ‖deriv g z‖ * (R * (1 - ‖a‖ ^ 2)) := by
    rw [hchain.deriv, norm_mul]
    congr 1
    rw [← ofReal_mul, norm_real, Real.norm_of_nonneg hkn]
  rw [hnorm, div_one] at hb
  have hanorm : ‖a‖ = ‖z‖ / R := by
    dsimp [a]
    rw [norm_div, norm_real, Real.norm_of_nonneg hR.le]
  rw [hanorm] at hb
  have hk : R * (1 - (‖z‖ / R) ^ 2) = (R ^ 2 - ‖z‖ ^ 2) / R := by field_simp <;> ring
  rw [hk] at hb
  have hb' : ‖deriv g z‖ * (R ^ 2 - ‖z‖ ^ 2) ≤ 2 * R * (M - (g z).re) := by
    have h := mul_le_mul_of_nonneg_right hb hR.le
    field_simp at h
    nlinarith
  have hBorel := borelCaratheodory_zero hM hg hgre hR (mem_ball_zero_iff.mpr hz) hg0
  have hdenR : 0 < R - ‖z‖ := sub_pos.mpr hz
  have hReal : -(g z).re ≤ ‖g z‖ := by
    exact (neg_le_abs _).trans (abs_re_le_norm _)
  have hHarnack : (M - (g z).re) * (R - ‖z‖) ≤ M * (R + ‖z‖) := by
    have h := (le_div_iff₀ hdenR).mp hBorel
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hb' hdenR.le
  have h2 := mul_le_mul_of_nonneg_left hHarnack (by positivity : 0 ≤ 2 * R)
  apply (le_div_iff₀ (sq_pos_of_pos hdenR)).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < R + ‖z‖)).mp
  nlinarith

/-- The off center derivative estimate includes the zero real part budget.
Source P0014 page 36 display 4.16. This removes the strict budget restriction by approximation.
-/
theorem normalized_derivative_bound_at_nonneg (g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hM : 0 ≤ M) (hg : DifferentiableOn ℂ g (ball 0 R)) (hg0 : g 0 = 0)
    (hgre : ∀ z ∈ ball 0 R, (g z).re ≤ M) (z : ℂ) (hz : ‖z‖ < R) :
    ‖deriv g z‖ ≤ 2 * M * R / (R - ‖z‖) ^ 2 := by
  have hden : 0 < (R - ‖z‖) ^ 2 := sq_pos_of_pos (sub_pos.mpr hz)
  apply le_of_forall_pos_le_add
  intro ε hε
  let D := ε * (R - ‖z‖) ^ 2 / (2 * R)
  have hD : 0 < D := by dsimp [D]; positivity
  have h := normalized_derivative_bound_at g R (M + D) hR (by linarith) hg hg0
    (fun w hw => (hgre w hw).trans (by linarith)) z hz
  convert h using 1 <;> dsimp [D] <;> field_simp <;> ring

/-- Landau on a disk centered at zero, with the sharp distance to boundary denominator.
Source P0014 page 36 display 4.16 and Montgomery and Vaughan Lemma 6.3.
-/
theorem landau_disk (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hM : ‖f 0‖ ≤ M) (hbound : ∀ z ∈ ball 0 R, ‖f z‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ < R) :
    ‖logDeriv f z‖ ≤ 2 * R * Real.log (M / ‖f 0‖) / (R - ‖z‖) ^ 2 := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hf0 := hn 0 h0
  have hn0 : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  obtain ⟨g, hgd, hg0, hge⟩ := Landau309.normalized_log_exists f R hR hf hn
  have hlog : 0 ≤ Real.log (M / ‖f 0‖) :=
    Real.log_nonneg ((one_le_div hn0).mpr hM)
  have hgre : ∀ w ∈ ball 0 R, (g w).re ≤ Real.log (M / ‖f 0‖) := by
    intro w hw
    have he := congrArg norm (hge w hw)
    rw [norm_exp, norm_div] at he
    have he' : (g w).re = Real.log (‖f w‖ / ‖f 0‖) := by
      rw [← he, Real.log_exp]
    rw [he']
    apply Real.log_le_log (div_pos (norm_pos_iff.mpr (hn w hw)) hn0)
    exact div_le_div_of_nonneg_right (hbound w hw) hn0.le
  have hzmem := mem_ball_zero_iff.mpr hz
  have hgder := (hgd.differentiableAt (isOpen_ball.mem_nhds hzmem)).hasDerivAt
  have hfd := (hf.differentiableAt (isOpen_ball.mem_nhds hzmem)).hasDerivAt.div_const (f 0)
  have he : exp ∘ g =ᶠ[𝓝 z] fun w => f w / f 0 := by
    filter_upwards [isOpen_ball.mem_nhds hzmem] with w hw
    exact hge w hw
  have heq := hgder.cexp.unique (hfd.congr_of_eventuallyEq he)
  rw [hge z hzmem] at heq
  have hder : deriv g z = logDeriv f z := by
    rw [logDeriv_apply]
    field_simp [hf0, hn z hzmem] at heq ⊢
    linear_combination heq
  rw [← hder]
  have h := normalized_derivative_bound_at_nonneg g R _ hR hlog hgd hg0 hgre z hz
  convert h using 1 <;> ring

/-- Landau with an inner radius r, the form displayed on P0014 page 36 in display 4.16.
The logarithmic derivative is bounded uniformly on the inner disk.
-/
theorem landau_inner_disk (f : ℂ → ℂ) (R r M : ℝ) (hR : 0 < R) (hr : r < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hn : ∀ w ∈ ball 0 R, f w ≠ 0)
    (hM : ‖f 0‖ ≤ M) (hbound : ∀ w ∈ ball 0 R, ‖f w‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖logDeriv f z‖ ≤ 2 * R * Real.log (M / ‖f 0‖) / (R - r) ^ 2 := by
  have hn0 : 0 < ‖f 0‖ := norm_pos_iff.mpr (hn 0 (mem_ball_self hR))
  have hlog : 0 ≤ Real.log (M / ‖f 0‖) :=
    Real.log_nonneg ((one_le_div hn0).mpr hM)
  have h := landau_disk f R M hR hf hn hM hbound z (hz.trans_lt hr)
  apply h.trans
  apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (sub_pos.mpr hr))
  nlinarith [sq_nonneg (R - r), norm_nonneg z]

end LeanLab.HelfgottMajor.LandauDisk309
