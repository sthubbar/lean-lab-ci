/-
Jia 1996 page 275, the first numerical integral in Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The coarse lower bound is weaker than the printed coefficient.
-/
import LeanLab.Languasco2004.Kernel548

namespace LeanLab.Languasco2004.Integral548
open Real intervalIntegral Kernel548
noncomputable section

/-- Page 275: positive denominators make the rational kernel integrable. -/
theorem rational_kernel_integrable (t a b : ℝ) (ht : 0 < t)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1 - t) :
    IntervalIntegrable (fun u : ℝ => 1 / (t * u * (1 - t - u)))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply continuousOn_const.div
    ((continuousOn_const.mul continuousOn_id).mul
      ((continuousOn_const.sub continuousOn_const).sub continuousOn_id))
  intro u hu
  exact (mul_pos (mul_pos ht (ha.trans_le hu.1)) (by dsimp; linarith [hu.2])).ne'

/-- Page 275: an elementary antiderivative removes the inner rational integral. -/
theorem rational_kernel_integral (t a b : ℝ) (ht : 0 < t)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1 - t) :
    (∫ u in a..b, 1 / (t * u * (1 - t - u))) =
      ((Real.log b - Real.log (1 - t - b)) -
        (Real.log a - Real.log (1 - t - a))) / (t * (1 - t)) := by
  have ht1 : 0 < 1 - t := (ha.trans_le hab).trans hb
  have hd : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => (Real.log u - Real.log (1 - t - u)) /
        (t * (1 - t))) (1 / (t * u * (1 - t - u))) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 < u := ha.trans_le hu.1
    have hv : 0 < 1 - t - u := by linarith [hu.2]
    have hd := ((Real.hasDerivAt_log hu0.ne').sub
      (((hasDerivAt_const u (1 - t)).sub (hasDerivAt_id u)).log hv.ne')).div_const
        (t * (1 - t))
    simp only [Pi.sub_apply, id_eq] at hd
    convert hd using 1
    field_simp
    ring
  have hi := integral_eq_sub_of_hasDerivAt hd
    (rational_kernel_integrable t a b ht hab ha hb)
  convert hi using 1
  ring

/-- Page 275: a uniform rational enclosure bounds the D47 kernel below by 25. -/
theorem region47_kernel_ge25 (t u : ℝ) (htl : 11 / 27 ≤ t) (htu : t ≤ 34 / 81)
    (hul : 17 / 12 - 23 / 8 * t ≤ u) (huu : u ≤ 25 / 72 - t / 4) :
    25 ≤ 1 / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, _, _⟩ := region47_argument t u htl htu hul huu
  have huB : u ≤ 53 / 216 := by linarith
  have hvB : 1 - t - u ≤ 83 / 216 := by linarith
  have htuB : t * u ≤ (34 / 81 : ℝ) * (53 / 216) :=
    mul_le_mul htu huB hu.le (by norm_num)
  have hD : t * u * (1 - t - u) ≤
      ((34 / 81 : ℝ) * (53 / 216)) * (83 / 216) :=
    mul_le_mul htuB hvB hv.le (by norm_num)
  apply (le_div_iff₀ (mul_pos (mul_pos ht hu) hv)).mpr
  norm_num at hD ⊢
  linarith

/-- Page 275: the first Omega47 integral before the outer integration. -/
def inner47 (t : ℝ) : ℝ :=
  ∫ u in (17 / 12 - 23 / 8 * t)..(25 / 72 - t / 4),
    1 / (t * u * (1 - t - u))

/-- Page 275: the inner integral equals an explicit continuous logarithmic expression. -/
theorem inner47_eq_log (t : ℝ) (htl : 11 / 27 ≤ t) (htu : t ≤ 34 / 81) :
    inner47 t =
      ((Real.log (25 / 72 - t / 4) - Real.log (1 - t - (25 / 72 - t / 4))) -
        (Real.log (17 / 12 - 23 / 8 * t) - Real.log (1 - t - (17 / 12 - 23 / 8 * t)))) /
        (t * (1 - t)) := by
  apply rational_kernel_integral
  all_goals linarith

/-- Page 275: the inner integral has the rigorous uniform kernel lower bound. -/
theorem inner47_ge (t : ℝ) (htl : 11 / 27 ≤ t) (htu : t ≤ 34 / 81) :
    25 * ((25 / 72 - t / 4) - (17 / 12 - 23 / 8 * t)) ≤ inner47 t := by
  have hab : 17 / 12 - 23 / 8 * t ≤ 25 / 72 - t / 4 := by linarith
  have hi := rational_kernel_integrable t (17 / 12 - 23 / 8 * t)
    (25 / 72 - t / 4) (by linarith) hab (by linarith) (by linarith)
  have hm := integral_mono_on hab (intervalIntegrable_const (c := (25 : ℝ))) hi
    (fun u hu => region47_kernel_ge25 t u htl htu hu.1 hu.2)
  simpa only [inner47, integral_const, smul_eq_mul, mul_comm] using hm

/-- Page 275: the inner rational integral varies continuously on its t interval. -/
theorem inner47_continuousOn : ContinuousOn inner47 (Set.Icc (11 / 27) (34 / 81)) := by
  have hL : ContinuousOn (fun t : ℝ => 17 / 12 - 23 / 8 * t)
      (Set.Icc (11 / 27) (34 / 81)) := by fun_prop
  have hU : ContinuousOn (fun t : ℝ => 25 / 72 - t / 4)
      (Set.Icc (11 / 27) (34 / 81)) := by fun_prop
  have hVL : ContinuousOn (fun t : ℝ => 1 - t - (17 / 12 - 23 / 8 * t))
      (Set.Icc (11 / 27) (34 / 81)) := by fun_prop
  have hVU : ContinuousOn (fun t : ℝ => 1 - t - (25 / 72 - t / 4))
      (Set.Icc (11 / 27) (34 / 81)) := by fun_prop
  have hc := ((hU.log (by intro t ht; have := ht.1; have := ht.2; dsimp; linarith)).sub
    (hVU.log (by intro t ht; have := ht.1; have := ht.2; dsimp; linarith))).sub
    ((hL.log (by intro t ht; have := ht.1; have := ht.2; dsimp; linarith)).sub
    (hVL.log (by intro t ht; have := ht.1; have := ht.2; dsimp; linarith)))
  have hd : ContinuousOn (fun t : ℝ => t * (1 - t))
      (Set.Icc (11 / 27) (34 / 81)) := by fun_prop
  have hdiv := hc.div hd (by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    exact (mul_pos ht0 ht1).ne')
  apply hdiv.congr
  intro t ht
  exact inner47_eq_log t ht.1 ht.2

/-- Page 275: the full rational integral has a certified coarse bound.
The accompanying strict comparison records why this bound alone is too weak. -/
theorem region47_coarse_lower :
    (0.005 : ℝ) ≤ ∫ t in (11 / 27 : ℝ)..(34 / 81), inner47 t := by
  have hi := inner47_continuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num)
  have hp : IntervalIntegrable (fun t : ℝ => 25 * ((21 / 8) * t - 77 / 72))
      MeasureTheory.volume (11 / 27) (34 / 81) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hm := integral_mono_on (by norm_num : (11 / 27 : ℝ) ≤ 34 / 81) hp hi
    (by
      intro t ht
      convert inner47_ge t ht.1 ht.2 using 1
      ring)
  have he : (∫ t in (11 / 27 : ℝ)..(34 / 81), 25 * ((21 / 8) * t - 77 / 72)) =
      875 / 174960 := by
    rw [integral_const_mul, integral_sub]
    · rw [integral_const_mul, integral_id, integral_const]
      norm_num
    · apply Continuous.intervalIntegrable; fun_prop
    · exact intervalIntegrable_const
  rw [he] at hm
  linarith

/-- Page 277: the coarse enclosure does not reach the printed Omega47 coefficient. -/
theorem coarse_coefficient_too_small : (0.005 : ℝ) < 0.005888 := by norm_num

#print axioms rational_kernel_integrable
#print axioms rational_kernel_integral
#print axioms region47_kernel_ge25
#print axioms inner47_eq_log
#print axioms inner47_ge
#print axioms inner47_continuousOn
#print axioms region47_coarse_lower
#print axioms coarse_coefficient_too_small
end
end LeanLab.Languasco2004.Integral548
