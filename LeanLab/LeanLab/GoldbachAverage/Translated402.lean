import LeanLab.GoldbachAverage.Rectangle402
import LeanLab.GoldbachAverage.Variance82

/-!
Goldston and Suriajaya, arXiv 2110.14250v2 page 19 first five displays.
Average the translated dyadic square over one increment interval.
The two resulting additive increments fill the rectangle from zero to two h.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Translated402
open MeasureTheory Set Filter

/-- The additive translation rectangle comparison in P0051 page 19 proof of Lemma 3. -/
theorem translated_square_to_rectangle_proved (x h : ℝ) (hh : 1 ≤ h) (hhx : h ≤ x / 4) :
    (∫ t in (x / 2)..x, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
      (2 / h) * (∫ u in (0 : ℝ)..(2 * h), ∫ y in (x / 4)..x,
        (Chebyshev.psi (y + u) - Chebyshev.psi y - u) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hA : 0 ≤ x / 4 := by positivity
  have hAx : x / 4 ≤ x := by linarith
  have hU : 0 ≤ 2 * h := by positivity
  let F : ℝ → ℝ → ℝ := fun u y => (Chebyshev.psi (y + u) - Chebyshev.psi y - u) ^ 2
  let J : ℝ → ℝ := fun u => ∫ y in (x / 4)..x, F u y
  let I : ℝ := ∫ t in (x / 2)..x, F h t
  have hfull (v : ℝ) (hv : 0 ≤ v) : IntervalIntegrable (F v) volume 0 x :=
    Decomp82.short_error_integrable hx0.le hv
  have hJI : IntervalIntegrable J volume 0 (2 * h) := by
    have hi := (Rectangle402.additive_square_integrable (x / 4) x (2 * h) hA hU).integral_prod_left
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).mpr
    dsimp only [J]
    simp_rw [intervalIntegral.integral_of_le hAx]
    exact hi
  have hJ0 : IntervalIntegrable J volume 0 h := hJI.mono_set (by
    rw [uIcc_of_le hh0.le, uIcc_of_le hU]
    intro u hu
    exact ⟨hu.1, by linarith [hu.2]⟩)
  have hJ1 : IntervalIntegrable J volume h (2 * h) := hJI.mono_set (by
    rw [uIcc_of_le (by linarith : h ≤ 2 * h), uIcc_of_le hU]
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩)
  have hJshift : IntervalIntegrable (fun u => J (u + h)) volume 0 h := by
    simpa only [sub_self, show 2 * h - h = h by ring] using hJ1.comp_add_right h
  have hp (u : ℝ) (hu : u ∈ Icc 0 h) : I ≤ 2 * (J (u + h) + J u) := by
    have ha : 0 ≤ x / 2 - u := by linarith [hu.2]
    have hab : x / 2 - u ≤ x - u := by linarith
    have hleft : x / 4 ≤ x / 2 - u := by linarith [hu.2]
    have hright : x - u ≤ x := by linarith [hu.1]
    have hi (v : ℝ) (hv : 0 ≤ v) : IntervalIntegrable (F v) volume (x / 2 - u) (x - u) :=
      (hfull v hv).mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le hx0.le]
        intro y hy
        exact ⟨ha.trans hy.1, hy.2.trans hright⟩)
    have hbase : IntervalIntegrable (F h) volume (x / 2) x :=
      (hfull h hh0.le).mono_set (by
        rw [uIcc_of_le (by linarith : x / 2 ≤ x), uIcc_of_le hx0.le]
        intro y hy
        exact ⟨by linarith [hy.1], hy.2⟩)
    have hshift : IntervalIntegrable (fun y => F h (y + u)) volume (x / 2 - u) (x - u) :=
      hbase.comp_add_right u
    have hpoint (y : ℝ) (_hy : y ∈ Icc (x / 2 - u) (x - u)) :
        F h (y + u) ≤ 2 * (F (u + h) y + F u y) := by
      dsimp [F]
      rw [show y + u + h = y + (u + h) by ring]
      nlinarith [sq_nonneg ((Chebyshev.psi (y + (u + h)) - Chebyshev.psi y - (u + h)) +
        (Chebyshev.psi (y + u) - Chebyshev.psi y - u))]
    have hm := intervalIntegral.integral_mono_on hab hshift
      (((hi (u + h) (by linarith [hu.1])).add (hi u hu.1)).const_mul 2) hpoint
    have htrans : (∫ y in (x / 2 - u)..(x - u), F h (y + u)) = I := by
      rw [intervalIntegral.integral_comp_add_right]
      simp only [sub_add_cancel, I]
    rw [htrans, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hi (u + h) (by linarith [hu.1])) (hi u hu.1)] at hm
    have hbound (v : ℝ) (hv : 0 ≤ v) : (∫ y in (x / 2 - u)..(x - u), F v y) ≤ J v := by
      have hlarge : IntervalIntegrable (F v) volume (x / 4) x :=
        (hfull v hv).mono_set (by
          rw [uIcc_of_le hAx, uIcc_of_le hx0.le]
          intro y hy
          exact ⟨hA.trans hy.1, hy.2⟩)
      exact intervalIntegral.integral_mono_interval hleft hab hright
        (Eventually.of_forall (fun y => sq_nonneg _)) hlarge
    exact hm.trans (by linarith [hbound (u + h) (by linarith [hu.1]), hbound u hu.1])
  have havg := intervalIntegral.integral_mono_on hh0.le intervalIntegrable_const
    ((hJshift.add hJ0).const_mul 2) hp
  have hsum : (∫ u in (0 : ℝ)..h, J (u + h)) + (∫ u in (0 : ℝ)..h, J u) =
      ∫ u in (0 : ℝ)..(2 * h), J u := by
    rw [intervalIntegral.integral_comp_add_right]
    simp only [zero_add, show h + h = 2 * h by ring]
    exact (add_comm _ _).trans (intervalIntegral.integral_add_adjacent_intervals hJ0 hJ1)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hJshift hJ0, hsum] at havg
  change I ≤ (2 / h) * ∫ u in (0 : ℝ)..(2 * h), J u
  calc I ≤ (2 * ∫ u in (0 : ℝ)..(2 * h), J u) / h := (le_div_iff₀ hh0).mpr (by simpa only [mul_comm I h] using havg)
    _ = _ := by ring

end LeanLab.GoldbachAverage.Translated402
