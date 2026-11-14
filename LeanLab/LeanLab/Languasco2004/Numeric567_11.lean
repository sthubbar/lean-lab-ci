/-
Jia 1996 pages 275 to 277, numerical term 11 in Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Polynomial567

namespace LeanLab.Languasco2004.Numeric567_11
open Real Set intervalIntegral Numeric548 Polynomial567
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF. Pages 275 to 277, term 11: exact polynomial integration retains a strict reserve. -/
theorem polynomial_integral :
    (7141 / 1000000 : ℝ) + 1/100000000 ≤ ∫ t in (4 / 9 : ℝ)..(701 / 1566), ∫ u in ((1 / 4) + (-1 / 4) * t)..((1 / 3) + (-1 / 3) * t), minorant 1 (1397 / 3132) (75 / 464) (7375 / 18792) t u := by sorry

/-- Pages 275 to 277, term 11: the full source integral exceeds its printed coefficient.
The reserve is one hundred millionth. No exceptional prime estimate is used. -/
theorem source_integral_lower :
    (7141 / 1000000 : ℝ) + 1/100000000 ≤ ∫ t in (4 / 9 : ℝ)..(701 / 1566), ∫ u in ((1 / 4) + (-1 / 4) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u := by
  let R := Icc (4 / 9 : ℝ) (701 / 1566) ×ˢ Icc (865 / 6264 : ℝ) (5 / 27)
  have ht (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 := by linarith [hz.1.1]
  have hu (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.2 := by linarith [hz.2.1]
  have hv (z : ℝ × ℝ) (hz : z ∈ R) : 0 < 1-z.1-z.2 := by
    linarith [hz.1.2, hz.2.2]
  have hF : ContinuousOn (Function.uncurry (kernel 1)) R := by
    norm_num only [kernel, Function.uncurry]
    have harg : ContinuousOn (fun z : ℝ × ℝ => (1-z.1)/z.2-2) R :=
      ((continuousOn_const.sub continuousOn_fst).div continuousOn_snd
        (fun z hz => (hu z hz).ne')).sub continuousOn_const
    have hargpos (z : ℝ × ℝ) (hz : z ∈ R) : 0 < (1-z.1)/z.2-2 := by
      apply sub_pos.mpr
      apply (lt_div_iff₀ (hu z hz)).mpr
      linarith [hz.1.2, hz.2.2]
    exact (continuousOn_const.add (harg.log (fun z hz => (hargpos z hz).ne'))).div
      (by fun_prop) (fun z hz => (mul_pos (mul_pos (ht z hz) (hu z hz)) (hv z hz)).ne')
  have hP : Continuous (Function.uncurry (fun t u => minorant 1 (1397 / 3132) (75 / 464) (7375 / 18792) t u)) := by
    unfold minorant invPoly5 invPoly7
    norm_num only
    simp only [ite_true, ite_false]
    fun_prop
  have hm := strip_integral_mono (kernel 1) (fun t u => minorant 1 (1397 / 3132) (75 / 464) (7375 / 18792) t u)
    (4 / 9) (701 / 1566) (865 / 6264) (5 / 27)
    (fun t => (1 / 4) + (-1 / 4) * t) (fun t => (1 / 3) + (-1 / 3) * t) (by norm_num) (by norm_num) hF hP
    (by fun_prop) (by fun_prop)
    (by intro t ht; refine ⟨?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2])
    (by
      intro t ht u hu
      apply minorant_log_le
      all_goals try norm_num
      all_goals linarith [ht.1, ht.2, hu.1, hu.2])
  exact polynomial_integral.trans hm

#print axioms polynomial_integral
#print axioms source_integral_lower
end
end LeanLab.Languasco2004.Numeric567_11
