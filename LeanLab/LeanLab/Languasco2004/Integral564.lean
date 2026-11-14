/-
Jia 1996 Lemma 27, pages 281 and 282, full remainder integral comparisons.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderData564

namespace LeanLab.Languasco2004.Integral564
open Real Set Finset intervalIntegral RemainderData564 MovingIntegral548
noncomputable section
set_option maxHeartbeats 0

/-- Pages 281 and 282: the source lower kernel is continuous on a common rectangle. -/
theorem kernel_continuousOn (i : Fin 16) :
    ContinuousOn (Function.uncurry (kernel i))
      (Icc (1/3:ℝ) (1/2) ×ˢ Icc (1/10:ℝ) (1/5)) := by
  let R := Icc (1/3:ℝ) (1/2) ×ˢ Icc (1/10:ℝ) (1/5)
  have ht (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 := by linarith [hz.1.1]
  have hu (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.2 := by linarith [hz.2.1]
  have hv (z : ℝ × ℝ) (hz : z ∈ R) : 0 < 1-z.1-z.2 := by
    linarith [hz.1.2, hz.2.2]
  have ha (z : ℝ × ℝ) (hz : z ∈ R) : 0 < (1-z.1)/z.2-2 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (hu z hz)).mpr
    linarith [hz.1.2, hz.2.2]
  unfold kernel
  split_ifs
  · have hc : ContinuousOn (fun z : ℝ × ℝ => (1-z.1)/z.2-2) R :=
      ((continuousOn_const.sub continuous_fst.continuousOn).div
        continuous_snd.continuousOn (fun z hz => (hu z hz).ne')).sub continuousOn_const
    exact (continuousOn_const.add (hc.log (fun z hz => (ha z hz).ne'))).div
      (by fun_prop) (fun z hz => (mul_pos (mul_pos (ht z hz) (hu z hz)) (hv z hz)).ne')
  · exact continuousOn_const.div (by fun_prop)
      (fun z hz => (mul_pos (ht z hz) (sq_pos_of_pos (hu z hz))).ne')

/-- Pages 281 and 282: the source inner integral is continuous on its exact t interval. -/
theorem source_inner_continuousOn (i : Fin 16) :
    let r := numericData i
    ContinuousOn (fun t : ℝ =>
      ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t), kernel i t u)
      (Icc (r 0 : ℝ) (r 1)) := by
  dsimp
  have hab : (numericData i 0 : ℝ) ≤ numericData i 1 := by
    fin_cases i <;> norm_num [numericData]
  have hF : ContinuousOn (Function.uncurry (kernel i))
      (Icc (numericData i 0 : ℝ) (numericData i 1) ×ˢ Icc (1/10:ℝ) (1/5)) := by
    apply (kernel_continuousOn i).mono
    intro z hz
    obtain ⟨ht, ht', _⟩ := row_endpoints i z.1 hz.1.1 hz.1.2
    exact ⟨⟨ht,ht'⟩,hz.2⟩
  apply moving_integral_continuousOn (kernel i)
    (numericData i 0) (numericData i 1) (1/10) (1/5)
    (fun t => (numericData i 2 : ℝ)+numericData i 3*t)
    (fun t => (numericData i 4 : ℝ)+numericData i 5*t)
    hab (by norm_num) hF (by fun_prop) (by fun_prop)
  intro t ht
  obtain ⟨_, _, hl, hlu, hu⟩ := row_endpoints i t ht.1 ht.2
  exact ⟨hl, hlu.trans hu, hl.trans hlu, hu⟩

/-- Pages 281 and 282: every polynomial inner integral is continuous. -/
theorem polynomial_inner_continuous (i : Fin 16) :
    let r := numericData i
    Continuous (fun t : ℝ =>
      ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t), polynomial i t u) := by
  dsimp
  have hc : Continuous (Function.uncurry (polynomial i)) := by
    unfold polynomial reciprocal logReciprocal
    split_ifs <;> fun_prop
  have hU := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => (numericData i 4 : ℝ)+numericData i 5*t) by fun_prop)
  have hL := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => (numericData i 2 : ℝ)+numericData i 3*t) by fun_prop)
  have hp (t : ℝ) : Continuous (polynomial i t) := by
    unfold polynomial reciprocal logReciprocal
    split_ifs <;> fun_prop
  have he : (fun t : ℝ => ∫ u in ((numericData i 2 : ℝ)+numericData i 3*t)..
      ((numericData i 4 : ℝ)+numericData i 5*t), polynomial i t u) =
      fun t : ℝ => (∫ u in (0:ℝ)..((numericData i 4 : ℝ)+numericData i 5*t), polynomial i t u) -
        (∫ u in (0:ℝ)..((numericData i 2 : ℝ)+numericData i 3*t), polynomial i t u) := by
    funext t
    exact (integral_interval_sub_left ((hp t).intervalIntegrable _ _)
      ((hp t).intervalIntegrable _ _)).symm
  rw [he]
  exact hU.sub hL

/-- Pages 281 and 282: comparison applies to the complete double integral. -/
theorem polynomial_integral_le (i : Fin 16) :
    let r := numericData i
    (∫ t in (r 0 : ℝ)..(r 1),
      ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t), polynomial i t u) ≤ sourceIntegral i := by
  dsimp [sourceIntegral]
  have hab : (numericData i 0 : ℝ) ≤ numericData i 1 := by
    fin_cases i <;> norm_num [numericData]
  apply integral_mono_on hab
    ((polynomial_inner_continuous i).intervalIntegrable _ _)
    ((source_inner_continuousOn i).intervalIntegrable_of_Icc hab)
  intro t ht
  obtain ⟨ht1, ht2, hl, hlu, hu⟩ := row_endpoints i t ht.1 ht.2
  have hp : Continuous (polynomial i t) := by unfold polynomial reciprocal logReciprocal; split_ifs <;> fun_prop
  have hk : ContinuousOn (kernel i t) (Icc ((numericData i 2 : ℝ)+numericData i 3*t)
      ((numericData i 4 : ℝ)+numericData i 5*t)) := by
    exact (kernel_continuousOn i).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu' => ⟨⟨ht1,ht2⟩,⟨hl.trans hu'.1,hu'.2.trans hu⟩⟩)
  apply integral_mono_on hlu (hp.intervalIntegrable _ _) (hk.intervalIntegrable_of_Icc hlu)
  intro u hu'
  exact polynomial_le i t u ht.1 ht.2 hu'.1 hu'.2

#print axioms kernel_continuousOn
#print axioms source_inner_continuousOn
#print axioms polynomial_inner_continuous
#print axioms polynomial_integral_le
end
end LeanLab.Languasco2004.Integral564
