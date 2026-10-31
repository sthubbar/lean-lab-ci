/-
AI wrote this Lean code. Goldbach is open.
Source: Li 2024 v4 page 7, defining differential equations for F and f.
These lemmas concern the explicit normalized curve used in the enclosures.
-/
import LeanLab.Li2024.S5Bounds

namespace LeanLab.Li2024.ClosedSieve

open Real intervalIntegral MeasureTheory
open LeanLab.Li2024.S5Bounds

theorem normalizedUpper_initial {s : ℝ} (_hs0 : 0 < s) (hs : s ≤ 3) :
    normalizedUpper s = 1 / s := by
  have he : s - 3 ≤ 0 := by linarith
  simp [normalizedUpper, max_eq_left he, correction]

theorem normalizedUpper_ode {s : ℝ} (hs : 3 < s) (_hs5 : s ≤ 5) :
    HasDerivAt (fun u => u * normalizedUpper u) (Real.log (s - 2) / (s - 1)) s := by
  let y : ℝ := s - 3
  have hy : 0 < y := by dsimp [y]; linarith
  let r : ℝ → ℝ := fun v => Real.log (1 + v) / (2 + v)
  have hc : ContinuousOn r (Set.uIcc 0 y) := by
    rw [Set.uIcc_of_le hy.le]
    apply ContinuousOn.div
    · exact (continuousOn_const.add continuousOn_id).log (by
        intro v hv
        change 1 + v ≠ 0
        linarith [hv.1])
    · exact continuousOn_const.add continuousOn_id
    · intro v hv
      change 2 + v ≠ 0
      linarith [hv.1]
  have hm : Measurable r := by unfold r; fun_prop
  have hcy : ContinuousAt r y := by
    apply ContinuousAt.div
    · apply ContinuousAt.log
      · fun_prop
      · linarith
    · fun_prop
    · linarith
  have hd : HasDerivAt correction (r y) y := by
    change HasDerivAt (fun u => ∫ v in (0 : ℝ)..u, r v) (r y) y
    exact integral_hasDerivAt_right hc.intervalIntegrable
      hm.stronglyMeasurable.stronglyMeasurableAtFilter hcy
  have hh := ((hd.comp s ((hasDerivAt_id s).sub_const 3)).const_add 1)
  have he : (fun u => u * normalizedUpper u) =ᶠ[nhds s]
      (fun u => 1 + correction (u - 3)) := by
    filter_upwards [eventually_gt_nhds hs] with u hu
    have hu0 : u ≠ 0 := by linarith
    have huy : 0 ≤ u - 3 := by linarith
    dsimp [normalizedUpper]
    rw [max_eq_right huy]
    field_simp
  have hfinal := hh.congr_of_eventuallyEq he
  convert hfinal using 1
  dsimp [r, y]
  congr 1 <;> ring

theorem correction_hasDerivAt {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt correction (Real.log (1 + y) / (2 + y)) y := by
  let r : ℝ → ℝ := fun v => Real.log (1 + v) / (2 + v)
  have hc : ContinuousOn r (Set.uIcc 0 y) := by
    rw [Set.uIcc_of_le hy]
    apply ContinuousOn.div
    · exact (continuousOn_const.add continuousOn_id).log (by
        intro v hv
        change 1 + v ≠ 0
        linarith [hv.1])
    · exact continuousOn_const.add continuousOn_id
    · intro v hv
      change 2 + v ≠ 0
      linarith [hv.1]
  have hm : Measurable r := by unfold r; fun_prop
  have hcy : ContinuousAt r y := by
    apply ContinuousAt.div
    · apply ContinuousAt.log
      · fun_prop
      · linarith
    · fun_prop
    · linarith
  change HasDerivAt (fun u => ∫ v in (0 : ℝ)..u, r v) (r y) y
  exact integral_hasDerivAt_right hc.intervalIntegrable
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hcy

theorem local_primitive_unique {G : ℝ → ℝ} (hG₃ : G 3 = 1)
    (hG : ∀ t ∈ Set.Icc (3 : ℝ) 5,
      HasDerivAt G (Real.log (t - 2) / (t - 1)) t)
    {s : ℝ} (hs : s ∈ Set.Icc (3 : ℝ) 5) :
    G s = s * normalizedUpper s := by
  let H : ℝ → ℝ := fun t => 1 + correction (t - 3)
  have hH : ∀ t ∈ Set.Icc (3 : ℝ) s,
      HasDerivAt H (Real.log (t - 2) / (t - 1)) t := by
    intro t ht
    have hy : 0 ≤ t - 3 := by linarith [ht.1]
    have hh := (((correction_hasDerivAt hy).comp t
      ((hasDerivAt_id t).sub_const 3)).const_add 1)
    convert hh using 1
    · rfl
    · congr 1 <;> ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.log (t - 2) / (t - 1))
      volume 3 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs.1]
    apply ContinuousOn.div
    · exact (continuousOn_id.sub continuousOn_const).log (by
        intro t ht
        change t - 2 ≠ 0
        linarith [ht.1])
    · exact continuousOn_id.sub continuousOn_const
    · intro t ht
      change t - 1 ≠ 0
      linarith [ht.1]
  have heG := integral_eq_sub_of_hasDerivAt (fun t ht => by
    rw [Set.uIcc_of_le hs.1] at ht
    exact hG t ⟨ht.1, ht.2.trans hs.2⟩) hint
  have heH := integral_eq_sub_of_hasDerivAt (fun t ht => by
    rw [Set.uIcc_of_le hs.1] at ht
    exact hH t ht) hint
  have hH₃ : H 3 = 1 := by simp [H, correction]
  rw [hG₃] at heG
  rw [hH₃] at heH
  have he : G s = H s := by linarith
  rw [he]
  have hs0 : s ≠ 0 := by linarith [hs.1]
  have hy : 0 ≤ s - 3 := by linarith [hs.1]
  dsimp [H, normalizedUpper]
  rw [max_eq_right hy]
  field_simp

theorem upper_eq_of_local_data {U : ℝ → ℝ}
    (hinit : ∀ s : ℝ, 0 < s → s ≤ 3 → U s = 1 / s)
    (hode : ∀ t ∈ Set.Icc (3 : ℝ) 5,
      HasDerivAt (fun t => t * U t) (Real.log (t - 2) / (t - 1)) t)
    {s : ℝ} (hs0 : 0 < s) (hs5 : s ≤ 5) : U s = normalizedUpper s := by
  by_cases hs3 : s ≤ 3
  · rw [hinit s hs0 hs3, normalizedUpper_initial hs0 hs3]
  · have h₃ : (3 : ℝ) * U 3 = 1 := by rw [hinit 3 (by norm_num) le_rfl]; norm_num
    have he := local_primitive_unique h₃ hode (s := s) ⟨by linarith, hs5⟩
    exact mul_left_cancel₀ hs0.ne' he

end LeanLab.Li2024.ClosedSieve

#print axioms LeanLab.Li2024.ClosedSieve.normalizedUpper_initial

#print axioms LeanLab.Li2024.ClosedSieve.normalizedUpper_ode

#print axioms LeanLab.Li2024.ClosedSieve.correction_hasDerivAt

#print axioms LeanLab.Li2024.ClosedSieve.local_primitive_unique

#print axioms LeanLab.Li2024.ClosedSieve.upper_eq_of_local_data
