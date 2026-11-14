/-
Jia 1996 page 281, supporting continuity of the first double integral.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Kernel548

namespace LeanLab.Languasco2004.MovingIntegral548
open Real Set intervalIntegral
noncomputable section

/-- Page 281 numerical support: a continuous kernel on a fixed compact rectangle
has a continuous moving inner integral when both continuous endpoints stay inside.
No integrability premise is left to a caller. -/
theorem moving_integral_continuousOn (F : ℝ → ℝ → ℝ) (a b c d : ℝ)
    (L U : ℝ → ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d))
    (hL : Continuous L) (hU : Continuous U)
    (hBounds : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ d ∧ c ≤ U t ∧ U t ≤ d) :
    ContinuousOn (fun t => ∫ u in L t..U t, F t u) (Icc a b) := by
  let ct := fun t : ℝ => max a (min b t)
  let cu := fun u : ℝ => max c (min d u)
  have hct (t : ℝ) : ct t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hcu (u : ℝ) : cu u ∈ Icc c d :=
    ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩
  have hfull : Continuous (Function.uncurry (fun t u => F (ct t) (cu u))) := by
    exact hF.comp_continuous
      (show Continuous (fun z : ℝ × ℝ => (ct z.1, cu z.2)) by dsimp [ct, cu]; fun_prop)
      (fun z => ⟨hct z.1, hcu z.2⟩)
  have hIU := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hfull hU
  have hIL := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hfull hL
  have he : (fun t => ∫ u in L t..U t, F (ct t) (cu u)) = fun t =>
      (∫ u in (0 : ℝ)..U t, F (ct t) (cu u)) -
      (∫ u in (0 : ℝ)..L t, F (ct t) (cu u)) := by
    funext t
    exact (integral_interval_sub_left ((hfull.uncurry_left t).intervalIntegrable _ _)
      ((hfull.uncurry_left t).intervalIntegrable _ _)).symm
  have hc : Continuous (fun t => ∫ u in L t..U t, F (ct t) (cu u)) := by
    rw [he]
    exact hIU.sub hIL
  apply hc.continuousOn.congr
  intro t ht
  obtain ⟨hcL, hLd, hcU, hUd⟩ := hBounds t ht
  apply integral_congr
  intro u hu
  have huL : c ≤ u := (le_min hcL hcU).trans hu.1
  have huU : u ≤ d := hu.2.trans (max_le hLd hUd)
  simp only [ct, cu, min_eq_right ht.2, max_eq_right ht.1,
    min_eq_right huU, max_eq_right huL]

#print axioms moving_integral_continuousOn
end
end LeanLab.Languasco2004.MovingIntegral548
