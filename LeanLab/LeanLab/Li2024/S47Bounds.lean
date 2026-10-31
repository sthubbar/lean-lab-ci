/-
AI wrote this Lean code. Goldbach is open.
Source: Li 2024 v4 pages 9 and 10, equations 17, 19 and 21.
The local table agrees with the displayed H lower bounds on (2.8, 3.6].
It is extended by constants outside that interval for integrability proofs.
-/
import LeanLab.Li2024.S5Bounds

namespace LeanLab.Li2024.S47Bounds

open Real intervalIntegral MeasureTheory
open LeanLab.Li2024.S5Bounds

noncomputable def localH (s : ℝ) : ℝ :=
  if s ≤ 2.9 then 0.0078162 else
  if s ≤ 3.0 then 0.0072943 else
  if s ≤ 3.1 then 0.0061642 else
  if s ≤ 3.2 then 0.0052233 else
  if s ≤ 3.3 then 0.0044073 else
  if s ≤ 3.4 then 0.0036995 else
  if s ≤ 3.5 then 0.0030860 else 0.0025551

theorem localH_properties : Measurable localH ∧
    (∀ s : ℝ, 0 ≤ localH s ∧ localH s ≤ 0.01) ∧ Antitone localH := by
  refine ⟨?_, ?_, ?_⟩
  · unfold localH
    repeat' first
      | exact measurable_const
      | apply Measurable.ite (measurableSet_le measurable_id measurable_const)
  · intro s
    unfold localH
    split_ifs <;> norm_num
  · intro x y hxy
    unfold localH
    split_ifs <;> norm_num at * <;> linarith

noncomputable def clippedExcess (t : ℝ) : ℝ := max 0 (excess t)

noncomputable def correctionLower (a b : ℝ) : ℝ :=
  (clippedExcess b) ^ 2 / (2 * (1 + clippedExcess a) * (2 + clippedExcess a))

noncomputable def correctionUpper (a : ℝ) : ℝ := (clippedExcess a) ^ 2 / 4

theorem correction_rectangle {a b t : ℝ} (ht : t ∈ Set.Icc a b) :
    correctionLower a b ≤ correction (clippedExcess t) ∧
      correction (clippedExcess t) ≤ correctionUpper a := by
  have h₀ : 0 ≤ clippedExcess b := le_max_left _ _
  have h₁ : 0 ≤ clippedExcess t := le_max_left _ _
  have h₂ : 0 ≤ clippedExcess a := le_max_left _ _
  have hbt : clippedExcess b ≤ clippedExcess t := by
    apply max_le_max le_rfl
    dsimp [excess]
    linarith [ht.2]
  have hta : clippedExcess t ≤ clippedExcess a := by
    apply max_le_max le_rfl
    dsimp [excess]
    linarith [ht.1]
  have hs₀ : (clippedExcess b) ^ 2 ≤ (clippedExcess t) ^ 2 := by nlinarith
  have hs₁ : (clippedExcess t) ^ 2 ≤ (clippedExcess a) ^ 2 := by nlinarith
  have hd : 2 * (1 + clippedExcess t) * (2 + clippedExcess t) ≤
      2 * (1 + clippedExcess a) * (2 + clippedExcess a) := by nlinarith
  have hq := correction_bounds h₁
  constructor
  · apply le_trans _ hq.1
    calc
      correctionLower a b ≤ (clippedExcess t) ^ 2 /
          (2 * (1 + clippedExcess a) * (2 + clippedExcess a)) := by
        exact div_le_div_of_nonneg_right hs₀ (by positivity)
      _ ≤ (clippedExcess t) ^ 2 /
          (2 * (1 + clippedExcess t) * (2 + clippedExcess t)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd
  · exact hq.2.trans (div_le_div_of_nonneg_right hs₁ (by norm_num))

noncomputable def d (t : ℝ) : ℝ := 57 / 64 - 5 / 2 * t
noncomputable def e (t : ℝ) : ℝ := 1 / 2 - t
noncomputable def tableAt (t : ℝ) : ℝ := localH ((1149 / 100) * e t)
noncomputable def curve (t : ℝ) : ℝ :=
  (4 / (t * d t)) * (1 + correction (clippedExcess t)) -
    tableAt t * (4 / (t * e t))
noncomputable def cellLower (a b : ℝ) : ℝ :=
  (4 / (b * d a)) * (1 + correctionLower a b) - tableAt b * (4 / (a * e b))
noncomputable def cellUpper (a b : ℝ) : ℝ :=
  (4 / (a * d b)) * (1 + correctionUpper a) - tableAt a * (4 / (b * e a))

theorem cell_pointwise {a b t : ℝ} (ha : (25 / 128 : ℝ) ≤ a)
    (hb : b ≤ (1 / 4 : ℝ)) (ht : t ∈ Set.Icc a b) :
    cellLower a b ≤ curve t ∧ curve t ≤ cellUpper a b := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith [ht.1, ht.2]
  have htp : 0 < t := by linarith [ht.1]
  have hda : 0 < d a := by dsimp [d]; linarith [ht.1, ht.2]
  have hdb : 0 < d b := by dsimp [d]; linarith
  have hdt : 0 < d t := by dsimp [d]; linarith [ht.2]
  have hea : 0 < e a := by dsimp [e]; linarith [ht.1, ht.2]
  have heb : 0 < e b := by dsimp [e]; linarith
  have het : 0 < e t := by dsimp [e]; linarith [ht.2]
  have hdat : d t ≤ d a := by dsimp [d]; linarith [ht.1]
  have hdtb : d b ≤ d t := by dsimp [d]; linarith [ht.2]
  have heat : e t ≤ e a := by dsimp [e]; linarith [ht.1]
  have hetb : e b ≤ e t := by dsimp [e]; linarith [ht.2]
  have hB₀ : 4 / (b * d a) ≤ 4 / (t * d t) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos htp hdt)
      (mul_le_mul ht.2 hdat hdt.le hbp.le)
  have hB₁ : 4 / (t * d t) ≤ 4 / (a * d b) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hap hdb)
      (mul_le_mul ht.1 hdtb hdb.le htp.le)
  have hE₀ : 4 / (b * e a) ≤ 4 / (t * e t) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos htp het)
      (mul_le_mul ht.2 heat het.le hbp.le)
  have hE₁ : 4 / (t * e t) ≤ 4 / (a * e b) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hap heb)
      (mul_le_mul ht.1 hetb heb.le htp.le)
  have hH₀ : tableAt a ≤ tableAt t := by
    apply localH_properties.2.2
    dsimp [e]
    linarith [ht.1]
  have hH₁ : tableAt t ≤ tableAt b := by
    apply localH_properties.2.2
    dsimp [e]
    linarith [ht.2]
  have hHt : 0 ≤ tableAt t := (localH_properties.2.1 _).1
  have hHb : 0 ≤ tableAt b := (localH_properties.2.1 _).1
  have hq := correction_rectangle ht
  have hqa : 0 ≤ correctionLower a b := by
    dsimp [correctionLower]
    have := le_max_left (0 : ℝ) (excess a)
    change 0 ≤ (clippedExcess b) ^ 2 / (2 * (1 + clippedExcess a) * (2 + clippedExcess a))
    have : 0 ≤ clippedExcess a := le_max_left _ _
    positivity
  have hqt : 0 ≤ correction (clippedExcess t) := hqa.trans hq.1
  have hR₀ := mul_le_mul hB₀ (show 1 + correctionLower a b ≤ 1 + correction (clippedExcess t) by linarith [hq.1]) (by linarith : 0 ≤ 1 + correctionLower a b)
    (by positivity : (0 : ℝ) ≤ 4 / (t * d t))
  have hR₁ := mul_le_mul hB₁ (show 1 + correction (clippedExcess t) ≤ 1 + correctionUpper a by linarith [hq.2]) (by linarith : 0 ≤ 1 + correction (clippedExcess t))
    (by positivity : (0 : ℝ) ≤ 4 / (a * d b))
  have hS₀ := mul_le_mul hH₀ hE₀ (by positivity : (0 : ℝ) ≤ 4 / (b * e a)) hHt
  have hS₁ := mul_le_mul hH₁ hE₁ (by positivity : (0 : ℝ) ≤ 4 / (t * e t)) hHb
  dsimp [cellLower, cellUpper, curve]
  constructor <;> linarith

theorem curve_integrable :
    IntervalIntegrable curve volume (25 / 128) (1 / 4) := by
  have hB : ContinuousOn (fun t : ℝ => 4 / (t * d t)) (Set.Icc (25 / 128) (1 / 4)) := by
    apply continuousOn_const.div (continuousOn_id.mul (by unfold d; fun_prop))
    intro t ht
    change t * d t ≠ 0
    apply mul_ne_zero
    · linarith [ht.1]
    · dsimp [d]
      linarith [ht.2]
  have hm : Continuous clippedExcess := by unfold clippedExcess excess; fun_prop
  have hQ : ContinuousOn (fun t => correction (clippedExcess t))
      (Set.Icc (25 / 128) (1 / 4)) := by
    apply correction_continuous.comp hm.continuousOn
    intro t ht
    constructor
    · exact le_max_left _ _
    · apply max_le (by norm_num)
      dsimp [excess]
      linarith [ht.1]
  have hR : ContinuousOn (fun t => (4 / (t * d t)) * (1 + correction (clippedExcess t)))
      (Set.Icc (25 / 128) (1 / 4)) := hB.mul (continuousOn_const.add hQ)
  have hM : Measurable tableAt := by
    unfold tableAt
    apply localH_properties.1.comp
    unfold e
    fun_prop
  have hH : IntegrableOn tableAt (Set.Icc (25 / 128 : ℝ) (1 / 4)) volume := by
    apply (integrableOn_const (C := (0.01 : ℝ)) (by simp)).mono' hM.aestronglyMeasurable
    exact ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ tableAt t from (localH_properties.2.1 _).1)]
      exact (localH_properties.2.1 _).2
  have hE : ContinuousOn (fun t : ℝ => 4 / (t * e t)) (Set.Icc (25 / 128) (1 / 4)) := by
    apply continuousOn_const.div (continuousOn_id.mul (by unfold e; fun_prop))
    intro t ht
    change t * e t ≠ 0
    apply mul_ne_zero
    · linarith [ht.1]
    · dsimp [e]
      linarith [ht.2]
  have hi : IntegrableOn curve (Set.Icc (25 / 128 : ℝ) (1 / 4)) volume :=
    hR.integrableOn_Icc.sub (hH.mul_continuousOn hE isCompact_Icc)
  apply IntegrableOn.intervalIntegrable
  simpa only [Set.uIcc_of_le (by norm_num : (25 / 128 : ℝ) ≤ 1 / 4)] using hi

theorem cell_integral_bounds {a b : ℝ} (ha : (25 / 128 : ℝ) ≤ a)
    (hb : b ≤ (1 / 4 : ℝ)) (hab : a ≤ b) :
    (b - a) * cellLower a b ≤ (∫ t in a..b, curve t) ∧
      (∫ t in a..b, curve t) ≤ (b - a) * cellUpper a b := by
  have hi : IntervalIntegrable curve volume a b := curve_integrable.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num)]
    intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩)
  have hlo := integral_mono_on hab (intervalIntegrable_const) hi
    (fun t ht => (cell_pointwise ha hb ht).1)
  have hup := integral_mono_on hab hi (intervalIntegrable_const)
    (fun t ht => (cell_pointwise ha hb ht).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using And.intro hlo hup

end LeanLab.Li2024.S47Bounds

#print axioms LeanLab.Li2024.S47Bounds.localH_properties

#print axioms LeanLab.Li2024.S47Bounds.correction_rectangle

#print axioms LeanLab.Li2024.S47Bounds.cell_pointwise

#print axioms LeanLab.Li2024.S47Bounds.curve_integrable

#print axioms LeanLab.Li2024.S47Bounds.cell_integral_bounds
