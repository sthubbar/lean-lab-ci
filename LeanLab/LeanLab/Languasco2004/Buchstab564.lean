/-
Jia 1996 Lemma 27, pages 281 and 282, and display 40 on page 261.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The comparison is CONDITIONAL ON the stated Buchstab segment and global lower bound.
No new Prop input or asserted Buchstab function is introduced.
-/
import LeanLab.Languasco2004.Numeric564

namespace LeanLab.Languasco2004.Buchstab564
open Real Set Finset intervalIntegral RemainderData564 Integral564 Numeric564
open BuchstabInitial316 Kernel548 MovingIntegral548
noncomputable section
set_option maxHeartbeats 0

/-- Pages 281 and 282: the full Buchstab kernel on a printed subdomain.
The function w is an explicit parameter, not the initial segment extended beyond three. -/
def buchstabRow (w : ℝ → ℝ) (i : Fin 16) : ℝ :=
  let r := numericData i
  ∫ t in (r 0 : ℝ)..(r 1),
    ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t),
      w ((1-t-u)/u) / (t*u^2)

/-- Pages 261, 281 and 282: the full kernel is continuous on the common rectangle
when w is continuous on its source domain beginning at one. -/
theorem full_kernel_continuousOn (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 1)) :
    ContinuousOn (fun z : ℝ × ℝ => w ((1-z.1-z.2)/z.2) / (z.1*z.2^2))
      (Icc (1/3:ℝ) (1/2) ×ˢ Icc (1/10:ℝ) (1/5)) := by
  let R := Icc (1/3:ℝ) (1/2) ×ˢ Icc (1/10:ℝ) (1/5)
  have ht (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 := by linarith [hz.1.1]
  have hu (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.2 := by linarith [hz.2.1]
  have ha (z : ℝ × ℝ) (hz : z ∈ R) : 1 ≤ (1-z.1-z.2)/z.2 := by
    apply (le_div_iff₀ (hu z hz)).mpr
    linarith [hz.1.2, hz.2.2]
  have hc : ContinuousOn (fun z : ℝ × ℝ => (1-z.1-z.2)/z.2) R :=
    ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn).div
      continuous_snd.continuousOn (fun z hz => (hu z hz).ne')
  exact (hw.comp hc (fun z hz => ha z hz)).div (by fun_prop)
    (fun z hz => (mul_pos (ht z hz) (sq_pos_of_pos (hu z hz))).ne')

/-- Pages 281 and 282: the complete full kernel inner integral is continuous. -/
theorem full_inner_continuousOn (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 1)) (i : Fin 16) :
    let r := numericData i
    ContinuousOn (fun t : ℝ => ∫ u in ((r 2 : ℝ)+r 3*t)..((r 4 : ℝ)+r 5*t),
      w ((1-t-u)/u) / (t*u^2)) (Icc (r 0 : ℝ) (r 1)) := by
  dsimp
  have hab : (numericData i 0 : ℝ) ≤ numericData i 1 := by
    fin_cases i <;> norm_num [numericData]
  have hF : ContinuousOn (fun z : ℝ × ℝ => w ((1-z.1-z.2)/z.2) / (z.1*z.2^2))
      (Icc (numericData i 0 : ℝ) (numericData i 1) ×ˢ Icc (1/10:ℝ) (1/5)) := by
    apply (full_kernel_continuousOn w hw).mono
    intro z hz
    obtain ⟨ht, ht', _⟩ := row_endpoints i z.1 hz.1.1 hz.1.2
    exact ⟨⟨ht,ht'⟩,hz.2⟩
  apply moving_integral_continuousOn
    (fun t u : ℝ => w ((1-t-u)/u) / (t*u^2))
    (numericData i 0) (numericData i 1) (1/10) (1/5)
    (fun t => (numericData i 2 : ℝ)+numericData i 3*t)
    (fun t => (numericData i 4 : ℝ)+numericData i 5*t)
    hab (by norm_num) hF (by fun_prop) (by fun_prop)
  intro t ht
  obtain ⟨_, _, hl, hlu, hu⟩ := row_endpoints i t ht.1 ht.2
  exact ⟨hl, hlu.trans hu, hl.trans hlu, hu⟩

/-- Pages 261, 281 and 282: the source lower kernel is below the full kernel.
CONDITIONAL ON the explicit initial segment and the global lower bound for w. -/
theorem row_kernel_buchstab_lower (w : ℝ → ℝ)
    (hinit : ∀ s : ℝ, 2 ≤ s → s ≤ 3 → w s = buchstabInitial s)
    (hglobal : ∀ s : ℝ, 3 ≤ s → 0.5607 ≤ w s)
    (i : Fin 16) (t u : ℝ)
    (htl : (numericData i 0 : ℝ) ≤ t) (htu : t ≤ (numericData i 1 : ℝ))
    (hul : (numericData i 2 : ℝ)+numericData i 3*t ≤ u)
    (huu : u ≤ (numericData i 4 : ℝ)+numericData i 5*t) :
    kernel i t u ≤ w ((1-t-u)/u) / (t*u^2) := by
  obtain ⟨ht, hu, hv, _⟩ := row_kernel_bounds i t u htl htu hul huu
  have hr := row_buchstab_range i t u htl htu hul huu
  by_cases hk : isLog i = true
  · simp only [hk, ↓reduceIte] at hr
    rw [hinit _ hr.1 hr.2]
    simpa only [kernel, hk, ↓reduceIte] using
      (initial_kernel_high t u ht hu hv hr.1).ge
  · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hr
    simpa only [kernel, hk, Bool.false_eq_true, ↓reduceIte] using
      div_le_div_of_nonneg_right (hglobal _ hr) (mul_pos ht (sq_pos_of_pos hu)).le

/-- Pages 281 and 282: the entire printed lower integral is below the full one.
CONDITIONAL ON continuity, the initial segment and the global Buchstab bound. -/
theorem row_integral_buchstab_lower (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 1))
    (hinit : ∀ s : ℝ, 2 ≤ s → s ≤ 3 → w s = buchstabInitial s)
    (hglobal : ∀ s : ℝ, 3 ≤ s → 0.5607 ≤ w s) (i : Fin 16) :
    sourceIntegral i ≤ buchstabRow w i := by
  dsimp [sourceIntegral, buchstabRow]
  have hab : (numericData i 0 : ℝ) ≤ numericData i 1 := by
    fin_cases i <;> norm_num [numericData]
  apply integral_mono_on hab
    ((source_inner_continuousOn i).intervalIntegrable_of_Icc hab)
    ((full_inner_continuousOn w hw i).intervalIntegrable_of_Icc hab)
  intro t ht
  obtain ⟨ht1, ht2, hl, hlu, hu⟩ := row_endpoints i t ht.1 ht.2
  have hk : ContinuousOn (kernel i t) (Icc ((numericData i 2 : ℝ)+numericData i 3*t)
      ((numericData i 4 : ℝ)+numericData i 5*t)) :=
    (kernel_continuousOn i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu' => ⟨⟨ht1,ht2⟩,⟨hl.trans hu'.1,hu'.2.trans hu⟩⟩)
  have hf : ContinuousOn (fun u : ℝ => w ((1-t-u)/u) / (t*u^2))
      (Icc ((numericData i 2 : ℝ)+numericData i 3*t)
      ((numericData i 4 : ℝ)+numericData i 5*t)) :=
    (full_kernel_continuousOn w hw).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu' => ⟨⟨ht1,ht2⟩,⟨hl.trans hu'.1,hu'.2.trans hu⟩⟩)
  apply integral_mono_on hlu (hk.intervalIntegrable_of_Icc hlu) (hf.intervalIntegrable_of_Icc hlu)
  intro u hu'
  exact row_kernel_buchstab_lower w hinit hglobal i t u ht.1 ht.2 hu'.1 hu'.2

/-- Page 282: the full sixteen row Buchstab sum exceeds the printed subtotal.
CONDITIONAL ON continuity, the initial segment and the global Buchstab bound.
The numerical subtotal is also CONDITIONAL ON the eight OPEN short_integral inputs. -/
theorem remainder_buchstab_lower (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 1))
    (hinit : ∀ s : ℝ, 2 ≤ s → s ≤ 3 → w s = buchstabInitial s)
    (hglobal : ∀ s : ℝ, 3 ≤ s → 0.5607 ≤ w s) :
    (0.0242792 : ℝ) ≤ ∑ i : Fin 16, buchstabRow w i := by
  exact remainder_numeric_margin.trans (sum_le_sum fun i _ =>
    row_integral_buchstab_lower w hw hinit hglobal i)

/-- Supporting domain model: clamp the initial logarithmic formula to two through three.
This tests the comparison hypotheses and does not assert the full delay equation. -/
def clampedInitial (s : ℝ) : ℝ :=
  (1+Real.log (max 2 (min 3 s)-1)) / max 2 (min 3 s)

/-- Pages 261, 281 and 282: the exact comparison hypotheses have a concrete model.
The model agrees with the source segment and stays constant after three. -/
theorem clamped_initial_instance :
    ContinuousOn clampedInitial (Ici 1) ∧
    (∀ s : ℝ, 2 ≤ s → s ≤ 3 → clampedInitial s = buchstabInitial s) ∧
    (∀ s : ℝ, 3 ≤ s → 0.5607 ≤ clampedInitial s) := by
  have hc : Continuous (fun s : ℝ => max 2 (min 3 s)) := by fun_prop
  have hp (s : ℝ) : 0 < max 2 (min 3 s) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have ha (s : ℝ) : 0 < max 2 (min 3 s)-1 := by have := le_max_left 2 (min 3 s); linarith
  have hcont : Continuous clampedInitial :=
    (continuous_const.add ((hc.sub continuous_const).log (fun s => (ha s).ne'))).div hc
      (fun s => (hp s).ne')
  refine ⟨hcont.continuousOn, ?_, ?_⟩
  · intro s hs2 hs3
    rw [buchstabInitial_eq_log hs2]
    simp [clampedInitial, min_eq_right hs3, max_eq_right hs2]
  · intro s hs
    have hlog : (0.69:ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    simp only [clampedInitial, min_eq_left hs, max_eq_right (by norm_num : (2:ℝ) ≤ 3)]
    norm_num
    linarith

#print axioms full_kernel_continuousOn
#print axioms full_inner_continuousOn
#print axioms row_kernel_buchstab_lower
#print axioms row_integral_buchstab_lower
#print axioms remainder_buchstab_lower
#print axioms clamped_initial_instance
end
end LeanLab.Languasco2004.Buchstab564
