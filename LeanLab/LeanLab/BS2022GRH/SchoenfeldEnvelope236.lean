/- AI wrote the Lean code for CODEX task236.
Schoenfeld count envelope for journal Lemma 14 p. 1237. Goldbach is open. -/
import LeanLab.BS2022GRH.SlicePartial236
import LeanLab.BS2022GRH.PublishedInputs232
namespace LeanLab.BS2022GRH.SliceMass236
open Real Finset Classical MeasureTheory intervalIntegral Filter Topology
noncomputable section

/-- The principal value li has its usual derivative above two, journal p. 1237. -/
theorem liPV_hasDeriv (x : ℝ) (hx : 2 < x) : HasDerivAt liPV (1 / log x) x := by
  have hcont (t : ℝ) (ht : 1 < t) : ContinuousAt (fun s : ℝ => 1 / log s) t := by
    exact continuousAt_const.div (continuousAt_log (by linarith : t ≠ 0)) (log_pos ht).ne'
  have hcc : ContinuousOn (fun t : ℝ => 1 / log t) (Set.uIcc 2 x) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le hx.le] at ht
    exact hcont t (by linarith [ht.1])
  have hint : IntervalIntegrable (fun t : ℝ => 1 / log t) volume 2 x := hcc.intervalIntegrable
  have hsm : StronglyMeasurableAtFilter (fun t : ℝ => 1 / log t) (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi (1 : ℝ)) isOpen_Ioi hcont x (show 1 < x by linarith)
  have hd := (integral_hasDerivAt_right hint hsm (hcont x (by linarith))).const_add (liPV 2)
  have heq : liPV =ᶠ[𝓝 x] (fun t => liPV 2 + ∫ s in (2 : ℝ)..t, 1 / log s) := by
    filter_upwards [eventually_gt_nhds hx] with t ht
    exact liPV_eq_add ht.le
  exact hd.congr_of_eventuallyEq heq

/-- The normalized logarithmic integral, journal p. 1237. -/
def normalizedLi (x : ℝ) : ℝ := log x * liPV x / x

/-- Differentiate the leading term in the uniform count envelope, p. 1237. -/
theorem normalizedLi_hasDeriv (x : ℝ) (hx : 2 < x) :
    HasDerivAt normalizedLi (((1 - log x) * liPV x + x) / x ^ 2) x := by
  have hx0 : 0 < x := by linarith
  have hl : log x ≠ 0 := (log_pos (by linarith : 1 < x)).ne'
  convert (((hasDerivAt_log hx0.ne').mul (liPV_hasDeriv x hx)).div (hasDerivAt_id x) hx0.ne') using 1
  · rfl
  · dsimp only [id_eq, Pi.mul_apply]
    field_simp
    <;> ring

/-- Three lower li terms on the real endpoint range, journal p. 1237.
Keep the positive third term in the existing integration by parts proof. -/
theorem li_lower_three_terms (x : ℝ) (hx : exp 11 ≤ x) :
    (1 + 1 / log x + 2 / log x ^ 2) * x / log x ≤ liPV x := by
  have hx2 : 2 ≤ x := by linarith [add_one_le_exp (11 : ℝ)]
  have hL : 0 < log x := log_pos (by linarith : 1 < x)
  rw [liPV_eq_add hx2, ← PublishedInputs232.LiProof232.IL_one_eq,
    PublishedInputs232.LiProof232.IL_one_expansion hx2]
  have hli2 := liPV_two_le
  have hA := PublishedInputs232.LiProof232.Aexpr_le
  have hI : (3.4 : ℝ) ≤ PublishedInputs232.LiProof232.I4f x := by
    have hbase := PublishedInputs232.LiProof232.I4f_exp11_ge
    have he2 : 2 ≤ exp (11 : ℝ) := by linarith [add_one_le_exp (11 : ℝ)]
    have hs : PublishedInputs232.LiProof232.I4f x =
        PublishedInputs232.LiProof232.I4f (exp 11) +
          ∫ t in exp 11..x, PublishedInputs232.LiProof232.f4 t := by
      unfold PublishedInputs232.LiProof232.I4f
      rw [integral_add_adjacent_intervals
        (PublishedInputs232.LiProof232.intervalIntegrable_f4 le_rfl he2)
        (PublishedInputs232.LiProof232.intervalIntegrable_f4 he2 hx2)]
    have hp : 0 ≤ ∫ t in exp 11..x, PublishedInputs232.LiProof232.f4 t := by
      apply integral_nonneg hx
      intro t _
      unfold PublishedInputs232.LiProof232.f4
      positivity
    linarith
  have he : (1 + 1 / log x + 2 / log x ^ 2) * x / log x =
      x / log x + x / log x ^ 2 + 2 * (x / log x ^ 3) := by field_simp <;> ring
  rw [he]
  linarith

/-- The elementary lower li estimate gives a nonpositive envelope derivative, p. 1237.
The lower estimate itself is proved in PublishedInputs232. -/
theorem normalizedLi_deriv_nonpos (x : ℝ) (hx : exp 11 ≤ x) :
    deriv normalizedLi x ≤ 0 := by
  have hx2 : 2 < x := by linarith [add_one_le_exp (11 : ℝ)]
  have hx0 : 0 < x := by linarith
  have hL : 11 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hl : 0 < log x := by linarith
  have hli := li_lower_three_terms x hx
  rw [(normalizedLi_hasDeriv x hx2).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hli (by linarith : 0 ≤ log x - 1)
  have hsmall : x ≤ (log x - 1) * ((1 + 1 / log x + 2 / log x ^ 2) * x / log x) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hl 3)).mp
    have hid : ((log x - 1) * ((1 + 1 / log x + 2 / log x ^ 2) * x / log x)) * log x ^ 3 =
        x * (log x ^ 3 + log x - 2) := by field_simp <;> ring
    rw [mul_comm (log x ^ 3) x, mul_comm (log x ^ 3) ((log x - 1) * ((1 + 1 / log x + 2 / log x ^ 2) * x / log x)), hid]
    nlinarith
  nlinarith

/-- The leading normalized li term decreases above exp 11, p. 1237. -/
theorem normalizedLi_antitone : AntitoneOn normalizedLi (Set.Ici (exp 11)) := by
  have hd (x : ℝ) (hx : exp 11 ≤ x) := normalizedLi_hasDeriv x
    (by linarith [add_one_le_exp (11 : ℝ)])
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (by
      have hx' : exp 11 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
      exact hx'.le)).differentiableAt.differentiableWithinAt)
  intro x hx
  exact normalizedLi_deriv_nonpos x (by
    have hx' : exp 11 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    exact hx'.le)

/-- The normalized Schoenfeld upper count envelope, journal p. 1237. -/
def primeEnvelope (x : ℝ) : ℝ := normalizedLi x + (log x / x ^ (1 / 4 : ℝ)) ^ 2 / (8 * π)

/-- Both terms of the Schoenfeld envelope decrease on this range, p. 1237. -/
theorem primeEnvelope_antitone : AntitoneOn primeEnvelope (Set.Ici (exp 11)) := by
  intro x hx y hy hxy
  change exp 11 ≤ x at hx
  change exp 11 ≤ y at hy
  have hli := normalizedLi_antitone hx hy hxy
  have hm := log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1 / 4)
  have h4x : exp ((1 : ℝ) / (1 / 4)) ≤ x := by
    calc exp ((1 : ℝ) / (1 / 4)) ≤ exp 11 := exp_le_exp.mpr (by norm_num)
         _ ≤ x := hx
  have h4y : exp ((1 : ℝ) / (1 / 4)) ≤ y := h4x.trans hxy
  have herr := hm (by simpa only [Set.mem_Ici, one_div] using h4x) (by simpa only [Set.mem_Ici, one_div] using h4y) hxy
  have hx0 : 0 < x := (exp_pos 11).trans_le hx
  have hy0 : 0 < y := (exp_pos 11).trans_le hy
  have hx1 : 1 ≤ x := by linarith [add_one_le_exp (11 : ℝ)]
  have hy1 : 1 ≤ y := hx1.trans hxy
  have he : (log y / y ^ (1 / 4 : ℝ)) ^ 2 ≤ (log x / x ^ (1 / 4 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (log_nonneg hy1) (rpow_nonneg hy0.le _)) herr 2
  exact add_le_add hli (div_le_div_of_nonneg_right he (by positivity))

/-- The normalized envelope equals the exact expression printed in Lemma 14, p. 1237. -/
theorem primeEnvelope_eq (x : ℝ) (hx : 0 < x) :
    primeEnvelope x = log x * (liPV x + √x * log x / (8 * π)) / x := by
  have hq : (x ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = √x := by
    rw [← rpow_natCast, ← rpow_mul hx.le]
    convert (sqrt_eq_rpow x).symm using 1 <;> congr 1 <;> norm_num
  have hs : √x ≠ 0 := (sqrt_pos.mpr hx).ne'
  have halg (L I S : ℝ) (hS : S ≠ 0) :
      L * I / S ^ 2 + L ^ 2 / S / (8 * π) = L * (I + S * L / (8 * π)) / S ^ 2 := by
    field_simp
    <;> ring
  unfold primeEnvelope normalizedLi
  rw [div_pow, hq]
  convert halg (log x) (liPV x) (√x) hs using 1 <;> rw [sq_sqrt hx.le]

/-- The uniform prime count used in Lemma 14 follows from Schoenfeld Corollary 1,
journal p. 1237. CONDITIONAL ON that published count estimate and GRH. -/
theorem prime_count_uniform (h1 : PaperInputs148.Lemma1J) (hG : ChenThresholdGRH.GRH)
    (y x : ℝ) (hy : exp 11 ≤ y) (hyx : y ≤ x) :
    PaperInputs148.primeCount x ≤
      (log y * (liPV y + √y * log y / (8 * π)) / y) * x / log x := by
  have hx : exp 11 ≤ x := hy.trans hyx
  have hx2657 : 2657 ≤ x := by linarith [PublishedInputs232.LiProof232.exp_eleven_ge]
  have hx0 : 0 < x := (exp_pos 11).trans_le hx
  have hy0 : 0 < y := (exp_pos 11).trans_le hy
  have hx1 : 1 < x := by linarith [add_one_le_exp (11 : ℝ)]
  have hlog : 0 < log x := log_pos hx1
  have hc := (abs_le.mp (PaperInputs148.lemma1_of_grh h1 hG x hx2657)).2
  have hc' : PaperInputs148.primeCount x ≤ liPV x + √x * log x / (8 * π) := by linarith
  have hm := mul_le_mul_of_nonneg_left hc' (div_nonneg hlog.le hx0.le)
  have he : log x / x * (liPV x + √x * log x / (8 * π)) = primeEnvelope x := by
    rw [primeEnvelope_eq x hx0]
    ring
  rw [he] at hm
  have hf := hm.trans (primeEnvelope_antitone hy hx hyx)
  have hf' := mul_le_mul_of_nonneg_right hf hx0.le
  have hid : (log x / x * PaperInputs148.primeCount x) * x =
      PaperInputs148.primeCount x * log x := by field_simp <;> ring
  rw [hid] at hf'
  rw [← primeEnvelope_eq y hy0]
  exact (le_div_iff₀ hlog).mpr hf'

end
end LeanLab.BS2022GRH.SliceMass236
#print axioms LeanLab.BS2022GRH.SliceMass236.liPV_hasDeriv
#print axioms LeanLab.BS2022GRH.SliceMass236.normalizedLi_hasDeriv
#print axioms LeanLab.BS2022GRH.SliceMass236.normalizedLi_deriv_nonpos
#print axioms LeanLab.BS2022GRH.SliceMass236.normalizedLi_antitone
#print axioms LeanLab.BS2022GRH.SliceMass236.primeEnvelope_antitone

#print axioms LeanLab.BS2022GRH.SliceMass236.li_lower_three_terms

#print axioms LeanLab.BS2022GRH.SliceMass236.primeEnvelope_eq
#print axioms LeanLab.BS2022GRH.SliceMass236.prime_count_uniform
