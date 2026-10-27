/- CODEX task85. AI wrote the Lean code.
A first derivative integral estimate used in the proof of Lu 2010 Lemma 4.
The full second derivative estimate is proved below. Binary Goldbach is open. -/
import LeanLab.ExceptionalSet.Lu2010Lemma4
open Real MeasureTheory
namespace LeanLab.ExceptionalSet.Lu2010FirstDerivative
theorem first_derivative_positive {f fp fpp : ℝ → ℝ} {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (fp x) x)
    (hfp : ∀ x ∈ Set.Icc a b, HasDerivAt fp (fpp x) x)
    (hc : ContinuousOn fpp (Set.Icc a b))
    (hp : ∀ x ∈ Set.Icc a b, d ≤ fp x)
    (hpp : ∀ x ∈ Set.Icc a b, 0 ≤ fpp x) :
    ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a b‖ ≤ 2/d := by
  have hfc : ContinuousOn f (Set.Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfpc : ContinuousOn fp (Set.Icc a b) := fun x hx => (hfp x hx).continuousAt.continuousWithinAt
  have hpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < fp x := hd.trans_le (hp x hx)
  let U : ℝ → ℂ := fun x => Complex.exp ((f x:ℂ)*Complex.I)
  let W : ℝ → ℝ := fun x => fpp x / (fp x)^2
  have hUc : ContinuousOn U (Set.Icc a b) := by dsimp [U]; fun_prop
  have hWc : ContinuousOn W (Set.Icc a b) := by
    dsimp [W]
    exact hc.div (hfpc.pow 2) (fun x hx => pow_ne_zero 2 (hpos x hx).ne')
  have hUWc : ContinuousOn (fun x => U x*(W x:ℂ)) (Set.Icc a b) := by fun_prop
  have hV : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun t => (fp t)⁻¹) (-W x) x := by
    intro x hx
    convert (hfp x hx).inv (hpos x hx).ne' using 1 <;> simp [W,neg_div]
  have hVint : (∫ x in a..b, W x) = (fp a)⁻¹-(fp b)⁻¹ := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hV x (by simpa [Set.uIcc_of_le hab] using hx))
      (hWc.neg.intervalIntegrable_of_Icc hab)
    rw [intervalIntegral.integral_neg] at hh
    linarith
  have hnormU (x : ℝ) : ‖U x‖=1 := Complex.norm_exp_ofReal_mul_I (f x)
  have hder (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt (fun t => U t*((fp t:ℝ):ℂ)⁻¹)
        (Complex.I*U x-U x*(W x:ℂ)) x := by
    have hu : HasDerivAt U ((fp x:ℂ)*Complex.I*U x) x := by
      simpa [U,mul_comm,mul_left_comm,mul_assoc] using
        (((hf x hx).ofReal_comp.mul_const Complex.I).cexp)
    have hv : HasDerivAt (fun t => ((fp t:ℝ):ℂ)⁻¹) (-(W x:ℂ)) x := by
      simpa only [Complex.ofReal_inv,Complex.ofReal_neg] using (hV x hx).ofReal_comp
    convert hu.mul hv using 1
    field_simp [(show (fp x:ℂ) ≠ 0 by exact_mod_cast (hpos x hx).ne')]
    <;> ring
  have hIint : IntervalIntegrable (fun x => Complex.I*U x) volume a b :=
    (continuousOn_const.mul hUc).intervalIntegrable_of_Icc hab
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (by simpa [Set.uIcc_of_le hab] using hx))
    (hIint.sub (hUWc.intervalIntegrable_of_Icc hab))
  rw [intervalIntegral.integral_sub
    hIint
    (hUWc.intervalIntegrable_of_Icc hab),intervalIntegral.integral_const_mul] at hi
  have he : Complex.I*(∫ x in a..b, U x) =
      U b*((fp b:ℝ):ℂ)⁻¹-U a*((fp a:ℝ):ℂ)⁻¹ + (∫ x in a..b, U x*(W x:ℂ)) := by
    linear_combination hi
  have htail : ‖∫ x in a..b, U x*(W x:ℂ)‖ ≤ (fp a)⁻¹-(fp b)⁻¹ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
    rw [← hVint]
    apply intervalIntegral.integral_mono_on hab (hUWc.norm.intervalIntegrable_of_Icc hab)
      (hWc.intervalIntegrable_of_Icc hab)
    intro x hx
    rw [norm_mul,hnormU,one_mul,Complex.norm_real,Real.norm_of_nonneg]
    exact div_nonneg (hpp x hx) (sq_nonneg _)
  have hboundary : ‖U b*((fp b:ℝ):ℂ)⁻¹-U a*((fp a:ℝ):ℂ)⁻¹‖ ≤ (fp b)⁻¹+(fp a)⁻¹ := by
    refine (norm_sub_le _ _).trans ?_
    simp [norm_mul,hnormU,Complex.norm_real,Real.norm_of_nonneg (hpos a ⟨le_rfl,hab⟩).le,
      Real.norm_of_nonneg (hpos b ⟨hab,le_rfl⟩).le]
  have hh := (norm_add_le (U b*((fp b:ℝ):ℂ)⁻¹-U a*((fp a:ℝ):ℂ)⁻¹)
    (∫ x in a..b, U x*(W x:ℂ))).trans (add_le_add hboundary htail)
  rw [← he,norm_mul,Complex.norm_I,one_mul] at hh
  have hinv : (fp a)⁻¹ ≤ d⁻¹ := inv_anti₀ hd (hp a ⟨le_rfl,hab⟩)
  unfold LeanLab.ExceptionalSet.Lu2010Lemma4.osc
  change ‖∫ x in a..b, U x‖ ≤ 2/d
  calc _ ≤ (fp b)⁻¹+(fp a)⁻¹+((fp a)⁻¹-(fp b)⁻¹) := hh
    _ ≤ 2/d := by rw [div_eq_mul_inv]; linarith
/-- The first derivative bound on the negative side, by reflection. -/
theorem first_derivative_negative {f fp fpp : ℝ → ℝ} {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (fp x) x)
    (hfp : ∀ x ∈ Set.Icc a b, HasDerivAt fp (fpp x) x)
    (hc : ContinuousOn fpp (Set.Icc a b))
    (hp : ∀ x ∈ Set.Icc a b, fp x ≤ -d)
    (hpp : ∀ x ∈ Set.Icc a b, 0 ≤ fpp x) :
    ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a b‖ ≤ 2/d := by
  have hmem (x : ℝ) (hx : x ∈ Set.Icc (-b) (-a)) : -x ∈ Set.Icc a b := by
    constructor <;> linarith [hx.1,hx.2]
  have hfs (x : ℝ) (hx : x ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (fun t => f (-t)) (-fp (-x)) x := by
    convert (hf (-x) (hmem x hx)).comp x (hasDerivAt_neg x) using 1 <;> simp [Function.comp_def,Pi.neg_def]
  have hfps (x : ℝ) (hx : x ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (fun t => -fp (-t)) (fpp (-x)) x := by
    convert ((hfp (-x) (hmem x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;> simp [Function.comp_def,Pi.neg_def]
  have hcs : ContinuousOn (fun t => fpp (-t)) (Set.Icc (-b) (-a)) :=
    hc.comp (by fun_prop) hmem
  have hh := first_derivative_positive (show -b ≤ -a by linarith) hd hfs hfps hcs
    (fun x hx => by linarith [hp (-x) (hmem x hx)]) (fun x hx => hpp (-x) (hmem x hx))
  unfold LeanLab.ExceptionalSet.Lu2010Lemma4.osc at *
  have heq := intervalIntegral.integral_comp_neg (fun x => Complex.exp ((f x:ℂ)*Complex.I)) (a := -b) (b := -a)
  simp only [neg_neg] at heq
  rw [heq] at hh
  exact hh

/-- Reversing the real phase conjugates the integral and preserves its norm. -/
theorem norm_osc_neg (f : ℝ → ℝ) (a b : ℝ) :
    ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc (fun x => -f x) a b‖ =
      ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a b‖ := by
  have he (x : ℝ) : Complex.exp (((-f x:ℝ):ℂ)*Complex.I) =
      (starRingEnd ℂ) (Complex.exp ((f x:ℂ)*Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  unfold LeanLab.ExceptionalSet.Lu2010Lemma4.osc
  simp_rw [he]
  rw [intervalIntegral.intervalIntegral_conj,Complex.norm_conj]

/-- Lu 2010 Lemma 4 for positive curvature, using two first derivative tails. -/
theorem second_derivative_positive {f fp fpp : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b) (hy : 0 < y)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (fp x) x)
    (hfp : ∀ x ∈ Set.Icc a b, HasDerivAt fp (fpp x) x)
    (hc : ContinuousOn fpp (Set.Icc a b))
    (hpp : ∀ x ∈ Set.Icc a b, y ≤ fpp x) :
    ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a b‖ ≤ 8 / Real.sqrt y := by
  let s := Real.sqrt y
  have hs : 0 < s := Real.sqrt_pos.mpr hy
  have hs2 : s^2=y := Real.sq_sqrt hy.le
  have hnonneg (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 ≤ fpp x := hy.le.trans (hpp x hx)
  have hfpc : ContinuousOn fp (Set.Icc a b) := fun x hx => (hfp x hx).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Set.Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn fp (Set.Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hfpc
    · intro x hx
      exact (hfp x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hnonneg x (interior_subset hx)
  have ha : a ∈ Set.Icc a b := ⟨le_rfl,hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab,le_rfl⟩
  by_cases hleft : s ≤ fp a
  · have hh := first_derivative_positive hab hs hf hfp hc
      (fun x hx => hleft.trans (hmono ha hx hx.1)) hnonneg
    exact hh.trans (by apply div_le_div_of_nonneg_right (by norm_num) hs.le)
  by_cases hright : fp b ≤ -s
  · have hh := first_derivative_negative hab hs hf hfp hc
      (fun x hx => (hmono hx hb hx.2).trans hright) hnonneg
    exact hh.trans (by apply div_le_div_of_nonneg_right (by norm_num) hs.le)
  have hex_c : ∃ c ∈ Set.Icc a b, fp c ≤ s ∧ -s ≤ fp c ∧ (c=a ∨ fp c=-s) := by
    by_cases hca : -s ≤ fp a
    · exact ⟨a,ha,(not_le.mp hleft).le,hca,Or.inl rfl⟩
    · obtain ⟨c,hc1,hc2⟩ := intermediate_value_Icc hab hfpc
        (show -s ∈ Set.Icc (fp a) (fp b) by constructor <;> linarith)
      exact ⟨c,hc1,by rw [hc2]; linarith,by rw [hc2],Or.inr hc2⟩
  obtain ⟨c,hcAB,hcs,hcneg,hca⟩ := hex_c
  have hsubc : Set.Icc c b ⊆ Set.Icc a b := fun x hx => ⟨hcAB.1.trans hx.1,hx.2⟩
  have hex_d : ∃ d ∈ Set.Icc c b, fp d ≤ s ∧ -s ≤ fp d ∧ (d=b ∨ fp d=s) := by
    by_cases hdb : fp b ≤ s
    · exact ⟨b,⟨hcAB.2,le_rfl⟩,hdb,(not_le.mp hright).le,Or.inl rfl⟩
    · obtain ⟨d,hd1,hd2⟩ := intermediate_value_Icc hcAB.2 (hfpc.mono hsubc)
        (show s ∈ Set.Icc (fp c) (fp b) by constructor <;> linarith)
      exact ⟨d,hd1,by rw [hd2],by rw [hd2]; linarith,Or.inr hd2⟩
  obtain ⟨d,hdCB,hds,hdneg,hdb⟩ := hex_d
  have hdAB := hsubc hdCB
  have hsub1 : Set.Icc a c ⊆ Set.Icc a b := fun x hx => ⟨hx.1,hx.2.trans hcAB.2⟩
  have hsub2 : Set.Icc c d ⊆ Set.Icc a b := fun x hx => ⟨hcAB.1.trans hx.1,hx.2.trans hdAB.2⟩
  have hsub3 : Set.Icc d b ⊆ Set.Icc a b := fun x hx => ⟨hdAB.1.trans hx.1,hx.2⟩
  have hfirst : ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a c‖ ≤ 2/s := by
    rcases hca with hca | hca
    · subst c
      simp only [LeanLab.ExceptionalSet.Lu2010Lemma4.osc,intervalIntegral.integral_same,norm_zero]
      positivity
    · exact first_derivative_negative hcAB.1 hs
        (fun x hx => hf x (hsub1 hx)) (fun x hx => hfp x (hsub1 hx)) (hc.mono hsub1)
        (fun x hx => (hmono (hsub1 hx) hcAB hx.2).trans_eq hca) (fun x hx => hnonneg x (hsub1 hx))
  have hthird : ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f d b‖ ≤ 2/s := by
    rcases hdb with hdb | hdb
    · subst d
      simp only [LeanLab.ExceptionalSet.Lu2010Lemma4.osc,intervalIntegral.integral_same,norm_zero]
      positivity
    · exact first_derivative_positive hdAB.2 hs
        (fun x hx => hf x (hsub3 hx)) (fun x hx => hfp x (hsub3 hx)) (hc.mono hsub3)
        (fun x hx => hdb ▸ hmono hdAB (hsub3 hx) hx.1) (fun x hx => hnonneg x (hsub3 hx))
  have hgap : y*(d-c) ≤ fp d-fp c := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) hdCB.1 intervalIntegrable_const
      ((hc.mono hsub2).intervalIntegrable_of_Icc hdCB.1) (fun x hx => hpp x (hsub2 hx))
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hfp x (hsub2 (by simpa [Set.uIcc_of_le hdCB.1] using hx)))
      ((hc.mono hsub2).intervalIntegrable_of_Icc hdCB.1)
    rw [he,intervalIntegral.integral_const,smul_eq_mul] at hi
    nlinarith
  have hlen : d-c ≤ 2/s := by
    apply (le_div_iff₀ hs).2
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hdCB.1)]
  have hmiddle : ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f c d‖ ≤ 2/s := by
    exact (LeanLab.ExceptionalSet.Lu2010Lemma4.norm_osc_le f c d).trans
      (by rw [abs_of_nonneg (sub_nonneg.mpr hdCB.1)]; exact hlen)
  have hint : IntervalIntegrable (fun x => Complex.exp ((f x:ℂ)*Complex.I)) volume a b :=
    (by fun_prop : ContinuousOn (fun x => Complex.exp ((f x:ℂ)*Complex.I)) (Set.Icc a b)).intervalIntegrable_of_Icc hab
  have hsplit : LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a b =
      LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a c + LeanLab.ExceptionalSet.Lu2010Lemma4.osc f c d +
        LeanLab.ExceptionalSet.Lu2010Lemma4.osc f d b := by
    unfold LeanLab.ExceptionalSet.Lu2010Lemma4.osc
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set (by simpa [Set.uIcc_of_le hab,Set.uIcc_of_le hcAB.1] using hsub1))
      (hint.mono_set (by simpa [Set.uIcc_of_le hab,Set.uIcc_of_le hdCB.1] using hsub2)),
      intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set (by simp only [Set.uIcc_of_le hab,Set.uIcc_of_le hdAB.1]; exact fun x hx => ⟨hx.1,hx.2.trans hdAB.2⟩))
      (hint.mono_set (by simpa [Set.uIcc_of_le hab,Set.uIcc_of_le hdAB.2] using hsub3))]
  rw [hsplit]
  have hn : ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a c + LeanLab.ExceptionalSet.Lu2010Lemma4.osc f c d + LeanLab.ExceptionalSet.Lu2010Lemma4.osc f d b‖ ≤ ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a c‖ + ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f c d‖ + ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f d b‖ := norm_add₃_le
  have hsdiv : 0 ≤ 2/s := by positivity
  change _ ≤ 8/s
  rw [show 8/s=4*(2/s) by ring]
  linarith

/-- The complete second derivative input of Lu 2010 page 2366 Lemma 4. -/
theorem secondDerivativeEstimate_proved : LeanLab.ExceptionalSet.Lu2010Lemma4.SecondDerivativeEstimate := by
  intro f hfd a b y hab hy hcurv
  have hfdiff : Differentiable ℝ f := hfd.differentiable (by norm_num)
  have hfpdiff : Differentiable ℝ (deriv f) := hfd.differentiable_deriv_two
  have hfpCD : ContDiff ℝ 1 (deriv f) := hfd.deriv'
  have hcont : Continuous (deriv (deriv f)) := hfpCD.continuous_deriv_one
  have hf (x : ℝ) (_hx : x ∈ Set.Icc a b) : HasDerivAt f (deriv f x) x :=
    (hfdiff x).hasDerivAt
  have hfp (x : ℝ) (_hx : x ∈ Set.Icc a b) : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (hfpdiff x).hasDerivAt
  have hbound : ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a b‖ ≤ 8 / Real.sqrt y := by
    rcases hcurv with hcurv | hcurv
    · exact second_derivative_positive hab hy hf hfp hcont.continuousOn hcurv
    · have hfn (x : ℝ) (hx : x ∈ Set.Icc a b) :
          HasDerivAt (fun t => -f t) (-deriv f x) x := by
        convert (hf x hx).neg using 1
      have hfpn (x : ℝ) (hx : x ∈ Set.Icc a b) :
          HasDerivAt (fun t => -deriv f t) (-deriv (deriv f) x) x := by
        convert (hfp x hx).neg using 1
      have hh := second_derivative_positive hab hy hfn hfpn hcont.neg.continuousOn
        (fun x hx => by linarith [hcurv x hx])
      rw [norm_osc_neg] at hh
      exact hh
  calc ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc f a b‖ ≤ 8 / Real.sqrt y := hbound
    _ = 8 * y ^ (-(1/2) : ℝ) := by
      rw [Real.rpow_neg hy.le,Real.sqrt_eq_rpow,div_eq_mul_inv]

end LeanLab.ExceptionalSet.Lu2010FirstDerivative
