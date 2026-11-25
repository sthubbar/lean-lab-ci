import LeanLab.ChenDoubleSieve.Decomp275b

/-!
Reduction of the two fourfold Buchstab terms F13 and F14 of Wu 2004 Section 10,
https://arxiv.org/pdf/0705.1652, equation 10.12 on page 41, whose printed values appear
in the final display on page 42 as 0.023310 and 0.182860, indices 10 and 11 of
`integralTerms` in Decomp275b.

Three steps. First, the Buchstab bound of Lemma 2.10 on page 9, used on page 41: omega is
at most 0.561522 on u at least 3.5; this is a LEAF. Second, PROVED here: every Buchstab
argument inside the two integrals is at least 3.5 by `fourfold13_argument` and
`fourfold14_argument`, so at each of the four levels the integral with omega is at most
the integral with the constant 0.561522. The comparison needs no integrability of the
omega side: a non integrable interval integral is zero in Mathlib, and the constant side
is nonnegative and continuous. Third, the constant case. For F13 it is PROVED: the three
inner integrals are done in closed form, the factor 1 over 1 minus t is bounded by a
cubic, the outer integral is done exactly, and the logarithms of 29/25 and 6/5 are
bounded by Taylor sums; python gave 0.0233097150 for the exact constant value and
0.0233097316 for the proved majorant, against 0.023310. For F14 the third level is a
dilogarithm, and the constant case is left as a LEAF; python with mpmath quadrature gives
0.1828591240 against 0.182860.
So value10_of_split depends only on the LEAF omega_le_const, and value11_of_split on
omega_le_const and const11_le.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Task275.Feed1122F1314
open Wu04Functional (IsLinearSieve IsBuchstab)
open Set MeasureTheory intervalIntegral Real

/-- LEAF: Wu 2004 page 9 Lemma 2.10, as used on page 41 for equation 10.12: the Buchstab
function is at most 0.561522 for u at least 3.5. Class HARD. -/
theorem omega_le_const (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ u : ℝ, 3.5 ≤ u → ω u ≤ 0.561522 := by
  sorry

/-- An interval integral is at most that of a nonnegative integrable majorant,
with no integrability assumed on the smaller function. -/
theorem integral_le_of_majorant {g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hh : IntervalIntegrable h volume a b) (h0 : ∀ x ∈ Icc a b, 0 ≤ h x)
    (hle : ∀ x ∈ Icc a b, g x ≤ h x) :
    (∫ x in a..b, g x) ≤ ∫ x in a..b, h x := by
  by_cases hg : IntervalIntegrable g volume a b
  · exact intervalIntegral.integral_mono_on hab hg hh hle
  · rw [intervalIntegral.integral_undef hg]
    exact intervalIntegral.integral_nonneg hab h0

/-- The upper primitive of a function continuous on a closed interval is continuous there. -/
theorem continuousOn_upper_primitive {φ : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hφ : ContinuousOn φ (Icc p q)) :
    ContinuousOn (fun t => ∫ x in t..q, φ x) (Icc p q) := by
  have hi : IntegrableOn φ (uIcc p q) volume := by
    rw [uIcc_of_le hpq]; exact hφ.integrableOn_Icc
  have := intervalIntegral.continuousOn_primitive_interval_left hi
  rwa [uIcc_of_le hpq] at this

/-- Level four of the constant case. -/
def K4 (c : ℝ) (last lower : ℝ → ℝ) (t3 : ℝ) : ℝ := ∫ t4 in lower t3..last t3, c / t4
/-- Level three of the constant case. -/
def K3 (c : ℝ) (last lower : ℝ → ℝ) (t3 : ℝ) : ℝ := K4 c last lower t3 / t3
/-- Level two of the constant case. -/
def K2 (c : ℝ) (last lower : ℝ → ℝ) (t2 : ℝ) : ℝ :=
  (∫ t3 in t2..kappa2, K3 c last lower t3) / t2 ^ 2
/-- Level one of the constant case. -/
def K1 (c : ℝ) (last lower weight : ℝ → ℝ) (t1 : ℝ) : ℝ :=
  (∫ t2 in t1..kappa2, K2 c last lower t2) / weight t1

theorem fourfold_const_eq (c : ℝ) (last lower weight : ℝ → ℝ) (a b : ℝ) :
    fourfold (fun _ => c) last a b lower weight = ∫ t1 in a..b, K1 c last lower weight t1 :=
  rfl

/-- The monotonicity step: with every Buchstab argument bounded by c, the fourfold integral
with omega is at most the fourfold integral with the constant c. -/
theorem fourfold_mono (ω last lower weight : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b)
    (ha : kappa1 ≤ a) (hb : b ≤ kappa2) (hc : 0 ≤ c)
    (hlow : ∀ t ∈ Icc kappa1 kappa2, 0 < lower t ∧ lower t ≤ last t)
    (hlowc : ContinuousOn lower (Icc kappa1 kappa2))
    (hlastc : ContinuousOn last (Icc kappa1 kappa2))
    (hw : ∀ t ∈ Icc a b, 0 < weight t) (hwc : ContinuousOn weight (Icc a b))
    (hω : ∀ t1 t2 t3 t4 : ℝ, t1 ∈ Icc a b → t2 ∈ Icc t1 kappa2 → t3 ∈ Icc t2 kappa2 →
      t4 ∈ Icc (lower t3) (last t3) → ω ((1 - t1 - t2 - t3 - t4) / t2) ≤ c) :
    fourfold ω last a b lower weight ≤ fourfold (fun _ => c) last a b lower weight := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hkk : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
  -- level four
  have hK4eq : ∀ t ∈ Icc kappa1 kappa2, K4 c last lower t = c * log (last t / lower t) := by
    intro t ht
    obtain ⟨h0, h1⟩ := hlow t ht
    have e : (∫ t4 in lower t..last t, c / t4) = c * ∫ t4 in lower t..last t, t4⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]; rfl
    rw [K4, e, integral_inv_of_pos h0 (lt_of_lt_of_le h0 h1)]
  have hK4c : ContinuousOn (K4 c last lower) (Icc kappa1 kappa2) := by
    refine ContinuousOn.congr ?_ hK4eq
    refine continuousOn_const.mul (ContinuousOn.log (hlastc.div hlowc ?_) ?_)
    · intro t ht; exact (hlow t ht).1.ne'
    · intro t ht
      have := hlow t ht
      exact (div_pos (lt_of_lt_of_le this.1 this.2) this.1).ne'
  have hK4n : ∀ t ∈ Icc kappa1 kappa2, 0 ≤ K4 c last lower t := by
    intro t ht
    obtain ⟨h0, h1⟩ := hlow t ht
    exact intervalIntegral.integral_nonneg h1 (fun x hx => div_nonneg hc (h0.trans_le hx.1).le)
  -- level three
  have hK3c : ContinuousOn (K3 c last lower) (Icc kappa1 kappa2) :=
    hK4c.div continuousOn_id (fun t ht => (hk.trans_le ht.1).ne')
  have hK3n : ∀ t ∈ Icc kappa1 kappa2, 0 ≤ K3 c last lower t := fun t ht =>
    div_nonneg (hK4n t ht) (hk.trans_le ht.1).le
  -- level two
  have hK2c : ContinuousOn (K2 c last lower) (Icc kappa1 kappa2) :=
    (continuousOn_upper_primitive hkk hK3c).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hk.trans_le ht.1).ne')
  have hK2n : ∀ t ∈ Icc kappa1 kappa2, 0 ≤ K2 c last lower t := by
    intro t ht
    refine div_nonneg (intervalIntegral.integral_nonneg ht.2 ?_) (sq_nonneg _)
    intro x hx; exact hK3n x ⟨ht.1.trans hx.1, hx.2⟩
  -- level one
  have hsub : Icc a b ⊆ Icc kappa1 kappa2 := Icc_subset_Icc ha hb
  have hK1c : ContinuousOn (K1 c last lower weight) (Icc a b) :=
    ((continuousOn_upper_primitive hkk hK2c).mono hsub).div hwc (fun t ht => (hw t ht).ne')
  have hK1n : ∀ t ∈ Icc a b, 0 ≤ K1 c last lower weight t := by
    intro t ht
    refine div_nonneg (intervalIntegral.integral_nonneg (hsub ht).2 ?_) (hw t ht).le
    intro x hx; exact hK2n x ⟨(hsub ht).1.trans hx.1, hx.2⟩
  rw [fourfold_const_eq]
  unfold fourfold
  refine integral_le_of_majorant hab
    (hK1c.intervalIntegrable_of_Icc hab) hK1n ?_
  intro t1 ht1
  have ht1' := hsub ht1
  rw [K1]
  refine div_le_div_of_nonneg_right ?_ (hw t1 ht1).le
  refine integral_le_of_majorant ht1'.2
    ((hK2c.mono (Icc_subset_Icc ht1'.1 le_rfl)).intervalIntegrable_of_Icc ht1'.2)
    (fun x hx => hK2n x ⟨ht1'.1.trans hx.1, hx.2⟩) ?_
  intro t2 ht2
  have ht2' : t2 ∈ Icc kappa1 kappa2 := ⟨ht1'.1.trans ht2.1, ht2.2⟩
  rw [K2]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  refine integral_le_of_majorant ht2.2
    ((hK3c.mono (Icc_subset_Icc ht2'.1 le_rfl)).intervalIntegrable_of_Icc ht2.2)
    (fun x hx => hK3n x ⟨ht2'.1.trans hx.1, hx.2⟩) ?_
  intro t3 ht3
  have ht3' : t3 ∈ Icc kappa1 kappa2 := ⟨ht2'.1.trans ht3.1, ht3.2⟩
  rw [K3]
  refine div_le_div_of_nonneg_right ?_ (hk.trans_le ht3'.1).le
  rw [K4]
  obtain ⟨hl0, hl1⟩ := hlow t3 ht3'
  refine integral_le_of_majorant hl1 ?_
    (fun x hx => div_nonneg hc (hl0.trans_le hx.1).le) ?_
  · exact (continuousOn_const.div continuousOn_id
      (fun x hx => (hl0.trans_le hx.1).ne')).intervalIntegrable_of_Icc hl1
  intro t4 ht4
  exact div_le_div_of_nonneg_right (hω t1 t2 t3 t4 ht1 ht2 ht3 ht4)
    (hl0.trans_le ht4.1).le

/-- LEAF: Wu 2004 page 41 equation 10.12 and page 42 final display, value of F14 with
omega replaced by the constant 0.561522; python with mpmath quadrature gives
0.1828591240. Class HARD. -/
theorem const11_le :
    36 / 5 * fourfold (fun _ => (0.561522 : ℝ)) (fun t => 1 / 3 - t) (1 / 12) (1 / 10)
        (fun _ => (29 / 250 : ℝ)) (fun t => t * (1 - t)) +
      8 * fourfold (fun _ => (0.561522 : ℝ)) (fun t => 1 / 3 - t) (1 / 10) (29 / 250)
        (fun _ => (29 / 250 : ℝ)) id ≤ (0.182860 : ℝ) := by
  sorry

theorem k1v : kappa1 = 1 / 12 := by norm_num [kappa1]
theorem k2v : kappa2 = 29 / 250 := by norm_num [kappa2]

theorem k2pos : (0 : ℝ) < kappa2 := by norm_num [kappa2]

/-- Closed form of level four for F13. -/
theorem K4_13 (c t : ℝ) (ht : 0 < t) :
    K4 c (fun _ => kappa2) id t = c * log (kappa2 / t) := by
  have e : (∫ t4 in t..kappa2, c / t4) = c * ∫ t4 in t..kappa2, t4⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]; rfl
  simp only [K4, id]
  rw [e, integral_inv_of_pos ht k2pos]

/-- Closed form of the level three integral for F13. -/
theorem intK3_13 (c t : ℝ) (ht : 0 < t) (htk : t ≤ kappa2) :
    (∫ x in t..kappa2, K3 c (fun _ => kappa2) id x) = c / 2 * (log (kappa2 / t)) ^ 2 := by
  have hcongr : EqOn (fun x => K3 c (fun _ => kappa2) id x)
      (fun x => c * (log kappa2 - log x) / x) (uIcc t kappa2) := by
    intro x hx
    rw [uIcc_of_le htk] at hx
    have hx0 : 0 < x := ht.trans_le hx.1
    simp only [K3, K4_13 c x hx0, log_div k2pos.ne' hx0.ne']
  rw [intervalIntegral.integral_congr hcongr]
  have hderiv : ∀ x ∈ uIcc t kappa2, HasDerivAt (fun x => -(c / 2) * (log kappa2 - log x) ^ 2)
      (c * (log kappa2 - log x) / x) x := by
    intro x hx
    rw [uIcc_of_le htk] at hx
    have hx0 : 0 < x := ht.trans_le hx.1
    have h1 := (((hasDerivAt_log hx0.ne').const_sub (log kappa2)).pow 2).const_mul (-(c / 2))
    convert h1 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun x => c * (log kappa2 - log x) / x) volume t kappa2 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le htk]
    have : ∀ x ∈ Icc t kappa2, x ≠ 0 := fun x hx => (ht.trans_le hx.1).ne'
    exact (continuousOn_const.mul (continuousOn_const.sub
      (continuousOn_log.mono (fun x hx => this x hx)))).div continuousOn_id this
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, log_div k2pos.ne' ht.ne']
  ring

/-- Closed form of level two for F13. -/
theorem K2_13 (c t : ℝ) (ht : 0 < t) (htk : t ≤ kappa2) :
    K2 c (fun _ => kappa2) id t = c / 2 * (log (kappa2 / t)) ^ 2 / t ^ 2 := by
  rw [K2, intK3_13 c t ht htk]

/-- Closed form of the level two integral for F13. -/
theorem intK2_13 (c t : ℝ) (ht : 0 < t) (htk : t ≤ kappa2) :
    (∫ x in t..kappa2, K2 c (fun _ => kappa2) id x) =
      c / 2 * (((log (kappa2 / t)) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2) := by
  have hcongr : EqOn (fun x => K2 c (fun _ => kappa2) id x)
      (fun x => c / 2 * (log kappa2 - log x) ^ 2 / x ^ 2) (uIcc t kappa2) := by
    intro x hx
    rw [uIcc_of_le htk] at hx
    have hx0 : 0 < x := ht.trans_le hx.1
    simp only [K2_13 c x hx0 hx.2, log_div k2pos.ne' hx0.ne']
  rw [intervalIntegral.integral_congr hcongr]
  have hderiv : ∀ x ∈ uIcc t kappa2, HasDerivAt
      (fun x => -(c / 2) * (((log kappa2 - log x) ^ 2 - 2 * (log kappa2 - log x) + 2) / x))
      (c / 2 * (log kappa2 - log x) ^ 2 / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le htk] at hx
    have hx0 : 0 < x := ht.trans_le hx.1
    have hY := (hasDerivAt_log hx0.ne').const_sub (log kappa2)
    have h1 := (((hY.pow 2).sub (hY.const_mul 2)).add_const 2).div (hasDerivAt_id x) hx0.ne'
    have h2 := h1.const_mul (-(c / 2))
    convert h2 using 1
    · funext y
      simp only [Pi.div_apply, Pi.sub_apply, Pi.pow_apply, id]
    · simp only [Pi.sub_apply, Pi.pow_apply, id]
      field_simp
      ring
  have hint : IntervalIntegrable (fun x => c / 2 * (log kappa2 - log x) ^ 2 / x ^ 2)
      volume t kappa2 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le htk]
    have : ∀ x ∈ Icc t kappa2, x ≠ 0 := fun x hx => (ht.trans_le hx.1).ne'
    exact (continuousOn_const.mul ((continuousOn_const.sub
      (continuousOn_log.mono (fun x hx => this x hx))).pow 2)).div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (this x hx))
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, log_div k2pos.ne' ht.ne']
  simp only [sub_self]
  ring

/-- The constant F13 fourfold integral as a single integral of elementary functions. -/
theorem fourfold13_const_eq (c a b : ℝ) (weight : ℝ → ℝ) (hab : a ≤ b) (ha : 0 < a)
    (hb : b ≤ kappa2) :
    fourfold (fun _ => c) (fun _ => kappa2) a b id weight =
      ∫ t in a..b, c / 2 * (((log (kappa2 / t)) ^ 2 - 2 * log (kappa2 / t) + 2) / t -
        2 / kappa2) / weight t := by
  rw [fourfold_const_eq]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  simp only [K1]
  rw [intK2_13 c t (ha.trans_le ht.1) (ht.2.trans hb)]

/-- The level one integrand of the constant F13 case. -/
def G13 (c t : ℝ) : ℝ :=
  c / 2 * (((log (kappa2 / t)) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2)

theorem G13_nonneg (c t : ℝ) (hc : 0 ≤ c) (ht : 0 < t) (htk : t ≤ kappa2) : 0 ≤ G13 c t := by
  have h := intK2_13 c t ht htk
  rw [G13, ← h]
  refine intervalIntegral.integral_nonneg htk (fun x hx => ?_)
  rw [K2_13 c x (ht.trans_le hx.1) hx.2]
  positivity

/-- Antiderivative for the B piece of F13. -/
def PhiB (c t : ℝ) : ℝ :=
  c / 2 * (-((log kappa2 - log t) * (log kappa2 - log t) - 4 * (log kappa2 - log t) + 6) / t -
    2 / kappa2 * log t)

theorem PhiB_deriv (c t : ℝ) (ht : 0 < t) : HasDerivAt (PhiB c) (G13 c t / t) t := by
  have hL := hasDerivAt_log ht.ne'
  have hX := hL.const_sub (log kappa2)
  have h1 := ((((hX.fun_mul hX).fun_sub (hX.const_mul 4)).add_const 6).fun_neg.fun_div
    (hasDerivAt_id t) ht.ne').fun_sub (hL.const_mul (2 / kappa2))
  have h2 := h1.const_mul (c / 2)
  unfold PhiB
  convert h2 using 1
  · rfl
  unfold G13
  rw [log_div k2pos.ne' ht.ne']
  simp only [id]
  field_simp
  ring

/-- Antiderivative for the majorant of the A piece of F13. -/
def PhiA (c t : ℝ) : ℝ :=
  c / 2 * (-((log kappa2 - log t) * (log kappa2 - log t) - 4 * (log kappa2 - log t) + 6) / t -
    ((log kappa2 - log t) * (log kappa2 - log t) * (log kappa2 - log t) / 3 -
      (log kappa2 - log t) * (log kappa2 - log t) + 2 * (log kappa2 - log t)) +
    ((log kappa2 - log t) * (log kappa2 - log t) + 2) * t +
    ((log kappa2 - log t) * (log kappa2 - log t) / 2 - (log kappa2 - log t) / 2 + 3 / 4) *
      (t * t) +
    10 / 9 * ((log kappa2 - log t) * (log kappa2 - log t) / 3 - 4 * (log kappa2 - log t) / 9 +
      14 / 27) * (t * t * t) -
    2 / kappa2 * (log t + t + t * t / 2 + t * t * t / 3 + 10 / 9 * (t * t * t * t) / 4))

theorem PhiA_deriv (c t : ℝ) (ht : 0 < t) :
    HasDerivAt (PhiA c) (G13 c t * (1 / t + 1 + t + t * t + 10 / 9 * (t * t * t))) t := by
  have hL := hasDerivAt_log ht.ne'
  have hX := hL.const_sub (log kappa2)
  have hI := hasDerivAt_id t
  have hXX := hX.fun_mul hX
  have hXXX := hXX.fun_mul hX
  have hTT := hI.fun_mul hI
  have hTTT := hTT.fun_mul hI
  have hTTTT := hTTT.fun_mul hI
  have t1 := (((hXX.fun_sub (hX.const_mul 4)).add_const 6).fun_neg.fun_div hI ht.ne')
  have t2 := ((hXXX.div_const 3).fun_sub hXX).fun_add (hX.const_mul 2)
  have t3 := (hXX.add_const 2).fun_mul hI
  have t4 := (((hXX.div_const 2).fun_sub (hX.div_const 2)).add_const (3 / 4)).fun_mul hTT
  have t5 := ((((hXX.div_const 3).fun_sub ((hX.const_mul 4).div_const 9)).add_const
    (14 / 27)).const_mul (10 / 9)).fun_mul hTTT
  have t6 := ((((hL.fun_add hI).fun_add (hTT.div_const 2)).fun_add (hTTT.div_const 3)).fun_add
    ((hTTTT.const_mul (10 / 9)).div_const 4)).const_mul (2 / kappa2)
  have h2 := (((((t1.fun_sub t2).fun_add t3).fun_add t4).fun_add t5).fun_sub t6).const_mul (c / 2)
  unfold PhiA
  convert h2 using 1
  · rfl
  unfold G13
  rw [log_div k2pos.ne' ht.ne']
  simp only [id]
  field_simp
  ring

theorem G13_cont (c p q : ℝ) (hp : 0 < p) : ContinuousOn (G13 c) (Icc p q) := by
  have hne : ∀ x ∈ Icc p q, x ≠ 0 := fun x hx => (hp.trans_le hx.1).ne'
  have hl : ContinuousOn (fun t => log (kappa2 / t)) (Icc p q) :=
    (continuousOn_const.div continuousOn_id hne).log
      (fun x hx => (div_pos k2pos (hp.trans_le hx.1)).ne')
  unfold G13
  exact continuousOn_const.mul ((((hl.pow 2).sub (continuousOn_const.mul hl)).add
    continuousOn_const).div continuousOn_id hne |>.sub continuousOn_const)

theorem pieceB (c : ℝ) :
    (∫ t in (1 / 10 : ℝ)..kappa2, G13 c t / t) = PhiB c kappa2 - PhiB c (1 / 10) := by
  have h10 : (1 / 10 : ℝ) ≤ kappa2 := by norm_num [kappa2]
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le h10] at hx
    exact PhiB_deriv c x (lt_of_lt_of_le (by norm_num) hx.1)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h10]
    exact (G13_cont c _ _ (by norm_num)).div continuousOn_id
      (fun x hx => (lt_of_lt_of_le (by norm_num) hx.1 : (0 : ℝ) < x).ne')

theorem pieceA (c : ℝ) (hc : 0 ≤ c) :
    (∫ t in kappa1..(1 / 10 : ℝ), G13 c t / (t * (1 - t))) ≤
      PhiA c (1 / 10) - PhiA c kappa1 := by
  have h10 : kappa1 ≤ (1 / 10 : ℝ) := by norm_num [kappa1]
  have hpos : ∀ x ∈ Icc kappa1 (1 / 10 : ℝ), 0 < x := fun x hx =>
    lt_of_lt_of_le (by norm_num [kappa1]) hx.1
  have hcont : ContinuousOn (fun t => G13 c t * (1 / t + 1 + t + t * t + 10 / 9 * (t * t * t)))
      (Icc kappa1 (1 / 10 : ℝ)) := by
    refine (G13_cont c _ _ (by norm_num [kappa1])).mul ?_
    refine ((((continuousOn_const.div continuousOn_id (fun x hx => (hpos x hx).ne')).add
      continuousOn_const).add continuousOn_id).add (continuousOn_id.mul continuousOn_id)).add
      (continuousOn_const.mul ((continuousOn_id.mul continuousOn_id).mul continuousOn_id))
  have hint : IntervalIntegrable _ volume _ _ := hcont.intervalIntegrable_of_Icc h10
  rw [← integral_eq_sub_of_hasDerivAt (fun x hx => PhiA_deriv c x
    (hpos x (by rwa [uIcc_of_le h10] at hx))) hint]
  have hG : ∀ x ∈ Icc kappa1 (1 / 10 : ℝ), 0 ≤ G13 c x := fun x hx =>
    G13_nonneg c x hc (hpos x hx) (hx.2.trans (by norm_num [kappa2]))
  refine integral_le_of_majorant h10 hint ?_ ?_
  · intro x hx
    have := hpos x hx
    exact mul_nonneg (hG x hx) (by positivity)
  · intro x hx
    have hx0 := hpos x hx
    have hx1 : x ≤ 1 / 10 := hx.2
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (hG x hx)
    rw [div_le_iff₀ (by nlinarith)]
    have e : (1 / x + 1 + x + x * x + 10 / 9 * (x * x * x)) * (x * (1 - x)) =
        1 + x ^ 4 * (1 / 9 - 10 / 9 * x) := by field_simp; ring
    rw [e]
    have : 0 ≤ x ^ 4 * (1 / 9 - 10 / 9 * x) := mul_nonneg (by positivity) (by linarith)
    linarith

/-- The final numerical comparison for F13 after exact integration. -/
theorem final13 :
    36 / 5 * (PhiA 0.561522 (1 / 10) - PhiA 0.561522 kappa1) +
      8 * (PhiB 0.561522 kappa2 - PhiB 0.561522 (1 / 10)) ≤ (0.023310 : ℝ) := by
  have ha : log (29 / 250 : ℝ) = log (1 / 10) + log (29 / 25) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have hb : log (1 / 12 : ℝ) = log (1 / 10) - log (6 / 5) := by
    rw [← log_div (by norm_num) (by norm_num)]; norm_num
  have hA := Real.abs_log_sub_add_sum_range_le (show |(-4 / 25 : ℝ)| < 1 by norm_num) 12
  have hB := Real.abs_log_sub_add_sum_range_le (show |(-1 / 5 : ℝ)| < 1 by norm_num) 14
  norm_num [Finset.sum_range_succ] at hA hB
  rw [abs_le] at hA hB
  unfold PhiA PhiB
  simp only [k1v, k2v]
  rw [ha, hb]
  generalize log (1 / 10 : ℝ) = l
  generalize log (29 / 25 : ℝ) = a at hA hB ⊢
  generalize log (6 / 5 : ℝ) = b at hA hB ⊢
  ring_nf
  ring_nf at hA hB
  obtain ⟨ha1, ha2⟩ := hA
  obtain ⟨hb1, hb2⟩ := hB
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hP1 : 0 ≤ 6130639525942384076 / 41306018829345703125 + 67108864 / 1251697540283203125 - a := by
    linarith
  have hP2 : 0 ≤ 80201899665047 / 439892578125000 + 1 / 24414062500 - b := by linarith
  nlinarith [mul_nonneg ha0 hP1, mul_nonneg hb0 hP1, mul_nonneg ha0 hP2, mul_nonneg hb0 hP2,
    mul_nonneg (mul_nonneg ha0 hb0) hP1, mul_nonneg (mul_nonneg hb0 hb0) hP1,
    mul_nonneg (mul_nonneg ha0 ha0) hP2, mul_nonneg (mul_nonneg hb0 hb0) hP2,
    mul_nonneg (mul_nonneg ha0 hb0) hP2, mul_nonneg (mul_nonneg ha0 ha0) hP1]

/-- PROVED from final13: the one dimensional form of the constant F13 case. -/
theorem oneD10_le :
    36 / 5 * (∫ t in kappa1..(1 / 10 : ℝ), G13 0.561522 t / (t * (1 - t))) +
      8 * (∫ t in (1 / 10 : ℝ)..kappa2, G13 0.561522 t / t) ≤ (0.023310 : ℝ) := by
  have hA := pieceA 0.561522 (by norm_num)
  have hB := pieceB 0.561522
  have hF := final13
  rw [hB]
  linarith

/-- PROVED from oneD10_le: the constant case of F13. -/
theorem const10_le :
    36 / 5 * fourfold (fun _ => (0.561522 : ℝ)) (fun _ => kappa2) kappa1 (1 / 10)
        id (fun t => t * (1 - t)) +
      8 * fourfold (fun _ => (0.561522 : ℝ)) (fun _ => kappa2) (1 / 10) kappa2
        id id ≤ (0.023310 : ℝ) := by
  rw [fourfold13_const_eq _ _ _ _ (by norm_num [kappa1]) (by norm_num [kappa1])
      (by norm_num [kappa2]),
    fourfold13_const_eq _ _ _ _ (by norm_num [kappa2]) (by norm_num) le_rfl]
  exact oneD10_le

/-- The F13 pieces: omega side at most the constant side. -/
theorem f13_mono (ω : ℝ → ℝ) (hω : IsBuchstab ω) (a b : ℝ) (weight : ℝ → ℝ)
    (hab : a ≤ b) (ha : kappa1 ≤ a) (hb : b ≤ kappa2)
    (hw : ∀ t ∈ Icc a b, 0 < weight t) (hwc : ContinuousOn weight (Icc a b)) :
    fourfold ω (fun _ => kappa2) a b id weight ≤
      fourfold (fun _ => (0.561522 : ℝ)) (fun _ => kappa2) a b id weight := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  refine fourfold_mono ω _ _ weight a b _ hab ha hb (by norm_num) ?_ continuousOn_id
    continuousOn_const hw hwc ?_
  · intro t ht; exact ⟨hk.trans_le ht.1, ht.2⟩
  · intro t1 t2 t3 t4 ht1 ht2 ht3 ht4
    apply omega_le_const ω hω
    exact fourfold13_argument t1 t2 t3 t4 (hk.trans_le (ha.trans (ht1.1.trans ht2.1)))
      (ht1.2.trans hb) ht2.2 ht3.2 ht4.2

/-- The F14 pieces: omega side at most the constant side. -/
theorem f14_mono (ω : ℝ → ℝ) (hω : IsBuchstab ω) (a b : ℝ) (weight : ℝ → ℝ)
    (hab : a ≤ b) (ha : kappa1 ≤ a) (hb : b ≤ kappa2)
    (hw : ∀ t ∈ Icc a b, 0 < weight t) (hwc : ContinuousOn weight (Icc a b)) :
    fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) a b (fun _ => kappa2) weight ≤
      fourfold (fun _ => (0.561522 : ℝ)) (fun t => 1 / 2 - 2 * kappa1 - t) a b
        (fun _ => kappa2) weight := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  refine fourfold_mono ω _ _ weight a b _ hab ha hb (by norm_num) ?_ continuousOn_const
    (by fun_prop) hw hwc ?_
  · intro t ht
    rw [k1v, k2v] at *
    exact ⟨by norm_num, by linarith [ht.2]⟩
  · intro t1 t2 t3 t4 ht1 ht2 ht3 ht4
    apply omega_le_const ω hω
    exact fourfold14_argument t1 t2 t3 t4 (hk.trans_le (ha.trans (ht1.1.trans ht2.1)))
      (ht1.2.trans hb) ht2.2 ht4.2

theorem weight_pos : ∀ t ∈ Icc kappa1 (1 / 10 : ℝ), 0 < t * (1 - t) := by
  intro t ht
  rw [k1v] at ht
  exact mul_pos (by linarith [ht.1]) (by linarith [ht.2])

/-- PROVED from the LEAF omega_le_const and the PROVED const10_le: exactly the statement of
leaf_value10 in Feed1122_Decomp275b_integral_evaluation, Wu 2004 page 42, F13. -/
theorem value10_of_split (F f ω : ℝ → ℝ) (_h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 10 ≤ (0.023310 : ℝ) := by
  have hkb : kappa1 ≤ 1 / 10 := by norm_num [kappa1]
  have hbk : (1 / 10 : ℝ) ≤ kappa2 := by norm_num [kappa2]
  have h1 := f13_mono ω hω kappa1 (1 / 10) (fun t => t * (1 - t)) hkb le_rfl hbk weight_pos
    (by fun_prop)
  have h2 := f13_mono ω hω (1 / 10) kappa2 id hbk hkb le_rfl
    (fun t ht => lt_of_lt_of_le (by norm_num) ht.1) continuousOn_id
  have h3 := const10_le
  simp only [integralTerms, Matrix.cons_val]
  linarith

/-- PROVED from the LEAFs omega_le_const and const11_le: exactly the statement of
leaf_value11 in Feed1122_Decomp275b_integral_evaluation, Wu 2004 page 42, F14. -/
theorem value11_of_split (F f ω : ℝ → ℝ) (_h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    integralTerms F f ω 11 ≤ (0.182860 : ℝ) := by
  have hkb : kappa1 ≤ 1 / 10 := by norm_num [kappa1]
  have hbk : (1 / 10 : ℝ) ≤ kappa2 := by norm_num [kappa2]
  have h1 := f14_mono ω hω kappa1 (1 / 10) (fun t => t * (1 - t)) hkb le_rfl hbk weight_pos
    (by fun_prop)
  have h2 := f14_mono ω hω (1 / 10) kappa2 id hbk hkb le_rfl
    (fun t ht => lt_of_lt_of_le (by norm_num) ht.1) continuousOn_id
  have h3 := const11_le
  have e : ∀ t : ℝ, 1 / 2 - 2 * (1 / 12) - t = 1 / 3 - t := fun t => by ring
  simp only [integralTerms, Matrix.cons_val]
  simp only [k1v, k2v] at h1 h2 ⊢
  simp only [e] at h1 h2 ⊢
  linarith

end LeanLab.ChenDoubleSieve.Task275.Feed1122F1314
