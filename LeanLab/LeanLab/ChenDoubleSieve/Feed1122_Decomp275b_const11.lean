import LeanLab.ChenDoubleSieve.Feed1122_Decomp275b_F13F14

/-!
Constant case of the fourfold term F14 of Wu 2004, https://arxiv.org/pdf/0705.1652,
equation 10.12 on page 41, printed value 0.182860 in the final display on page 42, index 11
of `integralTerms` in Decomp275b. With omega replaced by the constant 0.561522 from
Lemma 2.10 on page 9, the fourth level integral is c times log of the ratio of 1/3 minus t3
to kappa2; this is PROVED here as `K4_14`. The exact third level is a dilogarithm, so it is
replaced by a majorant, and the full bound `const11` is PROVED.

Python plan, checked with mpmath quadrature at 20 digits: the exact constant value is
0.1828591240 against 0.182860. Writing u for t3 minus 1/12 over 1/4, the log equals
log of 1 over 4 kappa2 plus log of 1 minus u, with u between 0 and 0.131 on the range, and
replacing log of 1 minus u by its degree 4 Taylor sum, an upper bound since u is
nonnegative, gives 0.1828598872, still under 0.182860 with slack 1.1e-7. The cubic
majorant of 1 over 1 minus t1 used in const10_le is too weak here, so a quartic one is used,
and the proved majorant is 0.1828598977.
The three outer levels are then integrals of polynomials times powers of log, done in
closed form as in Feed1122_Decomp275b_F13F14.

AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Const11
open LeanLab.ChenDoubleSieve.Task275.Feed1122F1314
open Set MeasureTheory intervalIntegral Real

/-- PROVED: closed form of level four for F14, Wu 2004 page 41 equation 10.12. -/
theorem K4_14 (c t : ℝ) (ht : t < 1 / 3 - kappa2) :
    K4 c (fun t => 1 / 3 - t) (fun _ => kappa2) t = c * log ((1 / 3 - t) / kappa2) := by
  have e : (∫ t4 in kappa2..(1 / 3 - t), c / t4) = c * ∫ t4 in kappa2..(1 / 3 - t), t4⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]; rfl
  simp only [K4]
  rw [e, integral_inv_of_pos k2pos (by linarith [k2pos])]

/-- PROVED: the degree 4 Taylor sum is an upper bound for log of 1 minus u on 0 to 1/2,
since the derivative of the difference is minus u to the 4 over 1 minus u. -/
theorem log_one_sub_le_taylor4 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    log (1 - u) ≤ -(u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4) := by
  let g : ℝ → ℝ := fun v => log (1 - v) + (v + v ^ 2 / 2 + v ^ 3 / 3 + v ^ 4 / 4)
  have hd : ∀ v ∈ Icc (0 : ℝ) (1 / 2), HasDerivAt g (-(v ^ 4) / (1 - v)) v := by
    intro v hv
    have hv1 : (1 - v) ≠ 0 := by linarith [hv.2]
    have hl := ((hasDerivAt_id v).const_sub 1).log hv1
    have hp := (((hasDerivAt_id v).add ((hasDerivAt_pow 2 v).div_const 2)).add
      ((hasDerivAt_pow 3 v).div_const 3)).add ((hasDerivAt_pow 4 v).div_const 4)
    convert hl.add hp using 1
    · funext y
      simp only [g, Pi.add_apply, id]
    · simp only [id]
      push_cast
      field_simp
      ring
  have hanti : AntitoneOn g (Icc (0 : ℝ) (1 / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2))
    · exact HasDerivAt.continuousOn (fun v hv => hd v hv)
    · intro v hv
      exact (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      have hv' := interior_subset hv
      rw [(hd v hv').deriv]
      have : 0 < 1 - v := by linarith [hv'.2]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [pow_nonneg hv'.1 4]) this.le
  have := hanti ⟨le_rfl, by norm_num⟩ ⟨h0, h1⟩ h0
  simp only [g, sub_zero, log_one] at this
  linarith

/-- PROVED: the level four log of F14 is at most log of 125/58 minus the degree 4 Taylor sum
in u equal to 4 t minus 1/3, for t from 1/12 to 29/250. -/
theorem log14_le_taylor (t : ℝ) (h0 : 1 / 12 ≤ t) (h1 : t ≤ 29 / 250) :
    log ((1 / 3 - t) / kappa2) ≤ log (125 / 58) -
      ((4 * t - 1 / 3) + (4 * t - 1 / 3) ^ 2 / 2 + (4 * t - 1 / 3) ^ 3 / 3 +
        (4 * t - 1 / 3) ^ 4 / 4) := by
  have e : (1 / 3 - t) / kappa2 = 125 / 58 * (1 - (4 * t - 1 / 3)) := by
    rw [k2v]; ring
  have hp : 0 < 1 - (4 * t - 1 / 3) := by linarith
  rw [e, log_mul (by norm_num) hp.ne']
  have := log_one_sub_le_taylor4 (4 * t - 1 / 3) (by linarith) (by linarith)
  linarith

/-- The polynomial majorant of the level four log of F14. -/
def P14 (t : ℝ) : ℝ :=
  log (125 / 58) - ((4 * t - 1 / 3) + (4 * t - 1 / 3) ^ 2 / 2 + (4 * t - 1 / 3) ^ 3 / 3 +
    (4 * t - 1 / 3) ^ 4 / 4)

/-- PROVED: the level three integral of the constant F14 case is at most the integral of
c P14 x over x, for t2 from 1/12 to kappa2 and c nonnegative. -/
theorem intK3_14_le (c t : ℝ) (hc : 0 ≤ c) (h0 : 1 / 12 ≤ t) (h1 : t ≤ kappa2) :
    (∫ x in t..kappa2, K3 c (fun t => 1 / 3 - t) (fun _ => kappa2) x) ≤
      ∫ x in t..kappa2, c * P14 x / x := by
  have hk2 : kappa2 = 29 / 250 := k2v
  have hpos : ∀ x ∈ Icc t kappa2, 0 < x := fun x hx => by linarith [hx.1]
  have hlt : ∀ x ∈ Icc t kappa2, x < 1 / 3 - kappa2 := fun x hx => by
    rw [hk2] at hx ⊢; linarith [hx.2]
  have hcongr : EqOn (fun x => K3 c (fun t => 1 / 3 - t) (fun _ => kappa2) x)
      (fun x => c * log ((1 / 3 - x) / kappa2) / x) (Icc t kappa2) := by
    intro x hx
    simp only [K3, K4_14 c x (hlt x hx)]
  have hne : ∀ x ∈ Icc t kappa2, x ≠ 0 := fun x hx => (hpos x hx).ne'
  have hcL : ContinuousOn (fun x => c * log ((1 / 3 - x) / kappa2) / x) (Icc t kappa2) := by
    refine (continuousOn_const.mul (ContinuousOn.log ?_ ?_)).div continuousOn_id hne
    · exact (continuousOn_const.sub continuousOn_id).div_const _
    · intro x hx
      have := hlt x hx
      exact (div_pos (by linarith) k2pos).ne'
  have hcR : ContinuousOn (fun x => c * P14 x / x) (Icc t kappa2) := by
    unfold P14
    exact (continuousOn_const.mul (by fun_prop)).div continuousOn_id hne
  rw [intervalIntegral.integral_congr (by rwa [uIcc_of_le h1])]
  refine intervalIntegral.integral_mono_on h1 (hcL.intervalIntegrable_of_Icc h1)
    (hcR.intervalIntegrable_of_Icc h1) ?_
  intro x hx
  refine div_le_div_of_nonneg_right ?_ (hpos x hx).le
  refine mul_le_mul_of_nonneg_left ?_ hc
  exact log14_le_taylor x (h0.trans hx.1) (hx.2.trans_eq hk2)

/-- Antiderivative of P14 x over x. -/
def R14 (x : ℝ) : ℝ :=
  (log (125 / 58) + 31 / 108) * log x - 80 / 27 * x - 8 / 3 * x ^ 2 - 16 * x ^ 4

theorem R14_deriv (x : ℝ) (hx : 0 < x) : HasDerivAt R14 (P14 x / x) x := by
  have h := ((((hasDerivAt_log hx.ne').const_mul (log (125 / 58) + 31 / 108)).sub
    ((hasDerivAt_id x).const_mul (80 / 27))).sub ((hasDerivAt_pow 2 x).const_mul (8 / 3))).sub
    ((hasDerivAt_pow 4 x).const_mul 16)
  convert h using 1
  · funext y; simp only [R14, Pi.sub_apply, id]
  · simp only [P14]
    push_cast
    field_simp
    ring

/-- PROVED: closed form of the majorant level three integral of F14. -/
theorem intP14 (c t : ℝ) (h0 : 0 < t) (h1 : t ≤ kappa2) :
    (∫ x in t..kappa2, c * P14 x / x) = c * (R14 kappa2 - R14 t) := by
  have hpos : ∀ x ∈ uIcc t kappa2, 0 < x := fun x hx => by
    rw [uIcc_of_le h1] at hx; linarith [hx.1]
  have e : (fun x => c * P14 x / x) = fun x => c * (P14 x / x) := by
    funext x; ring
  rw [e, intervalIntegral.integral_const_mul,
    integral_eq_sub_of_hasDerivAt (fun x hx => R14_deriv x (hpos x hx))]
  apply ContinuousOn.intervalIntegrable
  have hne : ∀ x ∈ uIcc t kappa2, x ≠ 0 := fun x hx => (hpos x hx).ne'
  unfold P14
  exact (by fun_prop : ContinuousOn (fun x : ℝ => log (125 / 58) - ((4 * x - 1 / 3) +
    (4 * x - 1 / 3) ^ 2 / 2 + (4 * x - 1 / 3) ^ 3 / 3 + (4 * x - 1 / 3) ^ 4 / 4)) _).div
    continuousOn_id hne

theorem P14_nonneg (x : ℝ) (h0 : 1 / 12 ≤ x) (h1 : x ≤ 29 / 250) : 0 ≤ P14 x := by
  have h := log14_le_taylor x h0 h1
  have hl : 0 ≤ log ((1 / 3 - x) / kappa2) := by
    apply Real.log_nonneg
    rw [k2v, le_div_iff₀ (by norm_num)]
    linarith
  unfold P14
  linarith

/-- PROVED: level two majorant of the constant F14 case. -/
theorem K2_14_le (c t : ℝ) (hc : 0 ≤ c) (h0 : 1 / 12 ≤ t) (h1 : t ≤ kappa2) :
    K2 c (fun t => 1 / 3 - t) (fun _ => kappa2) t ≤ c * (R14 kappa2 - R14 t) / t ^ 2 := by
  rw [K2, ← intP14 c t (by linarith) h1]
  exact div_le_div_of_nonneg_right (intK3_14_le c t hc h0 h1) (sq_nonneg _)

theorem maj2_nonneg (c t : ℝ) (hc : 0 ≤ c) (h0 : 1 / 12 ≤ t) (h1 : t ≤ kappa2) :
    0 ≤ c * (R14 kappa2 - R14 t) / t ^ 2 := by
  rw [← intP14 c t (by linarith) h1]
  refine div_nonneg (intervalIntegral.integral_nonneg h1 (fun x hx => ?_)) (sq_nonneg _)
  have hx0 : 0 < x := by linarith [hx.1]
  exact div_nonneg (mul_nonneg hc (P14_nonneg x (h0.trans hx.1) (hx.2.trans_eq k2v))) hx0.le

/-- Antiderivative of the level two majorant of F14, divided by c. -/
def S14 (t : ℝ) : ℝ :=
  -R14 kappa2 / t + (log (125 / 58) + 31 / 108) * (log t + 1) / t + 80 / 27 * log t +
    8 / 3 * t + 16 / 3 * t ^ 3

theorem S14_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt S14 ((R14 kappa2 - R14 t) / t ^ 2) t := by
  have hL := hasDerivAt_log ht.ne'
  have hI := hasDerivAt_id t
  have h := (((((hasDerivAt_const t (-R14 kappa2)).div hI ht.ne').add
    (((hL.add_const 1).const_mul (log (125 / 58) + 31 / 108)).div hI ht.ne')).add
    (hL.const_mul (80 / 27))).add (hI.const_mul (8 / 3))).add
    ((hasDerivAt_pow 3 t).const_mul (16 / 3))
  convert h using 1
  · funext y; simp only [S14, Pi.add_apply, Pi.div_apply, id]
  · simp only [R14, id]
    push_cast
    field_simp
    ring

/-- PROVED: level two integral majorant of the constant F14 case. -/
theorem intK2_14_le (c t : ℝ) (hc : 0 ≤ c) (h0 : 1 / 12 ≤ t) (h1 : t ≤ kappa2) :
    (∫ x in t..kappa2, K2 c (fun t => 1 / 3 - t) (fun _ => kappa2) x) ≤
      c * (S14 kappa2 - S14 t) := by
  have hpos : ∀ x ∈ uIcc t kappa2, 0 < x := fun x hx => by
    rw [uIcc_of_le h1] at hx; linarith [hx.1]
  have hne : ∀ x ∈ Icc t kappa2, x ≠ 0 := fun x hx => (hpos x (by rwa [uIcc_of_le h1])).ne'
  have hcont : ContinuousOn (fun x => c * (R14 kappa2 - R14 x) / x ^ 2) (Icc t kappa2) := by
    have hlog : ContinuousOn log (Icc t kappa2) := continuousOn_log.mono (fun x hx => hne x hx)
    unfold R14
    exact (continuousOn_const.mul (continuousOn_const.sub ((((continuousOn_const.mul hlog).sub
      (by fun_prop)).sub (by fun_prop)).sub (by fun_prop)))).div (by fun_prop)
      (fun x hx => pow_ne_zero 2 (hne x hx))
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) h1
  refine (integral_le_of_majorant h1 hint
    (fun x hx => maj2_nonneg c x hc (h0.trans hx.1) hx.2)
    (fun x hx => K2_14_le c x hc (h0.trans hx.1) hx.2)).trans_eq ?_
  have e : (fun x => c * (R14 kappa2 - R14 x) / x ^ 2) =
      fun x => c * ((R14 kappa2 - R14 x) / x ^ 2) := by funext x; ring
  rw [e, intervalIntegral.integral_const_mul,
    integral_eq_sub_of_hasDerivAt (fun x hx => S14_deriv x (hpos x hx))]
  unfold R14
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le h1]
  have hlog : ContinuousOn log (Icc t kappa2) :=
    continuousOn_log.mono (fun x hx => hne x hx)
  exact (continuousOn_const.sub ((((continuousOn_const.mul hlog).sub
    (by fun_prop)).sub (by fun_prop)).sub (by fun_prop))).div (by fun_prop)
    (fun x hx => pow_ne_zero 2 (hne x hx))

theorem G14_nonneg (t : ℝ) (h0 : 1 / 12 ≤ t) (h1 : t ≤ kappa2) :
    0 ≤ S14 kappa2 - S14 t := by
  have hpos : ∀ x ∈ uIcc t kappa2, 0 < x := fun x hx => by
    rw [uIcc_of_le h1] at hx; linarith [hx.1]
  have hne : ∀ x ∈ Icc t kappa2, x ≠ 0 := fun x hx => (hpos x (by rwa [uIcc_of_le h1])).ne'
  rw [← integral_eq_sub_of_hasDerivAt (fun x hx => S14_deriv x (hpos x hx))]
  · refine intervalIntegral.integral_nonneg h1 (fun x hx => ?_)
    have := maj2_nonneg 1 x zero_le_one (h0.trans hx.1) hx.2
    simpa using this
  unfold R14
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le h1]
  have hlog : ContinuousOn log (Icc t kappa2) :=
    continuousOn_log.mono (fun x hx => hne x hx)
  exact (continuousOn_const.sub ((((continuousOn_const.mul hlog).sub
    (by fun_prop)).sub (by fun_prop)).sub (by fun_prop))).div (by fun_prop)
    (fun x hx => pow_ne_zero 2 (hne x hx))

theorem S14_cont (p q : ℝ) (hp : 0 < p) : ContinuousOn S14 (Icc p q) := fun x hx =>
  (S14_deriv x (hp.trans_le hx.1)).continuousAt.continuousWithinAt

/-- The quartic majorant of 1 over t times 1 minus t on 0 to 1/10. -/
def W14 (t : ℝ) : ℝ := 1 / t + 1 + t + t ^ 2 + t ^ 3 + 10 / 9 * t ^ 4

theorem W14_ge (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1 / 10) : 1 / (t * (1 - t)) ≤ W14 t := by
  rw [div_le_iff₀ (by nlinarith)]
  have e : W14 t * (t * (1 - t)) = 1 + t ^ 5 * (1 / 9 - 10 / 9 * t) := by
    unfold W14; field_simp; ring
  rw [e]
  have : 0 ≤ t ^ 5 * (1 / 9 - 10 / 9 * t) := mul_nonneg (by positivity) (by linarith)
  linarith

/-- PROVED: reduction of const11 to two one dimensional integrals of elementary functions. -/
theorem const11_of_oneD
    (h : 36 / 5 * (∫ t in (1 / 12 : ℝ)..(1 / 10), 0.561522 * (S14 kappa2 - S14 t) * W14 t) +
      8 * (∫ t in (1 / 10 : ℝ)..kappa2, 0.561522 * (S14 kappa2 - S14 t) / t) ≤
        (0.182860 : ℝ)) :
    36 / 5 * fourfold (fun _ => (0.561522 : ℝ)) (fun t => 1 / 3 - t) (1 / 12) (1 / 10)
        (fun _ => (29 / 250 : ℝ)) (fun t => t * (1 - t)) +
      8 * fourfold (fun _ => (0.561522 : ℝ)) (fun t => 1 / 3 - t) (1 / 10) (29 / 250)
        (fun _ => (29 / 250 : ℝ)) id ≤ (0.182860 : ℝ) := by
  set c : ℝ := 0.561522 with hcdef
  have hc : 0 ≤ c := by norm_num [hcdef]
  rw [← k2v, fourfold_const_eq, fourfold_const_eq]
  have hA : (∫ t1 in (1 / 12 : ℝ)..(1 / 10),
      K1 c (fun t => 1 / 3 - t) (fun _ => kappa2) (fun t => t * (1 - t)) t1) ≤
      ∫ t in (1 / 12 : ℝ)..(1 / 10), c * (S14 kappa2 - S14 t) * W14 t := by
    have hab : (1 / 12 : ℝ) ≤ 1 / 10 := by norm_num
    have hcont : ContinuousOn (fun t => c * (S14 kappa2 - S14 t) * W14 t)
        (Icc (1 / 12 : ℝ) (1 / 10)) := by
      have hne : ∀ x ∈ Icc (1 / 12 : ℝ) (1 / 10), x ≠ 0 := fun x hx =>
        (lt_of_lt_of_le (by norm_num) hx.1 : (0 : ℝ) < x).ne'
      refine (continuousOn_const.mul (continuousOn_const.sub
        (S14_cont _ _ (by norm_num)))).mul ?_
      unfold W14
      exact ((continuousOn_const.div continuousOn_id hne).add continuousOn_const).add
        (by fun_prop) |>.add (by fun_prop) |>.add (by fun_prop) |>.add (by fun_prop)
    refine integral_le_of_majorant hab (hcont.intervalIntegrable_of_Icc hab) ?_ ?_
    · intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
      have hg := G14_nonneg x hx.1 (hx.2.trans (by norm_num [kappa2]))
      have hw : 0 ≤ W14 x := by unfold W14; positivity
      exact mul_nonneg (mul_nonneg hc hg) hw
    · intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
      have hxk : x ≤ kappa2 := hx.2.trans (by norm_num [kappa2])
      have hI := intK2_14_le c x hc hx.1 hxk
      have hg := G14_nonneg x hx.1 hxk
      have hW := W14_ge x hx0 hx.2
      have hd : 0 < x * (1 - x) := by nlinarith [hx.2]
      simp only [K1]
      rw [div_eq_mul_one_div, mul_assoc]
      calc (∫ t2 in x..kappa2, K2 c (fun t => 1 / 3 - t) (fun _ => kappa2) t2) *
            (1 / (x * (1 - x))) ≤ (c * (S14 kappa2 - S14 x)) * (1 / (x * (1 - x))) :=
            mul_le_mul_of_nonneg_right hI (by positivity)
        _ ≤ (c * (S14 kappa2 - S14 x)) * W14 x :=
            mul_le_mul_of_nonneg_left hW (mul_nonneg hc hg)
        _ = c * ((S14 kappa2 - S14 x) * W14 x) := by ring
  have hB : (∫ t1 in (1 / 10 : ℝ)..kappa2,
      K1 c (fun t => 1 / 3 - t) (fun _ => kappa2) id t1) ≤
      ∫ t in (1 / 10 : ℝ)..kappa2, c * (S14 kappa2 - S14 t) / t := by
    have hab : (1 / 10 : ℝ) ≤ kappa2 := by norm_num [kappa2]
    have hne : ∀ x ∈ Icc (1 / 10 : ℝ) kappa2, x ≠ 0 := fun x hx =>
      (lt_of_lt_of_le (by norm_num) hx.1 : (0 : ℝ) < x).ne'
    have hcont : ContinuousOn (fun t => c * (S14 kappa2 - S14 t) / t)
        (Icc (1 / 10 : ℝ) kappa2) :=
      (continuousOn_const.mul (continuousOn_const.sub
        (S14_cont _ _ (by norm_num)))).div continuousOn_id hne
    refine integral_le_of_majorant hab (hcont.intervalIntegrable_of_Icc hab) ?_ ?_
    · intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
      exact div_nonneg (mul_nonneg hc (G14_nonneg x (le_trans (by norm_num) hx.1) hx.2)) hx0.le
    · intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
      simp only [K1, id]
      exact div_le_div_of_nonneg_right (intK2_14_le c x hc (le_trans (by norm_num) hx.1) hx.2)
        hx0.le
  linarith

/-- Antiderivative for piece B of F14, divided by c. -/
def PB14 (t : ℝ) : ℝ :=
  S14 kappa2 * log t - (R14 kappa2 - (log (125 / 58) + 31 / 108)) / t +
    (log (125 / 58) + 31 / 108) * (log t + 1) / t - 40 / 27 * log t ^ 2 - 8 / 3 * t -
    16 / 9 * t ^ 3

theorem PB14_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt PB14 ((S14 kappa2 - S14 t) / t) t := by
  have hL := hasDerivAt_log ht.ne'
  have hI := hasDerivAt_id t
  have h := (((((hL.const_mul (S14 kappa2)).sub ((hasDerivAt_const t
    (R14 kappa2 - (log (125 / 58) + 31 / 108))).div hI ht.ne')).add
    (((hL.add_const 1).const_mul (log (125 / 58) + 31 / 108)).div hI ht.ne')).sub
    ((hL.pow 2).const_mul (40 / 27))).sub (hI.const_mul (8 / 3))).sub
    ((hasDerivAt_pow 3 t).const_mul (16 / 9))
  convert h using 1
  · funext y; simp only [PB14, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id]
  · simp only [S14, id]
    push_cast
    field_simp
    ring

/-- PROVED: closed form of piece B of F14. -/
theorem pieceB14 :
    (∫ t in (1 / 10 : ℝ)..kappa2, 0.561522 * (S14 kappa2 - S14 t) / t) =
      0.561522 * (PB14 kappa2 - PB14 (1 / 10)) := by
  have hab : (1 / 10 : ℝ) ≤ kappa2 := by norm_num [kappa2]
  have hpos : ∀ x ∈ uIcc (1 / 10 : ℝ) kappa2, 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le (by norm_num) hx.1
  have e : (fun t : ℝ => 0.561522 * (S14 kappa2 - S14 t) / t) =
      fun t => 0.561522 * ((S14 kappa2 - S14 t) / t) := by funext t; ring
  rw [e, intervalIntegral.integral_const_mul,
    integral_eq_sub_of_hasDerivAt (fun x hx => PB14_deriv x (hpos x hx))]
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (continuousOn_const.sub (S14_cont _ _ (by norm_num))).div continuousOn_id
    (fun x hx => (hpos x (by rwa [uIcc_of_le hab])).ne')

/-- Antiderivative for piece A of F14, divided by c, generated in python. -/
def PA14 (C0 C1 A y : ℝ) : ℝ :=
    ((-1) * C1 + (1) * A) * (y⁻¹) +
    ((1) * C0 + (1) * C1) * (log y) +
    ((-1 / 2) * A + (-40 / 27)) * (log y ^ 2) +
    ((1) * A) * (log y * y⁻¹) +
    ((-1) * A + (-80 / 27)) * (log y * y ^ 1) +
    ((-1 / 2) * A + (-40 / 27)) * (log y * y ^ 2) +
    ((-1 / 3) * A + (-80 / 81)) * (log y * y ^ 3) +
    ((-5 / 18) * A + (-20 / 27)) * (log y * y ^ 4) +
    ((-160 / 243)) * (log y * y ^ 5) +
    ((1) * C0 + (1) * C1 + (8 / 27) + (1) * A) * (y ^ 1) +
    ((1 / 2) * C0 + (1 / 2) * C1 + (-16 / 27) + (1 / 4) * A) * (y ^ 2) +
    ((1 / 3) * C0 + (1 / 3) * C1 + (-568 / 243) + (1 / 9) * A) * (y ^ 3) +
    ((1 / 4) * C0 + (5 / 18) * C1 + (-49 / 27) + (5 / 72) * A) * (y ^ 4) +
    ((2 / 9) * C0 + (-1784 / 1215)) * (y ^ 5) +
    ((-112 / 81)) * (y ^ 6) +
    ((-16 / 21)) * (y ^ 7) +
    ((-20 / 27)) * (y ^ 8)

theorem PA14_deriv (C0 C1 A t : ℝ) (ht : 0 < t) :
    HasDerivAt (PA14 C0 C1 A) ((C0 + C1 / t - A * log t / t - 80 / 27 * log t - 8 / 3 * t -
      16 / 3 * t ^ 3) * W14 t) t := by
  have hL := hasDerivAt_log ht.ne'
  have hV := hasDerivAt_inv ht.ne'
  have h := (((((((((((((((((hV.const_mul ((-1) * C1 + (1) * A)).add
      (hL.const_mul ((1) * C0 + (1) * C1))).add
      ((hL.pow 2).const_mul ((-1 / 2) * A + (-40 / 27)))).add
      ((hL.mul hV).const_mul ((1) * A))).add
      ((hL.mul (hasDerivAt_pow 1 t)).const_mul ((-1) * A + (-80 / 27)))).add
      ((hL.mul (hasDerivAt_pow 2 t)).const_mul ((-1 / 2) * A + (-40 / 27)))).add
      ((hL.mul (hasDerivAt_pow 3 t)).const_mul ((-1 / 3) * A + (-80 / 81)))).add
      ((hL.mul (hasDerivAt_pow 4 t)).const_mul ((-5 / 18) * A + (-20 / 27)))).add
      ((hL.mul (hasDerivAt_pow 5 t)).const_mul ((-160 / 243)))).add
      ((hasDerivAt_pow 1 t).const_mul ((1) * C0 + (1) * C1 + (8 / 27) + (1) * A))).add
      ((hasDerivAt_pow 2 t).const_mul ((1 / 2) * C0 + (1 / 2) * C1 + (-16 / 27) + (1 / 4) * A))).add
      ((hasDerivAt_pow 3 t).const_mul ((1 / 3) * C0 + (1 / 3) * C1 + (-568 / 243) + (1 / 9) * A))).add
      ((hasDerivAt_pow 4 t).const_mul ((1 / 4) * C0 + (5 / 18) * C1 + (-49 / 27) + (5 / 72) * A))).add
      ((hasDerivAt_pow 5 t).const_mul ((2 / 9) * C0 + (-1784 / 1215)))).add
      ((hasDerivAt_pow 6 t).const_mul ((-112 / 81)))).add
      ((hasDerivAt_pow 7 t).const_mul ((-16 / 21)))).add
      ((hasDerivAt_pow 8 t).const_mul ((-20 / 27))))
  convert h using 1
  · funext y; simp only [PA14, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  · simp only [W14]
    push_cast
    field_simp
    ring

/-- The constant A of F14. -/
def A14 : ℝ := log (125 / 58) + 31 / 108

theorem PA14_deriv' (t : ℝ) (ht : 0 < t) :
    HasDerivAt (PA14 (S14 kappa2) (R14 kappa2 - A14) A14)
      ((S14 kappa2 - S14 t) * W14 t) t := by
  refine (PA14_deriv _ _ _ t ht).congr_deriv ?_
  congr 1
  simp only [S14, A14]
  field_simp
  ring

/-- PROVED: closed form of piece A of F14. -/
theorem pieceA14 :
    (∫ t in (1 / 12 : ℝ)..(1 / 10), 0.561522 * (S14 kappa2 - S14 t) * W14 t) =
      0.561522 * (PA14 (S14 kappa2) (R14 kappa2 - A14) A14 (1 / 10) -
        PA14 (S14 kappa2) (R14 kappa2 - A14) A14 (1 / 12)) := by
  have hab : (1 / 12 : ℝ) ≤ 1 / 10 := by norm_num
  have hpos : ∀ x ∈ uIcc (1 / 12 : ℝ) (1 / 10), 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le (by norm_num) hx.1
  have e : (fun t : ℝ => 0.561522 * (S14 kappa2 - S14 t) * W14 t) =
      fun t => 0.561522 * ((S14 kappa2 - S14 t) * W14 t) := by funext t; ring
  rw [e, intervalIntegral.integral_const_mul,
    integral_eq_sub_of_hasDerivAt (fun x hx => PA14_deriv' x (hpos x hx))]
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  have hne : ∀ x ∈ Icc (1 / 12 : ℝ) (1 / 10), x ≠ 0 := fun x hx =>
    (hpos x (by rwa [uIcc_of_le hab])).ne'
  refine (continuousOn_const.sub (S14_cont _ _ (by norm_num))).mul ?_
  unfold W14
  exact ((continuousOn_const.div continuousOn_id hne).add continuousOn_const).add
    (by fun_prop) |>.add (by fun_prop) |>.add (by fun_prop) |>.add (by fun_prop)

/-- The final numerical comparison for F14 after exact integration. -/
theorem final14 :
    36 / 5 * (0.561522 * (PA14 (S14 kappa2) (R14 kappa2 - A14) A14 (1 / 10) -
        PA14 (S14 kappa2) (R14 kappa2 - A14) A14 (1 / 12))) +
      8 * (0.561522 * (PB14 kappa2 - PB14 (1 / 10))) ≤ (0.182860 : ℝ) := by
  have h10 : log (1 / 10 : ℝ) = -3 * log 2 + log (4 / 5) := by
    rw [show (1 / 10 : ℝ) = (4 / 5) / 2 ^ 3 by norm_num, log_div (by norm_num) (by norm_num),
      log_pow]; push_cast; ring
  have hk : log (29 / 250 : ℝ) = log (1 / 10) + log (29 / 25) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have h12 : log (1 / 12 : ℝ) = log (1 / 10) - log (6 / 5) := by
    rw [← log_div (by norm_num) (by norm_num)]; norm_num
  have hm : log (125 / 58 : ℝ) = -2 * log 2 - log (29 / 250) := by
    rw [show (125 / 58 : ℝ) = (1 / 2 ^ 2) / (29 / 250) by norm_num,
      log_div (by norm_num) (by norm_num), one_div, log_inv, log_pow]; push_cast; ring
  have hA := Real.abs_log_sub_add_sum_range_le (show |(-4 / 25 : ℝ)| < 1 by norm_num) 12
  have hB := Real.abs_log_sub_add_sum_range_le (show |(-1 / 5 : ℝ)| < 1 by norm_num) 14
  have hC := Real.abs_log_sub_add_sum_range_le (show |(1 / 5 : ℝ)| < 1 by norm_num) 14
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ] at hA hB hC
  rw [abs_le] at hA hB hC
  unfold PA14 PB14 S14 R14 A14
  simp only [k2v]
  rw [hm, hk, h12, h10]
  generalize log 2 = w at *
  generalize log (29 / 25 : ℝ) = a at *
  generalize log (6 / 5 : ℝ) = b at *
  generalize log (4 / 5 : ℝ) = d at *
  ring_nf
  ring_nf at hA hB hC
  obtain ⟨ha1, ha2⟩ := hA
  obtain ⟨hb1, hb2⟩ := hB
  obtain ⟨hd1, hd2⟩ := hC
  obtain ⟨v, rfl⟩ : ∃ v, d = w - v := ⟨w - d, by ring⟩
  ring_nf
  have haL : 0 ≤ a - (6130639525942384076 / 41306018829345703125 - 67108864 / 1251697540283203125) := by linarith
  have haH : 0 ≤ (6130639525942384076 / 41306018829345703125 + 67108864 / 1251697540283203125) - a := by linarith
  have hbL : 0 ≤ b - (80201899665047 / 439892578125000 - 1 / 24414062500) := by linarith
  have hbH : 0 ≤ (80201899665047 / 439892578125000 + 1 / 24414062500) - b := by linarith
  have hvL : 0 ≤ v - (6931471803 / 10000000000 + 98159192078393 / 439892578125000 - 1 / 24414062500) := by norm_num at h2a h2b ⊢; linarith
  have hvH : 0 ≤ (6931471808 / 10000000000 + 98159192078393 / 439892578125000 + 1 / 24414062500) - v := by norm_num at h2a h2b ⊢; linarith
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hv0 : 0 ≤ v := by linarith
  linarith [mul_nonneg ha0 haL,
    mul_nonneg ha0 haH,
    mul_nonneg ha0 hbL,
    mul_nonneg ha0 hbH,
    mul_nonneg ha0 hvL,
    mul_nonneg ha0 hvH,
    mul_nonneg hb0 haL,
    mul_nonneg hb0 haH,
    mul_nonneg hb0 hbL,
    mul_nonneg hb0 hbH,
    mul_nonneg hb0 hvL,
    mul_nonneg hb0 hvH,
    mul_nonneg hv0 haL,
    mul_nonneg hv0 haH,
    mul_nonneg hv0 hbL,
    mul_nonneg hv0 hbH,
    mul_nonneg hv0 hvL,
    mul_nonneg hv0 hvH,
    mul_nonneg (mul_nonneg ha0 ha0) haL,
    mul_nonneg (mul_nonneg ha0 ha0) haH,
    mul_nonneg (mul_nonneg ha0 ha0) hbL,
    mul_nonneg (mul_nonneg ha0 ha0) hbH,
    mul_nonneg (mul_nonneg ha0 ha0) hvL,
    mul_nonneg (mul_nonneg ha0 ha0) hvH,
    mul_nonneg (mul_nonneg ha0 hb0) haL,
    mul_nonneg (mul_nonneg ha0 hb0) haH,
    mul_nonneg (mul_nonneg ha0 hb0) hbL,
    mul_nonneg (mul_nonneg ha0 hb0) hbH,
    mul_nonneg (mul_nonneg ha0 hb0) hvL,
    mul_nonneg (mul_nonneg ha0 hb0) hvH,
    mul_nonneg (mul_nonneg ha0 hv0) haL,
    mul_nonneg (mul_nonneg ha0 hv0) haH,
    mul_nonneg (mul_nonneg ha0 hv0) hbL,
    mul_nonneg (mul_nonneg ha0 hv0) hbH,
    mul_nonneg (mul_nonneg ha0 hv0) hvL,
    mul_nonneg (mul_nonneg ha0 hv0) hvH,
    mul_nonneg (mul_nonneg hb0 hb0) haL,
    mul_nonneg (mul_nonneg hb0 hb0) haH,
    mul_nonneg (mul_nonneg hb0 hb0) hbL,
    mul_nonneg (mul_nonneg hb0 hb0) hbH,
    mul_nonneg (mul_nonneg hb0 hb0) hvL,
    mul_nonneg (mul_nonneg hb0 hb0) hvH,
    mul_nonneg (mul_nonneg hb0 hv0) haL,
    mul_nonneg (mul_nonneg hb0 hv0) haH,
    mul_nonneg (mul_nonneg hb0 hv0) hbL,
    mul_nonneg (mul_nonneg hb0 hv0) hbH,
    mul_nonneg (mul_nonneg hb0 hv0) hvL,
    mul_nonneg (mul_nonneg hb0 hv0) hvH,
    mul_nonneg (mul_nonneg hv0 hv0) haL,
    mul_nonneg (mul_nonneg hv0 hv0) haH,
    mul_nonneg (mul_nonneg hv0 hv0) hbL,
    mul_nonneg (mul_nonneg hv0 hv0) hbH,
    mul_nonneg (mul_nonneg hv0 hv0) hvL,
    mul_nonneg (mul_nonneg hv0 hv0) hvH]

/-- PROVED: Wu 2004 page 41 equation 10.12 and page 42 final display, value of F14 with
omega replaced by the constant 0.561522, at most 0.182860. This is exactly the statement of
const11_le in Feed1122_Decomp275b_F13F14. The level four log is bounded by a degree 4
Taylor sum, the next three levels are integrated exactly, 1 over t1 times 1 minus t1 is
bounded by a quartic, and the logarithms are bounded by Taylor sums and log_two bounds;
python gave 0.1828591240 for the exact value and 0.1828598977 for the proved majorant. -/
theorem const11 :
    36 / 5 * fourfold (fun _ => (0.561522 : ℝ)) (fun t => 1 / 3 - t) (1 / 12) (1 / 10)
        (fun _ => (29 / 250 : ℝ)) (fun t => t * (1 - t)) +
      8 * fourfold (fun _ => (0.561522 : ℝ)) (fun t => 1 / 3 - t) (1 / 10) (29 / 250)
        (fun _ => (29 / 250 : ℝ)) id ≤ (0.182860 : ℝ) := by
  apply const11_of_oneD
  rw [pieceA14, pieceB14]
  exact final14

end LeanLab.ChenDoubleSieve.Task275.Feed1122Const11
