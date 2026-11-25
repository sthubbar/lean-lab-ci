/-
Schoenfeld 1976, Math. Comp. 30, p. 340: "A direct calculation shows that (6.18) holds for
2,657 ≤ x < 2,659". The one numerical input of SchoenfeldFiniteS70.lean is the enclosure
`399.59 ≤ li 2657 ≤ 399.61`, true value `li 2657 = 399.596817`.

Here that enclosure is split into much smaller numerical LEAFs:
* `liPV 2 ≥ 1.045`, true `1.0451638`; the upper bound `liPV 2 ≤ 1.046` is already PROVED
  in LiTwo.lean.
* eleven dyadic pieces `∫_a^b dt / log t` on `[2, 4], [4, 8], ..., [1024, 2048], [2048, 2657]`,
  each enclosed to about `1e-4`, values from mpmath at 30 digits.
The assembly `liPV_2657_encl_S76`, with exactly the statement of the LEAF
`SchoenfeldFiniteS70.liPV_2657_encl`, is PROVED from these through `liPV_eq_add` and
additivity of the interval integral.

AI wrote this Lean code, Claude, ROUTE BURST S76 burst-20261122, step direct_2657_li.
Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.SchoenfeldFiniteS70
import LeanLab.BS2022GRH.LiTwo

namespace LeanLab.BS2022GRH.SchoenfeldLiS76
open Real MeasureTheory intervalIntegral Set

noncomputable section

/-- `1 / log t` is interval integrable on `[u, v]` when `2 ≤ u, v`. -/
lemma ii_inv_log {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t => 1 / log t) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => by
      rw [Set.mem_uIcc] at ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
  · intro t ht
    rw [Set.mem_uIcc] at ht
    have : (1 : ℝ) < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact (Real.log_pos this).ne'

/-- Additivity of `∫ dt / log t` over adjacent intervals in `[2, ∞)`. -/
lemma split {a b c : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    (∫ t in a..c, 1 / log t) = (∫ t in a..b, 1 / log t) + ∫ t in b..c, 1 / log t :=
  (intervalIntegral.integral_add_adjacent_intervals (ii_inv_log ha hb) (ii_inv_log hb hc)).symm

/-- The difference `log t - 2 (t - 1) / (t + 1)`. -/
def dC_S114 (t : ℝ) : ℝ := log t - 2 * (t - 1) / (t + 1)

/-- The derivative of `dC_S114` is `(t - 1)^2 / (t (t + 1)^2)`. -/
lemma dC_S114_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt dC_S114 ((t - 1) ^ 2 / (t * (t + 1) ^ 2)) t := by
  have hden : t + 1 ≠ 0 := by linarith
  have hn : HasDerivAt (fun x : ℝ => 2 * (x - 1)) (2 * 1) t :=
    ((hasDerivAt_id t).sub_const 1).const_mul 2
  have hd : HasDerivAt (fun x : ℝ => x + 1) 1 t := (hasDerivAt_id t).add_const 1
  have h : HasDerivAt dC_S114 _ t := (Real.hasDerivAt_log ht.ne').sub (hn.div hd hden)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `log t ≤ 2 (t - 1) / (t + 1)` for `0 < t ≤ 1`. -/
lemma log_le_two_S114 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : log t ≤ 2 * (t - 1) / (t + 1) := by
  have hmono : MonotoneOn dC_S114 (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro x hx
      exact (dC_S114_hasDerivAt hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (dC_S114_hasDerivAt hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hx0 : 0 < x := hx
      rw [(dC_S114_hasDerivAt hx0).deriv]
      positivity
  have h := hmono (show t ∈ Ioi (0:ℝ) from ht) (show (1:ℝ) ∈ Ioi 0 from Set.mem_Ioi.mpr one_pos) ht1
  have h1 : dC_S114 1 = 0 := by simp [dC_S114]
  unfold dC_S114 at h h1
  linarith

/-- On `(0, 1)`: `1/2 ≤ gli t`. -/
lemma gli_ge_half_S114 {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 1 / 2 ≤ gli t := by
  have hL := log_le_two_S114 ht ht1.le
  have hc : 2 * (t - 1) / (t + 1) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have h1 : 1 / (2 * (t - 1) / (t + 1)) ≤ 1 / log t := one_div_le_one_div_of_neg_of_le hc hL
  have hs : t - 1 ≠ 0 := by linarith
  have hs1 : t + 1 ≠ 0 := by linarith
  have e : 1 / (2 * (t - 1) / (t + 1)) - 1 / (t - 1) = 1 / 2 := by
    field_simp
    ring
  unfold gli
  linarith

/-- On `(0, 1)`: the geometric decomposition of `gli` with the tail bounded below by `1/2`. -/
lemma gli_ge_decomp_S114 {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (∑ k ∈ Finset.range 63, t ^ k) + LiTwo.mfun t + t ^ 63 * (1 / 2) ≤ gli t := by
  have hg := gli_ge_half_S114 ht ht1
  have hgeom : (∑ k ∈ Finset.range 63, t ^ k) = (t ^ 63 - 1) / (t - 1) :=
    geom_sum_eq (by linarith : t ≠ 1) 63
  have hlog : log t ≠ 0 := (log_neg ht ht1).ne
  have hs : t - 1 ≠ 0 := by linarith
  have hid : gli t = (∑ k ∈ Finset.range 63, t ^ k) + LiTwo.mfun t + t ^ 63 * gli t := by
    rw [hgeom]; unfold LiTwo.mfun gli; field_simp; ring
  have hp : 0 ≤ t ^ 63 := by positivity
  have hm := mul_le_mul_of_nonneg_left hg hp
  linarith

/-- `H_63 - log 64 + 1/128 ≤ ∫₀¹ g`. -/
lemma integral_left_ge_S114 :
    (∑ k ∈ Finset.range 63, (1 : ℝ) / (k + 1)) - log 64 + 1 / 128
      ≤ ∫ t in (0 : ℝ)..1, gli t := by
  have hP : IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.range 63, t ^ k) volume 0 1 :=
    (continuous_finsetSum _ (fun k _ => continuous_pow k)).intervalIntegrable 0 1
  have hT : IntervalIntegrable (fun t : ℝ => t ^ 63 * (1 / 2)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => t ^ 63 * (1 / 2))).intervalIntegrable 0 1
  have hR : IntervalIntegrable
      (fun t : ℝ => (∑ k ∈ Finset.range 63, t ^ k) + LiTwo.mfun t + t ^ 63 * (1 / 2))
      volume 0 1 := (hP.add LiTwo.mfun_ii).add hT
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hR
    (gli_ii le_rfl zero_le_one) (fun t ht => gli_ge_decomp_S114 ht.1 ht.2)
  have htail : ∫ t in (0 : ℝ)..1, t ^ 63 * (1 / 2) = 1 / 128 := by
    rw [intervalIntegral.integral_mul_const, integral_pow]; norm_num
  rw [intervalIntegral.integral_add (hP.add LiTwo.mfun_ii) hT,
    intervalIntegral.integral_add hP LiTwo.mfun_ii, LiTwo.integral_geom, LiTwo.integral_mfun,
    htail] at hmono
  linarith

/-- `H_63 ≥ 4.7282659`, true `4.72826590...`. -/
lemma harmonic63_ge_S114 : 4.7282659 ≤ ∑ k ∈ Finset.range 63, (1 : ℝ) / (k + 1) := by
  norm_num [Finset.sum_range_succ]


/-- Polynomial minorant of `exp s * gli (exp s)` on `(0, log 2]`. -/
def Pmin_S114 (s : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 8, s ^ i / ((i + 1).factorial : ℝ)) - 1 / 2 - s / 12

/-- `Pmin_S114 s ≤ exp s * gli (exp s)` for `s > 0`, from the degree 8 exponential minorant. -/
lemma Pmin_le_S114 {s : ℝ} (hs : 0 < s) : Pmin_S114 s ≤ exp s * gli (exp s) := by
  have hE := Real.sum_le_exp_of_nonneg hs.le 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hE
  push_cast at hE
  set Q : ℝ := s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 + s ^ 5 / 120 + s ^ 6 / 720
    + s ^ 7 / 5040 + s ^ 8 / 40320 with hQ
  set E : ℝ := exp s - 1 with hEdef
  have hQE : Q ≤ E := by rw [hQ, hEdef]; nlinarith [hE]
  have hQpos : 0 < Q := by positivity
  have hEpos : 0 < E := lt_of_lt_of_le hQpos hQE
  have hd : 0 < 12 - 6 * s + s ^ 2 := by nlinarith [sq_nonneg (s - 3)]
  have hpoly : 12 * s ≤ (12 - 6 * s + s ^ 2) * Q := by
    have h : (12 - 6 * s + s ^ 2) * Q - 12 * s = s ^ 4 * (s / 60 + s ^ 2 / 120 + s ^ 3 / 420
      + s ^ 4 / 2016 + s ^ 5 / 20160 + s ^ 6 / 40320) := by rw [hQ]; ring
    have : 0 ≤ s ^ 4 * (s / 60 + s ^ 2 / 120 + s ^ 3 / 420
      + s ^ 4 / 2016 + s ^ 5 / 20160 + s ^ 6 / 40320) := by positivity
    linarith
  have h2 : 1 / E ≤ (12 - 6 * s + s ^ 2) / (12 * s) := by
    rw [div_le_div_iff₀ hEpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hQE hd.le]
  have h1 : Q / s ≤ E / s := div_le_div_of_nonneg_right hQE hs.le
  have e1 : Q / s = ∑ i ∈ Finset.range 8, s ^ i / ((i + 1).factorial : ℝ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    rw [hQ]; field_simp; ring
  have e2 : (12 - 6 * s + s ^ 2) / (12 * s) = 1 / s - 1 / 2 + s / 12 := by
    field_simp; ring
  have e3 : exp s * gli (exp s) = E / s + 1 / s - 1 - 1 / E := by
    unfold gli
    rw [Real.log_exp, ← hEdef]
    have : exp s = E + 1 := by rw [hEdef]; ring
    rw [this]
    field_simp
    ring
  unfold Pmin_S114
  rw [e3]
  linarith

/-- The integral of the polynomial minorant over `[0, L]`. -/
lemma integral_Pmin_S114 (L : ℝ) : ∫ s in (0 : ℝ)..L, Pmin_S114 s
    = L / 2 + 5 * L ^ 2 / 24 + L ^ 3 / 18 + L ^ 4 / 96 + L ^ 5 / 600 + L ^ 6 / 4320
      + L ^ 7 / 35280 + L ^ 8 / 322560 := by
  have hc : ∀ s, Pmin_S114 s = 1 / 2 + 5 / 12 * s + 1 / 6 * s ^ 2 + 1 / 24 * s ^ 3
      + 1 / 120 * s ^ 4 + 1 / 720 * s ^ 5 + 1 / 5040 * s ^ 6 + 1 / 40320 * s ^ 7 := by
    intro s
    simp only [Pmin_S114, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring
  simp only [hc]
  rw [intervalIntegral.integral_deriv_eq_sub' (fun x : ℝ => (1/2 : ℝ) * x ^ 1 + (5/24 : ℝ) * x ^ 2 + (1/18 : ℝ) * x ^ 3 + (1/96 : ℝ) * x ^ 4 + (1/600 : ℝ) * x ^ 5 + (1/4320 : ℝ) * x ^ 6 + (1/35280 : ℝ) * x ^ 7 + (1/322560 : ℝ) * x ^ 8)]
  · ring
  · funext x
    have h := (((((((((hasDerivAt_pow 1 x).const_mul (1/2 : ℝ)).add ((hasDerivAt_pow 2 x).const_mul (5/24 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (1/18 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (1/96 : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (1/600 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (1/4320 : ℝ))).add ((hasDerivAt_pow 7 x).const_mul (1/35280 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (1/322560 : ℝ)))
    exact h.deriv.trans (by push_cast; ring)
  · intro x _
    fun_prop
  · exact (by fun_prop : Continuous (fun s : ℝ => 1 / 2 + 5 / 12 * s + 1 / 6 * s ^ 2
      + 1 / 24 * s ^ 3 + 1 / 120 * s ^ 4 + 1 / 720 * s ^ 5 + 1 / 5040 * s ^ 6
      + 1 / 40320 * s ^ 7)).continuousOn

/-- Change of variables `t = exp s`. -/
lemma integral_right_eq_S114 :
    ∫ t in (1 : ℝ)..2, gli t = ∫ s in Ioc 0 (log 2), exp s * gli (exp s) := by
  have himg : exp '' Ioc 0 (log 2) = Ioc 1 2 := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      refine ⟨by simpa using Real.exp_lt_exp.mpr hx0, ?_⟩
      calc exp x ≤ exp (log 2) := Real.exp_le_exp.mpr hx1
        _ = 2 := Real.exp_log (by norm_num)
    · rintro ⟨hy1, hy2⟩
      have hy0 : 0 < y := by linarith
      refine ⟨log y, ⟨Real.log_pos hy1, Real.log_le_log hy0 hy2⟩, Real.exp_log hy0⟩
  rw [intervalIntegral.integral_of_le (by norm_num), ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos x)]

/-- Integrability of the substituted integrand on `(0, log 2]`. -/
lemma integrableOn_right_S114 :
    IntegrableOn (fun s => exp s * gli (exp s)) (Ioc 0 (log 2)) := by
  have himg : exp '' Ioc 0 (log 2) ⊆ Icc 0 2 := by
    rintro _ ⟨x, ⟨_, hx1⟩, rfl⟩
    refine ⟨(Real.exp_pos x).le, ?_⟩
    calc exp x ≤ exp (log 2) := Real.exp_le_exp.mpr hx1
      _ = 2 := Real.exp_log (by norm_num)
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn gli).mp
    (gli_integrableOn.mono_set himg)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioc
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos x)]

/-- Lower bound for `∫₁² g`, true `0.4679481`; the bound is `0.4678686`. -/
lemma integral_right_ge_S114 :
    log 2 / 2 + 5 * log 2 ^ 2 / 24 + log 2 ^ 3 / 18 + log 2 ^ 4 / 96 + log 2 ^ 5 / 600
      + log 2 ^ 6 / 4320 + log 2 ^ 7 / 35280 + log 2 ^ 8 / 322560
      ≤ ∫ t in (1 : ℝ)..2, gli t := by
  rw [integral_right_eq_S114, ← integral_Pmin_S114,
    intervalIntegral.integral_of_le (Real.log_nonneg (by norm_num))]
  refine setIntegral_mono_on ?_ integrableOn_right_S114 measurableSet_Ioc
    (fun s hs => Pmin_le_S114 hs.1)
  exact (by unfold Pmin_S114; fun_prop : Continuous Pmin_S114).integrableOn_Ioc

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, the constant `li 2` inside `li 2657 ≅ 399.5968`, lower
bound. EASY. True value `li 2 = 1.0451637801`; the matching upper bound `1.046` is
`LiTwo.liPV_two_le_1046`. -/
theorem liPV_two_ge : 1.045 ≤ liPV 2 := by
  rw [liPV_two, ← intervalIntegral.integral_add_adjacent_intervals
    (gli_ii (a := 0) (b := 1) le_rfl zero_le_one) (gli_ii (a := 1) (b := 2) zero_le_one
    (by norm_num))]
  have hL := integral_left_ge_S114
  have hR := integral_right_ge_S114
  have h64 : log 64 = 6 * log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hH := harmonic63_ge_S114
  rw [h64] at hL
  have l0 : (0 : ℝ) ≤ 0.6931471803 := by norm_num
  have p2 := pow_le_pow_left₀ l0 hl.le 2
  have p3 := pow_le_pow_left₀ l0 hl.le 3
  have p4 := pow_le_pow_left₀ l0 hl.le 4
  have p5 := pow_le_pow_left₀ l0 hl.le 5
  have p6 := pow_le_pow_left₀ l0 hl.le 6
  have p7 := pow_le_pow_left₀ l0 hl.le 7
  have p8 := pow_le_pow_left₀ l0 hl.le 8
  norm_num at p2 p3 p4 p5 p6 p7 p8 hu hl
  linarith

/-- Change of variables `t = exp s` in `∫ dt / log t`. -/
lemma integral_inv_log_eq_S114p {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, 1 / log t) = ∫ s in log a..log b, exp s / s := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := log a) (b := log b)
    (f := exp) (f' := exp) (g := fun t => 1 / log t) continuous_exp.continuousOn
    (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
  rw [Real.exp_log ha, Real.exp_log hb] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  simp only [Function.comp, Real.log_exp]
  ring

/-- Pointwise minorant of `exp s / s` from the degree 8 exponential minorant. -/
lemma lo_pt_S114p {s : ℝ} (hs : 0 < s) :
    s⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * s ^ 1 + (1/6 : ℝ) * s ^ 2 + (1/24 : ℝ) * s ^ 3 + (1/120 : ℝ) * s ^ 4 + (1/720 : ℝ) * s ^ 5 + (1/5040 : ℝ) * s ^ 6 + (1/40320 : ℝ) * s ^ 7) ≤ exp s / s := by
  have hE := Real.sum_le_exp_of_nonneg hs.le 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hE
  push_cast at hE
  rw [le_div_iff₀ hs]
  have e : (s⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * s ^ 1 + (1/6 : ℝ) * s ^ 2 + (1/24 : ℝ) * s ^ 3 + (1/120 : ℝ) * s ^ 4 + (1/720 : ℝ) * s ^ 5 + (1/5040 : ℝ) * s ^ 6 + (1/40320 : ℝ) * s ^ 7)) * s = 1 + ((1 : ℝ) + (1/2 : ℝ) * s ^ 1 + (1/6 : ℝ) * s ^ 2 + (1/24 : ℝ) * s ^ 3 + (1/120 : ℝ) * s ^ 4 + (1/720 : ℝ) * s ^ 5 + (1/5040 : ℝ) * s ^ 6 + (1/40320 : ℝ) * s ^ 7) * s := by
    field_simp
  rw [e]
  nlinarith [hE]

/-- Pointwise majorant of `exp s / s` on `(0, 2]`, from `exp s = exp (s / 2) ^ 2`. -/
lemma hi_pt_S114p {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) :
    exp s / s ≤ s⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * s ^ 1 + (1/6 : ℝ) * s ^ 2 + (1/24 : ℝ) * s ^ 3 + (1/120 : ℝ) * s ^ 4 + (193/138240 : ℝ) * s ^ 5 + (11/55296 : ℝ) * s ^ 6 + (53/2211840 : ℝ) * s ^ 7 + (1/414720 : ℝ) * s ^ 8 + (53/265420800 : ℝ) * s ^ 9 + (7/530841600 : ℝ) * s ^ 10 + (49/76441190400 : ℝ) * s ^ 11) := by
  have hB := Real.exp_bound' (x := s / 2) (by positivity) (by linarith) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hB
  push_cast at hB
  have hsq : exp s = exp (s / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h2 := pow_le_pow_left₀ (Real.exp_pos (s / 2)).le hB 2
  rw [div_le_iff₀ hs, hsq]
  have e : (s⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * s ^ 1 + (1/6 : ℝ) * s ^ 2 + (1/24 : ℝ) * s ^ 3 + (1/120 : ℝ) * s ^ 4 + (193/138240 : ℝ) * s ^ 5 + (11/55296 : ℝ) * s ^ 6 + (53/2211840 : ℝ) * s ^ 7 + (1/414720 : ℝ) * s ^ 8 + (53/265420800 : ℝ) * s ^ 9 + (7/530841600 : ℝ) * s ^ 10 + (49/76441190400 : ℝ) * s ^ 11)) * s = 1 + ((1 : ℝ) + (1/2 : ℝ) * s ^ 1 + (1/6 : ℝ) * s ^ 2 + (1/24 : ℝ) * s ^ 3 + (1/120 : ℝ) * s ^ 4 + (193/138240 : ℝ) * s ^ 5 + (11/55296 : ℝ) * s ^ 6 + (53/2211840 : ℝ) * s ^ 7 + (1/414720 : ℝ) * s ^ 8 + (53/265420800 : ℝ) * s ^ 9 + (7/530841600 : ℝ) * s ^ 10 + (49/76441190400 : ℝ) * s ^ 11) * s := by
    field_simp
  rw [e]
  nlinarith [h2]

/-- Lower bound for `∫ exp s / s` on `[a, b] ⊂ (0, ∞)` by an explicit antiderivative. -/
lemma int_lo_S114p {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (log b + ((1 : ℝ) * b ^ 1 + (1/4 : ℝ) * b ^ 2 + (1/18 : ℝ) * b ^ 3 + (1/96 : ℝ) * b ^ 4 + (1/600 : ℝ) * b ^ 5 + (1/4320 : ℝ) * b ^ 6 + (1/35280 : ℝ) * b ^ 7 + (1/322560 : ℝ) * b ^ 8)) - (log a + ((1 : ℝ) * a ^ 1 + (1/4 : ℝ) * a ^ 2 + (1/18 : ℝ) * a ^ 3 + (1/96 : ℝ) * a ^ 4 + (1/600 : ℝ) * a ^ 5 + (1/4320 : ℝ) * a ^ 6 + (1/35280 : ℝ) * a ^ 7 + (1/322560 : ℝ) * a ^ 8))
      ≤ ∫ s in a..b, exp s / s := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hD : ∀ x ∈ uIcc a b, HasDerivAt (fun x => log x + ((1 : ℝ) * x ^ 1 + (1/4 : ℝ) * x ^ 2 + (1/18 : ℝ) * x ^ 3 + (1/96 : ℝ) * x ^ 4 + (1/600 : ℝ) * x ^ 5 + (1/4320 : ℝ) * x ^ 6 + (1/35280 : ℝ) * x ^ 7 + (1/322560 : ℝ) * x ^ 8))
      (x⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * x ^ 1 + (1/6 : ℝ) * x ^ 2 + (1/24 : ℝ) * x ^ 3 + (1/120 : ℝ) * x ^ 4 + (1/720 : ℝ) * x ^ 5 + (1/5040 : ℝ) * x ^ 6 + (1/40320 : ℝ) * x ^ 7)) x := by
    intro x hx
    have h := (Real.hasDerivAt_log (hpos x hx).ne').add (((((((((hasDerivAt_pow 1 x).const_mul (1 : ℝ)).add ((hasDerivAt_pow 2 x).const_mul (1/4 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (1/18 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (1/96 : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (1/600 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (1/4320 : ℝ))).add ((hasDerivAt_pow 7 x).const_mul (1/35280 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (1/322560 : ℝ)))
    exact h.congr_deriv (by push_cast; ring)
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * x ^ 1 + (1/6 : ℝ) * x ^ 2 + (1/24 : ℝ) * x ^ 3 + (1/120 : ℝ) * x ^ 4 + (1/720 : ℝ) * x ^ 5 + (1/5040 : ℝ) * x ^ 6 + (1/40320 : ℝ) * x ^ 7)) (uIcc a b) := by
    apply ContinuousOn.add
    · exact continuousOn_inv₀.mono (fun x hx => (hpos x hx).ne')
    · exact (by fun_prop : Continuous (fun x : ℝ => (1 : ℝ) + (1/2 : ℝ) * x ^ 1 + (1/6 : ℝ) * x ^ 2 + (1/24 : ℝ) * x ^ 3 + (1/120 : ℝ) * x ^ 4 + (1/720 : ℝ) * x ^ 5 + (1/5040 : ℝ) * x ^ 6 + (1/40320 : ℝ) * x ^ 7)).continuousOn
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable
  have hf : IntervalIntegrable (fun s : ℝ => exp s / s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact continuous_exp.continuousOn.div continuousOn_id (fun x hx => (hpos x hx).ne')
  have hm := intervalIntegral.integral_mono_on hab hcont.intervalIntegrable hf
    (fun x hx => lo_pt_S114p (lt_of_lt_of_le ha hx.1))
  rw [hI] at hm
  exact hm

/-- Upper bound for `∫ exp s / s` on `[a, b] ⊂ (0, 2]` by an explicit antiderivative. -/
lemma int_hi_S114p {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ s in a..b, exp s / s)
      ≤ (log b + ((1 : ℝ) * b ^ 1 + (1/4 : ℝ) * b ^ 2 + (1/18 : ℝ) * b ^ 3 + (1/96 : ℝ) * b ^ 4 + (1/600 : ℝ) * b ^ 5 + (193/829440 : ℝ) * b ^ 6 + (11/387072 : ℝ) * b ^ 7 + (53/17694720 : ℝ) * b ^ 8 + (1/3732480 : ℝ) * b ^ 9 + (53/2654208000 : ℝ) * b ^ 10 + (7/5839257600 : ℝ) * b ^ 11 + (49/917294284800 : ℝ) * b ^ 12)) - (log a + ((1 : ℝ) * a ^ 1 + (1/4 : ℝ) * a ^ 2 + (1/18 : ℝ) * a ^ 3 + (1/96 : ℝ) * a ^ 4 + (1/600 : ℝ) * a ^ 5 + (193/829440 : ℝ) * a ^ 6 + (11/387072 : ℝ) * a ^ 7 + (53/17694720 : ℝ) * a ^ 8 + (1/3732480 : ℝ) * a ^ 9 + (53/2654208000 : ℝ) * a ^ 10 + (7/5839257600 : ℝ) * a ^ 11 + (49/917294284800 : ℝ) * a ^ 12)) := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hD : ∀ x ∈ uIcc a b, HasDerivAt (fun x => log x + ((1 : ℝ) * x ^ 1 + (1/4 : ℝ) * x ^ 2 + (1/18 : ℝ) * x ^ 3 + (1/96 : ℝ) * x ^ 4 + (1/600 : ℝ) * x ^ 5 + (193/829440 : ℝ) * x ^ 6 + (11/387072 : ℝ) * x ^ 7 + (53/17694720 : ℝ) * x ^ 8 + (1/3732480 : ℝ) * x ^ 9 + (53/2654208000 : ℝ) * x ^ 10 + (7/5839257600 : ℝ) * x ^ 11 + (49/917294284800 : ℝ) * x ^ 12))
      (x⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * x ^ 1 + (1/6 : ℝ) * x ^ 2 + (1/24 : ℝ) * x ^ 3 + (1/120 : ℝ) * x ^ 4 + (193/138240 : ℝ) * x ^ 5 + (11/55296 : ℝ) * x ^ 6 + (53/2211840 : ℝ) * x ^ 7 + (1/414720 : ℝ) * x ^ 8 + (53/265420800 : ℝ) * x ^ 9 + (7/530841600 : ℝ) * x ^ 10 + (49/76441190400 : ℝ) * x ^ 11)) x := by
    intro x hx
    have h := (Real.hasDerivAt_log (hpos x hx).ne').add (((((((((((((hasDerivAt_pow 1 x).const_mul (1 : ℝ)).add ((hasDerivAt_pow 2 x).const_mul (1/4 : ℝ))).add ((hasDerivAt_pow 3 x).const_mul (1/18 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (1/96 : ℝ))).add ((hasDerivAt_pow 5 x).const_mul (1/600 : ℝ))).add ((hasDerivAt_pow 6 x).const_mul (193/829440 : ℝ))).add ((hasDerivAt_pow 7 x).const_mul (11/387072 : ℝ))).add ((hasDerivAt_pow 8 x).const_mul (53/17694720 : ℝ))).add ((hasDerivAt_pow 9 x).const_mul (1/3732480 : ℝ))).add ((hasDerivAt_pow 10 x).const_mul (53/2654208000 : ℝ))).add ((hasDerivAt_pow 11 x).const_mul (7/5839257600 : ℝ))).add ((hasDerivAt_pow 12 x).const_mul (49/917294284800 : ℝ)))
    exact h.congr_deriv (by push_cast; ring)
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹ + ((1 : ℝ) + (1/2 : ℝ) * x ^ 1 + (1/6 : ℝ) * x ^ 2 + (1/24 : ℝ) * x ^ 3 + (1/120 : ℝ) * x ^ 4 + (193/138240 : ℝ) * x ^ 5 + (11/55296 : ℝ) * x ^ 6 + (53/2211840 : ℝ) * x ^ 7 + (1/414720 : ℝ) * x ^ 8 + (53/265420800 : ℝ) * x ^ 9 + (7/530841600 : ℝ) * x ^ 10 + (49/76441190400 : ℝ) * x ^ 11)) (uIcc a b) := by
    apply ContinuousOn.add
    · exact continuousOn_inv₀.mono (fun x hx => (hpos x hx).ne')
    · exact (by fun_prop : Continuous (fun x : ℝ => (1 : ℝ) + (1/2 : ℝ) * x ^ 1 + (1/6 : ℝ) * x ^ 2 + (1/24 : ℝ) * x ^ 3 + (1/120 : ℝ) * x ^ 4 + (193/138240 : ℝ) * x ^ 5 + (11/55296 : ℝ) * x ^ 6 + (53/2211840 : ℝ) * x ^ 7 + (1/414720 : ℝ) * x ^ 8 + (53/265420800 : ℝ) * x ^ 9 + (7/530841600 : ℝ) * x ^ 10 + (49/76441190400 : ℝ) * x ^ 11)).continuousOn
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable
  have hf : IntervalIntegrable (fun s : ℝ => exp s / s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact continuous_exp.continuousOn.div continuousOn_id (fun x hx => (hpos x hx).ne')
  have hm := intervalIntegral.integral_mono_on hab hf hcont.intervalIntegrable
    (fun x hx => hi_pt_S114p (lt_of_lt_of_le ha hx.1) (le_trans hx.2 hb))
  rw [hI] at hm
  exact hm

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_2^4 dt / log t`. EASY.
True value `1.9224213149`. -/
theorem piece_2_4 : 1.9223 ≤ (∫ t in (2 : ℝ)..4, 1 / log t) ∧
    (∫ t in (2 : ℝ)..4, 1 / log t) ≤ 1.9225 := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  norm_num at hl hu
  have hA : 0 < log 2 := by linarith
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog : log (2 * log 2) - log (log 2) = log 2 := by
    rw [Real.log_mul (by norm_num) hA.ne']; ring
  rw [integral_inv_log_eq_S114p (by norm_num) (by norm_num), h4]
  have hL := int_lo_S114p hA (by linarith : log 2 ≤ 2 * log 2)
  have hH := int_hi_S114p hA (by linarith : log 2 ≤ 2 * log 2) (by linarith)
  have eL : (log (2 * log 2) + ((1 : ℝ) * (2 * log 2) ^ 1 + (1/4 : ℝ) * (2 * log 2) ^ 2 + (1/18 : ℝ) * (2 * log 2) ^ 3 + (1/96 : ℝ) * (2 * log 2) ^ 4 + (1/600 : ℝ) * (2 * log 2) ^ 5 + (1/4320 : ℝ) * (2 * log 2) ^ 6 + (1/35280 : ℝ) * (2 * log 2) ^ 7 + (1/322560 : ℝ) * (2 * log 2) ^ 8)) - (log (log 2) + ((1 : ℝ) * log 2 ^ 1 + (1/4 : ℝ) * log 2 ^ 2 + (1/18 : ℝ) * log 2 ^ 3 + (1/96 : ℝ) * log 2 ^ 4 + (1/600 : ℝ) * log 2 ^ 5 + (1/4320 : ℝ) * log 2 ^ 6 + (1/35280 : ℝ) * log 2 ^ 7 + (1/322560 : ℝ) * log 2 ^ 8))
      = log 2 + ((1 : ℝ) * log 2 ^ 1 + (3/4 : ℝ) * log 2 ^ 2 + (7/18 : ℝ) * log 2 ^ 3 + (5/32 : ℝ) * log 2 ^ 4 + (31/600 : ℝ) * log 2 ^ 5 + (7/480 : ℝ) * log 2 ^ 6 + (127/35280 : ℝ) * log 2 ^ 7 + (17/21504 : ℝ) * log 2 ^ 8) := by linear_combination hlog
  have eH : (log (2 * log 2) + ((1 : ℝ) * (2 * log 2) ^ 1 + (1/4 : ℝ) * (2 * log 2) ^ 2 + (1/18 : ℝ) * (2 * log 2) ^ 3 + (1/96 : ℝ) * (2 * log 2) ^ 4 + (1/600 : ℝ) * (2 * log 2) ^ 5 + (193/829440 : ℝ) * (2 * log 2) ^ 6 + (11/387072 : ℝ) * (2 * log 2) ^ 7 + (53/17694720 : ℝ) * (2 * log 2) ^ 8 + (1/3732480 : ℝ) * (2 * log 2) ^ 9 + (53/2654208000 : ℝ) * (2 * log 2) ^ 10 + (7/5839257600 : ℝ) * (2 * log 2) ^ 11 + (49/917294284800 : ℝ) * (2 * log 2) ^ 12)) - (log (log 2) + ((1 : ℝ) * log 2 ^ 1 + (1/4 : ℝ) * log 2 ^ 2 + (1/18 : ℝ) * log 2 ^ 3 + (1/96 : ℝ) * log 2 ^ 4 + (1/600 : ℝ) * log 2 ^ 5 + (193/829440 : ℝ) * log 2 ^ 6 + (11/387072 : ℝ) * log 2 ^ 7 + (53/17694720 : ℝ) * log 2 ^ 8 + (1/3732480 : ℝ) * log 2 ^ 9 + (53/2654208000 : ℝ) * log 2 ^ 10 + (7/5839257600 : ℝ) * log 2 ^ 11 + (49/917294284800 : ℝ) * log 2 ^ 12))
      = log 2 + ((1 : ℝ) * log 2 ^ 1 + (3/4 : ℝ) * log 2 ^ 2 + (7/18 : ℝ) * log 2 ^ 3 + (5/32 : ℝ) * log 2 ^ 4 + (31/600 : ℝ) * log 2 ^ 5 + (1351/92160 : ℝ) * log 2 ^ 6 + (1397/387072 : ℝ) * log 2 ^ 7 + (901/1179648 : ℝ) * log 2 ^ 8 + (511/3732480 : ℝ) * log 2 ^ 9 + (18073/884736000 : ℝ) * log 2 ^ 10 + (14329/5839257600 : ℝ) * log 2 ^ 11 + (4459/20384317440 : ℝ) * log 2 ^ 12) := by linear_combination hlog
  rw [eL] at hL
  rw [eH] at hH
  have l0 : (0 : ℝ) ≤ 6931471803 / 10000000000 := by norm_num
  have p2 := pow_le_pow_left₀ l0 hl.le 2
  have q2 := pow_le_pow_left₀ hA.le hu.le 2
  have p3 := pow_le_pow_left₀ l0 hl.le 3
  have q3 := pow_le_pow_left₀ hA.le hu.le 3
  have p4 := pow_le_pow_left₀ l0 hl.le 4
  have q4 := pow_le_pow_left₀ hA.le hu.le 4
  have p5 := pow_le_pow_left₀ l0 hl.le 5
  have q5 := pow_le_pow_left₀ hA.le hu.le 5
  have p6 := pow_le_pow_left₀ l0 hl.le 6
  have q6 := pow_le_pow_left₀ hA.le hu.le 6
  have p7 := pow_le_pow_left₀ l0 hl.le 7
  have q7 := pow_le_pow_left₀ hA.le hu.le 7
  have p8 := pow_le_pow_left₀ l0 hl.le 8
  have q8 := pow_le_pow_left₀ hA.le hu.le 8
  have p9 := pow_le_pow_left₀ l0 hl.le 9
  have q9 := pow_le_pow_left₀ hA.le hu.le 9
  have p10 := pow_le_pow_left₀ l0 hl.le 10
  have q10 := pow_le_pow_left₀ hA.le hu.le 10
  have p11 := pow_le_pow_left₀ l0 hl.le 11
  have q11 := pow_le_pow_left₀ hA.le hu.le 11
  have p12 := pow_le_pow_left₀ l0 hl.le 12
  have q12 := pow_le_pow_left₀ hA.le hu.le 12
  norm_num at p2 q2 p3 q3 p4 q4 p5 q5 p6 q6 p7 q7 p8 q8 p9 q9 p10 q10 p11 q11 p12 q12
  constructor <;> linarith

lemma exp_upper_S114p {u : ℝ} (hu : 0 ≤ u) {n : ℕ} (hn : u / (n.succ : ℝ) ≤ 1 / 2) :
    exp u ≤ (∑ m ∈ Finset.range n, u ^ m / m.factorial) + u ^ n / n.factorial * 2 := by
  have h := Complex.exp_bound' (x := (u : ℂ)) (n := n)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]; exact hn)
  have e : Complex.exp (u : ℂ) - ∑ m ∈ Finset.range n, (u : ℂ) ^ m / (m.factorial : ℂ)
      = ((exp u - ∑ m ∈ Finset.range n, u ^ m / m.factorial : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu] at h
  have := (abs_le.mp h).2
  linarith

lemma G_hasDerivAt_S114p (N : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x => log (log x) +
        ∑ k ∈ Finset.range N, (log x) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)))
      ((∑ m ∈ Finset.range (N + 1), (log t) ^ m / m.factorial) / (t * log t)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : 0 < log t := Real.log_pos ht
  have hL : HasDerivAt log t⁻¹ t := Real.hasDerivAt_log ht0
  have h1 : HasDerivAt (fun x => log (log x)) ((log t)⁻¹ * t⁻¹) t :=
    (Real.hasDerivAt_log hl.ne').comp t hL
  have h2 : HasDerivAt (fun x => ∑ k ∈ Finset.range N,
      (log x) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)))
      (∑ k ∈ Finset.range N, ((↑(k + 1) : ℝ) * (log t) ^ k * t⁻¹) /
        ((k + 1) * ((k + 1).factorial : ℝ))) t := by
    apply HasDerivAt.fun_sum
    intro k _
    have := (hL.pow (k + 1)).div_const ((k + 1) * ((k + 1).factorial : ℝ))
    simpa using this
  refine (h1.add h2).congr_deriv ?_
  rw [Finset.sum_range_succ', add_div, Finset.sum_div]
  have hs : ∀ k ∈ Finset.range N, ((↑(k + 1) : ℝ) * (log t) ^ k * t⁻¹) /
        ((k + 1) * ((k + 1).factorial : ℝ)) =
      (log t) ^ (k + 1) / ((k + 1).factorial : ℝ) / (t * log t) := by
    intro k _
    have hf : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hs]
  field_simp
  ring

/-- Reusable: for `1 < a ≤ b`, `log b ≤ U`, `U / (N + 2) ≤ 1 / 2`, with
`G x = log (log x) + ∑_{k < N} (log x)^(k+1) / ((k+1) (k+1)!)`:
`G b - G a ≤ ∫_a^b dt / log t ≤ G b - G a + (b - a) * (2 U^N / ((N+1)! a))`. -/
lemma li_piece_S114p (N : ℕ) {a b U : ℝ} (ha : 1 < a) (hab : a ≤ b) (hU : log b ≤ U)
    (hUN : U / ((N + 1 : ℕ).succ : ℝ) ≤ 1 / 2) :
    ((log (log b) + ∑ k ∈ Finset.range N, (log b) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)))
      - (log (log a) + ∑ k ∈ Finset.range N,
          (log a) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))))
      ≤ ∫ t in a..b, 1 / log t ∧
    ∫ t in a..b, 1 / log t ≤
    ((log (log b) + ∑ k ∈ Finset.range N, (log b) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)))
      - (log (log a) + ∑ k ∈ Finset.range N,
          (log a) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))))
      + (b - a) * (2 * U ^ N / (((N + 1).factorial : ℝ) * a)) := by
  set g : ℝ → ℝ := fun t => (∑ m ∈ Finset.range (N + 1), (log t) ^ m / m.factorial) / (t * log t)
    with hg
  have hpos : ∀ t ∈ Icc a b, 1 < t := fun t ht => lt_of_lt_of_le ha ht.1
  have hcont : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.div
    · apply continuousOn_finsetSum
      intro m _
      apply ContinuousOn.div_const
      apply ContinuousOn.pow
      exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht])
    · apply ContinuousOn.mul continuousOn_id
      exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht])
    · intro t ht
      have h1 := hpos t ht
      exact (mul_pos (by linarith) (Real.log_pos h1)).ne'
  have hgi : IntervalIntegrable g volume a b :=
    (hcont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  have hFTC : ∫ t in a..b, g t =
      ((log (log b) + ∑ k ∈ Finset.range N,
          (log b) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)))
      - (log (log a) + ∑ k ∈ Finset.range N,
          (log a) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)))) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hgi
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact G_hasDerivAt_S114p N (hpos t ht)
  have hfi : IntervalIntegrable (fun t => 1 / log t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht])
    · intro t ht; exact (Real.log_pos (hpos t ht)).ne'
  -- pointwise
  have hpt : ∀ t ∈ Icc a b, g t ≤ 1 / log t ∧
      1 / log t ≤ g t + 2 * U ^ N / (((N + 1).factorial : ℝ) * a) := by
    intro t ht
    have h1 := hpos t ht
    have ht0 : 0 < t := by linarith
    have hu : 0 < log t := Real.log_pos h1
    have hub : log t ≤ U := (Real.log_le_log ht0 ht.2).trans hU
    have het : exp (log t) = t := Real.exp_log ht0
    set u := log t
    set S := ∑ m ∈ Finset.range (N + 1), u ^ m / m.factorial
    have hS : S ≤ t := het ▸ Real.sum_le_exp_of_nonneg hu.le (N + 1)
    have hS2 : t ≤ S + u ^ (N + 1) / ((N + 1).factorial : ℝ) * 2 :=
      het ▸ exp_upper_S114p hu.le (le_trans (by gcongr) hUN)
    have htu : 0 < t * u := mul_pos ht0 hu
    have hgt : g t = S / (t * u) := rfl
    have hf : 0 < ((N + 1).factorial : ℝ) := by positivity
    rw [hgt]
    constructor
    · rw [div_le_div_iff₀ htu hu]; nlinarith
    · have hUu : u ^ N ≤ U ^ N := pow_le_pow_left₀ hu.le hub N
      have hU0 : 0 ≤ U := hu.le.trans hub
      have key : 1 / u ≤ S / (t * u) + 2 * u ^ N / (((N + 1).factorial : ℝ) * t) := by
        rw [show S / (t * u) + 2 * u ^ N / (((N + 1).factorial : ℝ) * t)
            = (S + u ^ (N + 1) / ((N + 1).factorial : ℝ) * 2) / (t * u) by
              field_simp; ring]
        rw [div_le_div_iff₀ hu htu]; nlinarith
      have h3 : 2 * u ^ N / (((N + 1).factorial : ℝ) * t) ≤
          2 * U ^ N / (((N + 1).factorial : ℝ) * a) := by
        apply div_le_div₀ (by positivity) (by linarith) (by positivity)
        exact mul_le_mul_of_nonneg_left ht.1 hf.le
      linarith
  constructor
  · rw [← hFTC]
    exact intervalIntegral.integral_mono_on hab hgi hfi (fun t ht => (hpt t ht).1)
  · have hci : IntervalIntegrable (fun t => g t + 2 * U ^ N / (((N + 1).factorial : ℝ) * a))
        volume a b := hgi.add intervalIntegrable_const
    have := intervalIntegral.integral_mono_on hab hfi hci (fun t ht => (hpt t ht).2)
    rw [intervalIntegral.integral_add hgi intervalIntegrable_const, hFTC,
      intervalIntegral.integral_const, smul_eq_mul] at this
    exact this

/-- The polynomial in `log 2` of the `[4, 8]` piece is monotone. -/
lemma poly48_mono_S114p {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∑ k ∈ Finset.range 16, ((3 : ℝ) ^ (k + 1) - 2 ^ (k + 1)) * x ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤
    ∑ k ∈ Finset.range 16, ((3 : ℝ) ^ (k + 1) - 2 ^ (k + 1)) * y ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
  apply Finset.sum_le_sum
  intro k _
  have hc : (0 : ℝ) ≤ 3 ^ (k + 1) - 2 ^ (k + 1) := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3) (k + 1)
    linarith
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) hc

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_4^8 dt / log t`. EASY.
True value `2.2861332045`. -/
theorem piece_4_8 : 2.2860 ≤ (∫ t in (4 : ℝ)..8, 1 / log t) ∧
    (∫ t in (4 : ℝ)..8, 1 / log t) ≤ 2.2862 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have h3a := Real.log_three_gt_d9
  have h3b := Real.log_three_lt_d9
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hll : log (log (8 : ℝ)) - log (log 4) = log 3 - log 2 := by
    rw [h8, h4, Real.log_mul (by norm_num) hLpos.ne', Real.log_mul (by norm_num) hLpos.ne']
    ring
  have hsum : (∑ k ∈ Finset.range 16,
        (log (8 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 16, (log (4 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 16, ((3 : ℝ) ^ (k + 1) - 2 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [h8, h4, mul_pow, mul_pow]
    ring
  have hP1 := poly48_mono_S114p (by norm_num) hL1.le
  have hP2 := poly48_mono_S114p hLpos.le hL2.le
  have hv1 : (2.2860 : ℝ) - 1.0986122885 + 0.6931471808 + 0.00001 ≤
      ∑ k ∈ Finset.range 16, ((3 : ℝ) ^ (k + 1) - 2 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 16, ((3 : ℝ) ^ (k + 1) - 2 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (2.2862 : ℝ) - 1.0986122888 + 0.6931471803 - 0.00001 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((8 : ℝ) - 4) * (2 * (2.08 : ℝ) ^ 16 / (((16 + 1).factorial : ℝ) * 4)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (8 : ℝ) ≤ 2.08 := by rw [h8]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 16 (a := 4) (b := 8) (U := 2.08) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- Monotonicity in `x` of `∑ (p^(k+1) - q^(k+1)) x^(k+1) / ((k+1) (k+1)!)` for `0 ≤ q ≤ p`. -/
lemma polyPQ_mono_S114p8_16 (N : ℕ) {p q x y : ℝ} (hq : 0 ≤ q) (hpq : q ≤ p) (hx : 0 ≤ x)
    (hxy : x ≤ y) :
    ∑ k ∈ Finset.range N, (p ^ (k + 1) - q ^ (k + 1)) * x ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤
    ∑ k ∈ Finset.range N, (p ^ (k + 1) - q ^ (k + 1)) * y ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
  apply Finset.sum_le_sum
  intro k _
  have hc : (0 : ℝ) ≤ p ^ (k + 1) - q ^ (k + 1) := by
    have := pow_le_pow_left₀ hq hpq (k + 1)
    linarith
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) hc

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_8^16 dt / log t`. EASY.
True value `3.2659981642`. -/
theorem piece_8_16 : 3.2659 ≤ (∫ t in (8 : ℝ)..16, 1 / log t) ∧
    (∫ t in (8 : ℝ)..16, 1 / log t) ≤ 3.2661 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have ha : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hll : log (log (16 : ℝ)) - log (log 8) = log 4 - log 3 := by
    rw [hb, ha, Real.log_mul (by norm_num) hLpos.ne', Real.log_mul (by norm_num) hLpos.ne']
    ring
  have h3a := Real.log_three_gt_d9
  have h3b := Real.log_three_lt_d9
  have h4' : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hLL1 : (0.2876820715 : ℝ) ≤ log 4 - log 3 := by linarith
  have hLL2 : log 4 - log 3 ≤ (0.2876820735 : ℝ) := by linarith
  have hsum : (∑ k ∈ Finset.range 16,
        (log (16 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 16, (log (8 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 16, ((4 : ℝ) ^ (k + 1) - 3 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyPQ_mono_S114p8_16 16 (p := 4) (q := 3) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyPQ_mono_S114p8_16 16 (p := 4) (q := 3) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (3.2659 : ℝ) - (0.2876820715 : ℝ) + 0.00001 ≤
      ∑ k ∈ Finset.range 16, ((4 : ℝ) ^ (k + 1) - 3 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 16, ((4 : ℝ) ^ (k + 1) - 3 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (3.2661 : ℝ) - (0.2876820735 : ℝ) - 0.00001 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((16 : ℝ) - 8) * (2 * (2.78 : ℝ) ^ 16 / (((16 + 1).factorial : ℝ) * 8)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (16 : ℝ) ≤ 2.78 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 16 (a := 8) (b := 16) (U := 2.78) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_16^32 dt / log t`. EASY.
True value `5.0853757134`. -/
theorem piece_16_32 : 5.0853 ≤ (∫ t in (16 : ℝ)..32, 1 / log t) ∧
    (∫ t in (16 : ℝ)..32, 1 / log t) ≤ 5.0855 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (32 : ℝ) = 5 * log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have ha : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hll : log (log (32 : ℝ)) - log (log 16) = log 5 - log 4 := by
    rw [hb, ha, Real.log_mul (by norm_num) hLpos.ne', Real.log_mul (by norm_num) hLpos.ne']
    ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 / 5 : ℝ))
    (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at hser
  have hs : (∑ i ∈ Finset.range 8, (1 / 5 : ℝ) ^ (i + 1) / (i + 1)) = 14643791 / 65625000 := by
    norm_num [Finset.sum_range_succ]
  have hr : (1 / 5 : ℝ) ^ (8 + 1) / (1 - 1 / 5) = 1 / 1562500 := by norm_num
  rw [hs, hr, show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num,
    Real.log_div (by norm_num) (by norm_num)] at hser
  obtain ⟨hs1, hs2⟩ := abs_le.mp hser
  have hLL1 : (0.2231420 : ℝ) ≤ log 5 - log 4 := by linarith
  have hLL2 : log 5 - log 4 ≤ (0.2231450 : ℝ) := by linarith
  have hsum : (∑ k ∈ Finset.range 18,
        (log (32 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 18, (log (16 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 18, ((5 : ℝ) ^ (k + 1) - 4 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyPQ_mono_S114p8_16 18 (p := 5) (q := 4) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyPQ_mono_S114p8_16 18 (p := 5) (q := 4) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (5.0853 : ℝ) - (0.2231420 : ℝ) + 0.00001 ≤
      ∑ k ∈ Finset.range 18, ((5 : ℝ) ^ (k + 1) - 4 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 18, ((5 : ℝ) ^ (k + 1) - 4 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (5.0855 : ℝ) - (0.2231450 : ℝ) - 0.00001 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((32 : ℝ) - 16) * (2 * (3.47 : ℝ) ^ 18 / (((18 + 1).factorial : ℝ) * 16)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (32 : ℝ) ≤ 3.47 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 18 (a := 16) (b := 32) (U := 3.47) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_32^64 dt / log t`. EASY.
True value `8.3295761510`. -/
theorem piece_32_64 : 8.3295 ≤ (∫ t in (32 : ℝ)..64, 1 / log t) ∧
    (∫ t in (32 : ℝ)..64, 1 / log t) ≤ 8.3297 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (64 : ℝ) = 6 * log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have ha : log (32 : ℝ) = 5 * log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hll : log (log (64 : ℝ)) - log (log 32) = log 6 - log 5 := by
    rw [hb, ha, Real.log_mul (by norm_num) hLpos.ne', Real.log_mul (by norm_num) hLpos.ne']
    ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 / 6 : ℝ))
    (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)] at hser
  have hs : (∑ i ∈ Finset.range 8, (1 / 6 : ℝ) ^ (i + 1) / (i + 1)) = 85744451 / 470292480 := by
    norm_num [Finset.sum_range_succ]
  have hr : (1 / 6 : ℝ) ^ (8 + 1) / (1 - 1 / 6) = 1 / 8398080 := by norm_num
  rw [hs, hr, show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num,
    Real.log_div (by norm_num) (by norm_num)] at hser
  obtain ⟨hs1, hs2⟩ := abs_le.mp hser
  have hLL1 : (0.1823214 : ℝ) ≤ log 6 - log 5 := by linarith
  have hLL2 : log 6 - log 5 ≤ (0.1823217 : ℝ) := by linarith
  have hsum : (∑ k ∈ Finset.range 20,
        (log (64 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 20, (log (32 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 20, ((6 : ℝ) ^ (k + 1) - 5 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyPQ_mono_S114p8_16 20 (p := 6) (q := 5) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyPQ_mono_S114p8_16 20 (p := 6) (q := 5) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (8.3295 : ℝ) - (0.1823214 : ℝ) + 0.00001 ≤
      ∑ k ∈ Finset.range 20, ((6 : ℝ) ^ (k + 1) - 5 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 20, ((6 : ℝ) ^ (k + 1) - 5 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (8.3297 : ℝ) - (0.1823217 : ℝ) - 0.00001 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((64 : ℝ) - 32) * (2 * (4.16 : ℝ) ^ 20 / (((20 + 1).factorial : ℝ) * 32)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (64 : ℝ) ≤ 4.16 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 20 (a := 32) (b := 64) (U := 4.16) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- Generic monotonicity of the doubling-piece polynomial, `0 ≤ d ≤ c`. -/
lemma polyCD_mono_S114g1 (N : ℕ) {c d x y : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) (hx : 0 ≤ x)
    (hxy : x ≤ y) :
    ∑ k ∈ Finset.range N, (c ^ (k + 1) - d ^ (k + 1)) * x ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤
    ∑ k ∈ Finset.range N, (c ^ (k + 1) - d ^ (k + 1)) * y ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
  apply Finset.sum_le_sum
  intro k _
  have hc : (0 : ℝ) ≤ c ^ (k + 1) - d ^ (k + 1) := by
    have := pow_le_pow_left₀ hd hdc (k + 1)
    linarith
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) hc

/-- Series enclosure of `-log (1 - x)` for `0 ≤ x < 1`. -/
lemma neglog_one_sub_S114g1 {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ -log (1 - x) ∧
    -log (1 - x) ≤ (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  have h2 := abs_le.mp h
  constructor <;> linarith [h2.1, h2.2]

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_64^128 dt / log t`. EASY.
True value `14.107879989`. -/
theorem piece_64_128 : 14.1078 ≤ (∫ t in (64 : ℝ)..128, 1 / log t) ∧
    (∫ t in (64 : ℝ)..128, 1 / log t) ≤ 14.1080 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (128 : ℝ) = 7 * log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have ha : log (64 : ℝ) = 6 * log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hq : (1 : ℝ) - 1 / 7 = log (64 : ℝ) / log 128 := by
    rw [ha, hb]; field_simp; norm_num
  have hll : log (log (128 : ℝ)) - log (log 64) = -log (1 - 1 / 7) := by
    rw [hq, Real.log_div (by rw [ha]; positivity) (by rw [hb]; positivity)]
    ring
  obtain ⟨hq1, hq2⟩ := neglog_one_sub_S114g1 (x := 1 / 7) (by norm_num) (by norm_num) 10
  have hq3 : (0.15415067 : ℝ) ≤ (∑ i ∈ Finset.range 10, (1 / 7 : ℝ) ^ (i + 1) / (i + 1)) -
      (1 / 7 : ℝ) ^ (10 + 1) / (1 - 1 / 7) := by
    norm_num [Finset.sum_range_succ]
  have hq4 : (∑ i ∈ Finset.range 10, (1 / 7 : ℝ) ^ (i + 1) / (i + 1)) +
      (1 / 7 : ℝ) ^ (10 + 1) / (1 - 1 / 7) ≤ 0.15415069 := by
    norm_num [Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range 21,
        (log (128 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 21, (log (64 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 21, ((7 : ℝ) ^ (k + 1) - 6 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyCD_mono_S114g1 21 (c := 7) (d := 6) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyCD_mono_S114g1 21 (c := 7) (d := 6) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (13.95372922 : ℝ) ≤
      ∑ k ∈ Finset.range 21, ((7 : ℝ) ^ (k + 1) - 6 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 21, ((7 : ℝ) ^ (k + 1) - 6 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (13.95372928 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((128 : ℝ) - 64) * (2 * (4.86 : ℝ) ^ 21 / (((21 + 1).factorial : ℝ) * 64)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (128 : ℝ) ≤ 4.86 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 21 (a := 64) (b := 128) (U := 4.86) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_128^256 dt / log t`. EASY.
True value `24.470517021`. -/
theorem piece_128_256 : 24.4704 ≤ (∫ t in (128 : ℝ)..256, 1 / log t) ∧
    (∫ t in (128 : ℝ)..256, 1 / log t) ≤ 24.4706 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (256 : ℝ) = 8 * log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have ha : log (128 : ℝ) = 7 * log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hq : (1 : ℝ) - 1 / 8 = log (128 : ℝ) / log 256 := by
    rw [ha, hb]; field_simp; norm_num
  have hll : log (log (256 : ℝ)) - log (log 128) = -log (1 - 1 / 8) := by
    rw [hq, Real.log_div (by rw [ha]; positivity) (by rw [hb]; positivity)]
    ring
  obtain ⟨hq1, hq2⟩ := neglog_one_sub_S114g1 (x := 1 / 8) (by norm_num) (by norm_num) 10
  have hq3 : (0.13353139 : ℝ) ≤ (∑ i ∈ Finset.range 10, (1 / 8 : ℝ) ^ (i + 1) / (i + 1)) -
      (1 / 8 : ℝ) ^ (10 + 1) / (1 - 1 / 8) := by
    norm_num [Finset.sum_range_succ]
  have hq4 : (∑ i ∈ Finset.range 10, (1 / 8 : ℝ) ^ (i + 1) / (i + 1)) +
      (1 / 8 : ℝ) ^ (10 + 1) / (1 - 1 / 8) ≤ 0.13353140 := by
    norm_num [Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range 23,
        (log (256 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 23, (log (128 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 23, ((8 : ℝ) ^ (k + 1) - 7 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyCD_mono_S114g1 23 (c := 8) (d := 7) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyCD_mono_S114g1 23 (c := 8) (d := 7) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (24.33698552 : ℝ) ≤
      ∑ k ∈ Finset.range 23, ((8 : ℝ) ^ (k + 1) - 7 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 23, ((8 : ℝ) ^ (k + 1) - 7 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (24.33698562 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((256 : ℝ) - 128) * (2 * (5.55 : ℝ) ^ 23 / (((23 + 1).factorial : ℝ) * 128)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (256 : ℝ) ≤ 5.55 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 23 (a := 128) (b := 256) (U := 5.55) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_256^512 dt / log t`. EASY.
True value `43.208051831`. -/
theorem piece_256_512 : 43.2080 ≤ (∫ t in (256 : ℝ)..512, 1 / log t) ∧
    (∫ t in (256 : ℝ)..512, 1 / log t) ≤ 43.2082 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (512 : ℝ) = 9 * log 2 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
  have ha : log (256 : ℝ) = 8 * log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hq : (1 : ℝ) - 1 / 9 = log (256 : ℝ) / log 512 := by
    rw [ha, hb]; field_simp; norm_num
  have hll : log (log (512 : ℝ)) - log (log 256) = -log (1 - 1 / 9) := by
    rw [hq, Real.log_div (by rw [ha]; positivity) (by rw [hb]; positivity)]
    ring
  obtain ⟨hq1, hq2⟩ := neglog_one_sub_S114g1 (x := 1 / 9) (by norm_num) (by norm_num) 10
  have hq3 : (0.11778303 : ℝ) ≤ (∑ i ∈ Finset.range 10, (1 / 9 : ℝ) ^ (i + 1) / (i + 1)) -
      (1 / 9 : ℝ) ^ (10 + 1) / (1 - 1 / 9) := by
    norm_num [Finset.sum_range_succ]
  have hq4 : (∑ i ∈ Finset.range 10, (1 / 9 : ℝ) ^ (i + 1) / (i + 1)) +
      (1 / 9 : ℝ) ^ (10 + 1) / (1 - 1 / 9) ≤ 0.11778304 := by
    norm_num [Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range 25,
        (log (512 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 25, (log (256 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 25, ((9 : ℝ) ^ (k + 1) - 8 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyCD_mono_S114g1 25 (c := 9) (d := 8) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyCD_mono_S114g1 25 (c := 9) (d := 8) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (43.09026864 : ℝ) ≤
      ∑ k ∈ Finset.range 25, ((9 : ℝ) ^ (k + 1) - 8 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 25, ((9 : ℝ) ^ (k + 1) - 8 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (43.09026883 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((512 : ℝ) - 256) * (2 * (6.24 : ℝ) ^ 25 / (((25 + 1).factorial : ℝ) * 256)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (512 : ℝ) ≤ 6.24 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 25 (a := 256) (b := 512) (U := 6.24) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- Generic monotonicity of the doubling-piece polynomial, `0 ≤ d ≤ c`. -/
lemma polyCD_mono_S114_512_1024 (N : ℕ) {c d x y : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) (hx : 0 ≤ x)
    (hxy : x ≤ y) :
    ∑ k ∈ Finset.range N, (c ^ (k + 1) - d ^ (k + 1)) * x ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤
    ∑ k ∈ Finset.range N, (c ^ (k + 1) - d ^ (k + 1)) * y ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
  apply Finset.sum_le_sum
  intro k _
  have hc : (0 : ℝ) ≤ c ^ (k + 1) - d ^ (k + 1) := by
    have := pow_le_pow_left₀ hd hdc (k + 1)
    linarith
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) hc

/-- Series enclosure of `-log (1 - x)` for `0 ≤ x < 1`. -/
lemma neglog_one_sub_S114_512_1024 {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ -log (1 - x) ∧
    -log (1 - x) ≤ (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0] at h
  have h2 := abs_le.mp h
  constructor <;> linarith [h2.1, h2.2]

/-- Monotonicity of the li series sum `∑ x^(k+1) / ((k+1) (k+1)!)` for `0 ≤ x`. -/
lemma liS_mono_S114_512_1024 (N : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∑ k ∈ Finset.range N, x ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)) ≤
    ∑ k ∈ Finset.range N, y ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)) := by
  apply Finset.sum_le_sum
  intro k _
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ hx hxy _

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_512^1024 dt / log t`. EASY.
True value `77.356922513`. -/
theorem piece_512_1024 : 77.3568 ≤ (∫ t in (512 : ℝ)..1024, 1 / log t) ∧
    (∫ t in (512 : ℝ)..1024, 1 / log t) ≤ 77.3570 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (1024 : ℝ) = 10 * log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have ha : log (512 : ℝ) = 9 * log 2 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hq : (1 : ℝ) - 1 / 10 = log (512 : ℝ) / log 1024 := by
    rw [ha, hb]; field_simp; norm_num
  have hll : log (log (1024 : ℝ)) - log (log 512) = -log (1 - 1 / 10) := by
    rw [hq, Real.log_div (by rw [ha]; positivity) (by rw [hb]; positivity)]
    ring
  obtain ⟨hq1, hq2⟩ := neglog_one_sub_S114_512_1024 (x := 1 / 10) (by norm_num) (by norm_num) 10
  have hq3 : (0.10536051 : ℝ) ≤ (∑ i ∈ Finset.range 10, (1 / 10 : ℝ) ^ (i + 1) / (i + 1)) -
      (1 / 10 : ℝ) ^ (10 + 1) / (1 - 1 / 10) := by
    norm_num [Finset.sum_range_succ]
  have hq4 : (∑ i ∈ Finset.range 10, (1 / 10 : ℝ) ^ (i + 1) / (i + 1)) +
      (1 / 10 : ℝ) ^ (10 + 1) / (1 - 1 / 10) ≤ 0.10536052 := by
    norm_num [Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range 27,
        (log (1024 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 27, (log (512 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 27, ((10 : ℝ) ^ (k + 1) - 9 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyCD_mono_S114_512_1024 27 (c := 10) (d := 9) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyCD_mono_S114_512_1024 27 (c := 10) (d := 9) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (77.25156175 : ℝ) ≤
      ∑ k ∈ Finset.range 27, ((10 : ℝ) ^ (k + 1) - 9 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 27, ((10 : ℝ) ^ (k + 1) - 9 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (77.25156213 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((1024 : ℝ) - 512) * (2 * (6.94 : ℝ) ^ 27 / (((27 + 1).factorial : ℝ) * 512)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (1024 : ℝ) ≤ 6.94 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 27 (a := 512) (b := 1024) (U := 6.94) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_1024^2048 dt / log t`. EASY.
True value `140.03637599`. -/
theorem piece_1024_2048 : 140.0363 ≤ (∫ t in (1024 : ℝ)..2048, 1 / log t) ∧
    (∫ t in (1024 : ℝ)..2048, 1 / log t) ≤ 140.0365 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hb : log (2048 : ℝ) = 11 * log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; norm_num
  have ha : log (1024 : ℝ) = 10 * log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hq : (1 : ℝ) - 1 / 11 = log (1024 : ℝ) / log 2048 := by
    rw [ha, hb]; field_simp; norm_num
  have hll : log (log (2048 : ℝ)) - log (log 1024) = -log (1 - 1 / 11) := by
    rw [hq, Real.log_div (by rw [ha]; positivity) (by rw [hb]; positivity)]
    ring
  obtain ⟨hq1, hq2⟩ := neglog_one_sub_S114_512_1024 (x := 1 / 11) (by norm_num) (by norm_num) 10
  have hq3 : (0.09531017 : ℝ) ≤ (∑ i ∈ Finset.range 10, (1 / 11 : ℝ) ^ (i + 1) / (i + 1)) -
      (1 / 11 : ℝ) ^ (10 + 1) / (1 - 1 / 11) := by
    norm_num [Finset.sum_range_succ]
  have hq4 : (∑ i ∈ Finset.range 10, (1 / 11 : ℝ) ^ (i + 1) / (i + 1)) +
      (1 / 11 : ℝ) ^ (10 + 1) / (1 - 1 / 11) ≤ 0.09531018 := by
    norm_num [Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range 29,
        (log (2048 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) -
      (∑ k ∈ Finset.range 29, (log (1024 : ℝ)) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ))) =
      ∑ k ∈ Finset.range 29, ((11 : ℝ) ^ (k + 1) - 10 ^ (k + 1)) * (log 2) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hb, ha, mul_pow, mul_pow]
    ring
  have hP1 := polyCD_mono_S114_512_1024 29 (c := 11) (d := 10) (by norm_num) (by norm_num)
    (by norm_num) hL1.le
  have hP2 := polyCD_mono_S114_512_1024 29 (c := 11) (d := 10) (by norm_num) (by norm_num)
    hLpos.le hL2.le
  have hv1 : (139.94106538 : ℝ) ≤
      ∑ k ∈ Finset.range 29, ((11 : ℝ) ^ (k + 1) - 10 ^ (k + 1)) * (0.6931471803 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 29, ((11 : ℝ) ^ (k + 1) - 10 ^ (k + 1)) * (0.6931471808 : ℝ) ^ (k + 1) /
        ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (139.94106613 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((2048 : ℝ) - 1024) * (2 * (7.63 : ℝ) ^ 29 / (((29 + 1).factorial : ℝ) * 1024)) ≤ 0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (2048 : ℝ) ≤ 7.63 := by rw [hb]; linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 29 (a := 1024) (b := 2048) (U := 7.63) (by norm_num) (by norm_num) hU
    (by norm_num)
  constructor <;> linarith

/-- PROVED in S114, was a LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_2048^2657 dt / log t`. EASY.
True value `78.482401275`. -/
theorem piece_2048_2657 : 78.4823 ≤ (∫ t in (2048 : ℝ)..2657, 1 / log t) ∧
    (∫ t in (2048 : ℝ)..2657, 1 / log t) ≤ 78.4825 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have ha : log (2048 : ℝ) = 11 * log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < log (2 : ℝ) := by linarith
  have hq : log (2657 : ℝ) - log 2048 = -log (1 - 609 / 2657) := by
    rw [show (1 : ℝ) - 609 / 2657 = 2048 / 2657 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨hq1, hq2⟩ := neglog_one_sub_S114_512_1024 (x := 609 / 2657) (by norm_num) (by norm_num) 14
  have hq3 : (0.2603339592 : ℝ) ≤ (∑ i ∈ Finset.range 14, (609 / 2657 : ℝ) ^ (i + 1) / (i + 1)) -
      (609 / 2657 : ℝ) ^ (14 + 1) / (1 - 609 / 2657) := by
    norm_num [Finset.sum_range_succ]
  have hq4 : (∑ i ∈ Finset.range 14, (609 / 2657 : ℝ) ^ (i + 1) / (i + 1)) +
      (609 / 2657 : ℝ) ^ (14 + 1) / (1 - 609 / 2657) ≤ 0.2603339600 := by
    norm_num [Finset.sum_range_succ]
  have hLlo : (7.8849529425 : ℝ) ≤ log 2657 := by linarith
  have hLhi : log (2657 : ℝ) ≤ 7.884952949 := by linarith
  have hLp : 0 < log (2657 : ℝ) := by linarith
  have hll : log (log (2657 : ℝ)) - log (log 2048) =
      -log (1 - (log 2657 - log 2048) / log 2657) := by
    rw [show (1 : ℝ) - (log 2657 - log 2048) / log 2657 = log 2048 / log 2657 by
        rw [sub_div, div_self hLp.ne']; ring,
      Real.log_div (by rw [ha]; positivity) hLp.ne']
    ring
  have hx1 : (0.033016 : ℝ) ≤ (log 2657 - log 2048) / log 2657 := by
    rw [le_div_iff₀ hLp]; linarith
  have hx2 : (log 2657 - log 2048) / log 2657 ≤ (0.033017 : ℝ) := by
    rw [div_le_iff₀ hLp]; linarith
  have hm1 : -log (1 - (0.033016 : ℝ)) ≤ -log (1 - (log 2657 - log 2048) / log 2657) := by
    have := Real.log_le_log (by linarith) (by linarith :
      1 - (log 2657 - log 2048) / log 2657 ≤ 1 - (0.033016 : ℝ))
    linarith
  have hm2 : -log (1 - (log 2657 - log 2048) / log 2657) ≤ -log (1 - (0.033017 : ℝ)) := by
    have := Real.log_le_log (by norm_num) (by linarith :
      1 - (0.033017 : ℝ) ≤ 1 - (log 2657 - log 2048) / log 2657)
    linarith
  obtain ⟨hn1, -⟩ := neglog_one_sub_S114_512_1024 (x := 0.033016) (by norm_num) (by norm_num) 8
  obtain ⟨-, hn2⟩ := neglog_one_sub_S114_512_1024 (x := 0.033017) (by norm_num) (by norm_num) 8
  have hn3 : (0.03357332 : ℝ) ≤ (∑ i ∈ Finset.range 8, (0.033016 : ℝ) ^ (i + 1) / (i + 1)) -
      (0.033016 : ℝ) ^ (8 + 1) / (1 - 0.033016) := by
    norm_num [Finset.sum_range_succ]
  have hn4 : (∑ i ∈ Finset.range 8, (0.033017 : ℝ) ^ (i + 1) / (i + 1)) +
      (0.033017 : ℝ) ^ (8 + 1) / (1 - 0.033017) ≤ 0.03357437 := by
    norm_num [Finset.sum_range_succ]
  have hS1 := liS_mono_S114_512_1024 28 (by norm_num) hLlo
  have hS2 := liS_mono_S114_512_1024 28 (by linarith) hLhi
  have hS3 := liS_mono_S114_512_1024 28 (x := log 2048) (y := 7.6246189888) (by rw [ha]; positivity)
    (by rw [ha]; linarith)
  have hS4 := liS_mono_S114_512_1024 28 (x := 7.6246189833) (y := log 2048) (by norm_num)
    (by rw [ha]; linarith)
  have hv1 : (396.95464340 : ℝ) ≤
      ∑ k ∈ Finset.range 28, (7.8849529425 : ℝ) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv2 : ∑ k ∈ Finset.range 28, (7.884952949 : ℝ) ^ (k + 1) /
      ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (396.95464560 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv3 : ∑ k ∈ Finset.range 28, (7.6246189888 : ℝ) ^ (k + 1) /
      ((k + 1) * ((k + 1).factorial : ℝ)) ≤ (318.50581817 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hv4 : (318.50581669 : ℝ) ≤
      ∑ k ∈ Finset.range 28, (7.6246189833 : ℝ) ^ (k + 1) / ((k + 1) * ((k + 1).factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have herr : ((2657 : ℝ) - 2048) * (2 * (7.89 : ℝ) ^ 28 / (((28 + 1).factorial : ℝ) * 2048)) ≤
      0.000001 := by
    norm_num [Nat.factorial]
  have hU : log (2657 : ℝ) ≤ 7.89 := by linarith
  obtain ⟨lo, hi⟩ := li_piece_S114p 28 (a := 2048) (b := 2657) (U := 7.89) (by norm_num)
    (by norm_num) hU (by norm_num)
  constructor <;> linarith

/-- Schoenfeld 1976 p. 340, `li 2657 ≅ 399.5968`, the exact statement of the LEAF
`SchoenfeldFiniteS70.liPV_2657_encl`. PROVED from the twelve LEAFs above. -/
theorem liPV_2657_encl_S76 : 399.59 ≤ liPV 2657 ∧ liPV 2657 ≤ 399.61 := by
  rw [liPV_eq_add (by norm_num : (2 : ℝ) ≤ 2657)]
  rw [split (b := 4) (by norm_num) (by norm_num) (by norm_num),
    split (a := 4) (b := 8) (by norm_num) (by norm_num) (by norm_num),
    split (a := 8) (b := 16) (by norm_num) (by norm_num) (by norm_num),
    split (a := 16) (b := 32) (by norm_num) (by norm_num) (by norm_num),
    split (a := 32) (b := 64) (by norm_num) (by norm_num) (by norm_num),
    split (a := 64) (b := 128) (by norm_num) (by norm_num) (by norm_num),
    split (a := 128) (b := 256) (by norm_num) (by norm_num) (by norm_num),
    split (a := 256) (b := 512) (by norm_num) (by norm_num) (by norm_num),
    split (a := 512) (b := 1024) (by norm_num) (by norm_num) (by norm_num),
    split (a := 1024) (b := 2048) (by norm_num) (by norm_num) (by norm_num)]
  have h0 := liPV_two_ge
  have h0' := LiTwo.liPV_two_le_1046
  obtain ⟨a1, b1⟩ := piece_2_4
  obtain ⟨a2, b2⟩ := piece_4_8
  obtain ⟨a3, b3⟩ := piece_8_16
  obtain ⟨a4, b4⟩ := piece_16_32
  obtain ⟨a5, b5⟩ := piece_32_64
  obtain ⟨a6, b6⟩ := piece_64_128
  obtain ⟨a7, b7⟩ := piece_128_256
  obtain ⟨a8, b8⟩ := piece_256_512
  obtain ⟨a9, b9⟩ := piece_512_1024
  obtain ⟨a10, b10⟩ := piece_1024_2048
  obtain ⟨a11, b11⟩ := piece_2048_2657
  constructor <;> linarith

end

end LeanLab.BS2022GRH.SchoenfeldLiS76

#print axioms LeanLab.BS2022GRH.SchoenfeldLiS76.split
#print axioms LeanLab.BS2022GRH.SchoenfeldLiS76.liPV_2657_encl_S76
