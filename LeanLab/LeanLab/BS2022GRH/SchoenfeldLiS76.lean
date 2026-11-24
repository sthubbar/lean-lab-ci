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

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_2^4 dt / log t`. EASY.
True value `1.9224213149`. -/
theorem piece_2_4 : 1.9223 ≤ (∫ t in (2 : ℝ)..4, 1 / log t) ∧
    (∫ t in (2 : ℝ)..4, 1 / log t) ≤ 1.9225 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_4^8 dt / log t`. EASY.
True value `2.2861332045`. -/
theorem piece_4_8 : 2.2860 ≤ (∫ t in (4 : ℝ)..8, 1 / log t) ∧
    (∫ t in (4 : ℝ)..8, 1 / log t) ≤ 2.2862 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_8^16 dt / log t`. EASY.
True value `3.2659981642`. -/
theorem piece_8_16 : 3.2659 ≤ (∫ t in (8 : ℝ)..16, 1 / log t) ∧
    (∫ t in (8 : ℝ)..16, 1 / log t) ≤ 3.2661 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_16^32 dt / log t`. EASY.
True value `5.0853757134`. -/
theorem piece_16_32 : 5.0853 ≤ (∫ t in (16 : ℝ)..32, 1 / log t) ∧
    (∫ t in (16 : ℝ)..32, 1 / log t) ≤ 5.0855 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_32^64 dt / log t`. EASY.
True value `8.3295761510`. -/
theorem piece_32_64 : 8.3295 ≤ (∫ t in (32 : ℝ)..64, 1 / log t) ∧
    (∫ t in (32 : ℝ)..64, 1 / log t) ≤ 8.3297 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_64^128 dt / log t`. EASY.
True value `14.107879989`. -/
theorem piece_64_128 : 14.1078 ≤ (∫ t in (64 : ℝ)..128, 1 / log t) ∧
    (∫ t in (64 : ℝ)..128, 1 / log t) ≤ 14.1080 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_128^256 dt / log t`. EASY.
True value `24.470517021`. -/
theorem piece_128_256 : 24.4704 ≤ (∫ t in (128 : ℝ)..256, 1 / log t) ∧
    (∫ t in (128 : ℝ)..256, 1 / log t) ≤ 24.4706 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_256^512 dt / log t`. EASY.
True value `43.208051831`. -/
theorem piece_256_512 : 43.2080 ≤ (∫ t in (256 : ℝ)..512, 1 / log t) ∧
    (∫ t in (256 : ℝ)..512, 1 / log t) ≤ 43.2082 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_512^1024 dt / log t`. EASY.
True value `77.356922513`. -/
theorem piece_512_1024 : 77.3568 ≤ (∫ t in (512 : ℝ)..1024, 1 / log t) ∧
    (∫ t in (512 : ℝ)..1024, 1 / log t) ≤ 77.3570 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_1024^2048 dt / log t`. EASY.
True value `140.03637599`. -/
theorem piece_1024_2048 : 140.0363 ≤ (∫ t in (1024 : ℝ)..2048, 1 / log t) ∧
    (∫ t in (1024 : ℝ)..2048, 1 / log t) ≤ 140.0365 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_2048^2657 dt / log t`. EASY.
True value `78.482401275`. -/
theorem piece_2048_2657 : 78.4823 ≤ (∫ t in (2048 : ℝ)..2657, 1 / log t) ∧
    (∫ t in (2048 : ℝ)..2657, 1 / log t) ≤ 78.4825 := by
  sorry

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
