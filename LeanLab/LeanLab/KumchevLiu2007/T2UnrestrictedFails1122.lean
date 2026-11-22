/-
UNIT P1122-0144 REPAIR, QUESTION Q2. Kumchev and Liu 2007, P0088, arXiv 0801.0130,
page 6 display 22 for j = 2.

Display 22 asserts T_j(beta) << Y_j / (1 + Y |beta|) for |beta| at most 1/2. For j = 2
the sum T2 runs over m in the window from Y^(1/2)/2 to Y^(1/2) with phase m^2 beta.
At beta = 1/3 the phase e(m^2/3) is 1 or e(1/3), so its imaginary part is never
negative, and the positive weight f2 of page 15 leaves no cancellation. Hence
|T2(1/3)| >> 1/log X, while the unrestricted display 22 would force
|T2(1/3)| << Y^(-1/2). This file proves that the unrestricted form of display 22
for T2, with T2 exactly as in Prep1121KLMajorArc, is false. It confirms QUESTION Q2:
display 22 for j = 2 fails at beta of order one, and T2BoundProp keeps only
|beta| at most Y^(-1/2)/4.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc

namespace LeanLab.KumchevLiu2007.Burst1122T2Fails

open Real Complex MeasureTheory Filter Asymptotics LeanLab.KumchevLiu2007 Task556a
open LeanLab.KumchevLiu2007.Prep1121KLMajor
open scoped BigOperators Topology

/-- P0088 page 6 display 22 for j = 2, the phase at beta = 1/3: m^2 mod 3 is 0 or 1,
so the imaginary part of e(m^2/3) is 0 when 3 divides m and sqrt 3 / 2 otherwise. -/
theorem fourier_sq_third_im (m : ℕ) :
    (fourier ((m ^ 2 : ℕ) : ℤ) (((1 / 3 : ℝ)) : AddCircle (1 : ℝ))).im =
      if m % 3 = 0 then 0 else Real.sqrt 3 / 2 := by
  rw [fourier_coe_apply]
  have harg : (2 * (π : ℂ) * Complex.I * (((m ^ 2 : ℕ) : ℤ) : ℂ) * ((1 / 3 : ℝ) : ℂ) /
      ((1 : ℝ) : ℂ)) = ((2 * π * ((m ^ 2 : ℕ) : ℝ) / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I_im]
  have hdm : m ^ 2 = 3 * (m ^ 2 / 3) + m ^ 2 % 3 := (Nat.div_add_mod _ _).symm
  have hr : m ^ 2 % 3 = if m % 3 = 0 then 0 else 1 := by
    rw [Nat.pow_mod]
    have h3 := Nat.mod_lt m (by norm_num : 3 > 0)
    interval_cases (m % 3) <;> simp
  set k := m ^ 2 / 3
  have hcast : ((m ^ 2 : ℕ) : ℝ) = 3 * (k : ℝ) + ((m ^ 2 % 3 : ℕ) : ℝ) := by
    conv_lhs => rw [hdm]
    push_cast; ring
  have hsin : Real.sin (2 * π * ((m ^ 2 : ℕ) : ℝ) / 3) =
      Real.sin (2 * π * ((m ^ 2 % 3 : ℕ) : ℝ) / 3) := by
    rw [hcast, ← Real.sin_add_nat_mul_two_pi (2 * π * ((m ^ 2 % 3 : ℕ) : ℝ) / 3) k]
    congr 1; ring
  rw [hsin, hr]
  split_ifs
  · simp
  · have h1 : 2 * π * (((1 : ℕ)) : ℝ) / 3 = π - π / 3 := by push_cast; ring
    rw [h1, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- P0088 page 6 display 22 for j = 2, at beta = 1/3 every phase e(m^2/3) has
nonnegative imaginary part. -/
theorem fourier_sq_third_im_nonneg (m : ℕ) :
    0 ≤ (fourier ((m ^ 2 : ℕ) : ℤ) (((1 / 3 : ℝ)) : AddCircle (1 : ℝ))).im := by
  rw [fourier_sq_third_im]
  split_ifs
  · exact le_refl _
  · positivity

/-- P0088 page 6 display 22 for j = 2, at beta = 1/3 the phase e(m^2/3) has imaginary
part at least 1/2 when 3 does not divide m. -/
theorem fourier_sq_third_im_ge (m : ℕ) (hm : m % 3 ≠ 0) :
    1 / 2 ≤ (fourier ((m ^ 2 : ℕ) : ℤ) (((1 / 3 : ℝ)) : AddCircle (1 : ℝ))).im := by
  rw [fourier_sq_third_im, ite_eq_right_of_eq_false _ _ (eq_false hm)]
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- P0088 page 15, the weight f2 of T2: when 1 < z0 at most u^(1/2) the integral term is
nonnegative, so f2(u) is at least 1/log u. -/
theorem f2Weight_ge_inv_log {z0 u : ℝ} (hz0 : 1 < z0) (hzu : z0 ≤ Real.sqrt u) :
    1 / Real.log u ≤ f2Weight z0 u := by
  unfold f2Weight
  have hint : 0 ≤ ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) := by
    apply intervalIntegral.integral_nonneg hzu
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hz0 ht.1
    have hs1 : 1 < Real.sqrt u := lt_of_lt_of_le ht1 ht.2
    have hu0 : 0 ≤ u := by
      by_contra h; push Not at h
      rw [Real.sqrt_eq_zero'.mpr h.le] at hs1; linarith
    have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
    have htu : t ≤ u := by nlinarith [ht.2]
    have hut : 1 ≤ u / t := by rw [le_div_iff₀ (by linarith)]; linarith
    apply one_div_nonneg.mpr
    apply mul_nonneg (mul_nonneg (by linarith) (Real.log_nonneg ht1.le))
      (Real.log_nonneg hut)
  linarith

/-- P0088 page 2 display 5, the square root window: once Y^(1/2) is at least 4 it
holds an integer not divisible by 3. -/
theorem exists_squareWindow_not_dvd_three {Y : ℝ} (hs : 4 ≤ Real.sqrt Y) :
    ∃ m ∈ squareWindow Y, m % 3 ≠ 0 := by
  set s := Real.sqrt Y
  set n0 := ⌈s / 2⌉₊
  have hn0lo : s / 2 ≤ (n0 : ℝ) := Nat.le_ceil _
  have hn0hi : (n0 : ℝ) < s / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have mem : ∀ m : ℕ, s / 2 ≤ (m : ℝ) → (m : ℝ) < s → m ∈ squareWindow Y := by
    intro m h1 h2
    unfold squareWindow
    refine Finset.mem_filter.mpr ⟨?_, h1, h2⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.le_floor h2.le
  by_cases h : n0 % 3 = 0
  · refine ⟨n0 + 1, mem _ (by push_cast; linarith) (by push_cast; linarith), ?_⟩
    omega
  · exact ⟨n0, mem _ hn0lo (by linarith), h⟩

/-- P0088 page 6 display 22 for j = 2, the lower bound at beta = 1/3. With
z0 = Y^(1/4) P^(-2) above one, z0^2 at most Y^(1/2)/2 and Y^(1/2) at least 4, every term
of Im T2(1/3) is nonnegative and one term is at least 1/(2 log m1), so
|T2(1/3)| is at least 1/(2M) whenever log Y^(1/2) is at most M. -/
theorem T2_third_norm_lower {Y P M : ℝ}
    (hz : 1 < Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ))
    (hz2 : (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) ^ 2 ≤ Real.sqrt Y / 2)
    (hs : 4 ≤ Real.sqrt Y) (hM : Real.log (Real.sqrt Y) ≤ M) :
    1 / (2 * M) ≤ ‖T2 Y P (1 / 3)‖ := by
  set z0 := Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) with hz0
  have hz0pos : 0 < z0 := by linarith
  -- facts on window members
  have hwin : ∀ m ∈ squareWindow Y, 2 ≤ (m : ℝ) ∧ (m : ℝ) < Real.sqrt Y ∧
      1 / Real.log (m : ℝ) ≤ f2Weight z0 (m : ℝ) := by
    intro m hm
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hm
    have hm2 : 2 ≤ (m : ℝ) := by linarith
    refine ⟨hm2, h2, f2Weight_ge_inv_log hz ?_⟩
    rw [Real.le_sqrt hz0pos.le (by linarith)]
    linarith
  have hterm : ∀ m ∈ squareWindow Y,
      0 ≤ f2Weight z0 (m : ℝ) *
        (fourier ((m ^ 2 : ℕ) : ℤ) (((1 / 3 : ℝ)) : AddCircle (1 : ℝ))).im := by
    intro m hm
    obtain ⟨hm2, _, hw⟩ := hwin m hm
    have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
    have : 0 < 1 / Real.log (m : ℝ) := by positivity
    exact mul_nonneg (by linarith) (fourier_sq_third_im_nonneg m)
  have him : (T2 Y P (1 / 3)).im = ∑ m ∈ squareWindow Y, f2Weight z0 (m : ℝ) *
      (fourier ((m ^ 2 : ℕ) : ℤ) (((1 / 3 : ℝ)) : AddCircle (1 : ℝ))).im := by
    unfold T2
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.im_ofReal_mul]
  obtain ⟨m1, hm1, hm13⟩ := exists_squareWindow_not_dvd_three hs
  obtain ⟨hm12, hm1s, hw1⟩ := hwin m1 hm1
  have hlog1 : 0 < Real.log (m1 : ℝ) := Real.log_pos (by linarith)
  have hlogM : Real.log (m1 : ℝ) ≤ M :=
    (Real.log_le_log (by linarith) hm1s.le).trans hM
  have hMpos : 0 < M := by linarith
  have hsingle := Finset.single_le_sum hterm hm1
  have hge := fourier_sq_third_im_ge m1 hm13
  have hinvM : 1 / M ≤ 1 / Real.log (m1 : ℝ) := one_div_le_one_div_of_le hlog1 hlogM
  have hwpos : 0 ≤ f2Weight z0 (m1 : ℝ) := by
    have : 0 < 1 / Real.log (m1 : ℝ) := by positivity
    linarith
  have hprod : f2Weight z0 (m1 : ℝ) * (1 / 2) ≤ f2Weight z0 (m1 : ℝ) *
      (fourier ((m1 ^ 2 : ℕ) : ℤ) (((1 / 3 : ℝ)) : AddCircle (1 : ℝ))).im :=
    mul_le_mul_of_nonneg_left hge hwpos
  have hnorm : (T2 Y P (1 / 3)).im ≤ ‖T2 Y P (1 / 3)‖ :=
    (le_abs_self _).trans (Complex.abs_im_le_norm _)
  have h2M : 1 / (2 * M) = (1 / M) * (1 / 2) := by field_simp
  rw [h2M]
  calc (1 / M) * (1 / 2) ≤ f2Weight z0 (m1 : ℝ) * (1 / 2) := by linarith
    _ ≤ _ := hprod
    _ ≤ _ := hsingle
    _ = (T2 Y P (1 / 3)).im := him.symm
    _ ≤ _ := hnorm

/-- P0088 page 6 display 22 for j = 2, the asymptotic inputs for B = 1 and eps = 1/4:
for X large, log X is at least 2, (log X)^2 < X^(17/96), 6 C log X < X^(17/48) and
X^(17/48) is at least 4. -/
theorem eventually_large {C : ℝ} (hC : 0 < C) : ∀ᶠ X : ℝ in atTop,
    2 ≤ Real.log X ∧ Real.log X ^ (2 : ℝ) < X ^ (17 / 96 : ℝ) ∧
      6 * C * Real.log X < X ^ (17 / 48 : ℝ) ∧ 4 ≤ X ^ (17 / 48 : ℝ) ∧ 1 ≤ X := by
  have h0 : ∀ᶠ X : ℝ in atTop, 1 ≤ X := eventually_ge_atTop 1
  have h1 : ∀ᶠ X : ℝ in atTop, 2 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  have h2 : ∀ᶠ X : ℝ in atTop, Real.log X ^ (2 : ℝ) < X ^ (17 / 96 : ℝ) := by
    have ho := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 17 / 96)
    filter_upwards [ho.bound (by norm_num : (0 : ℝ) < 1 / 2), h0] with X hX hX1
    have hXs : 0 < X ^ (17 / 96 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hXs] at hX
    linarith [le_abs_self (Real.log X ^ (2 : ℝ))]
  have h3 : ∀ᶠ X : ℝ in atTop, 6 * C * Real.log X < X ^ (17 / 48 : ℝ) := by
    have ho := isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 17 / 48)
    filter_upwards [ho.bound (by positivity : (0 : ℝ) < 1 / (12 * C)), h0] with X hX hX1
    have hXs : 0 < X ^ (17 / 48 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hXs, Real.rpow_one] at hX
    have hl := le_abs_self (Real.log X)
    have h6 : 6 * C * Real.log X ≤ 6 * C * (1 / (12 * C) * X ^ (17 / 48 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hl.trans hX) (by positivity)
    have he : 6 * C * (1 / (12 * C) * X ^ (17 / 48 : ℝ)) = X ^ (17 / 48 : ℝ) / 2 := by
      field_simp; ring
    linarith
  have h4 : ∀ᶠ X : ℝ in atTop, 4 ≤ X ^ (17 / 48 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 17 / 48)).eventually_ge_atTop 4
  filter_upwards [h0, h1, h2, h3, h4] with X a b c d e
  exact ⟨b, c, d, e, a⟩

/-- P0088 page 6 display 22 for j = 2 WITHOUT the restriction |beta| at most Y^(-1/2)/4
is false. At beta = 1/3 with B = 1 and eps = 1/4, |T2(1/3)| is at least 1/(2 log X),
while the unrestricted bound gives at most 3 C Y^(-1/2), and Y^(1/2) = X^(17/48)
outgrows 6 C log X. This confirms QUESTION Q2. -/
theorem T2_unrestricted_display22_fails :
    ¬ (∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ β : ℝ, |β| ≤ 1 / 2 →
        ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤
          C * Real.sqrt (windowY X ε) / (1 + windowY X ε * |β|)) := by
  intro H
  obtain ⟨C, X0, hC, hb⟩ := H 1 one_pos (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨X, ⟨hL2, hz, hcmp, hs4, hX1⟩, hXX0⟩ :=
    ((eventually_large hC).and (eventually_ge_atTop X0)).exists
  have hXpos : 0 < X := by linarith
  have hb' := hb X hXX0 (1 / 3) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [Real.rpow_one, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at hb'
  have hY : windowY X (1 / 4) = X ^ (17 / 24 : ℝ) := by unfold windowY; norm_num
  have hsq : Real.sqrt (windowY X (1 / 4)) = X ^ (17 / 48 : ℝ) := by
    rw [hY, Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]; norm_num
  have hY4 : windowY X (1 / 4) ^ (1 / 4 : ℝ) = X ^ (17 / 96 : ℝ) := by
    rw [hY, ← Real.rpow_mul hXpos.le]; norm_num
  have hYs : windowY X (1 / 4) = (X ^ (17 / 48 : ℝ)) ^ 2 := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; norm_num
  have hss : (X ^ (17 / 96 : ℝ)) ^ 2 = X ^ (17 / 48 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; norm_num
  set L := Real.log X with hLdef
  set s := X ^ (17 / 48 : ℝ) with hsdef
  set w := X ^ (17 / 96 : ℝ) with hwdef
  have hLpos : 0 < L := by linarith
  have hspos : 0 < s := by linarith
  rw [Real.rpow_two] at hz
  have hzp : L ^ (-2 : ℤ) = (L ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  have hL2pos : 0 < L ^ 2 := by positivity
  have hz1 : 1 < windowY X (1 / 4) ^ (1 / 4 : ℝ) * L ^ (-2 : ℤ) := by
    rw [hY4, hzp, ← div_eq_mul_inv, one_lt_div hL2pos]; exact hz
  have hz2 : (windowY X (1 / 4) ^ (1 / 4 : ℝ) * L ^ (-2 : ℤ)) ^ 2 ≤
      Real.sqrt (windowY X (1 / 4)) / 2 := by
    rw [hY4, hzp, hsq, mul_pow, hss, inv_pow]
    have h4 : 4 ≤ L ^ 2 := by nlinarith
    have h16 : 2 ≤ (L ^ 2) ^ 2 := by nlinarith
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hspos.le (by norm_num) h16
  have hM : Real.log (Real.sqrt (windowY X (1 / 4))) ≤ L := by
    rw [hsq, hsdef, Real.log_rpow hXpos]; nlinarith
  have hlow := T2_third_norm_lower hz1 hz2 (by rw [hsq]; exact hs4) hM
  have hup := hlow.trans hb'
  rw [hsq, hYs] at hup
  have hden : 0 < 1 + s ^ 2 * (1 / 3) := by positivity
  rw [div_le_div_iff₀ (by positivity) hden] at hup
  nlinarith [mul_lt_mul_of_pos_right hcmp hspos]

#print axioms fourier_sq_third_im
#print axioms fourier_sq_third_im_nonneg
#print axioms fourier_sq_third_im_ge
#print axioms f2Weight_ge_inv_log
#print axioms exists_squareWindow_not_dvd_three
#print axioms T2_third_norm_lower
#print axioms eventually_large
#print axioms T2_unrestricted_display22_fails

end LeanLab.KumchevLiu2007.Burst1122T2Fails
