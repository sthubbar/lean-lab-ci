/-
P0032 Riesel-Vaughan 1983, Lemma 6, page 55: (4.1) `π(x) > x/log x + 0.9911 x/(log x)²` for
`log x ≥ 17` and (4.2) `π(x) < x/log x + 1.0151 x/(log x)²` for `log x ≥ 300`, from explicit
bounds for Chebyshev's `θ` by partial summation, Mathlib's
`Chebyshev.primeCounting_eq_theta_div_log_add_integral`, as on pages 56 and 57.
Unit U-6733, CLOUD 20261020T2113Z-cloud51, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

CONDITIONAL, counted apart:
* `lemma6ii_of_dusart`: `Lemma6ii`, CONDITIONAL ON `DusartThm52k2`, the lab's cited Dusart 2010
  Theorem 5.2 entry `|θ(x) - x| ≤ 0.01 x/log² x` for `x ≥ 7713133853`, Common/ThetaWindowDusart.
  The paper uses the weaker `θ(x) < x + 0.00822 x/log x` from Rosser-Schoenfeld 1975; the split
  point is `y = e^63`, the head `∫₂^y` is bounded by `π(y) ≤ y + 1`, and the tail by the primitive
  `t/log² t + 2.1 t/log³ t`, whose derivative dominates `1/log² t` once `log t ≥ 63`.
  Coefficient reached about 1.0081 against the paper's 1.0151.
* `lemma6i_of_rs_dusart`: `Lemma6i`, CONDITIONAL ON `RS1975Cor2Thm7`, Rosser-Schoenfeld 1975
  Corollary 2 to Theorem 7 as quoted on page 57, `θ(x) > x - x/(40 log x)` for `x ≥ 678407`,
  and `DusartThm52k2`. Split point `y = e^13.5 ≥ 678407`, head dropped as nonnegative, tail from
  below by the primitive `t/log² t + 1.975 t/log³ t`; at `x` itself Rosser-Schoenfeld is used for
  `17 ≤ log x ≤ 25` and Dusart for `log x > 25`. The paper uses Rosser-Schoenfeld for
  `17 ≤ log x ≤ 35` and its (4.5) for `log x ≥ 32`.
PROVED unconditional helpers: `hasDerivAt_Gprim`, `pi_split`, `head_le`, `head_nonneg`,
`sq_mul_exp_le`, the exponential bounds, and `tail_lower`, `tail_upper` given their θ inputs.
KNOWN mathematics.
-/
import LeanLab.RieselVaughan1983.Lemma15
import LeanLab.Common.ThetaWindowDusart

open Real Chebyshev MeasureTheory Set

noncomputable section
namespace LeanLab.RieselVaughan1983.Lemma6Theta

open LeanLab.RieselVaughan1983 LeanLab.Common.ThetaWindow


/-- The primitive `G_a(t) = t/log² t + a t/log³ t`. -/
def Gprim (a t : ℝ) : ℝ := t / log t ^ 2 + a * t / log t ^ 3

/-- Its derivative `1/log² t + (a - 2)/log³ t - 3a/log⁴ t`. -/
def Gprim' (a t : ℝ) : ℝ := 1 / log t ^ 2 + (a - 2) / log t ^ 3 - 3 * a / log t ^ 4

lemma hasDerivAt_Gprim (a : ℝ) {t : ℝ} (ht : 1 < t) : HasDerivAt (Gprim a) (Gprim' a t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (log_pos ht).ne'
  have h2 := (hasDerivAt_id t).div ((hasDerivAt_log ht0).pow 2) (pow_ne_zero 2 hl)
  have h3 := ((hasDerivAt_id t).const_mul a).div ((hasDerivAt_log ht0).pow 3) (pow_ne_zero 3 hl)
  have h := h2.add h3
  unfold Gprim Gprim'
  convert h using 1
  · ext s; simp [id]
  · simp only [id, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring

lemma theta_integrableOn (x : ℝ) {a b : ℝ} (h2a : 2 ≤ a) (hbx : b ≤ x) :
    IntegrableOn (fun t ↦ θ t / (t * log t ^ 2)) (Icc a b) volume :=
  (integrableOn_theta_div_id_mul_log_sq x).mono_set (Icc_subset_Icc h2a hbx)

/-- Abel summation split at `y`: `π(x) = θ(x)/log x + ∫₂^y + ∫_y^x θ(t)/(t log² t) dt`. -/
lemma pi_split {x y : ℝ} (h2y : 2 ≤ y) (hyx : y ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) = θ x / log x + (∫ t in (2 : ℝ)..y, θ t / (t * log t ^ 2)) +
      ∫ t in y..x, θ t / (t * log t ^ 2) := by
  rw [primeCounting_eq_theta_div_log_add_integral (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := y)]
  · ring
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le h2y).2 (theta_integrableOn x le_rfl hyx)
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hyx).2 (theta_integrableOn x h2y le_rfl)

/-- `∫₂^y θ(t)/(t log² t) dt = π(y) - θ(y)/log y ≤ π(y) ≤ y + 1`. -/
lemma head_le {y : ℝ} (h2y : 2 ≤ y) :
    (∫ t in (2 : ℝ)..y, θ t / (t * log t ^ 2)) ≤ y + 1 := by
  have h := primeCounting_eq_theta_div_log_add_integral h2y
  have hθ : 0 ≤ θ y / log y := div_nonneg (theta_nonneg y) (log_nonneg (by linarith))
  have hπ : (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ y + 1 := by
    have h1 : Nat.primeCounting ⌊y⌋₊ ≤ ⌊y⌋₊ + 1 := Nat.count_le _
    have h2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
    have : (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ (⌊y⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    linarith
  linarith

lemma head_nonneg {y : ℝ} (h2y : 2 ≤ y) :
    0 ≤ ∫ t in (2 : ℝ)..y, θ t / (t * log t ^ 2) :=
  intervalIntegral.integral_nonneg h2y fun t ht ↦ by
    have : 0 < t := by linarith [ht.1]
    positivity [theta_nonneg t]

lemma Gprim_continuousOn (a : ℝ) {y x : ℝ} (hy : 1 < y) : ContinuousOn (Gprim a) (Icc y x) :=
  fun t ht ↦ (hasDerivAt_Gprim a (by linarith [ht.1])).continuousAt.continuousWithinAt

/-- Rosser-Schoenfeld 1975, Math. Comp. 29, Corollary 2 to Theorem 7, as quoted by Riesel-Vaughan
on page 57: `θ(x) > x - x/(40 log x)` for `x ≥ 678407`. Stated with `≤`, weaker. CITED. -/
def RS1975Cor2Thm7 : Prop :=
  ∀ t : ℝ, 678407 ≤ t → t - t / (40 * log t) ≤ θ t

/-- Lower bound for the tail integral from Rosser-Schoenfeld: for `678407 ≤ y ≤ x`,
`G_{1.975}(x) - G_{1.975}(y) ≤ ∫_y^x θ(t)/(t log² t) dt`. -/
lemma tail_lower (hRS : RS1975Cor2Thm7) {y x : ℝ} (hy : 678407 ≤ y) (hyx : y ≤ x) :
    Gprim 1.975 x - Gprim 1.975 y ≤ ∫ t in y..x, θ t / (t * log t ^ 2) := by
  refine intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hyx
    (Gprim_continuousOn _ (by linarith)) (fun t ht ↦ (hasDerivAt_Gprim _ (by linarith [ht.1])).hasDerivWithinAt)
    (theta_integrableOn x (by linarith) le_rfl) (fun t ht ↦ ?_)
  have ht : 678407 ≤ t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := log_pos (by linarith)
  have e1 : Gprim' 1.975 t = 1 / log t ^ 2 - 1 / (40 * log t ^ 3) - 5.925 / log t ^ 4 := by
    unfold Gprim'; field_simp; ring
  have e2 : (t - t / (40 * log t)) / (t * log t ^ 2) = 1 / log t ^ 2 - 1 / (40 * log t ^ 3) := by
    field_simp
  have h4 : 0 ≤ 5.925 / log t ^ 4 := by positivity
  calc Gprim' 1.975 t ≤ (t - t / (40 * log t)) / (t * log t ^ 2) := by rw [e1, e2]; linarith
    _ ≤ θ t / (t * log t ^ 2) := by gcongr; exact hRS t ht

/-- Upper bound for the tail integral from Dusart: for `e^63 ≤ y ≤ x`,
`∫_y^x θ(t)/(t log² t) dt ≤ 1.00001 (G_{2.1}(x) - G_{2.1}(y))`. -/
lemma tail_upper (hD : DusartThm52k2) {y x : ℝ} (hy : exp 63 ≤ y) (hyx : y ≤ x)
    (h63 : 7713133853 ≤ exp 63) :
    (∫ t in y..x, θ t / (t * log t ^ 2)) ≤ 1.00001 * Gprim 2.1 x - 1.00001 * Gprim 2.1 y := by
  have hy1 : 1 < y := by linarith
  refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le (g := fun t ↦ 1.00001 * Gprim 2.1 t)
    hyx (fun t ht ↦ ((Gprim_continuousOn 2.1 hy1) t ht).const_smul (1.00001 : ℝ))
    (fun t ht ↦ ((hasDerivAt_Gprim 2.1 (by linarith [ht.1])).const_mul (1.00001 : ℝ)).hasDerivWithinAt)
    (theta_integrableOn x (by linarith) le_rfl) (fun t ht ↦ ?_)
  have ht : y ≤ t := ht.1.le
  have ht0 : 0 < t := by linarith
  have hl : 63 ≤ log t := by
    rw [← log_exp 63]; exact log_le_log (exp_pos _) (by linarith)
  have hl0 : 0 < log t := by linarith
  have hθ : θ t ≤ t + 0.01 * t / log t ^ 2 := by
    have := hD t (by linarith); linarith [le_abs_self (θ t - t)]
  have hsq : 3969 ≤ log t ^ 2 := by nlinarith
  have hθ' : θ t ≤ 1.00001 * t := by
    have : 0.01 * t / log t ^ 2 ≤ 0.01 * t / 3969 := by gcongr
    linarith
  have e1 : Gprim' 2.1 t = 1 / log t ^ 2 + (0.1 * log t - 6.3) / log t ^ 4 := by
    unfold Gprim'; field_simp; ring
  have h4 : 0 ≤ (0.1 * log t - 6.3) / log t ^ 4 := div_nonneg (by linarith) (by positivity)
  calc θ t / (t * log t ^ 2) ≤ 1.00001 * t / (t * log t ^ 2) := by gcongr
    _ = 1.00001 * (1 / log t ^ 2) := by field_simp
    _ ≤ 1.00001 * Gprim' 2.1 t := by rw [e1]; linarith

/-- `L² e^{L₀} ≤ L₀² e^{L}` for `2 ≤ L₀ ≤ L`: `L² e^{-L}` decreases on `[2, ∞)`. -/
lemma sq_mul_exp_le {L0 L : ℝ} (h0 : 2 ≤ L0) (h : L0 ≤ L) : L ^ 2 * exp L0 ≤ L0 ^ 2 * exp L := by
  have hu : 0 ≤ L - L0 := by linarith
  have he := quadratic_le_exp_of_nonneg hu
  have hE : exp L = exp L0 * exp (L - L0) := by rw [← exp_add]; ring_nf
  have h1 : 0 ≤ (L - L0) * L0 * (L0 - 2) := mul_nonneg (mul_nonneg hu (by linarith)) (by linarith)
  have h2 : 0 ≤ (L - L0) ^ 2 * (L0 ^ 2 / 2 - 1) := mul_nonneg (sq_nonneg _) (by nlinarith)
  have key : L ^ 2 ≤ L0 ^ 2 * (1 + (L - L0) + (L - L0) ^ 2 / 2) := by nlinarith
  have hp := exp_pos L0
  rw [hE]
  calc L ^ 2 * exp L0 ≤ L0 ^ 2 * (1 + (L - L0) + (L - L0) ^ 2 / 2) * exp L0 := by gcongr
    _ ≤ L0 ^ 2 * exp (L - L0) * exp L0 := by gcongr
    _ = L0 ^ 2 * (exp L0 * exp (L - L0)) := by ring

lemma exp_nat_ge (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ exp n := by
  rw [← exp_one_pow]; exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le n

lemma exp_half_ge : (1.625 : ℝ) ≤ exp 0.5 := by
  have := quadratic_le_exp_of_nonneg (x := (0.5 : ℝ)) (by norm_num); norm_num at this ⊢; linarith

lemma exp_add_half (n : ℕ) : (2.7182818283 : ℝ) ^ n * 1.625 ≤ exp (n + 0.5) := by
  rw [exp_add]
  exact mul_le_mul (exp_nat_ge n) exp_half_ge (by norm_num) (exp_pos _).le

lemma exp_3_5 : (32.6 : ℝ) ≤ exp 3.5 := by
  have := exp_add_half 3; norm_num at this ⊢; linarith

lemma exp_13_5 : (678407 : ℝ) ≤ exp 13.5 := by
  have := exp_add_half 13; norm_num at this ⊢; linarith

lemma exp_11_5 : (50000 : ℝ) ≤ exp 11.5 := by
  have := exp_add_half 11; norm_num at this ⊢; linarith

lemma exp_25 : (7713133853 : ℝ) ≤ exp 25 := by
  have := exp_nat_ge 25; norm_num at this ⊢; linarith

lemma exp_20 : (200000000 : ℝ) ≤ exp 20 := by
  have := exp_nat_ge 20; norm_num at this ⊢; linarith



/-- **Lemma 6 (ii)**, (4.2) p. 55, CONDITIONAL ON `DusartThm52k2`. -/
theorem lemma6ii_of_dusart (hD : DusartThm52k2) : Lemma6ii := by
  intro x hx L300
  set L := log x with hL
  have hxe : x = exp L := (exp_log hx).symm
  have hL0 : 0 < L := by linarith
  have h63 : 7713133853 ≤ exp 63 := le_trans exp_25 (exp_le_exp.2 (by norm_num))
  have hyx : exp 63 ≤ x := by rw [hxe]; exact exp_le_exp.2 (by linarith)
  have h2y : (2 : ℝ) ≤ exp 63 := by linarith
  rw [pi_split h2y hyx]
  have hI1 := head_le h2y
  have hI2 := tail_upper hD le_rfl hyx h63
  have hGy : 0 ≤ Gprim 2.1 (exp 63) := by
    unfold Gprim; rw [log_exp]; positivity
  have hθ : θ x ≤ x + 0.01 * x / L ^ 2 := by
    have := hD x (by linarith); linarith [le_abs_self (θ x - x)]
  set B := x / L ^ 2 with hB
  set C := x / L ^ 3 with hC
  have hBpos : 0 < B := by positivity
  have hCB : C ≤ B / 300 := by
    rw [hC, hB, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ x * L ^ 2 * (L - 300) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hθL : θ x / L ≤ x / L + 0.01 * C := by
    rw [div_le_iff₀ hL0]
    have : 0.01 * C * L = 0.01 * x / L ^ 2 := by rw [hC]; field_simp
    calc θ x ≤ x + 0.01 * x / L ^ 2 := hθ
      _ = (x / L + 0.01 * C) * L := by rw [add_mul, this]; field_simp
  have hGx : Gprim 2.1 x = B + 2.1 * C := by unfold Gprim; rw [← hL, hB, hC]; ring
  -- the head term is tiny: `e^63 + 1 ≤ B/1000`
  have hmono := sq_mul_exp_le (L0 := 300) (L := L) (by norm_num) L300
  have he237 : (200000000 : ℝ) ≤ exp 237 := le_trans exp_20 (exp_le_exp.2 (by norm_num))
  have hsplit : exp 300 = exp 63 * exp 237 := by rw [← exp_add]; norm_num
  have hy1 : (1 : ℝ) ≤ exp 63 := by linarith
  have hhead : exp 63 + 1 ≤ B / 1000 := by
    rw [hB, le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]
    rw [hsplit, ← hxe] at hmono
    have hp := exp_pos 63
    have hL2 : 0 < L ^ 2 := by positivity
    have h1 : L ^ 2 * exp 63 * 200000000 ≤ L ^ 2 * exp 63 * exp 237 := by gcongr
    have h2 : L ^ 2 * 1 ≤ L ^ 2 * exp 63 := by gcongr
    nlinarith
  rw [hGx] at hI2
  rw [← hL]
  have hT : 10151 / 10000 * x / L ^ 2 = 10151 / 10000 * B := by rw [hB]; ring
  rw [hT]
  linarith

/-- **Lemma 6 (i)**, (4.1) p. 55, CONDITIONAL ON `RS1975Cor2Thm7` and `DusartThm52k2`. -/
theorem lemma6i_of_rs_dusart (hRS : RS1975Cor2Thm7) (hD : DusartThm52k2) : Lemma6i := by
  intro x hx L17
  set L := log x with hL
  have hxe : x = exp L := (exp_log hx).symm
  have hL0 : 0 < L := by linarith
  have hyx : exp 13.5 ≤ x := by rw [hxe]; exact exp_le_exp.2 (by linarith)
  have hy := exp_13_5
  have h2y : (2 : ℝ) ≤ exp 13.5 := by linarith
  rw [pi_split h2y hyx, ← hL]
  have hI1 := head_nonneg h2y
  have hI2 := tail_lower hRS hy hyx
  have hGy : Gprim 1.975 (exp 13.5) ≤ 0.00629 * exp 13.5 := by
    unfold Gprim; rw [log_exp]
    have hp := exp_pos 13.5
    have : exp 13.5 / 13.5 ^ 2 + 1.975 * exp 13.5 / 13.5 ^ 3 =
        (1 / 13.5 ^ 2 + 1.975 / 13.5 ^ 3) * exp 13.5 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
  set B := x / L ^ 2 with hB
  set C := x / L ^ 3 with hC
  have hBpos : 0 < B := by positivity
  have hCpos : 0 < C := by positivity
  have hGx : Gprim 1.975 x = B + 1.975 * C := by unfold Gprim; rw [← hL, hB, hC]; ring
  rw [hGx] at hI2
  have hCL : C * L = B := by rw [hC, hB]; field_simp
  have hBL : B * L = x / L := by rw [hB]; field_simp
  have hT : 9911 / 10000 * x / L ^ 2 = 9911 / 10000 * B := by rw [hB]; ring
  rw [hT]
  rcases le_or_gt L 25 with h25 | h25
  · -- `17 ≤ log x ≤ 25`: Rosser-Schoenfeld at `x`
    have hθ := hRS x (by linarith)
    have hθL : x / L - B / 40 ≤ θ x / L := by
      rw [le_div_iff₀ hL0]
      have : (x / L - B / 40) * L = x - x / (40 * L) := by rw [hB]; field_simp
      linarith
    have hCB : B / 25 ≤ C := by
      have : B ≤ C * 25 := by rw [← hCL]; exact mul_le_mul_of_nonneg_left h25 hCpos.le
      linarith
    have hmono := sq_mul_exp_le (L0 := 17) (L := L) (by norm_num) L17
    have hsplit : exp 17 = exp 13.5 * exp 3.5 := by rw [← exp_add]; norm_num
    rw [hsplit, ← hxe] at hmono
    have h35 := exp_3_5
    have hyB : exp 13.5 ≤ 8.87 * B := by
      rw [hB, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      have hp := exp_pos 13.5
      nlinarith
    nlinarith
  · -- `log x > 25`: Dusart at `x`
    have hθ : x - 0.01 * x / L ^ 2 ≤ θ x := by
      have hx25 : exp 25 ≤ x := by rw [hxe]; exact exp_le_exp.2 h25.le
      have := hD x (by linarith [exp_25]); linarith [neg_abs_le (θ x - x)]
    have hθL : x / L - 0.01 * C ≤ θ x / L := by
      rw [le_div_iff₀ hL0]
      have : (x / L - 0.01 * C) * L = x - 0.01 * x / L ^ 2 := by rw [hC]; field_simp
      linarith
    have hmono := sq_mul_exp_le (L0 := 25) (L := L) (by norm_num) h25.le
    have hsplit : exp 25 = exp 13.5 * exp 11.5 := by rw [← exp_add]; norm_num
    rw [hsplit, ← hxe] at hmono
    have h115 := exp_11_5
    have hyB : exp 13.5 ≤ 0.0125 * B := by
      rw [hB, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      have hp := exp_pos 13.5
      nlinarith
    nlinarith

end LeanLab.RieselVaughan1983.Lemma6Theta
