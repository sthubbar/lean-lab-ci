/- AI wrote this Lean code for CODEX task232.
Published analytic inputs for DecompC169b. Goldbach is open. -/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.ModelC233

namespace LeanLab.BS2022GRH.PublishedInputs232
open Real Finset ChenThresholdGRH

/-- LEAF. Journal Lemma 5 p. 1216, Buthe 2014 display 4.6.
The squarefree count is the Mobius square sum. -/
theorem lemma5_mu : PaperInputs148.Lemma5MuJ := by
  sorry

/-- LEAF. Journal Lemma 5 p. 1216, Ramare 2019 Theorem 3.1.
Keep the reciprocal totient weight rather than replacing it by one. -/
theorem lemma5_phi : PaperInputs148.Lemma5PhiJ := by
  sorry

/-- LEAF. Schoenfeld Corollary 1, journal Lemma 1 p. 1215. -/
theorem lemma1_schoenfeld : PaperInputs148.Lemma1J := by
  sorry

/-- LEAF. Robin Theorem 11, journal Lemma 4 p. 1216. -/
theorem lemma4_robin : PaperInputs148.Lemma4J := by
  sorry

/-- LEAF. Rosser and Schoenfeld 1962 Theorem 18, journal Lemma 2 p. 1215. -/
theorem lemma2_theta : PaperInputs148.Lemma2J := by
  sorry

/-- LEAF. Weighted reciprocal prime sum, journal p. 1234 first display.
Bordignon and Starichkova apply reference 7 Lemma 1 part ii and evaluate the integral. -/
theorem weighted_reciprocal_primes (n : ℕ) (α : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hα : 0 < α) (hα1 : α < 1 / 24) :
    (∑ q ∈ U7153.Qset n,
      (1 : ℝ) / ((q : ℝ) * log ((n : ℝ) ^ (1 / 2 - α) / q))) ≤
      (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / ((1 / 2 - α) * log n) +
        512 / (kA α * log n ^ 3) := by
  sorry

/-- LEAF. Unweighted reciprocal prime interval, journal p. 1234.
Rosser and Schoenfeld reference 16 Theorem 5. The lower endpoint is inclusive. -/
theorem reciprocal_prime_interval (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n) :
    (∑ q ∈ U7153.Qset n, (1 : ℝ) / q) ≤ log (8 / 3) + 64 / log n ^ 2 := by
  sorry

/-- A concrete nonempty domain check for the squarefree counting input, p. 1216. -/
theorem lemma5_mu_one_instance :
    ((((Icc 1 ⌊(1 : ℝ)⌋₊).filter (fun n => Squarefree n)).card : ℝ)) ≤
      Lemma5Coeffs138.mMu 1 * 1 := by
  have hcard : ((((Icc 1 ⌊(1 : ℝ)⌋₊).filter (fun n => Squarefree n)).card : ℝ)) ≤ 1 := by
    have h := card_filter_le (Icc 1 ⌊(1 : ℝ)⌋₊) (fun n => Squarefree n)
    norm_num at h ⊢
    exact_mod_cast h
  have hπ : π ^ 2 ≤ (16 : ℝ) := by nlinarith [pi_pos, pi_lt_four]
  have hdiv : (6 : ℝ) / 16 ≤ 6 / π ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hπ
  apply hcard.trans
  norm_num [Lemma5Coeffs138.mMu]
  linarith

/-- A concrete nonempty weighted domain check for Lemma 5, p. 1216. -/
theorem lemma5_phi_two_instance :
    (∑ n ∈ (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun n => Squarefree n), (1 : ℝ) / n.totient) ≤
      Mphi 2 * log 2 := by
  have hset : (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun n => Squarefree n) = {1, 2} := by
    ext n
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    norm_num only [Nat.floor_ofNat] 
    constructor
    · intro h
      omega
    · intro h
      rcases h with rfl | rfl
      · norm_num
      · exact ⟨⟨by norm_num, le_rfl⟩, Nat.prime_two.squarefree⟩
  rw [hset]
  norm_num only [sum_insert, mem_singleton, reduceCtorEq, not_false_eq_true, sum_singleton,
    Nat.totient_one, Nat.totient_two, Nat.cast_one, div_one]
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hmin : 0 ≤ min (2.44 / (√(2 : ℝ) * log 2)) (11 / (√(2 : ℝ) * log 2 ^ 2)) := by positivity
  have hmul := mul_nonneg hmin hlog.le
  calc
    (2 : ℝ) ≤ log 2 + 1.333 := by linarith [log_two_gt_d9]
    _ ≤ log 2 + 1.333 + min (2.44 / (√(2 : ℝ) * log 2))
        (11 / (√(2 : ℝ) * log 2 ^ 2)) * log 2 := le_add_of_nonneg_right hmul
    _ = _ := by unfold Mphi; field_simp


/-! ### Proof of `li_bounds_large`

Everything below is a private development for the leaf `li_bounds_large`: the
principal-value logarithmic integral `liPV` is expanded by three integrations by
parts into `y/L + y/L² + 2y/L³ - A + liPV 2 + 6∫₂^y dt/(log t)^4`, the integral is
bounded above by a convexity (trapezoid) sum on the partition `exp (11 - k/10)` and
below by the monotonicity of the integrand, and the comparison functions are
extended to all `y ≥ exp 11` by monotonicity.  Nothing here changes an existing
statement. -/
namespace LiProof232
open Real MeasureTheory Filter Topology Set
noncomputable section

lemma exp_eleven_le : exp 11 ≤ 59874.142 := by
  have h1 : exp (11 : ℝ) = exp 1 ^ 11 := by
    simpa using Real.exp_nat_mul (x := (1 : ℝ)) 11
  rw [h1]
  have h2 : exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have h3 : exp 1 ^ 11 ≤ (2.7182818286 : ℝ) ^ 11 := by gcongr
  have h4 : (2.7182818286 : ℝ) ^ 11 ≤ 59874.142 := by norm_num
  linarith

/-- `exp (-1/8) ≤ 481/512`, from `exp (1/8) ≥ 1 + 1/8 + (1/8)²/2 = 145/128`. -/
lemma exp_neg_eighth_le : exp (-(1/8)) ≤ 481/512 := by
  have h2 : ∑ i ∈ Finset.range 3, ((1/8 : ℝ)) ^ i / (i.factorial : ℝ) ≤ exp (1/8) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 3
  have h3 : (145/128 : ℝ) ≤ exp (1/8) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at h2 ⊢
    linarith
  have h5 : (exp (1/8))⁻¹ ≤ (145/128 : ℝ)⁻¹ := by
    have h6 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 145/128) h3
    simpa [one_div] using h6
  have h6 : (145/128 : ℝ)⁻¹ ≤ 481/512 := by norm_num
  have h7 : exp (-(1/8)) = (exp (1/8))⁻¹ := by
    rw [show (-(1/8) : ℝ) = -(1/8) by norm_num, Real.exp_neg]
  rw [h7]
  linarith

lemma exp_shift_le (k : ℕ) : exp (11 - (k : ℝ)/8) ≤ 59874.142 * (481/512)^k := by
  have hs : (11 : ℝ) - (k : ℝ)/8 = 11 + (k : ℝ) * (-(1/8)) := by ring
  rw [hs, Real.exp_add, Real.exp_nat_mul]
  have hp : (0 : ℝ) < exp (-(1/8)) := exp_pos _
  have h8 : exp (-(1/8)) ≤ 481/512 := exp_neg_eighth_le
  have h3 : exp (-(1/8)) ^ k ≤ (481/512)^k := by gcongr
  exact mul_le_mul exp_eleven_le h3 (by positivity) (by norm_num)

/-! ## The integrand `f4 x = (log x)⁻⁴` -/

/-- `f4 x = 1 / (log x)^4`, the integrand in the integration by parts. -/
def f4 (x : ℝ) : ℝ := ((log x)^4)⁻¹

lemma f4_exp (s : ℝ) : f4 (exp s) = (s^4)⁻¹ := by simp [f4]

lemma f4_pos {x : ℝ} (hx : 1 < x) : 0 < f4 x := by
  have h : 0 < log x := log_pos hx
  simp only [f4]
  positivity

lemma continuousOn_f4 : ContinuousOn f4 (Ici (2:ℝ)) := by
  have h0 : ContinuousOn (fun x : ℝ => log x) (Ici (2:ℝ)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    have hx2 : (2:ℝ) ≤ x := hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have h1 : ContinuousOn (fun x : ℝ => (log x)^4) (Ici (2:ℝ)) := h0.pow 4
  refine h1.inv₀ (fun x hx => ?_)
  have hx2 : (2:ℝ) ≤ x := hx
  have hpos : 0 < log x := log_pos (by linarith)
  positivity

lemma intervalIntegrable_f4 {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable f4 volume a b := by
  apply ContinuousOn.intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact continuousOn_f4.mono (by intro x hx; exact le_trans ha hx.1)
  · rw [uIcc_of_ge h]
    exact continuousOn_f4.mono (by intro x hx; exact le_trans hb hx.1)

/-! ## Derivatives and convexity of `f4` -/

/-- The derivative of `f4`. -/
def f4d (x : ℝ) : ℝ := -4 * (x * (log x)^5)⁻¹

/-- The second derivative of `f4`. -/
def f4dd (x : ℝ) : ℝ := (4 * log x + 20) * (x^2 * (log x)^6)⁻¹

lemma hasDerivAt_f4 {x : ℝ} (hx : 1 < x) : HasDerivAt f4 (f4d x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog : log x ≠ 0 := (log_pos hx).ne'
  have h1 : HasDerivAt (fun y : ℝ => log y) x⁻¹ x := hasDerivAt_log hx0
  have h2 : HasDerivAt (fun y : ℝ => (log y)^4) ((4:ℝ) * (log x)^3 * x⁻¹) x := h1.pow 4
  have h3 : HasDerivAt (fun y : ℝ => ((log y)^4)⁻¹)
      (-((4:ℝ) * (log x)^3 * x⁻¹) / ((log x)^4)^2) x :=
    h2.inv (by positivity)
  have hval : (-((4:ℝ) * (log x)^3 * x⁻¹) / ((log x)^4)^2) = f4d x := by
    simp only [f4d]
    field_simp
    try ring
  rw [hval] at h3
  exact h3

lemma hasDerivAt_f4d {x : ℝ} (hx : 1 < x) : HasDerivAt f4d (f4dd x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog : log x ≠ 0 := (log_pos hx).ne'
  have h1 : HasDerivAt (fun y : ℝ => log y) x⁻¹ x := hasDerivAt_log hx0
  have h2' := (hasDerivAt_id (x : ℝ)).mul (h1.pow 5)
  have h2 : HasDerivAt (fun y : ℝ => y * (log y)^5)
      ((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) x := by
    have hfun : (fun y : ℝ => y * (log y)^5) = id * (fun y : ℝ => log y)^5 := by
      funext y; simp
    rw [hfun]
    convert h2' using 1
    try simp
    try ring
  have h3 : HasDerivAt (fun y : ℝ => (y * (log y)^5)⁻¹)
      (-((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) / (x * (log x)^5)^2) x :=
    h2.inv (by positivity)
  have h4 : HasDerivAt (fun y : ℝ => -4 * (y * (log y)^5)⁻¹)
      (-4 * (-((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) / (x * (log x)^5)^2)) x :=
    h3.const_mul (-4)
  have hval : (-4 * (-((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) / (x * (log x)^5)^2)) = f4dd x := by
    simp only [f4dd]
    field_simp
    try ring
  rw [hval] at h4
  exact h4

lemma deriv_f4_eq {x : ℝ} (hx : 1 < x) : deriv f4 x = f4d x := (hasDerivAt_f4 hx).deriv

lemma convexOn_f4 : ConvexOn ℝ (Ioi (1:ℝ)) f4 := by
  have hconv : Convex ℝ (Ioi (1:ℝ)) := convex_Ioi 1
  have hdiff1 : DifferentiableOn ℝ f4 (Ioi (1:ℝ)) := fun x hx =>
    (hasDerivAt_f4 hx).differentiableAt.differentiableWithinAt
  have hdiff2 : DifferentiableOn ℝ (deriv f4) (Ioi (1:ℝ)) := by
    intro x hx
    have h2 : deriv f4 =ᶠ[𝓝 x] f4d := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using deriv_f4_eq hy
    exact ((hasDerivAt_f4d hx).congr_of_eventuallyEq h2).differentiableAt.differentiableWithinAt
  refine convexOn_of_deriv2_nonneg' hconv hdiff1 hdiff2 (fun x hx => ?_)
  have h2 : deriv f4 =ᶠ[𝓝 x] f4d := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using deriv_f4_eq hy
  have h3 : deriv^[2] f4 x = deriv f4d x := by
    rw [show deriv^[2] f4 = deriv (deriv f4) from rfl, h2.deriv_eq]
  rw [h3, (hasDerivAt_f4d hx).deriv]
  have hx1 : (1:ℝ) < x := hx
  have hlog : 0 < log x := log_pos hx1
  have hx0 : 0 < x := by linarith
  simp only [f4dd]
  have h5 : (0:ℝ) < 4 * log x + 20 := by linarith
  have h6 : (0:ℝ) < x^2 * (log x)^6 := by positivity
  exact mul_nonneg h5.le (inv_nonneg.mpr h6.le)

/-! ## The trapezoid bound -/

/-- For the convex `f4`, the integral is at most the trapezoid area. -/
lemma integral_f4_le_trapz {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, f4 t ≤ (b - a) * (f4 a + f4 b) / 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  have ha1 : (1:ℝ) < a := by linarith
  have hb1 : (1:ℝ) < b := by linarith
  have hbda : (0:ℝ) < b - a := by linarith
  have hchord : ∀ t ∈ Icc a b, f4 t ≤ ((b - t) * f4 a + (t - a) * f4 b) / (b - a) := by
    intro t ht
    obtain ⟨hta, htb⟩ := ht
    set p : ℝ := (b - t) / (b - a) with hp
    set q : ℝ := (t - a) / (b - a) with hq
    have hp0 : 0 ≤ p := div_nonneg (by linarith) hbda.le
    have hq0 : 0 ≤ q := div_nonneg (by linarith) hbda.le
    have hpq : p + q = 1 := by
      simp only [hp, hq]
      field_simp
      ring
    obtain ⟨-, hcv⟩ := convexOn_f4
    have hconv : f4 (p * a + q * b) ≤ p * f4 a + q * f4 b :=
      hcv ha1 hb1 hp0 hq0 hpq
    have hpt : p * a + q * b = t := by
      simp only [hp, hq]
      field_simp
      ring
    rw [← hpt]
    refine hconv.trans_eq ?_
    simp only [hp, hq]
    field_simp
    ring
  have hint1 : IntervalIntegrable f4 volume a b := intervalIntegrable_f4 ha (le_trans ha hab)
  have hint2 : IntervalIntegrable (fun t : ℝ => ((b - t) * f4 a + (t - a) * f4 b) / (b - a))
      volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hchord
  have hsq : ∀ x : ℝ, HasDerivAt (fun s : ℝ => s^2/2) x x := by
    intro x
    have h4 : HasDerivAt (fun s : ℝ => s^2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h5 : HasDerivAt (fun s : ℝ => s^2/2) ((2 : ℝ) * x / 2) x := h4.div_const 2
    convert h5 using 1
    try ring
  have hprim : ∀ x ∈ uIcc a b, HasDerivAt
      (fun s : ℝ => (f4 a * (b * s - s^2/2) + f4 b * (s^2/2 - a * s)) / (b - a))
      (((b - x) * f4 a + (x - a) * f4 b) / (b - a)) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => b * s - s^2/2) (b - x) x := by
      have hb1' : HasDerivAt (fun s : ℝ => b * s) b x := by
        simpa using (hasDerivAt_id x).const_mul (b:ℝ)
      have h6 := hb1'.sub (hsq x)
      convert h6 using 1
      try ring
    have h7 : HasDerivAt (fun s : ℝ => s^2/2 - a * s) (x - a) x := by
      have h8 : HasDerivAt (fun s : ℝ => a * s) a x := by
        simpa using (hasDerivAt_id x).const_mul (a:ℝ)
      have h6 := (hsq x).sub h8
      convert h6 using 1
      try ring
    have h9 := h1.const_mul (f4 a)
    have h10 := h7.const_mul (f4 b)
    have h11 := h9.add h10
    have h12 : HasDerivAt (fun s : ℝ =>
        (f4 a * (b * s - s^2/2) + f4 b * (s^2/2 - a * s)) / (b - a))
        ((f4 a * (b - x) + f4 b * (x - a)) / (b - a)) x := h11.div_const (b - a)
    convert h12 using 1
    try ring
  have hval : (∫ t in a..b, ((b - t) * f4 a + (t - a) * f4 b) / (b - a))
      = (b - a) * (f4 a + f4 b) / 2 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hprim hint2
    rw [this]
    field_simp
    try ring
  rw [hval] at hmono
  exact hmono



/-! ## Exponential bounds at `1/10` (the partition of `[2, exp 11]`) -/

lemma exp_tenth_ge : (1.10517 : ℝ) ≤ exp (1/10) := by
  have h2 : ∑ i ∈ Finset.range 5, ((1/10 : ℝ)) ^ i / (i.factorial : ℝ) ≤ exp (1/10) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2 ⊢
  linarith

lemma exp_tenth_le : exp (1/10) ≤ 1.10518 := by
  by_contra h
  push_neg at h
  have e1 : exp (1:ℝ) = exp (1/10)^10 := by
    simpa using Real.exp_nat_mul (x := (1/10 : ℝ)) 10
  have h2 : exp (1:ℝ) ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have h2' : exp (1/10)^10 ≤ 2.7182818286 := by rw [← e1]; exact h2
  have h3 : (1.10518:ℝ)^10 < exp (1/10)^10 :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num : (10:ℕ) ≠ 0)
  have h4 : (2.7182818286:ℝ) < (1.10518:ℝ)^10 := by norm_num
  linarith

lemma exp_neg_tenth_le : exp (-(1/10)) ≤ 904839/1000000 := by
  have h3 : (1.10517 : ℝ) ≤ exp (1/10) := exp_tenth_ge
  have h5 : (exp (1/10))⁻¹ ≤ (1.10517 : ℝ)⁻¹ := by
    have h6 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1.10517) h3
    simpa [one_div] using h6
  have h6 : (1.10517 : ℝ)⁻¹ ≤ 904839/1000000 := by norm_num
  have h7 : exp (-(1/10)) = (exp (1/10))⁻¹ := by
    rw [show (-(1/10) : ℝ) = -(1/10) by norm_num, Real.exp_neg]
  rw [h7]
  linarith

lemma one_sub_exp_neg_tenth_le : 1 - exp (-(1/10)) ≤ 0.09518 := by
  have h3 : exp (1/10) ≤ 1.10518 := exp_tenth_le
  have hpos : (0:ℝ) < exp (1/10) := exp_pos _
  have h4 : (1.10518 : ℝ)⁻¹ ≤ exp (-(1/10)) := by
    have h6 := one_div_le_one_div_of_le hpos h3
    have h7 : exp (-(1/10)) = (exp (1/10))⁻¹ := by
      rw [show (-(1/10) : ℝ) = -(1/10) by norm_num, Real.exp_neg]
    rw [h7]
    simpa [one_div] using h6
  have h5 : (1 - (1.10518:ℝ)⁻¹) ≤ 0.09518 := by norm_num
  linarith

lemma exp_shift_le10 (k : ℕ) : exp (11 - (k : ℝ)/10) ≤ 59874.142 * (904839/1000000)^k := by
  have hs : (11 : ℝ) - (k : ℝ)/10 = 11 + (k : ℝ) * (-(1/10)) := by ring
  rw [hs, Real.exp_add, Real.exp_nat_mul]
  have hp : (0 : ℝ) < exp (-(1/10)) := exp_pos _
  have h8 : exp (-(1/10)) ≤ 904839/1000000 := exp_neg_tenth_le
  have h3 : exp (-(1/10)) ^ k ≤ (904839/1000000)^k := by gcongr
  exact mul_le_mul exp_eleven_le h3 (by positivity) (by norm_num)

/-! ## The partition `tpt k = exp (11 - k/10)` -/

/-- `tpt k = exp (11 - k/10)`, a decreasing family from `exp 11` down past `2`. -/
def tpt (k : ℕ) : ℝ := exp (11 - (k:ℝ)/10)

lemma tpt_zero : tpt 0 = exp 11 := by norm_num [tpt]

lemma tpt_anti : Antitone tpt := by
  intro k l hkl
  simp only [tpt]
  apply exp_le_exp.mpr
  have h : (k:ℝ) ≤ (l:ℝ) := by exact_mod_cast hkl
  linarith

lemma two_le_tpt_103 : (2:ℝ) ≤ tpt 103 := by
  have h1 : (2.01 : ℝ) ≤ exp (7/10) := by
    have h2 : ∑ i ∈ Finset.range 5, ((7/10:ℝ))^i / (i.factorial : ℝ) ≤ exp (7/10) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h2 ⊢
    linarith
  have h3 : exp (7/10) ≤ exp (11 - (103:ℝ)/10) := by
    apply exp_le_exp.mpr
    norm_num
  have h4 : tpt 103 = exp (11 - (103:ℝ)/10) := rfl
  rw [h4]
  linarith

lemma two_le_tpt {k : ℕ} (hk : k ≤ 103) : (2:ℝ) ≤ tpt k :=
  le_trans two_le_tpt_103 (tpt_anti hk)

lemma f4_tpt (k : ℕ) : f4 (tpt k) = ((11 - (k:ℝ)/10)^4)⁻¹ := by
  simp only [tpt, f4, Real.log_exp]

lemma tpt_sub_le (k : ℕ) :
    tpt k - tpt (k+1) ≤ 59874.142 * (904839/1000000)^k * 0.09518 := by
  have hsplit : tpt k - tpt (k+1) = exp (11 - (k:ℝ)/10) * (1 - exp (-(1/10))) := by
    have step : exp ((11 - (k:ℝ)/10) + (-(1/10))) =
        exp (11 - (k:ℝ)/10) * exp (-(1/10)) := Real.exp_add _ _
    simp only [tpt, Nat.cast_add, Nat.cast_one]
    rw [show (11:ℝ) - ((k:ℝ)+1)/10 = (11 - (k:ℝ)/10) + (-(1/10)) by ring, step]
    ring
  rw [hsplit]
  have h2 : exp (11 - (k:ℝ)/10) ≤ 59874.142 * (904839/1000000)^k := exp_shift_le10 k
  have h3 : 1 - exp (-(1/10)) ≤ 0.09518 := one_sub_exp_neg_tenth_le
  have h4 : (0:ℝ) ≤ 1 - exp (-(1/10)) := by
    have h5 : exp (-(1/10)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; norm_num
    linarith
  calc exp (11 - (k:ℝ)/10) * (1 - exp (-(1/10)))
      ≤ (59874.142 * (904839/1000000)^k) * 0.09518 := mul_le_mul h2 h3 h4 (by norm_num)
    _ = _ := by ring

/-- The closed-form upper bound for the `k`-th trapezoid term. -/
def Db (k : ℕ) : ℝ :=
  (59874.142 * (904839/1000000)^k * 0.09518) *
    (((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹) / 2

lemma term_le_Db (k : ℕ) :
    (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2 ≤ Db k := by
  have h1 : tpt k - tpt (k+1) ≤ 59874.142 * (904839/1000000)^k * 0.09518 := tpt_sub_le k
  have h2 : (0:ℝ) ≤ ((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹ := by positivity
  simp only [f4_tpt, Nat.cast_add, Nat.cast_one, Db]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) (by norm_num)

/-! ## The numerical table -/

/-- `Q k` bounds `(904839/1000000)^k` from above, and `Ct k` bounds the `k`-th trapezoid term. -/
def Q : ℕ → ℝ
  | 0 => 1.000000000000
  | 1 => 0.904839000000
  | 2 => 0.818733615921
  | 3 => 0.740822106297
  | 4 => 0.670324733840
  | 5 => 0.606535961844
  | 6 => 0.548817393179
  | 7 => 0.496591381227
  | 8 => 0.449335248799
  | 9 => 0.406576057189
  | 10 => 0.367885873011
  | 11 => 0.332877485450
  | 12 => 0.301200531058
  | 13 => 0.272537987322
  | 14 => 0.246602999911
  | 15 => 0.223136011837
  | 16 => 0.201902165815
  | 17 => 0.182688953814
  | 18 => 0.165304090281
  | 19 => 0.149573587746
  | 20 => 0.135340015563
  | 21 => 0.122460924343
  | 22 => 0.110807420322
  | 23 => 0.100262875397
  | 24 => 0.090721759912
  | 25 => 0.082088586518
  | 26 => 0.074276954537
  | 27 => 0.067208685267
  | 28 => 0.060813039569
  | 29 => 0.055026009911
  | 30 => 0.049789679782
  | 31 => 0.045051644065
  | 32 => 0.040764484565
  | 33 => 0.036885295450
  | 34 => 0.033375253850
  | 35 => 0.030199231319
  | 36 => 0.027325442268
  | 37 => 0.024725125857
  | 38 => 0.022372258156
  | 39 => 0.020243291698
  | 40 => 0.018316919817
  | 41 => 0.016573863411
  | 42 => 0.014996677995
  | 43 => 0.013569579121
  | 44 => 0.012278284403
  | 45 => 0.011109870581
  | 46 => 0.010052644187
  | 47 => 0.009096024514
  | 48 => 0.008230437726
  | 49 => 0.007447221042
  | 50 => 0.006738536041
  | 51 => 0.006097290213
  | 52 => 0.005517065980
  | 53 => 0.004992056465
  | 54 => 0.004517007380
  | 55 => 0.004087164441
  | 56 => 0.003698225786
  | 57 => 0.003346298922
  | 58 => 0.003027861771
  | 59 => 0.002739727418
  | 60 => 0.002479012218
  | 61 => 0.002243106937
  | 62 => 0.002029650638
  | 63 => 0.001836507054
  | 64 => 0.001661743207
  | 65 => 0.001503610062
  | 66 => 0.001360525025
  | 67 => 0.001231056104
  | 68 => 0.001113907575
  | 69 => 0.001007907017
  | 70 => 0.000911993578
  | 71 => 0.000825207358
  | 72 => 0.000746679801
  | 73 => 0.000675625005
  | 74 => 0.000611331854
  | 75 => 0.000553156904
  | 76 => 0.000500517940
  | 77 => 0.000452888153
  | 78 => 0.000409790864
  | 79 => 0.000370794756
  | 80 => 0.000335509557
  | 81 => 0.000303582133
  | 82 => 0.000274692954
  | 83 => 0.000248552898
  | 84 => 0.000224900356
  | 85 => 0.000203498614
  | 86 => 0.000184133483
  | 87 => 0.000166611157
  | 88 => 0.000150756273
  | 89 => 0.000136410156
  | 90 => 0.000123429230
  | 91 => 0.000111683582
  | 92 => 0.000101055661
  | 93 => 0.000091439104
  | 94 => 0.000082737668
  | 95 => 0.000074864269
  | 96 => 0.000067740111
  | 97 => 0.000061293895
  | 98 => 0.000055461107
  | 99 => 0.000050183373
  | 100 => 0.000045407874
  | 101 => 0.000041086816
  | 102 => 0.000037176954
  | 103 => 0.000033639158
  | _ => 0

def Ct : ℕ → ℝ
  | 0 => 0.396478
  | 1 => 0.372160
  | 2 => 0.349453
  | 3 => 0.328244
  | 4 => 0.308431
  | 5 => 0.289919
  | 6 => 0.272617
  | 7 => 0.256444
  | 8 => 0.241322
  | 9 => 0.227180
  | 10 => 0.213952
  | 11 => 0.201575
  | 12 => 0.189993
  | 13 => 0.179152
  | 14 => 0.169001
  | 15 => 0.159496
  | 16 => 0.150593
  | 17 => 0.142252
  | 18 => 0.134436
  | 19 => 0.127110
  | 20 => 0.120242
  | 21 => 0.113802
  | 22 => 0.107762
  | 23 => 0.102096
  | 24 => 0.096779
  | 25 => 0.091790
  | 26 => 0.087107
  | 27 => 0.082710
  | 28 => 0.078581
  | 29 => 0.074703
  | 30 => 0.071061
  | 31 => 0.067639
  | 32 => 0.064423
  | 33 => 0.061402
  | 34 => 0.058562
  | 35 => 0.055893
  | 36 => 0.053384
  | 37 => 0.051025
  | 38 => 0.048808
  | 39 => 0.046723
  | 40 => 0.044764
  | 41 => 0.042922
  | 42 => 0.041192
  | 43 => 0.039565
  | 44 => 0.038038
  | 45 => 0.036603
  | 46 => 0.035257
  | 47 => 0.033994
  | 48 => 0.032810
  | 49 => 0.031700
  | 50 => 0.030662
  | 51 => 0.029691
  | 52 => 0.028784
  | 53 => 0.027939
  | 54 => 0.027153
  | 55 => 0.026424
  | 56 => 0.025748
  | 57 => 0.025126
  | 58 => 0.024553
  | 59 => 0.024030
  | 60 => 0.023556
  | 61 => 0.023128
  | 62 => 0.022747
  | 63 => 0.022412
  | 64 => 0.022123
  | 65 => 0.021880
  | 66 => 0.021683
  | 67 => 0.021534
  | 68 => 0.021433
  | 69 => 0.021382
  | 70 => 0.021384
  | 71 => 0.021441
  | 72 => 0.021556
  | 73 => 0.021734
  | 74 => 0.021980
  | 75 => 0.022299
  | 76 => 0.022699
  | 77 => 0.023189
  | 78 => 0.023780
  | 79 => 0.024485
  | 80 => 0.025320
  | 81 => 0.026304
  | 82 => 0.027463
  | 83 => 0.028825
  | 84 => 0.030429
  | 85 => 0.032322
  | 86 => 0.034563
  | 87 => 0.037231
  | 88 => 0.040426
  | 89 => 0.044279
  | 90 => 0.048969
  | 91 => 0.054734
  | 92 => 0.061907
  | 93 => 0.070952
  | 94 => 0.082542
  | 95 => 0.097666
  | 96 => 0.117826
  | 97 => 0.145377
  | 98 => 0.184149
  | 99 => 0.240660
  | 100 => 0.326590
  | 101 => 0.464262
  | 102 => 0.699826
  | 103 => 0.059970
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma Q_step : ∀ k < 103, Q k * 0.904839 ≤ Q (k+1) := by
  intro k hk
  interval_cases k <;> simp only [Q] <;> norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma geom_le : ∀ k, k ≤ 103 → ((904839/1000000 : ℝ))^k ≤ Q k
  | 0, _ => by simp only [Q]; norm_num
  | (n+1), hn => by
    have hn' : n ≤ 103 := by omega
    have hQpos : (0:ℝ) ≤ Q n := by
      have h99 := geom_le n hn'
      have : (0:ℝ) ≤ ((904839/1000000 : ℝ))^n := by positivity
      linarith
    have hstep : Q n * 0.904839 ≤ Q (n+1) := by
      have hn'' : n < 103 := by omega
      interval_cases n <;> simp only [Q] <;> norm_num
    rw [pow_succ]
    calc ((904839/1000000 : ℝ))^n * (904839/1000000) ≤ Q n * 0.904839 := by
          apply mul_le_mul (geom_le n hn') (by norm_num) (by norm_num) hQpos
      _ ≤ Q (n+1) := hstep

/-- The trapezoid term with `Q` in place of the power. -/
def DbQ (k : ℕ) : ℝ :=
  (59874.142 * Q k * 0.09518) *
    (((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹) / 2

lemma Db_le_DbQ {k : ℕ} (hk : k ≤ 103) : Db k ≤ DbQ k := by
  have h1 : ((904839/1000000 : ℝ))^k ≤ Q k := geom_le k hk
  have h2 : (0:ℝ) ≤ ((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹ := by positivity
  simp only [Db, DbQ]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ h2
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma DbQ_le_Ct : ∀ k < 103, DbQ k ≤ Ct k := by
  intro k hk
  interval_cases k <;> (simp only [DbQ, Q, Ct] <;> norm_num)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma Db_le_Ct : ∀ k < 103, Db k ≤ Ct k := by
  intro k hk
  have hk' : k ≤ 103 := by omega
  exact (Db_le_DbQ hk').trans (DbQ_le_Ct k hk)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma Ct_sum_le : (∑ k ∈ Finset.range 104, Ct k) ≤ 10.33 := by
  simp only [Finset.sum_range_succ, Ct]
  norm_num

/-- The partition bound: `∫_2^{tpt 0} ≤ Σ (trapezoids) + ∫_2^{tpt N}`. -/
lemma I4_partial (N : ℕ) (hN : N ≤ 103) :
    ∫ x in (2:ℝ)..tpt 0, f4 x ≤
      (∑ k ∈ Finset.range N, (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
        + ∫ x in (2:ℝ)..tpt N, f4 x := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ 103 := le_trans (Nat.le_succ n) hN
    have hn1 : n + 1 ≤ 103 := hN
    have h2n : (2:ℝ) ≤ tpt n := two_le_tpt hn
    have h2n1 : (2:ℝ) ≤ tpt (n+1) := two_le_tpt hn1
    have hanti : tpt (n+1) ≤ tpt n := tpt_anti (Nat.le_succ n)
    have hsplit : (∫ x in (2:ℝ)..tpt (n+1), f4 x) + (∫ x in (tpt (n+1))..tpt n, f4 x)
        = ∫ x in (2:ℝ)..tpt n, f4 x :=
      intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_f4 le_rfl h2n1)
        (intervalIntegrable_f4 h2n1 h2n)
    have hstep0 := integral_f4_le_trapz (a := tpt (n+1)) (b := tpt n) h2n1 hanti
    have hstep : ∫ x in (tpt (n+1))..tpt n, f4 x ≤
        (tpt n - tpt (n+1)) * (f4 (tpt n) + f4 (tpt (n+1)))/2 := by
      rw [add_comm (f4 (tpt (n+1))) (f4 (tpt n))] at hstep0
      exact hstep0
    have ih' := ih hn
    have key : (∑ k ∈ Finset.range n,
          (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
          + ∫ x in (2:ℝ)..tpt n, f4 x ≤
        (∑ k ∈ Finset.range (n+1),
          (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
          + ∫ x in (2:ℝ)..tpt (n+1), f4 x := by
      rw [Finset.sum_range_succ, ← hsplit]
      linarith
    exact ih'.trans key

/-- `∫_2^{exp 11} dt/(log t)^4 ≤ 10.33`, the numerical core. -/
lemma I4_exp11_le : ∫ x in (2:ℝ)..exp 11, f4 x ≤ 10.33 := by
  have hpart := I4_partial 103 le_rfl
  rw [tpt_zero] at hpart
  have hCt103 : Ct 103 = 0.059970 := by simp only [Ct]
  have hlast : ∫ x in (2:ℝ)..tpt 103, f4 x ≤ Ct 103 := by
    refine (integral_f4_le_trapz (a := 2) (b := tpt 103) le_rfl two_le_tpt_103).trans ?_
    have hle : tpt 103 ≤ 59874.142 * (904839/1000000)^103 := exp_shift_le10 103
    have hbase : (2:ℝ) ≤ 59874.142 * (904839/1000000)^103 := by norm_num
    have hd : tpt 103 - 2 ≤ 59874.142 * (904839/1000000)^103 - 2 := by linarith
    have hf2 : f4 2 ≤ ((0.6931471803:ℝ)^4)⁻¹ := by
      have hlog : (0.6931471803:ℝ) ≤ log 2 := le_of_lt Real.log_two_gt_d9
      have h0 : (0:ℝ) < 0.6931471803 := by norm_num
      have hp : (0.6931471803:ℝ)^4 ≤ (log 2)^4 := pow_le_pow_left₀ h0.le hlog 4
      have h6 := one_div_le_one_div_of_le (by positivity : (0:ℝ) < (0.6931471803:ℝ)^4) hp
      simpa [f4, one_div] using h6
    have hfl : f4 (tpt 103) = ((0.7:ℝ)^4)⁻¹ := by
      simp only [tpt, f4, Real.log_exp]
      norm_num
    have hS : f4 2 + f4 (tpt 103) ≤ ((0.6931471803:ℝ)^4)⁻¹ + ((0.7:ℝ)^4)⁻¹ := by
      rw [hfl]; linarith
    have hSn : (0:ℝ) ≤ f4 2 + f4 (tpt 103) := by
      have h1 : (0:ℝ) ≤ f4 2 := by simp only [f4]; positivity
      have h2 : (0:ℝ) ≤ f4 (tpt 103) := by simp only [f4]; positivity
      linarith
    have hb : (tpt 103 - 2) * (f4 2 + f4 (tpt 103))/2 ≤
        (59874.142 * (904839/1000000)^103 - 2) *
          (((0.6931471803:ℝ)^4)⁻¹ + ((0.7:ℝ)^4)⁻¹)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hd hS hSn (by linarith)
    rw [hCt103]
    refine hb.trans ?_
    norm_num
  have hsum : (∑ k ∈ Finset.range 103,
        (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
      ≤ (∑ k ∈ Finset.range 103, Ct k) := by
    apply Finset.sum_le_sum
    intro k hk
    exact (term_le_Db k).trans (Db_le_Ct k (Finset.mem_range.mp hk))
  have hcsum : (∑ k ∈ Finset.range 103, Ct k) + Ct 103 ≤ 10.33 := by
    have h := Ct_sum_le
    rw [Finset.sum_range_succ] at h
    exact h
  linarith

/-! ## Integrability of the integrands `(log t)^{-k}` -/

lemma continuousOn_logpow_inv {k : ℕ} :
    ContinuousOn (fun t : ℝ => ((log t)^k)⁻¹) (Ici (2:ℝ)) := by
  have h0 : ContinuousOn (fun t : ℝ => log t) (Ici (2:ℝ)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    have hx2 : (2:ℝ) ≤ x := hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith
  have h1 : ContinuousOn (fun t : ℝ => (log t)^k) (Ici (2:ℝ)) := h0.pow k
  refine h1.inv₀ (fun x hx => ?_)
  have hx2 : (2:ℝ) ≤ x := hx
  have hpos : 0 < log x := log_pos (by linarith)
  positivity

lemma ii_logpow_inv {k : ℕ} {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => ((log t)^k)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact continuousOn_logpow_inv.mono (by intro x hx; exact le_trans ha hx.1)
  · rw [uIcc_of_ge h]
    exact continuousOn_logpow_inv.mono (by intro x hx; exact le_trans hb hx.1)

lemma continuousOn_f4_Ioi : ContinuousOn f4 (Ioi (1:ℝ)) := by
  have h0 : ContinuousOn (fun t : ℝ => log t) (Ioi (1:ℝ)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    have hx1 : (1:ℝ) < x := hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith
  have h1 : ContinuousOn (fun t : ℝ => (log t)^4) (Ioi (1:ℝ)) := h0.pow 4
  refine h1.inv₀ (fun x hx => ?_)
  have hx1 : (1:ℝ) < x := hx
  have hpos : 0 < log x := log_pos hx1
  positivity

lemma intervalIntegrable_f4_Ioi {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable f4 volume a b := by
  apply ContinuousOn.intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact continuousOn_f4_Ioi.mono (by intro x hx; exact lt_of_lt_of_le ha hx.1)
  · rw [uIcc_of_ge h]
    exact continuousOn_f4_Ioi.mono (by intro x hx; exact lt_of_lt_of_le hb hx.1)

/-! ## The partial integrals `IL k y = ∫_2^y dt/(log t)^k` -/

/-- `IL k y = ∫_2^y dt / (log t)^k`. -/
noncomputable def IL (k : ℕ) (y : ℝ) : ℝ := ∫ t in (2:ℝ)..y, ((log t)^k)⁻¹

/-- The partial integral `∫_2^y dt/(log t)^4`, the same as `IL 4`. -/
noncomputable def I4f (y : ℝ) : ℝ := ∫ t in (2:ℝ)..y, f4 t

/-- One integration by parts: `∫_2^y dt/log t = y/log y - 2/log 2 + ∫_2^y dt/(log t)²`. -/
lemma IL_rec1 {y : ℝ} (hy : 2 ≤ y) : IL 1 y = y/log y - 2/log 2 + IL 2 y := by
  have hderiv : ∀ t ∈ uIcc (2:ℝ) y, HasDerivAt (fun s : ℝ => s/log s) (1/log t - 1/(log t)^2) t := by
    intro t ht
    rw [uIcc_of_le hy] at ht
    have ht2 : (2:ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : log t ≠ 0 := (log_pos (by linarith)).ne'
    have h1 : HasDerivAt (fun s : ℝ => log s) t⁻¹ t := hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => (log s)⁻¹) (-(t⁻¹) / (log t)^2) t := h1.inv hlog
    have h3 := (hasDerivAt_id t).mul h2
    have hval : 1 * (log t)⁻¹ + t * (-(t⁻¹) / (log t)^2) = 1/log t - 1/(log t)^2 := by
      field_simp
      ring
    rw [← hval]
    have hfun : (fun s : ℝ => s/log s) = id * (fun s : ℝ => (log s)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h3
  have ha : IntervalIntegrable (fun t : ℝ => 1/log t) volume 2 y := by
    simpa using ii_logpow_inv (k := 1) le_rfl hy
  have hb : IntervalIntegrable (fun t : ℝ => 1/(log t)^2) volume 2 y := by
    simpa using ii_logpow_inv (k := 2) le_rfl hy
  have hint : IntervalIntegrable (fun t : ℝ => 1/log t - 1/(log t)^2) volume 2 y := ha.sub hb
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub ha hb] at hInt
  have e1 : (∫ t in (2:ℝ)..y, 1/log t) = IL 1 y := by simp [IL, div_eq_mul_inv]
  have e2 : (∫ t in (2:ℝ)..y, 1/(log t)^2) = IL 2 y := by simp [IL, div_eq_mul_inv]
  rw [e1, e2] at hInt
  simp only [div_eq_mul_inv] at hInt ⊢
  linarith

/-- `∫_2^y dt/(log t)² = y/(log y)² - 2/(log 2)² + 2∫_2^y dt/(log t)³`. -/
lemma IL_rec2 {y : ℝ} (hy : 2 ≤ y) :
    IL 2 y = y/(log y)^2 - 2/(log 2)^2 + 2 * IL 3 y := by
  have hderiv : ∀ t ∈ uIcc (2:ℝ) y,
      HasDerivAt (fun s : ℝ => s/(log s)^2) (1/(log t)^2 - 2 * (1/(log t)^3)) t := by
    intro t ht
    rw [uIcc_of_le hy] at ht
    have ht2 : (2:ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : log t ≠ 0 := (log_pos (by linarith)).ne'
    have h1 : HasDerivAt (fun s : ℝ => log s) t⁻¹ t := hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => (log s)^2) (2 * log t * t⁻¹) t := by
      have hfun : (fun s : ℝ => (log s)^2) = (fun s : ℝ => log s)^2 := by
        funext s; rfl
      rw [hfun]
      simpa using h1.pow 2
    have h3 : HasDerivAt (fun s : ℝ => ((log s)^2)⁻¹)
        (-(2 * log t * t⁻¹) / ((log t)^2)^2) t := h2.inv (by positivity)
    have h4 := (hasDerivAt_id t).mul h3
    have hval : 1 * ((log t)^2)⁻¹ + t * (-(2 * log t * t⁻¹) / ((log t)^2)^2)
        = 1/(log t)^2 - 2 * (1/(log t)^3) := by
      field_simp
      ring
    rw [← hval]
    have hfun : (fun s : ℝ => s/(log s)^2) = id * (fun s : ℝ => ((log s)^2)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h4
  have ha : IntervalIntegrable (fun t : ℝ => 1/(log t)^2) volume 2 y := by
    simpa using ii_logpow_inv (k := 2) le_rfl hy
  have hb : IntervalIntegrable (fun t : ℝ => 2 * (1/(log t)^3)) volume 2 y := by
    have h := ii_logpow_inv (k := 3) (a := 2) (b := y) le_rfl hy
    simpa [mul_comm] using h.const_mul 2
  have hint : IntervalIntegrable (fun t : ℝ => 1/(log t)^2 - 2 * (1/(log t)^3)) volume 2 y :=
    ha.sub hb
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul] at hInt
  have e1 : (∫ t in (2:ℝ)..y, 1/(log t)^2) = IL 2 y := by simp [IL, div_eq_mul_inv]
  have e2 : (∫ t in (2:ℝ)..y, 1/(log t)^3) = IL 3 y := by simp [IL, div_eq_mul_inv]
  rw [e1, e2] at hInt
  simp only [div_eq_mul_inv] at hInt ⊢
  linarith

/-- `∫_2^y dt/(log t)³ = y/(log y)³ - 2/(log 2)³ + 3∫_2^y dt/(log t)⁴`. -/
lemma IL_rec3 {y : ℝ} (hy : 2 ≤ y) :
    IL 3 y = y/(log y)^3 - 2/(log 2)^3 + 3 * I4f y := by
  have hderiv : ∀ t ∈ uIcc (2:ℝ) y,
      HasDerivAt (fun s : ℝ => s/(log s)^3) (1/(log t)^3 - 3 * ((log t)^4)⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hy] at ht
    have ht2 : (2:ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : log t ≠ 0 := (log_pos (by linarith)).ne'
    have h1 : HasDerivAt (fun s : ℝ => log s) t⁻¹ t := hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => (log s)^3) (3 * (log t)^2 * t⁻¹) t := h1.pow 3
    have h3 : HasDerivAt (fun s : ℝ => ((log s)^3)⁻¹)
        (-(3 * (log t)^2 * t⁻¹) / ((log t)^3)^2) t := h2.inv (by positivity)
    have h4 := (hasDerivAt_id t).mul h3
    have hval : 1 * ((log t)^3)⁻¹ + t * (-(3 * (log t)^2 * t⁻¹) / ((log t)^3)^2)
        = 1/(log t)^3 - 3 * ((log t)^4)⁻¹ := by
      field_simp
      ring
    rw [← hval]
    have hfun : (fun s : ℝ => s/(log s)^3) = id * (fun s : ℝ => ((log s)^3)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h4
  have ha : IntervalIntegrable (fun t : ℝ => 1/(log t)^3) volume 2 y := by
    simpa using ii_logpow_inv (k := 3) le_rfl hy
  have hb : IntervalIntegrable (fun t : ℝ => 3 * ((log t)^4)⁻¹) volume 2 y := by
    have h := ii_logpow_inv (k := 4) (a := 2) (b := y) le_rfl hy
    simpa [mul_comm] using h.const_mul 3
  have hint : IntervalIntegrable (fun t : ℝ => 1/(log t)^3 - 3 * ((log t)^4)⁻¹) volume 2 y :=
    ha.sub hb
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul] at hInt
  have e1 : (∫ t in (2:ℝ)..y, 1/(log t)^3) = IL 3 y := by simp [IL, div_eq_mul_inv]
  have e2 : (∫ t in (2:ℝ)..y, ((log t)^4)⁻¹) = I4f y := by simp [I4f, f4]
  rw [e1, e2] at hInt
  simp only [div_eq_mul_inv] at hInt ⊢
  linarith

/-- `A = 2/log 2 + 2/(log 2)² + 4/(log 2)³`, the constant of the expansion. -/
def Aexpr : ℝ := 2/log 2 + 2/(log 2)^2 + 4/(log 2)^3

lemma Aexpr_ge : (19.0592 : ℝ) ≤ Aexpr := by
  have h2 : (0.6931471803 : ℝ) ≤ log 2 := le_of_lt Real.log_two_gt_d9
  have h3 : log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have h4 : (0:ℝ) < log 2 := by linarith
  have hsq : (log 2)^2 ≤ (0.6931471808:ℝ)^2 := pow_le_pow_left₀ h4.le h3 2
  have hcb : (log 2)^3 ≤ (0.6931471808:ℝ)^3 := pow_le_pow_left₀ h4.le h3 3
  have e1 : (2:ℝ)/0.6931471808 ≤ 2/log 2 := div_le_div_of_nonneg_left (by norm_num) h4 h3
  have e2 : (2:ℝ)/(0.6931471808)^2 ≤ 2/(log 2)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
  have e3 : (4:ℝ)/(0.6931471808)^3 ≤ 4/(log 2)^3 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hcb
  have e4 : (19.0592:ℝ) ≤ 2/(0.6931471808:ℝ) + 2/(0.6931471808:ℝ)^2 + 4/(0.6931471808:ℝ)^3 := by
    norm_num
  simp only [Aexpr]
  linarith

/-- The three integration-by-parts steps combined. -/
lemma IL_one_expansion {y : ℝ} (hy : 2 ≤ y) :
    IL 1 y = y/log y + y/(log y)^2 + 2 * (y/(log y)^3) - Aexpr + 6 * I4f y := by
  rw [IL_rec1 hy, IL_rec2 hy, IL_rec3 hy]
  simp only [Aexpr, div_eq_mul_inv]
  ring

/-! ## The monotonicity of `ψ y = y/(log y)³ - 6∫_2^y dt/(log t)^4` -/

lemma IL_one_eq (y : ℝ) : IL 1 y = ∫ t in (2:ℝ)..y, 1/log t := by
  simp [IL, div_eq_mul_inv]

lemma I4f_hasDerivAt {y : ℝ} (hy : 1 < y) : HasDerivAt I4f (f4 y) y := by
  have hcont : ContinuousAt f4 y := by
    have hfun : f4 = fun s : ℝ => ((log s)^4)⁻¹ := rfl
    rw [hfun]
    have h1 : ContinuousAt (fun s : ℝ => log s) y := Real.continuousAt_log (by linarith)
    refine (h1.pow 4).inv₀ ?_
    have hpos : 0 < log y := log_pos hy
    exact (pow_pos hpos 4).ne'
  have hsm : StronglyMeasurableAtFilter f4 (𝓝 y) volume := by
    have hcont' : ∀ x ∈ Ioi (1:ℝ), ContinuousAt f4 x := by
      intro x hx
      have hx1 : (1:ℝ) < x := hx
      have hfun : f4 = fun s : ℝ => ((log s)^4)⁻¹ := rfl
      rw [hfun]
      have h1 : ContinuousAt (fun s : ℝ => log s) x := Real.continuousAt_log (by linarith)
      refine (h1.pow 4).inv₀ ?_
      have hpos : 0 < log x := log_pos hx1
      exact (pow_pos hpos 4).ne'
    exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioi (1:ℝ)) isOpen_Ioi hcont' y hy
  have hint : IntervalIntegrable f4 volume 2 y := intervalIntegrable_f4_Ioi (by norm_num) hy
  exact intervalIntegral.integral_hasDerivAt_right hint hsm hcont


lemma exp_eleven_ge : (59874.1414 : ℝ) ≤ exp 11 := by
  have h1 : exp (11 : ℝ) = exp 1 ^ 11 := by
    simpa using Real.exp_nat_mul (x := (1 : ℝ)) 11
  rw [h1]
  have h2 : (2.7182818283 : ℝ) ≤ exp 1 := le_of_lt Real.exp_one_gt_d9
  have h3 : (2.7182818283:ℝ)^11 ≤ exp 1^11 := pow_le_pow_left₀ (by norm_num) h2 11
  have h4 : (59874.1414:ℝ) ≤ (2.7182818283:ℝ)^11 := by norm_num
  linarith

lemma f4_antitone : AntitoneOn f4 (Ici (2:ℝ)) := by
  intro a ha b hb hab
  have ha2 : (2:ℝ) ≤ a := ha
  have hb2 : (2:ℝ) ≤ b := hb
  have ha1 : (1:ℝ) < a := by linarith
  have hb1 : (1:ℝ) < b := by linarith
  have hla : 0 < log a := log_pos ha1
  have h1 : log a ≤ log b := log_le_log (by linarith) hab
  have h2 : (log a)^4 ≤ (log b)^4 := pow_le_pow_left₀ hla.le h1 4
  simp only [f4]
  simpa [one_div] using one_div_le_one_div_of_le (pow_pos hla 4) h2

/-- A crude lower bound for the whole integral, enough to dominate the expansion constant. -/
lemma I4f_exp11_ge : (3.4:ℝ) ≤ I4f (exp 11) := by
  have hy2 : (2:ℝ) ≤ exp 11 := by
    have h := Real.add_one_le_exp (11:ℝ)
    linarith
  have hexp11 : (59874.1414 : ℝ) ≤ exp 11 := exp_eleven_ge
  have hmono : ∫ x in (2:ℝ)..(exp 11), f4 x ≥ (exp 11 - 2) * f4 (exp 11) := by
    have hc : IntervalIntegrable (fun _ : ℝ => f4 (exp 11)) volume 2 (exp 11) := intervalIntegrable_const
    have hexp2 : (2:ℝ) ≤ exp 11 := hy2
    have hle : ∀ x ∈ Icc (2:ℝ) (exp 11), f4 (exp 11) ≤ f4 x := by
      intro x hx
      have hx2 : (2:ℝ) ≤ x := hx.1
      exact f4_antitone (by simpa using hx2) hexp2 hx.2
    have := intervalIntegral.integral_mono_on hy2 hc (intervalIntegrable_f4 le_rfl hy2) hle
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have hf4 : f4 (exp 11) = ((11:ℝ)^4)⁻¹ := by simp only [f4, Real.log_exp]
  have hval : (3.4:ℝ) ≤ (exp 11 - 2) * f4 (exp 11) := by
    rw [hf4]
    have h5 : (59874.1414 - 2) * ((11:ℝ)^4)⁻¹ ≤ (exp 11 - 2) * ((11:ℝ)^4)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h6 : (3.4:ℝ) ≤ (59874.1414 - 2) * ((11:ℝ)^4)⁻¹ := by norm_num
    linarith
  simp only [I4f]
  linarith

lemma Aexpr_le : Aexpr ≤ 19.0594 := by
  have h2 : (0.6931471803 : ℝ) ≤ log 2 := le_of_lt Real.log_two_gt_d9
  have h3 : (0:ℝ) < 0.6931471803 := by norm_num
  have hsq : (0.6931471803:ℝ)^2 ≤ (log 2)^2 := pow_le_pow_left₀ h3.le h2 2
  have hcb : (0.6931471803:ℝ)^3 ≤ (log 2)^3 := pow_le_pow_left₀ h3.le h2 3
  have e1 : (2:ℝ)/log 2 ≤ 2/0.6931471803 := div_le_div_of_nonneg_left (by norm_num) h3 h2
  have e2 : (2:ℝ)/(log 2)^2 ≤ 2/(0.6931471803)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
  have e3 : (4:ℝ)/(log 2)^3 ≤ 4/(0.6931471803)^3 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hcb
  have e4 : (2:ℝ)/0.6931471803 + 2/(0.6931471803)^2 + 4/(0.6931471803)^3 ≤ 19.0594 := by
    norm_num
  simp only [Aexpr]
  linarith

/-- `ψ y = y/(log y)³ - 6∫_2^y dt/(log t)^4`. -/
noncomputable abbrev psi (y : ℝ) : ℝ := y/(log y)^3 - 6 * I4f y

lemma psi_hasDerivAt {y : ℝ} (hy : 1 < y) : HasDerivAt psi ((log y - 9)/(log y)^4) y := by
  have hlog : (0:ℝ) < log y := log_pos hy
  have hy0 : y ≠ 0 := by linarith
  have h2 : HasDerivAt (fun s : ℝ => (log s)^3) (3 * (log y)^2 * y⁻¹) y := by
    have hfun : (fun s : ℝ => (log s)^3) = (fun s : ℝ => log s)^3 := by
      funext s; rfl
    rw [hfun]
    simpa using (hasDerivAt_log hy0).pow 3
  have h3 : HasDerivAt (fun s : ℝ => ((log s)^3)⁻¹)
      (-(3 * (log y)^2 * y⁻¹) / ((log y)^3)^2) y := h2.inv (by positivity)
  have h4 := (hasDerivAt_id y).mul h3
  have hval1 : 1 * ((log y)^3)⁻¹ + y * (-(3 * (log y)^2 * y⁻¹) / ((log y)^3)^2)
      = ((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹ := by
    field_simp
    ring
  have hfirst : HasDerivAt (fun s : ℝ => s/(log s)^3) (((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹) y := by
    rw [← hval1]
    have hfun : (fun s : ℝ => s/(log s)^3) = id * (fun s : ℝ => ((log s)^3)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h4
  have hsecond : HasDerivAt (fun s : ℝ => 6 * I4f s) (6 * f4 y) y :=
    (I4f_hasDerivAt hy).const_mul 6
  have hsum := hfirst.sub hsecond
  have hval2 : ((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹ - 6 * f4 y = (log y - 9)/(log y)^4 := by
    simp only [f4]
    field_simp
    ring
  have hsum' : HasDerivAt (fun s : ℝ => s / (log s)^3 - 6 * I4f s)
      (((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹ - 6 * f4 y) y := hsum
  rw [hval2] at hsum'
  simpa only [psi] using hsum'

lemma psi_mono : MonotoneOn psi (Ici (exp 11)) := by
  have hexp1 : (1:ℝ) < exp 11 := by
    have h := Real.add_one_le_exp (11:ℝ)
    linarith
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
  · intro y hy
    have hy1 : (1:ℝ) < y := lt_of_lt_of_le hexp1 hy
    exact (psi_hasDerivAt hy1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy1 : (1:ℝ) < y := lt_of_lt_of_le hexp1 (le_of_lt hy)
    exact (psi_hasDerivAt hy1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy1 : (1:ℝ) < y := lt_of_lt_of_le hexp1 (le_of_lt hy)
    rw [(psi_hasDerivAt hy1).deriv]
    have hL : (11:ℝ) ≤ log y := by
      have h := Real.log_le_log (Real.exp_pos 11) (le_of_lt hy)
      rwa [Real.log_exp] at h
    have hpos : (0:ℝ) < log y := by linarith
    apply div_nonneg _ (by positivity)
    linarith


/-- **The journal's two logarithmic integral bounds**, journal Lemma 11 proof p. 1228. -/
theorem li_bounds_large_proof (n : ℕ) (hn : exp 11 ≤ (n : ℝ)) :
    (1 + 1 / log (n : ℝ)) * n / log n ≤ LeanLab.BS2022GRH.liPV n ∧
      LeanLab.BS2022GRH.liPV n ≤ (1 + 1 / log (n : ℝ) + 3 / log n ^ 2) * n / log n := by
  have hy : (2:ℝ) ≤ (n:ℝ) := by
    have h : (2:ℝ) ≤ exp 11 := by
      have h2 := Real.add_one_le_exp (11:ℝ)
      linarith
    linarith
  have hy1 : (1:ℝ) < (n:ℝ) := by linarith
  have hL : (0:ℝ) < log (n:ℝ) := log_pos hy1
  have hL11 : (11:ℝ) ≤ log (n:ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 11) hn
    rwa [Real.log_exp] at h
  constructor
  · rw [LeanLab.BS2022GRH.liPV_eq_add hy, ← IL_one_eq, IL_one_expansion hy]
    have hli2 : (0:ℝ) ≤ LeanLab.BS2022GRH.liPV 2 := (LeanLab.BS2022GRH.liPV_two_le).1
    have hAup : Aexpr ≤ 19.0594 := Aexpr_le
    have hI4up : (3.4:ℝ) ≤ I4f (n:ℝ) := by
      have h1 : (3.4:ℝ) ≤ I4f (exp 11) := I4f_exp11_ge
      have hsplit : I4f (n:ℝ) = I4f (exp 11) + ∫ x in (exp 11)..(n:ℝ), f4 x := by
        rw [I4f, I4f]
        rw [intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_f4 le_rfl (by
          have h := Real.add_one_le_exp (11:ℝ); linarith)) (intervalIntegrable_f4 (by
          have h := Real.add_one_le_exp (11:ℝ); linarith) hy)]
      have h2 : (0:ℝ) ≤ ∫ x in (exp 11)..(n:ℝ), f4 x := by
        apply intervalIntegral.integral_nonneg hn
        intro t ht
        simp only [f4]
        positivity
      linarith
    have expand : (1 + 1 / log (n:ℝ)) * (n:ℝ)/log (n:ℝ)
        = (n:ℝ)/log (n:ℝ) + (n:ℝ)/(log (n:ℝ))^2 := by
      field_simp
      try ring
    rw [expand]
    simp only [div_eq_mul_inv] at hI4up ⊢
    have hpos : (0:ℝ) ≤ 2 * ((n:ℝ) * ((log (n:ℝ))^3)⁻¹) := by positivity
    linarith [hli2, hI4up, hAup, hpos]
  · rw [LeanLab.BS2022GRH.liPV_eq_add hy, ← IL_one_eq, IL_one_expansion hy]
    have hli2 : LeanLab.BS2022GRH.liPV 2 ≤ 2 := (LeanLab.BS2022GRH.liPV_two_le).2
    have hA := Aexpr_ge
    have hpsi : psi (exp 11) ≤ psi (n:ℝ) :=
      psi_mono (mem_Ici.mpr le_rfl) (hn : (n:ℝ) ∈ Ici (exp 11)) hn
    have hexp11 : (59874.1414 : ℝ) ≤ exp 11 := exp_eleven_ge
    have hI4e : I4f (exp 11) ≤ 10.33 := I4_exp11_le
    have hI4 : 6 * I4f (n:ℝ) ≤ (n:ℝ)/(log (n:ℝ))^3 + (Aexpr - 2) := by
      have hbase : -(Aexpr - 2) ≤ psi (exp 11) := by
        have h11 : ((11:ℝ))^3 = 1331 := by norm_num
        have h11' : ((11:ℝ)) * 11 * 11 = 1331 := by norm_num
        simp only [psi, Real.log_exp, div_eq_mul_inv, h11]
        have h1 : (44.984 : ℝ) ≤ exp 11 / 1331 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1331)]
          linarith
        linarith
      have hle : psi (exp 11) ≤ psi (n:ℝ) := hpsi
      simp only [psi, div_eq_mul_inv] at hle hbase ⊢
      linarith
    have expand : (1 + 1 / log (n:ℝ) + 3 / log (n:ℝ) ^ 2) * (n:ℝ)/log (n:ℝ)
        = (n:ℝ)/log (n:ℝ) + (n:ℝ)/(log (n:ℝ))^2 + 3 * ((n:ℝ)/(log (n:ℝ))^3) := by
      field_simp
      try ring
    rw [expand]
    simp only [div_eq_mul_inv] at hI4 hli2 ⊢
    linarith

end
end LiProof232

/-- LEAF. The two logarithmic integral bounds printed in the proof of Lemma 11, p. 1228.
The principal value convention is the existing lab liPV. -/
theorem li_bounds_large (n : ℕ) (hn : exp 11 ≤ (n : ℝ)) :
    (1 + 1 / log (n : ℝ)) * n / log n ≤ liPV n ∧
      liPV n ≤ (1 + 1 / log (n : ℝ) + 3 / log n ^ 2) * n / log n := by
  exact LiProof232.li_bounds_large_proof n hn

/-- LEAF. The upper half of journal Lemma 10 at z, pp. 1227 and 1232 display 23.
The lab UNfull convention is retained. This is a non-strict upper estimate. -/
theorem density_upper (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n) :
    DecompC169a.density n ≤ 8 * UNfull n / log n *
      (1 + 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) := by
  sorry

end LeanLab.BS2022GRH.PublishedInputs232
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_mu
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_phi
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma1_schoenfeld
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma4_robin
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma2_theta

#print axioms LeanLab.BS2022GRH.PublishedInputs232.weighted_reciprocal_primes

#print axioms LeanLab.BS2022GRH.PublishedInputs232.reciprocal_prime_interval

#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_mu_one_instance
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_phi_two_instance

#print axioms LeanLab.BS2022GRH.PublishedInputs232.li_bounds_large
#print axioms LeanLab.BS2022GRH.PublishedInputs232.density_upper
