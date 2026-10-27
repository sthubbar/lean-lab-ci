/-
P0013 large denominator main theorem, page 3 and pages 70 to 72.
The Type I leaf keeps the separate estimates before equation 5.61.
The odd restriction keeps a separate even prime power correction.
The existing MinorSI2 audit records a gap in the printed Type I bound.
The supported assembly has an enlarged budget. The 1218 result remains CITED only.
AI wrote the Lean code for CODEX task119. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.EvenPrimePowers119
import LeanLab.HelfgottArcs.MinorMain

namespace LeanLab.HelfgottArcs.Decomp119
open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Page 9 equation 2.21. The restriction of an arithmetic function to n at most T. -/
noncomputable def cut (f : ArithmeticFunction ℝ) (T : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ T then f n else 0, by simp⟩

/-- Page 70. The second choice of U. -/
noncomputable def U (x : ℝ) : ℝ := 500 * Real.sqrt 6 * x ^ ((1 : ℝ) / 3)

/-- Page 70. The second choice of V. -/
noncomputable def V (x : ℝ) : ℝ := x ^ ((1 : ℝ) / 3) / 3

/-- Page 9 equations 2.21 and 2.22. An odd weighted convolution coefficient sum. -/
noncomputable def weighted (f : ArithmeticFunction ℝ) (α x : ℝ) : ℂ :=
  ∑ n ∈ range ⌈x⌉₊, (f n : ℂ) *
    (if Odd n then e (α * n) * (eta2 (n / x) : ℂ) else 0)

/-- Page 9 equation 2.21. The Type I logarithmic sum, in convolution notation. -/
noncomputable def I₁ (α x : ℝ) : ℂ :=
  weighted (cut (moebius : ArithmeticFunction ℝ) (U x) * log) α x

/-- Page 9 equation 2.21. The second Type I sum, in convolution notation. -/
noncomputable def I₂ (α x : ℝ) : ℂ :=
  weighted (cut (moebius : ArithmeticFunction ℝ) (U x) * cut vonMangoldt (V x) *
    (zeta : ArithmeticFunction ℝ)) α x

/-- Page 9 equation 2.21. The Type II sum, in convolution notation. -/
noncomputable def II (α x : ℝ) : ℂ :=
  weighted (((moebius : ArithmeticFunction ℝ) - cut (moebius : ArithmeticFunction ℝ) (U x)) *
    (vonMangoldt - cut vonMangoldt (V x)) * (zeta : ArithmeticFunction ℝ)) α x

/-- Page 9 equation 2.21. The short von Mangoldt remainder. -/
noncomputable def shortR (α x : ℝ) : ℂ := weighted (cut vonMangoldt (V x)) α x

/-- Page 9 equation 2.23. The even contribution, with prime powers retained. -/
noncomputable def evenR (α x : ℝ) : ℂ :=
  ∑ n ∈ range ⌈x⌉₊, if Even n then
    (vonMangoldt n : ℂ) * e (α * n) * (eta2 (n / x) : ℂ) else 0

/-- LEAF. Page 9 equations 2.20 to 2.23. Vaughan's exact identity with the even remainder. -/
theorem vaughan_split (α x : ℝ) (hx : 0 < x) :
    S eta2 α x = I₁ α x - I₂ α x + II α x + shortR α x + evenR α x := by
  have hid : vonMangoldt =
      cut (moebius : ArithmeticFunction ℝ) (U x) * log -
        cut (moebius : ArithmeticFunction ℝ) (U x) * cut vonMangoldt (V x) *
          (zeta : ArithmeticFunction ℝ) +
        ((moebius : ArithmeticFunction ℝ) - cut (moebius : ArithmeticFunction ℝ) (U x)) *
          (vonMangoldt - cut vonMangoldt (V x)) * (zeta : ArithmeticFunction ℝ) +
        cut vonMangoldt (V x) := by
    rw [← vonMangoldt_mul_zeta]
    have hmu : (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
      coe_moebius_mul_coe_zeta
    linear_combination - (vonMangoldt - cut vonMangoldt (V x)) * hmu
  have hw := congrArg (fun f : ArithmeticFunction ℝ => weighted f α x) hid
  have hw' : weighted vonMangoldt α x = I₁ α x - I₂ α x + II α x + shortR α x := by
    simpa only [weighted, I₁, I₂, II, shortR, ArithmeticFunction.add_apply,
      sub_eq_add_neg, ArithmeticFunction.neg_apply, Complex.ofReal_add, Complex.ofReal_neg,
      add_mul, neg_mul, sum_add_distrib, sum_neg_distrib] using hw
  rw [← hw', S_eta2_eq_sum α x hx]
  unfold weighted evenR
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  by_cases ho : Odd n
  · simp [ho, Nat.not_even_iff_odd.mpr ho, mul_assoc]
  · simp [ho, Nat.not_odd_iff_even.mp ho, mul_assoc]

/-- LEAF. Pages 51 and 70. The short remainder vanishes below the support of eta2. -/
theorem shortR_zero (α x : ℝ) (hx : 2.16e20 ≤ x) : shortR α x = 0 := by
  have hx0 : 0 < x := by linarith
  have hp : x ^ ((1 : ℝ) / 3) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hs : Real.sqrt x ≤ x / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  unfold shortR weighted
  apply sum_eq_zero
  intro n hn
  by_cases hnV : (n : ℝ) ≤ V x
  · have hn4 : (n : ℝ) / x < 1 / 4 := by
      rw [div_lt_iff₀ hx0]
      unfold V at hnV
      linarith
    have hz : eta2 ((n : ℝ) / x) = 0 := eta2_of_lt hn4
    simp [hz]
  · simp [cut, hnV]


/-- LEAF. Page 70, last Type I logarithmic bound before equation 5.58.
Inputs include Granville and Ramare 1996 Lemma 10.2 and Ramare, page 7 equations 2.9 and 2.10. -/
theorem typeI₁_bound (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖I₁ α x‖ ≤ 4.1982 * x ^ ((2 : ℝ) / 3) * Real.log x +
      0.001063 * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2 := by
  sorry

/-- Pages 70 and 71, corrected 3.49 plus the larger of the separate 3.50 and 3.51 bounds.
The first term uses MinorSI2.firstLine_eq, not the incorrect printed 3/2 coefficient.
The 3.51 term is kept before its final coarse rounding. -/
noncomputable def typeI₂Budget (x : ℝ) : ℝ :=
  let A := x ^ ((2 : ℝ) / 3) * Real.log x
  let B := x ^ ((2 : ℝ) / 3) * Real.log x ^ 2
  3 * x ^ ((2 : ℝ) / 3) * (2 / 3 * Real.log x - Real.log 18) + 0.02017 * A +
    max (1177.64 * A + 0.0006406 * B)
      (1212.591 * A + 29.131 * Real.sqrt x * Real.log x)

/-- LEAF. Pages 70 and 71, the sum of separate Type I estimates with corrected 3.49.
Inputs include Rosser and Schoenfeld 1962 and the explicit prime sum bounds on pages 8 and 9.
This statement does not use the unsupported printed total 1213.15. -/
theorem typeI₂_bound (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖I₂ α x‖ ≤ typeI₂Budget x := by
  sorry

/-- LEAF. Page 72 equation 5.60, including its two smaller cases.
Inputs include Montgomery and Vaughan 1974 and Montgomery 1968 through Lemma 4.3. -/
theorem typeII_bound (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖II α x‖ ≤ 0.272652 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF. Page 9 equation 2.23. A derived allowance for the retained even contribution. -/
theorem evenR_bound (α x : ℝ) (hx : 2.16e20 ≤ x) :
    ‖evenR α x‖ ≤ 0.65 * x ^ ((2 : ℝ) / 3) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hc0 : (0 : ℝ) < ⌈x⌉₊ := hx0.trans_le (Nat.le_ceil x)
  have hc : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have hh := Nat.ceil_lt_add_one hx0.le
    linarith
  have hlog : Real.log (⌈x⌉₊ : ℝ) ≤ 2 * Real.log x := by
    have hh := Real.log_le_log hc0 hc
    rw [Real.log_mul (by norm_num) hx0.ne'] at hh
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ x)
    linarith
  have hp : 16 ≤ x ^ ((2 : ℝ) / 3) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4 ^ (3 : ℕ))
      (by linarith : (4 : ℝ) ^ (3 : ℕ) ≤ x) (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at hh
    norm_num at hh
    exact hh
  calc
    _ ≤ 4 * Real.log 2 * Real.log (⌈x⌉₊ : ℝ) :=
      EvenPrimePowers119.norm_even_sum_le α x hx0
    _ ≤ 8 * Real.log x := by
      have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * Real.log 2)
      have h2 := Real.log_two_lt_d9
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) hL


/-- LEAF. Page 72 equation 5.61. Absorb the logarithm squared term into the spare Type II coefficient. -/
theorem absorb_log_sq (x : ℝ) (hx : 2.16e20 ≤ x) :
    (0.001063 + 0.0006406) * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2 ≤
      (0.2727 - 0.272652) * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  let s := x ^ ((1 : ℝ) / 12)
  let t := x ^ ((1 : ℝ) / 6)
  have hs0 : 0 ≤ s := Real.rpow_nonneg hx0.le _
  have hs : 32 ≤ s := by
    have hb : (32 : ℝ) ^ (12 : ℕ) ≤ x := by linarith
    have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 32 ^ (12 : ℕ)) hb
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at hh
    norm_num at hh
    exact hh
  have ht : t = s ^ 2 := by
    dsimp [t, s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    norm_num
  have hlog : Real.log x ≤ 12 * s := by
    have hh := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 12)
    dsimp [s]
    linarith
  have hcube : (32 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  have hfour : 32768 * s ≤ s ^ 4 := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hcube)]
  have hroot : Real.sqrt (Real.log x) ≤ t / 40 := by
    rw [Real.sqrt_le_iff]
    constructor
    · rw [ht]; positivity
    · rw [ht]
      nlinarith
  have hsq := Real.sq_sqrt hL
  have ht0 : 0 ≤ t := Real.rpow_nonneg hx0.le _
  have hr0 := Real.sqrt_nonneg (Real.log x)
  have hscale : (0.001063 + 0.0006406) * Real.log x ≤
      (0.2727 - 0.272652) * t * Real.sqrt (Real.log x) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hroot)]
  have hp : x ^ ((5 : ℝ) / 6) = x ^ ((2 : ℝ) / 3) * t := by
    dsimp [t]
    rw [← Real.rpow_add hx0]
    congr 1
    norm_num
  have hlp : Real.log x ^ ((3 : ℝ) / 2) = Real.log x * Real.sqrt (Real.log x) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = Real.log x ^ (1 : ℝ) * Real.log x ^ ((1 : ℝ) / 2) :=
        Real.rpow_add (Real.log_pos (by linarith : 1 < x)) _ _
      _ = _ := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hp, hlp]
  have hh := mul_le_mul_of_nonneg_left hscale
    (mul_nonneg (Real.rpow_nonneg hx0.le ((2 : ℝ) / 3)) hL)
  nlinarith


/-- Derived total from the supported separate estimates, including the even allowance.
No comparison with the cited constant 1218 is assumed. -/
noncomputable def largeBudget (x : ℝ) : ℝ :=
  4.1982 * x ^ ((2 : ℝ) / 3) * Real.log x +
    0.001063 * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2 + typeI₂Budget x +
    0.272652 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) +
    0.65 * x ^ ((2 : ℝ) / 3) * Real.log x

/-- The supported budget assembly, CONDITIONAL ON the three displayed analytic estimates. -/
theorem large_budget_of_estimates (x α : ℝ) (hx : 2.16e20 ≤ x)
    (h1 : ‖I₁ α x‖ ≤ 4.1982 * x ^ ((2 : ℝ) / 3) * Real.log x +
      0.001063 * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2)
    (h2 : ‖I₂ α x‖ ≤ typeI₂Budget x)
    (h3 : ‖II α x‖ ≤ 0.272652 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2)) :
    ‖S eta2 α x‖ ≤ largeBudget x := by
  have he := evenR_bound α x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [vaughan_split α x hx0, shortR_zero α x hx, add_zero]
  calc
    ‖I₁ α x - I₂ α x + II α x + evenR α x‖ ≤
        ‖I₁ α x‖ + ‖I₂ α x‖ + ‖II α x‖ + ‖evenR α x‖ := by
      calc
        _ ≤ ‖I₁ α x - I₂ α x + II α x‖ + ‖evenR α x‖ := norm_add_le _ _
        _ ≤ (‖I₁ α x - I₂ α x‖ + ‖II α x‖) + ‖evenR α x‖ := by
          gcongr; exact norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_sub_le _ _
    _ ≤ largeBudget x := by
      unfold largeBudget
      linarith

/-- The supported total, CONDITIONAL ON the three analytic leaves. -/
theorem large_budget_from_leaves (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖S eta2 α x‖ ≤ largeBudget x :=
  large_budget_of_estimates x α h.1 (typeI₁_bound x α a q δ h hq)
    (typeI₂_bound x α a q δ h hq) (typeII_bound x α a q δ h hq)

/-- Existing F-5006 arithmetic audit, with a certified excess greater than 0.4.
This is the coarse 1213.15 contribution model, not a lower bound for the actual sum
or for largeBudget. No comparison of the supported budget with 1218 is supplied. -/
theorem coarse_1218_shortfall :
    MinorMain.target (Real.log 2.16e20) (1000 * Real.sqrt 6) + 0.4 <
      MinorMain.total (Real.log 2.16e20) (1000 * Real.sqrt 6)
        (3 * (2 / 3 * Real.log 2.16e20 - Real.log 18) / Real.log 2.16e20 + 0.02017) :=
  MinorMain.corrected_exceeds

/-- CITED ONLY. Compatibility alias to the original cited Main Theorem.
This is not derived from the supported leaves. The rejected assembly is withdrawn.
The comparison with 1218 remains open. See large_budget_from_leaves and coarse_1218_shortfall. -/
theorem minorArcs_large (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (hq : x ^ ((1 : ℝ) / 3) / 6 < q) : ‖S eta2 α x‖ ≤ minorBoundLarge x :=
  LeanLab.HelfgottArcs.minorArcs_large x α a q δ h hq

end LeanLab.HelfgottArcs.Decomp119
