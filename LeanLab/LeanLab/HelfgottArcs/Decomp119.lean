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
import LeanLab.PNTPort.LargeSieve.Dual

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

/-- Derived chord bound for the trigonometric sums on P0013 pages 10 and 11.
The distance is the absolute difference from the nearest integer. -/
theorem phase_chord_lower252 (α : ℝ) : 4 * |α - round α| ≤ ‖e α - 1‖ := by
  have he : LeanLab.PNTPort.LargeSieve.e α = e α := by
    unfold LeanLab.PNTPort.LargeSieve.e e
    congr 1
    push_cast
    ring
  simpa only [LeanLab.PNTPort.LargeSieve.dist0, he] using
    LeanLab.PNTPort.LargeSieve.four_dist0_le α

/-- Derived interval length bound for P0013 pages 10 and 11. -/
theorem interval_phase_length252 (α : ℝ) (M N : ℕ) :
    ‖∑ n ∈ range N, e (α * (M + n))‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ range N, ‖e (α * (M + n))‖ := norm_sum_le _ _
    _ = N := by simp [e, Complex.norm_exp]



/-- Derived finite geometric sum estimate for P0013 pages 10 and 11. -/
theorem interval_phase_chord252 (α : ℝ) (M N : ℕ) (hα : e α ≠ 1) :
    ‖∑ n ∈ range N, e (α * (M + n))‖ ≤ 2 / ‖e α - 1‖ := by
  have he (n : ℕ) : e (α * (M + n)) = e (α * M) * e α ^ n := by
    unfold e
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [← mul_sum, norm_mul, show ‖e (α * M)‖ = 1 by simp [e, Complex.norm_exp], one_mul,
    geom_sum_eq hα, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖e α ^ N - 1‖ ≤ ‖e α ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, e, Complex.norm_exp]

/-- Derived geometric minimum for P0013 pages 10 and 11.
Positive distance excludes the totalized reciprocal at integer frequencies. -/
theorem interval_phase_min252 (α : ℝ) (M N : ℕ) (hα : 0 < |α - round α|) :
    ‖∑ n ∈ range N, e (α * (M + n))‖ ≤ min (N : ℝ) (1 / (2 * |α - round α|)) := by
  have hc := phase_chord_lower252 α
  have hn : e α ≠ 1 := by
    intro he
    rw [he, sub_self, norm_zero] at hc
    linarith
  apply le_min (interval_phase_length252 α M N)
  apply (interval_phase_chord252 α M N hn).trans
  apply (div_le_div_iff₀ (by linarith : 0 < ‖e α - 1‖) (by positivity)).mpr
  linarith

/-- Distance stability for the rational approximation on P0013 page 10. -/
theorem nearest_distance_stable252 (α β : ℝ) : |β - round β| - |α - β| ≤ |α - round α| := by
  have h := round_le β (round α)
  have ht : |β - (round α : ℝ)| ≤ |α - β| + |α - round α| := by
    calc
      _ = |(β - α) + (α - round α)| := by congr 1; ring
      _ ≤ |β - α| + |α - round α| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm β α]
  linarith

/-- Derived rational residue estimate for P0013 pages 10 and 11. -/
theorem residue_gap252 (q r : ℕ) (hq : 0 < q) (hr : 1 ≤ r) (hrq : r < q)
    (β : ℝ) (hβ : |β - (r : ℝ) / q| ≤ 1 / (2 * q)) :
    ((min r (q-r):ℕ) : ℝ) / (2*q) ≤ |β - round β| := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hd : |(r:ℝ)/q - round ((r:ℝ)/q)| = ((min r (q-r):ℕ):ℝ)/q := by
    rw [abs_sub_round_div_natCast_eq, Nat.mod_eq_of_lt hrq]
  have hh := nearest_distance_stable252 β ((r:ℝ)/q)
  rw [hd] at hh
  have hm' : (1:ℝ) ≤ (min r (q-r):ℕ) := by exact_mod_cast (by omega : 1 ≤ min r (q-r))
  have hscale : 1 / (2 * (q:ℝ)) ≤ ((min r (q-r):ℕ):ℝ) / (2*q) := by
    exact div_le_div_of_nonneg_right hm' (by positivity)
  have hid : ((min r (q-r):ℕ):ℝ)/q = 2*(((min r (q-r):ℕ):ℝ)/(2*q)) := by ring
  linarith


/-- Derived rational residue estimate for P0013 pages 10 and 11. -/
theorem residue_harmonic252 (q : ℕ) (hq : 1 ≤ q) :
    ∑ r ∈ Icc 1 (q-1), (q:ℝ) / ((min r (q-r):ℕ):ℝ) ≤
      2 * q * (1 + Real.log q) := by
  have hpoint (r : ℕ) (hr : r ∈ Icc 1 (q-1)) :
      (q:ℝ) / ((min r (q-r):ℕ):ℝ) ≤ (q:ℝ)/r + (q:ℝ)/(q-r:ℕ) := by
    have hrbounds := mem_Icc.mp hr
    have hr0 : (0:ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
    have hqr : (0:ℝ) < (q-r:ℕ) := by exact_mod_cast (by omega : 0 < q-r)
    rcases le_total r (q-r) with hh | hh
    · rw [min_eq_left hh]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right hh]
      exact le_add_of_nonneg_left (by positivity)
  have hreflect : ∑ r ∈ Icc 1 (q-1), (q:ℝ)/(q-r:ℕ) =
      ∑ r ∈ Icc 1 (q-1), (q:ℝ)/r := by
    apply sum_bij (fun r _ => q-r)
    · intro r hr; simp only [mem_Icc] at *; omega
    · intro r hr s hs he; simp only [mem_Icc] at *; omega
    · intro r hr
      refine ⟨q-r, ?_, ?_⟩ <;> simp only [mem_Icc] at * <;> omega
    · intro r hr; rfl
  have hh : ∑ r ∈ Icc 1 (q-1), (q:ℝ)/r = q * (harmonic (q-1):ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      div_eq_mul_inv, mul_sum]
  calc
    _ ≤ ∑ r ∈ Icc 1 (q-1), ((q:ℝ)/r + (q:ℝ)/(q-r:ℕ)) := sum_le_sum hpoint
    _ = 2*q*(harmonic (q-1):ℝ) := by rw [sum_add_distrib, hreflect, hh]; ring
    _ ≤ 2*q*(1+Real.log q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (harmonic_le_one_add_log (q-1)).trans (by
        by_cases h : q=1
        · subst q; norm_num
        · gcongr
          · exact_mod_cast (by omega : 0 < q-1)
          · exact_mod_cast (by omega : q-1 ≤ q))


/-- Derived rational residue estimate for P0013 pages 10 and 11. -/
theorem dirichlet_residue_min252 (q : ℕ) (hq : 1 ≤ q) (β : ℕ → ℝ) (N : ℝ)
    (hβ : ∀ r ∈ Icc 1 (q-1), |β r - (r:ℝ)/q| ≤ 1/(2*q)) :
    ∑ r ∈ Icc 1 (q-1), min N (1/(2*|β r-round (β r)|)) ≤
      min ((q-1:ℕ)*N) (2*q*(1+Real.log q)) := by
  apply le_min
  · calc
      _ ≤ ∑ _r ∈ Icc 1 (q-1), N := sum_le_sum (fun _ _ => min_le_left _ _)
      _ = _ := by simp
  · apply le_trans (sum_le_sum (fun r hr => ?_)) (residue_harmonic252 q hq)
    have hr1 := (mem_Icc.mp hr).1
    have hrq : r < q := by have := (mem_Icc.mp hr).2; omega
    have hg := residue_gap252 q r (by omega) hr1 hrq (β r) (hβ r hr)
    have hm : (0:ℝ) < ((min r (q-r):ℕ):ℝ) := by exact_mod_cast (by omega : 0 < min r (q-r))
    have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hd : 0 < |β r - round (β r)| := lt_of_lt_of_le (by positivity) hg
    apply (min_le_right _ _).trans
    apply (div_le_div_iff₀ (by positivity) hm).mpr
    have hh' := (div_le_iff₀ (by positivity : 0 < 2*(q:ℝ))).mp hg
    nlinarith

/-- Derived coefficient or approximation input for P0013 pages 9 to 11. -/
theorem integer_residue_distance252 (a : ℤ) (q : ℕ) (hq : 0 < q) :
    |(a:ℝ)/q - round ((a:ℝ)/q)| =
      ((min ((a % (q:ℤ)).toNat) (q - (a % (q:ℤ)).toNat):ℕ):ℝ)/q := by
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hqm : (q:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hr0 : 0 ≤ a % (q:ℤ) := Int.emod_nonneg a hqm
  have hrq : (a % (q:ℤ)).toNat < q := by
    have hh := Int.emod_lt_of_pos a (show (0:ℤ) < q by exact_mod_cast hq)
    omega
  have hid : (a:ℝ)/q = ((a % (q:ℤ)).toNat:ℝ)/q + (a / (q:ℤ):ℤ) := by
    have hh := Int.emod_add_mul_ediv a (q:ℤ)
    have hh' := congrArg (fun k : ℤ => (k:ℝ)) hh
    push_cast at hh'
    have hrcast : ((a % (q:ℤ)).toNat:ℝ) = (a % (q:ℤ):ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg hr0
    rw [hrcast]
    field_simp
    linarith
  rw [hid, round_add_intCast]
  push_cast
  rw [show ((a % (q:ℤ)).toNat:ℝ)/q + (a / (q:ℤ):ℤ) -
    ((round (((a % (q:ℤ)).toNat:ℝ)/q):ℤ) + (a / (q:ℤ):ℤ)) =
    ((a % (q:ℤ)).toNat:ℝ)/q - round (((a % (q:ℤ)).toNat:ℝ)/q) by ring]
  rw [abs_sub_round_div_natCast_eq, Nat.mod_eq_of_lt hrq, Nat.cast_min]

/-- Derived coefficient or approximation input for P0013 pages 9 to 11. -/
theorem minor_phase_error252 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ) (n : ℕ) :
    |2 * α * n - (a:ℝ) * n / q| ≤
      (n:ℝ) / (q * (3/4 * x ^ ((2:ℝ)/3))) := by
  have he := h.2.2.1
  have hb := h.2.2.2.2.2
  have hid : 2 * α * n - (a:ℝ)*n/q = δ/x * n := by rw [he]; ring
  rw [hid, abs_mul, show |(n:ℝ)| = (n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    _ ≤ (1 / (q * (3/4 * x ^ ((2:ℝ)/3)))) * n :=
      mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg n)
    _ = _ := by ring


/-- Derived coefficient or approximation input for P0013 pages 9 to 11. -/
theorem minor_phase_error_half252 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (n : ℕ) (hn : (n:ℝ) ≤ (3/4*x^((2:ℝ)/3))/2) :
    |2*α*n - (a:ℝ)*n/q| ≤ 1/(2*q) := by
  apply (minor_phase_error252 x α a q δ h n).trans
  have hx0 : 0 < x := by linarith [h.1]
  have hq0 : (0:ℝ) < q := by exact_mod_cast h.2.1
  have hQ : 0 < 3/4*x^((2:ℝ)/3) := by positivity
  apply (div_le_div_iff₀ (mul_pos hq0 hQ) (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2*(q:ℝ))
  nlinarith

/-- Rational residues are distinct in a q interval, as used on P0013 page 10. -/
theorem coprime_residue_injective252 (a : ℤ) (q M : ℕ) (hq : 0 < q) (ha : Int.gcd a q = 1) :
    Set.InjOn (fun n : ℕ => (a*n) % (q:ℤ)) (Ico M (M+q)) := by
  intro n hn m hm he
  have hc : Int.gcd (q:ℤ) a = 1 := by rw [Int.gcd_comm]; exact ha
  have hd : (q:ℤ) ∣ a*((m:ℤ)-n) := by
    rw [mul_sub]
    exact (Int.modEq_iff_dvd).mp he
  have hd' := Int.dvd_of_dvd_mul_right_of_gcd_one hd hc
  have hn' := mem_Ico.mp hn
  have hm' := mem_Ico.mp hm
  rcases le_total n m with hh | hh
  · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (show (0:ℤ) ≤ (m:ℤ)-n by omega)
      (show (m:ℤ)-n < (q:ℤ) by omega) hd'
    omega
  · have hdn : (q:ℤ) ∣ (n:ℤ)-m := by simpa only [neg_sub] using dvd_neg.mpr hd'
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (show (0:ℤ) ≤ (n:ℤ)-m by omega)
      (show (n:ℤ)-m < (q:ℤ) by omega) hdn
    omega


/-- Derived Dirichlet reciprocal sum under MinorHyp, P0013 pages 10 to 13.
Only the portion below Q over two and not divisible by q is included. -/
theorem minor_reciprocal_sum252 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (s : Finset ℕ) (M : ℕ) (hs : s ⊆ Ico M (M+q))
    (hn : ∀ n ∈ s, (n:ℝ) ≤ (3/4*x^((2:ℝ)/3))/2)
    (hnd : ∀ n ∈ s, ¬ (q:ℤ) ∣ (n:ℤ)) (L : ℝ) :
    ∑ n ∈ s, min L (1/(2*|2*α*n-round (2*α*n)|)) ≤
      min ((s.card:ℝ)*L) (2*q*(1+Real.log q)) := by
  have hq := h.2.1
  have hqpos : 0 < q := by omega
  have hq0 : (0:ℝ) < q := by exact_mod_cast hqpos
  have ha := h.2.2.2.2.1
  let r : ℕ → ℕ := fun n => ((a*n) % (q:ℤ)).toNat
  have hr0 (n : ℕ) : 0 ≤ (a*n) % (q:ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hqpos))
  have hmem (n : ℕ) (hn' : n ∈ s) : r n ∈ Icc 1 (q-1) := by
    have hlt : r n < q := by
      have hh := Int.emod_lt_of_pos (a*n) (show (0:ℤ)<q by exact_mod_cast hqpos)
      dsimp [r]; omega
    have hne : (a*n) % (q:ℤ) ≠ 0 := by
      intro he
      have hd := Int.dvd_iff_emod_eq_zero.mpr he
      have hd' := Int.dvd_of_dvd_mul_right_of_gcd_one hd (by rw [Int.gcd_comm]; exact ha)
      exact hnd n hn' hd'
    have hp : 0 < r n := by dsimp [r]; have := hr0 n; omega
    simp only [mem_Icc]; omega
  have hinj : Set.InjOn r s := by
    intro n hn' m hm' he
    apply coprime_residue_injective252 a q M hqpos ha (hs hn') (hs hm')
    have he' := congrArg (fun k : ℕ => (k:ℤ)) he
    simpa only [r, Int.toNat_of_nonneg (hr0 n), Int.toNat_of_nonneg (hr0 m)] using he'
  have hp (n : ℕ) (hn' : n ∈ s) :
      min L (1/(2*|2*α*n-round (2*α*n)|)) ≤
        (q:ℝ)/((min (r n) (q-r n):ℕ):ℝ) := by
    have hb := minor_phase_error_half252 x α a q δ h n (hn n hn')
    have hd := nearest_distance_stable252 (2*α*n) ((a:ℝ)*n/q)
    have he := integer_residue_distance252 (a*n) q hqpos
    simp only [Int.cast_mul, Int.cast_natCast] at he
    rw [he] at hd
    change (((min (r n) (q-r n):ℕ):ℝ)/q) - |2*α*n-(a:ℝ)*n/q| ≤ _ at hd
    have hm : (1:ℝ) ≤ ((min (r n) (q-r n):ℕ):ℝ) := by
      have hh := mem_Icc.mp (hmem n hn')
      exact_mod_cast (by omega : 1 ≤ min (r n) (q-r n))
    have hg : ((min (r n) (q-r n):ℕ):ℝ)/(2*q) ≤ |2*α*n-round (2*α*n)| := by
      have hh : 1/(2*(q:ℝ)) ≤ ((min (r n) (q-r n):ℕ):ℝ)/(2*q) :=
        div_le_div_of_nonneg_right hm (by positivity)
      have heq : ((min (r n) (q-r n):ℕ):ℝ)/q =
        2*(((min (r n) (q-r n):ℕ):ℝ)/(2*q)) := by ring
      linarith
    have hmp : (0:ℝ) < ((min (r n) (q-r n):ℕ):ℝ) := by linarith
    have hdp : 0 < |2*α*n-round (2*α*n)| := lt_of_lt_of_le (by positivity) hg
    apply (min_le_right _ _).trans
    apply (div_le_div_iff₀ (by positivity) hmp).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 2*(q:ℝ))).mp hg
    nlinarith
  apply le_min
  · calc
      _ ≤ ∑ _n ∈ s, L := sum_le_sum (fun _ _ => min_le_left _ _)
      _ = _ := by simp
  · calc
      _ ≤ ∑ n ∈ s, (q:ℝ)/((min (r n) (q-r n):ℕ):ℝ) := sum_le_sum hp
      _ = ∑ k ∈ s.image r, (q:ℝ)/((min k (q-k):ℕ):ℝ) := (sum_image (f := fun k => (q:ℝ)/((min k (q-k):ℕ):ℝ)) hinj).symm
      _ ≤ ∑ k ∈ Icc 1 (q-1), (q:ℝ)/((min k (q-k):ℕ):ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro k hk; obtain ⟨n, hn', rfl⟩ := mem_image.mp hk; exact hmem n hn'
        · intros; positivity
      _ ≤ _ := residue_harmonic252 q hq

/-- Derived coefficient or approximation input for P0013 pages 9 to 11. -/
theorem cut_moebius_abs252 (T : ℝ) (n : ℕ) : |cut (ArithmeticFunction.moebius : ArithmeticFunction ℝ) T n| ≤ 1 := by
  by_cases hn : (n:ℝ) ≤ T
  · simp only [cut, ArithmeticFunction.coe_mk, if_pos hn]
    change |((ArithmeticFunction.moebius n : ℤ):ℝ)| ≤ 1
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · simp [cut, hn]


/-- Derived coefficient or approximation input for P0013 pages 9 to 11. -/
theorem cut_mangoldt_abs252 (T : ℝ) (n : ℕ) : |cut ArithmeticFunction.vonMangoldt T n| ≤ Real.log n := by
  by_cases hn : (n:ℝ) ≤ T
  · simp only [cut, ArithmeticFunction.coe_mk, if_pos hn]
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log
  · simp only [cut, ArithmeticFunction.coe_mk, if_neg hn, abs_zero]
    by_cases hn0 : n=0
    · simp [hn0]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0))

/-- Cut coefficient domination, derived from P0013 page 9. -/
theorem cut_abs_le252 (f : ArithmeticFunction ℝ) (T : ℝ) (n : ℕ) : |cut f T n| ≤ |f n| := by
  by_cases hn : (n:ℝ) ≤ T
  · simp [cut, hn]
  · simp [cut, hn]


/-- Pointwise Type I convolution bound, derived from P0013 page 9. -/
theorem cut_convolution_log252 (U V : ℝ) (n : ℕ) :
    |(cut (moebius : ArithmeticFunction ℝ) U * cut vonMangoldt V) n| ≤ Real.log n := by
  rw [mul_comm, mul_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [← log_apply, ← vonMangoldt_mul_zeta, mul_apply]
  apply sum_le_sum
  intro d hd
  rw [abs_mul]
  have hmu := cut_moebius_abs252 U d.2
  have hl := cut_abs_le252 vonMangoldt V d.1
  rw [abs_of_nonneg vonMangoldt_nonneg] at hl
  have hz : (zeta : ArithmeticFunction ℝ) d.2 = 1 := by
    rw [natCoe_apply, zeta_apply_ne (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd)]
    norm_num
  rw [hz, mul_one]
  exact (mul_le_mul_of_nonneg_left hmu (abs_nonneg _)).trans (by simpa using hl)

/-- Derived Cauchy Schwarz and weak large sieve input for P0013 page 45.
This retains the lab constant N plus two over delta, not the paper constant. -/
theorem bilinear_weak_sieve252 (s : Finset ℕ) (α δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ m ∈ s, ∀ m' ∈ s, m ≠ m' →
      δ ≤ |α*m - α*m' - round (α*m - α*m')|)
    (A : ℕ → ℂ) (B : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ‖∑ m ∈ s, A m * ∑ n ∈ Ioc M (M+N), B n * e ((n:ℝ)*α*m)‖^2 ≤
      (N+2/δ) * (∑ m ∈ s, ‖A m‖^2) *
        ∑ n ∈ Ioc M (M+N), ‖B n‖^2 := by
  have ht : ‖∑ m ∈ s, A m * ∑ n ∈ Ioc M (M+N), B n * e ((n:ℝ)*α*m)‖ ≤
      ∑ m ∈ s, ‖A m‖ * ‖∑ n ∈ Ioc M (M+N), B n * e ((n:ℝ)*α*m)‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun m => A m * ∑ n ∈ Ioc M (M+N), B n * e ((n:ℝ)*α*m))
  have hc := sum_mul_sq_le_sq_mul_sq s (fun m => ‖A m‖)
    (fun m => ‖∑ n ∈ Ioc M (M+N), B n * e ((n:ℝ)*α*m)‖)
  have he (t : ℝ) : LeanLab.PNTPort.LargeSieve.e t = e t := by
    unfold LeanLab.PNTPort.LargeSieve.e e
    congr 1
    push_cast
    ring
  have hls := LeanLab.PNTPort.LargeSieve.large_sieve hδ hs B M N
  simp only [he, ← mul_assoc] at hls
  have ht0 : 0 ≤ ∑ m ∈ s, ‖A m‖ * ‖∑ n ∈ Ioc M (M+N), B n * e ((n:ℝ)*α*m)‖ :=
    sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ (∑ m ∈ s, ‖A m‖ * ‖∑ n ∈ Ioc M (M+N), B n * e ((n:ℝ)*α*m)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ ≤ _ := hc.trans (by
      have hh := mul_le_mul_of_nonneg_left hls (sum_nonneg (s := s) (fun m hm => sq_nonneg ‖A m‖))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hh)

/-- The proved weak sieve constant is strictly above the sharp one from P0013 page 45.
This compares budgets and does not refute the paper's estimate. -/
theorem weak_sieve_constant_gap252 (N δ : ℝ) (hδ : 0 < δ) :
    N-1+1/δ < N+2/δ := by
  simp only [div_eq_mul_inv, one_mul]
  have hi := inv_pos.mpr hδ
  linarith


/-- Elementary low frequency portion of P0013 page 75 Lemma A.2.
The interval from seven eighths to 655 still requires its certificate. -/
theorem a2_low_frequency252 (δ : ℝ) (hδ : |δ| ≤ 7/8) :
    ‖(-2*Real.pi*Complex.I*(δ:ℂ))^2*fhat eta2 δ‖ ≤ 31.521 := by
  have hp : Real.pi < 22/7 := by linarith [Real.pi_lt_d20]
  have hn : ‖-2*(Real.pi:ℂ)*Complex.I*(δ:ℂ)‖ = 2*Real.pi*|δ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_mul, norm_pow, hn]
  have hb : 2*Real.pi*|δ| ≤ 11/2 := by nlinarith [Real.pi_pos, abs_nonneg δ]
  have hs : (2*Real.pi*|δ|)^2 ≤ (11/2:ℝ)^2 := pow_le_pow_left₀ (by positivity) hb 2
  have hf := norm_fhat_eta2_le_one δ
  have hm := mul_le_mul_of_nonneg_left hf (sq_nonneg (2*Real.pi*|δ|))
  nlinarith

/-- Nonzero residue distance for the short approximation range, P0013 pages 10 and 13. -/
theorem minor_nonresonant_distance252 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (n : ℕ) (hn : (n:ℝ) ≤ (3/4*x^((2:ℝ)/3))/2) (hnd : ¬ (q:ℤ) ∣ (n:ℤ)) :
    1/(2*q) ≤ |2*α*n-round (2*α*n)| := by
  have hq := h.2.1
  have hqp : 0 < q := by omega
  have hq0 : (0:ℝ) < q := by exact_mod_cast hqp
  have ha := h.2.2.2.2.1
  have hb := minor_phase_error_half252 x α a q δ h n hn
  have hd := nearest_distance_stable252 (2*α*n) ((a:ℝ)*n/q)
  have he := integer_residue_distance252 (a*n) q hqp
  simp only [Int.cast_mul, Int.cast_natCast] at he
  rw [he] at hd
  have hr0 : 0 ≤ (a*n) % (q:ℤ) := Int.emod_nonneg _ (by exact_mod_cast hqp.ne')
  have hrq : (a*n) % (q:ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hqp)
  have hrne : (a*n) % (q:ℤ) ≠ 0 := by
    intro hz
    have hh := Int.dvd_iff_emod_eq_zero.mpr hz
    exact hnd (Int.dvd_of_dvd_mul_right_of_gcd_one hh (by rw [Int.gcd_comm]; exact ha))
  have hm : (1:ℝ) ≤ ((min (((a*n) % (q:ℤ)).toNat) (q-((a*n) % (q:ℤ)).toNat):ℕ):ℝ) := by
    exact_mod_cast (show 1 ≤ min (((a*n) % (q:ℤ)).toNat) (q-((a*n) % (q:ℤ)).toNat) by omega)
  have hh := div_le_div_of_nonneg_right hm hq0.le
  have hid : 1/(q:ℝ) = 2*(1/(2*q)) := by ring
  linarith

/-- Full short block reciprocal bound, derived from P0013 pages 10 to 13.
At zero distance use the length cap, and retain at most one q multiple. -/
theorem minor_clipped_reciprocal_sum252 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (s : Finset ℕ) (M : ℕ) (hs : s ⊆ Ico M (M+q))
    (hn : ∀ n ∈ s, (n:ℝ) ≤ (3/4*x^((2:ℝ)/3))/2) (L : ℝ) (hL : 0 ≤ L) :
    ∑ n ∈ s, (if |2*α*n-round (2*α*n)| = 0 then L
      else min L (1/(2*|2*α*n-round (2*α*n)|))) ≤
      min ((s.card:ℝ)*L) (L+2*q*(1+Real.log q)) := by
  let F : ℕ → ℝ := fun n => if |2*α*n-round (2*α*n)| = 0 then L
    else min L (1/(2*|2*α*n-round (2*α*n)|))
  let t := s.filter (fun n : ℕ => (q:ℤ) ∣ (n:ℤ))
  let u := s.filter (fun n : ℕ => ¬ (q:ℤ) ∣ (n:ℤ))
  have hqp : 0 < q := by have := h.2.1; omega
  have hF (n : ℕ) : F n ≤ L := by
    dsimp [F]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hc : t.card ≤ 1 := by
    apply card_le_one.mpr
    intro n hn' m hm'
    have hn'' := mem_filter.mp hn'
    have hm'' := mem_filter.mp hm'
    apply coprime_residue_injective252 1 q M hqp (by simp) (hs hn''.1) (hs hm''.1)
    simpa only [one_mul] using
      (Int.emod_eq_zero_of_dvd hn''.2).trans (Int.emod_eq_zero_of_dvd hm''.2).symm
  have ht : ∑ n ∈ t, F n ≤ L := by
    calc
      _ ≤ ∑ _n ∈ t, L := sum_le_sum (fun n _ => hF n)
      _ = (t.card:ℝ)*L := by simp
      _ ≤ (1:ℝ)*L := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hL
      _ = _ := one_mul _
  have hu : ∑ n ∈ u, F n ≤ 2*q*(1+Real.log q) := by
    have hs' : u ⊆ Ico M (M+q) := fun n hn' => hs (mem_filter.mp hn').1
    have hnd : ∀ n ∈ u, ¬ (q:ℤ) ∣ (n:ℤ) := fun n hn' => (mem_filter.mp hn').2
    have hn' : ∀ n ∈ u, (n:ℝ) ≤ (3/4*x^((2:ℝ)/3))/2 :=
      fun n hn' => hn n (mem_filter.mp hn').1
    calc
      _ = ∑ n ∈ u, min L (1/(2*|2*α*n-round (2*α*n)|)) := by
        apply sum_congr rfl
        intro n hn''
        have hd := minor_nonresonant_distance252 x α a q δ h n (hn' n hn'') (hnd n hn'')
        have hq0 : (0:ℝ) < q := by exact_mod_cast hqp
        have hdne : |2*α*n-round (2*α*n)| ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hd)
        exact if_neg hdne
      _ ≤ _ := (minor_reciprocal_sum252 x α a q δ h u M hs' hn' hnd L).trans (min_le_right _ _)
  change (∑ n ∈ s, F n) ≤ _
  apply le_min
  · calc
      _ ≤ ∑ _n ∈ s, L := sum_le_sum (fun n _ => hF n)
      _ = _ := by simp
  · have he := sum_filter_add_sum_filter_not s (fun n : ℕ => (q:ℤ) ∣ (n:ℤ)) F
    change (∑ n ∈ t, _) + (∑ n ∈ u, _) = _ at he
    rw [← he]
    exact add_le_add ht hu

/-- Whole short block of geometric sums, derived from P0013 pages 10 to 13.
The possible q multiple contributes at most one interval length. -/
theorem minor_interval_phase_sum252 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (s : Finset ℕ) (M : ℕ) (hs : s ⊆ Ico M (M+q))
    (hn : ∀ n ∈ s, (n:ℝ) ≤ (3/4*x^((2:ℝ)/3))/2) (K N : ℕ) :
    ∑ n ∈ s, ‖∑ k ∈ range N, e ((2*α*n)*(K+k))‖ ≤
      min ((s.card:ℝ)*N) ((N:ℝ)+2*q*(1+Real.log q)) := by
  calc
    _ ≤ ∑ n ∈ s, (if |2*α*n-round (2*α*n)| = 0 then (N:ℝ)
        else min (N:ℝ) (1/(2*|2*α*n-round (2*α*n)|))) := by
      apply sum_le_sum
      intro n _
      by_cases hd : |2*α*n-round (2*α*n)| = 0
      · rw [if_pos hd]
        exact interval_phase_length252 (2*α*n) K N
      · rw [if_neg hd]
        exact interval_phase_min252 (2*α*n) K N
          (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd))
    _ ≤ _ := minor_clipped_reciprocal_sum252 x α a q δ h s M hs hn N (Nat.cast_nonneg N)

end LeanLab.HelfgottArcs.Decomp119
