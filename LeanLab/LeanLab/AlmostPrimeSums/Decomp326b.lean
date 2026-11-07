import LeanLab.AlmostPrimeSums.Decomp326a

/-!
AI wrote this Lean code for CODEX task326. Goldbach is open.
This is the lower main sum supply unit. The second stopping term and the remaining even stopping terms
are separated before their analytic estimates.
Sources: Nathanson pp. 242 to 244 equation 9.11, pp. 244 to 245
Lemma 9.4, and p. 256 Theorem 9.6.
Heath Brown, Lectures on sieves, pp. 35 to 36,
https://arxiv.org/abs/math/0209360.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b
open Finset Real BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a

/-- The second stopping term as a moving first boundary. This is the
finite recursion in Nathanson p. 244 equation 9.14 at n equal to two.
The inner prime set is truncated below p. -/
noncomputable def rosserSecondBoundary326 (s : BoundingSieve) (z D : ℝ) : ℝ :=
  ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
    s.nu p * rosserIntervalBoundary326 s (exp (log (D / (p : ℝ)) / 3)) (p : ℝ)

/-- The second continuous stopping coefficient on the range two through
four. Nathanson p. 246, the displayed evaluation following equation 9.20.
No approximation outside that parameter range is asserted. -/
noncomputable def rosserSecondModel326 (u : ℝ) : ℝ :=
  (u - 3 * log (u - 1) + 3 * log 3 - 4) / u

/-- The explicit second continuous coefficient is nonnegative on the
paper range. Nathanson p. 246, positivity following equation 9.17.
The proof uses the standard logarithm tangent inequality. -/
theorem rosserSecondModel_nonneg326 {u : ℝ} (hu : 2 ≤ u) (_hu4 : u ≤ 4) :
    0 ≤ rosserSecondModel326 u := by
  have hu1 : 0 < u - 1 := by linarith
  have hh := log_le_sub_one_of_pos (div_pos hu1 (by norm_num : (0 : ℝ) < 3))
  rw [log_div hu1.ne' (by norm_num)] at hh
  apply div_nonneg _ (by linarith : 0 ≤ u)
  nlinarith

/-- The second continuous stopping coefficient vanishes at four.
Nathanson p. 246 equation 9.19 at n equal to two. -/
theorem rosserSecondModel_four326 : rosserSecondModel326 4 = 0 := by
  unfold rosserSecondModel326
  norm_num

/-- The second model is exactly the integral recurrence applied to the
first continuous stopping coefficient. Nathanson p. 246 equations 9.20
and 9.21 at n equal to two. This evaluates the continuous coefficient
only and uses no prime distribution estimate. -/
theorem rosserSecondModel_eq_integral326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    rosserSecondModel326 u = (∫ t in u..(4 : ℝ), 3 / (t - 1) - 1) / u := by
  have hcont : ContinuousOn (fun t : ℝ => 3 / (t - 1)) (Set.uIcc u 4) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    rw [Set.uIcc_of_le hu4] at ht
    change t - 1 ≠ 0
    linarith [ht.1]
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume)
  have hshift : (∫ t in u..(4 : ℝ), 1 / (t - 1)) = log (3 / (u - 1)) := by
    calc
      _ = ∫ t in (u - 1)..((4 : ℝ) - 1), 1 / t :=
        intervalIntegral.integral_comp_sub_right (fun t : ℝ => 1 / t) 1
      _ = _ := by
        norm_num only [show (4 : ℝ) - 1 = 3 by norm_num]
        exact integral_one_div_of_pos (by linarith) (by norm_num)
  have hmul : (∫ t in u..(4 : ℝ), 3 / (t - 1)) =
      3 * ∫ t in u..(4 : ℝ), 1 / (t - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hmul, hshift,
    intervalIntegral.integral_const, log_div (by norm_num) (by linarith : u - 1 ≠ 0)]
  unfold rosserSecondModel326
  simp only [smul_eq_mul, mul_one]
  ring

/-- The logarithmic partial summation kernel has exactly the second
continuous coefficient. This is a derived change of variables form of
the integral on Nathanson p. 246 and the partial summation step on
pp. 251 to 252. No discrete prime comparison is asserted. -/
theorem rosserSecondModel_eq_kernel326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    rosserSecondModel326 u =
      ∫ x in (1 / 4 : ℝ)..(1 / u),
        3 / (1 - x) ^ 2 * (1 / (u * x) - 1) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hbounds : (1 / 4 : ℝ) ≤ 1 / u := by
    exact one_div_le_one_div_of_le hu0 hu4
  have hhalf : 1 / u ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hu
  let G : ℝ → ℝ := fun x =>
    (3 / u) * (log x - log (1 - x)) + (3 / u - 3) / (1 - x)
  have hd : ∀ x ∈ Set.uIcc (1 / 4 : ℝ) (1 / u),
      HasDerivAt G (3 / (1 - x) ^ 2 * (1 / (u * x) - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hbounds] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hlogx := hasDerivAt_log hx0.ne'
    have hlog1 := ((hasDerivAt_id x).const_sub 1).log hx1.ne'
    have hinv := ((hasDerivAt_id x).const_sub 1).inv hx1.ne'
    convert ((hlogx.sub hlog1).const_mul (3 / u)).add
      (hinv.const_mul (3 / u - 3)) using 1
    · funext y
      dsimp [G]
      ring
    · simp only [id_eq]
      field_simp [hu0.ne', hx0.ne', hx1.ne']
      <;> ring
  have hcont : ContinuousOn
      (fun x : ℝ => 3 / (1 - x) ^ 2 * (1 / (u * x) - 1))
      (Set.uIcc (1 / 4 : ℝ) (1 / u)) := by
    apply ContinuousOn.mul
    · apply continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      intro x hx
      rw [Set.uIcc_of_le hbounds] at hx
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      exact pow_ne_zero 2 hx1.ne'
    · apply ContinuousOn.sub _ continuousOn_const
      apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      intro x hx
      rw [Set.uIcc_of_le hbounds] at hx
      exact mul_ne_zero hu0.ne' (ne_of_gt (by linarith [hx.1] : 0 < x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  have hsub : 1 - 1 / u = (u - 1) / u := by field_simp
  dsimp [G, rosserSecondModel326]
  rw [hsub, log_div hu1.ne' hu0.ne', log_div (by norm_num : (1 : ℝ) ≠ 0) hu0.ne']
  norm_num [log_div, hu0.ne']
  field_simp [hu0.ne', hu1.ne']
  <;> ring

/-- The second stopping term is nonnegative. Nathanson p. 242 Lemma 9.3
and the finite recursion on p. 244. -/
theorem rosserSecondBoundary_nonneg326 (s : BoundingSieve) (z D : ℝ) :
    0 ≤ rosserSecondBoundary326 s z D := by
  apply Finset.sum_nonneg
  intro p hp
  have hpP := (Finset.mem_filter.mp hp).1
  exact mul_nonneg (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
    (Nat.dvd_of_mem_primeFactors hpP)).le (rosserIntervalBoundary_nonneg326 s _ _)

/-- The second stopping term is bounded by an explicit finite density
sum. For z at least eight and D at least z squared, every internal cube
threshold is at least two, so the moving prefix density bound applies.
This is the n equal to two reduction in Nathanson pp. 253 to 254 and
BJS p. 11, retaining the full local K over log threshold loss. -/
theorem rosserSecondBoundary_le_density_sum326 (s : BoundingSieve) (K z D : ℝ)
    (hden : LinearDensity s K) (hz : 8 ≤ z) (hDz : z ^ 2 ≤ D) :
    rosserSecondBoundary326 s z D ≤
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        s.nu p * rosserPrefixProduct326 s p *
          max 0 (log (p : ℝ) / log (exp (log (D / (p : ℝ)) / 3)) *
            (1 + K / log (exp (log (D / (p : ℝ)) / 3))) - 1) := by
  unfold rosserSecondBoundary326
  apply Finset.sum_le_sum
  intro p hp
  have hpP := (Finset.mem_filter.mp hp).1
  have hpz := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hpP).pos
  have hnu : 0 ≤ s.nu p := (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
    (Nat.dvd_of_mem_primeFactors hpP)).le
  have hV : 0 ≤ rosserPrefixProduct326 s p := Finset.prod_nonneg fun q hq =>
    (sub_pos.mpr (s.nu_lt_one_of_prime q
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))).le
  have hcut : 8 * (p : ℝ) ≤ D := by
    calc
      8 * (p : ℝ) ≤ 8 * z := mul_le_mul_of_nonneg_left hpz.le (by norm_num)
      _ ≤ z ^ 2 := by nlinarith
      _ ≤ D := hDz
  have hw : 2 ≤ exp (log (D / (p : ℝ)) / 3) := by
    have h8 : (8 : ℝ) ≤ D / (p : ℝ) := (le_div_iff₀ hp0).mpr (by simpa [mul_comm] using hcut)
    have hh := log_le_log (by norm_num : (0 : ℝ) < 8) h8
    have hlog8 : log (8 : ℝ) = 3 * log 2 := by
      convert log_pow (2 : ℝ) 3 using 1 <;> norm_num
    rw [hlog8] at hh
    calc
      (2 : ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
      _ ≤ exp (log (D / (p : ℝ)) / 3) := exp_le_exp.mpr (by linarith)
  by_cases hwlt : exp (log (D / (p : ℝ)) / 3) < p
  · have hh := rosserIntervalBoundary_le_density326 s K _ _ hden hw hwlt
    have hmax := mul_le_mul_of_nonneg_left (le_max_right 0
      (log (p : ℝ) / log (exp (log (D / (p : ℝ)) / 3)) *
        (1 + K / log (exp (log (D / (p : ℝ)) / 3))) - 1)) hV
    have hprod := mul_le_mul_of_nonneg_left (hh.trans hmax) hnu
    nlinarith only [hprod]
  · rw [rosserIntervalBoundary_eq_zero326 s _ _ (le_of_not_gt hwlt), mul_zero]
    exact mul_nonneg (mul_nonneg hnu hV) (le_max_left _ _)

/-- The second stopping recursion is an explicit sum of prefix product
differences, including empty internal intervals. Nathanson p. 245
equation 9.13 substituted into p. 244 equation 9.14. -/
theorem rosserSecondBoundary_eq_products326 (s : BoundingSieve) (z D : ℝ) :
    rosserSecondBoundary326 s z D =
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        s.nu p * (rosserPrefixProduct326 s (min (exp (log (D / (p : ℝ)) / 3)) p) -
          rosserPrefixProduct326 s p) := by
  unfold rosserSecondBoundary326
  apply Finset.sum_congr rfl
  intro p hp
  rw [rosserIntervalBoundary_eq_min326]

/-- The logarithmic cube threshold is equivalent to the exact stopping
inequality. Derived change of parameters in Nathanson p. 245 equation
9.13. All three real inputs are positive. -/
theorem rosser_threshold_le_iff326 (D p q : ℝ) (hD : 0 < D) (hp : 0 < p) (hq : 0 < q) :
    exp (log (D / p) / 3) ≤ q ↔ D ≤ p * q ^ 3 := by
  have he := rosser_first_threshold_cube (D / p) (div_pos hD hp)
  constructor
  · intro hh
    have hc := pow_le_pow_left₀ (exp_pos (log (D / p) / 3)).le hh 3
    rw [he] at hc
    simpa only [mul_comm] using (div_le_iff₀ hp).mp hc
  · intro hh
    have hc : D / p ≤ q ^ 3 := (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hq.le
    simpa only [he] using hc

/-- The second stopping term is exactly the finite double prime sum
with the failed cube cutoff. Nathanson p. 242 definition of T two and
p. 245 proof of equation 9.14. -/
theorem rosserSecondBoundary_eq_pairs326 (s : BoundingSieve) (z D : ℝ) (hD : 0 < D) :
    rosserSecondBoundary326 s z D =
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        s.nu p * ∑ q ∈ s.prodPrimes.primeFactors.filter
            (fun q : ℕ => q < p ∧ D ≤ (p : ℝ) * (q : ℝ) ^ 3),
          s.nu q * ∏ r ∈ s.prodPrimes.primeFactors.filter (fun r => r < q), (1 - s.nu r) := by
  classical
  unfold rosserSecondBoundary326 rosserIntervalBoundary326
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  congr 1
  apply Finset.sum_congr
  · ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq, hw, hqp⟩
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
      exact ⟨hq, by exact_mod_cast hqp, (rosser_threshold_le_iff326 D p q hD hp0 hq0).mp hw⟩
    · rintro ⟨hq, hqp, hcut⟩
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
      exact ⟨hq, (rosser_threshold_le_iff326 D p q hD hp0 hq0).mpr hcut,
        by exact_mod_cast hqp⟩
  · intro q hq
    rfl

/-- The second stopping term vanishes for D at least z to the fourth,
including the endpoint. Nathanson p. 242 Lemma 9.3 with n equal to two. -/
theorem rosserSecondBoundary_eq_zero326 (s : BoundingSieve) (z D : ℝ)
    (hz : 2 ≤ z) (hDz : z ^ 4 ≤ D) : rosserSecondBoundary326 s z D = 0 := by
  have hz0 : 0 < z := by linarith
  have hD : 0 < D := (pow_pos hz0 4).trans_le hDz
  rw [rosserSecondBoundary_eq_pairs326 s z D hD]
  apply Finset.sum_eq_zero
  intro p hp
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hpz := (Finset.mem_filter.mp hp).2
  have he : s.prodPrimes.primeFactors.filter
      (fun q : ℕ => q < p ∧ D ≤ (p : ℝ) * (q : ℝ) ^ 3) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro q hq
    obtain ⟨hqP, hqp, hcut⟩ := Finset.mem_filter.mp hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hqP).pos
    have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
    have hqz : (q : ℝ) < z := hqp'.trans hpz
    have hcube : (q : ℝ) ^ 3 < z ^ 3 := pow_lt_pow_left₀ hqz hq0.le (by norm_num)
    have hprod : (p : ℝ) * (q : ℝ) ^ 3 < z * z ^ 3 :=
      mul_lt_mul hpz hcube.le (pow_pos hq0 3) hz0.le
    have hzpow : z * z ^ 3 = z ^ 4 := by ring
    rw [hzpow] at hprod
    linarith
  rw [he, Finset.sum_empty, mul_zero]

/-- A candidate quadratic density error is absorbed by the requested
logarithmic scale. This is scalar error bookkeeping for the second term
calculation in Nathanson pp. 253 to 256. It does not assert that the
discrete stopping error satisfies this candidate envelope. -/
theorem second_error_absorption326 (K L : ℝ) (hK : 0 ≤ K) (hL : 1 ≤ L) :
    5 * (6 * K / L) + 5 * (6 * K / L) ^ 2 ≤
      (30 * K + 180 * K ^ 2) * L ^ (-(1 / 3 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hi0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hL0.le
  have hi1 : L⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hL
  have hisq : (L⁻¹) ^ 2 ≤ L⁻¹ := by nlinarith
  have hp : L⁻¹ ≤ L ^ (-(1 / 3 : ℝ)) := by
    rw [← rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hs := mul_le_mul_of_nonneg_left hisq (show 0 ≤ 180 * K ^ 2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hp (show 0 ≤ 30 * K + 180 * K ^ 2 by positivity)
  simp only [div_eq_mul_inv]
  nlinarith only [hs, hb]

/-- LEAF. The normalized second stopping term is bounded by its continuous
coefficient and a logarithmic error. This is only one double prime sum,
not the full lower moment. K is positive and z exceeds the fixed cutoff.
Nathanson p. 246 evaluation of f two, p. 253 Theorem 9.5 at n equal to
two, and BJS p. 11 Lemma 11. The varying error requires the small prime
separation from the lab density condition. -/
theorem jr_lower_second326 (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ),
      2 ≤ z → max 8 (exp (K + 2)) < z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      rosserSecondBoundary326 s z D /
          (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤
        rosserSecondModel326 (log D / log z) + C * log D ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- LEAF. The higher even stopping terms after removing the exact second
term satisfy their remaining coefficient bound. K is positive and z
exceeds the fixed cutoff. The separate second term is not estimated here.
Nathanson pp. 242 to 244 equation 9.11 and p. 256 Theorem 9.6 with
n equal to two removed from the sum. The logarithmic error remains OPEN. -/
theorem jr_lower_higher326 (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ),
      2 ≤ z → max 8 (exp (K + 2)) < z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D false n) -
          rosserSecondBoundary326 s z D /
            (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤
        1 - 2 * exp eulerMascheroniConstant * log (log D / log z - 1) /
          (log D / log z) - rosserSecondModel326 (log D / log z) +
          C * log D ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- The explicit lower coefficient formula also holds at the endpoint two.
Derived endpoint check for Nathanson p. 266 Theorem 9.8. -/
theorem fsieve_eq_log_of_two_le326 {u : ℝ} (hu : 2 ≤ u) :
    fsieve u = 2 * exp eulerMascheroniConstant * log (u - 1) / u := by
  rcases eq_or_lt_of_le hu with he | he
  · subst u
    norm_num [fsieve]
  · exact ite_eq_right (not_le_of_gt he)

/-- The remaining lower continuous coefficient after the second term
is strictly positive on the full range two through four. This confirms
the sign of the higher even series in Nathanson p. 251 equation 9.28.
It uses the explicit formulas on pp. 246 and 266. -/
theorem lower_higher_coefficient_pos326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    0 < 1 - fsieve u - rosserSecondModel326 u := by
  have hu0 : 0 < u := by linarith
  have hlog : log (u - 1) ≤ log 3 := log_le_log (by linarith) (by linarith)
  have hgamma := sieve_exp_gamma_bounds.1
  have hcoeff : 0 ≤ 2 * exp eulerMascheroniConstant - 3 := by linarith
  have hh := mul_le_mul_of_nonneg_left hlog hcoeff
  have hf := fsieve_four_lt_one
  rw [fsieve_four] at hf
  have hid : 1 - fsieve u - rosserSecondModel326 u =
      (4 - 3 * log 3 - (2 * exp eulerMascheroniConstant - 3) * log (u - 1)) / u := by
    rw [fsieve_eq_log_of_two_le326 hu]
    unfold rosserSecondModel326
    field_simp [hu0.ne']
    ring
  rw [hid]
  exact div_pos (by nlinarith) hu0

/-- Exact supply for jr_mainSum_lower from the second term and higher term leaves
and the proved bounded cutoff estimate. CONDITIONAL ON the two open
lower moment estimates. The conclusion is the exact original statement.
Nathanson p. 256 Theorem 9.6 and Heath Brown p. 36 Corollary 5.1. -/
theorem jr_mainSum_lower_supply326 (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))) ≤ s.mainSum (rosserWeight D false) := by
  by_cases hzero : K = 0
  · subst K
    exact jr_mainSum_lower_zero
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hzero)
  obtain ⟨Cb, hCb, hb⟩ := rosser_defect_log_bounded K (max 8 (exp (K + 2))) hK
    (by linarith [le_max_left (8 : ℝ) (exp (K + 2))])
  obtain ⟨C1, hC1, h1⟩ := jr_lower_second326 K hKpos
  obtain ⟨C2, hC2, h2⟩ := jr_lower_higher326 K hKpos
  refine ⟨Cb + C1 + C2, by positivity, ?_⟩
  intro s z D hz hzD hDz hP hden
  have hzsq : z ≤ z ^ 2 := by nlinarith
  have hzD' : z ≤ D := hzsq.trans hzD
  have hld : 0 < log D := log_pos (by linarith)
  have hlz : 0 < log z := log_pos (by linarith)
  have herr : 0 ≤ log D ^ (-(1 / 3 : ℝ)) := (rpow_pos_of_pos hld _).le
  have hs2 : 2 ≤ log D / log z := by
    apply (le_div_iff₀ hlz).mpr
    have hh := log_le_log (by positivity : 0 < z ^ 2) hzD
    rw [log_pow] at hh
    norm_num at hh
    linarith
  have hs4 : log D / log z ≤ 4 := by
    apply (div_le_iff₀ hlz).mpr
    have hh := log_le_log (by linarith : 0 < D) hDz
    rw [log_pow] at hh
    norm_num at hh
    linarith
  apply (rosser_lower_mainSum_iff_defect s D _).mpr
  by_cases hzB : z ≤ max 8 (exp (K + 2))
  · have hDz5 : D ≤ z ^ 5 := hDz.trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ z) (by norm_num))
    have hh := hb s z D hz hzB hzD' hDz5 hP hden false
    have hf := fsieve_lt_one _ (by linarith : 0 < log D / log z) hs4
    nlinarith [mul_nonneg hC1.le herr, mul_nonneg hC2.le herr]
  · have hlarge := lt_of_not_ge hzB
    rw [fsieve_eq_log_of_two_le326 hs2]
    have hsecond := h1 s z D hz hlarge hzD hDz hP hden
    have hhigher := h2 s z D hz hlarge hzD hDz hP hden
    nlinarith [mul_nonneg hCb.le herr]

/-- A concrete two prime sieve with four equally weighted elements and
local densities one half. Derived nonempty model of BJS p. 4 equations
3 and 4, used to check the stopping term definitions. -/
noncomputable def pairSieve326 : BoundingSieve where
  support := {1, 2, 3, 6}
  prodPrimes := 6
  prodPrimes_squarefree := by
    change Squarefree (2 * 3 : ℕ)
    exact (Nat.squarefree_mul (by norm_num : (2 : ℕ).Coprime 3)).mpr
      ⟨Nat.squarefree_two, Nat.prime_three.squarefree⟩
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := 4
  nu := ArithmeticFunction.prodPrimeFactors (fun _ => (1 / 2 : ℝ))
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := by
    intro p hp hpP
    norm_num [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]
  nu_lt_one_of_prime := by
    intro p hp hpP
    norm_num [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]

/-- The nonempty two prime model satisfies the density condition with
K equal to three log three. Derived concrete instance of the density
hypothesis used by the linear sieve in BJS p. 4 equation 4. -/
theorem pairSieve_density326 : LinearDensity pairSieve326 (3 * log 3) := by
  intro w w' hw hww'
  have hlw : 0 < log w := log_pos (by linarith)
  have hl3 : 0 < log 3 := log_pos (by norm_num)
  have hr : 1 ≤ log w' / log w := (le_div_iff₀ hlw).mpr
    (by simpa using (log_le_log (by linarith : 0 < w) hww'.le))
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by norm_num [Nat.primeFactors]
  change ∏ p ∈ (6 : ℕ).primeFactors.filter
    (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'), (1 - pairSieve326.nu p)⁻¹ ≤ _
  rw [hpf]
  have hn2 : pairSieve326.nu 2 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  have hn3 : pairSieve326.nu 3 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  by_cases hw3 : w ≤ 3
  · have hlog : log w ≤ log 3 := log_le_log (by linarith) hw3
    have hk : 3 ≤ 3 * log 3 / log w := (le_div_iff₀ hlw).mpr (by linarith)
    have hprod : (∏ p ∈ ({2, 3} : Finset ℕ).filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'), (1 - pairSieve326.nu p)⁻¹) ≤ 4 := by
      simp only [Finset.filter_insert, Finset.filter_singleton, Nat.cast_ofNat]
      split_ifs <;> norm_num [hn2, hn3]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hk)]
  · have he : ({2, 3} : Finset ℕ).filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w') = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨hp, hwp, _⟩
      rcases hp with rfl | rfl <;> norm_num at hwp <;> linarith
    rw [he, Finset.prod_empty]
    have hk : 0 ≤ 3 * log 3 / log w := div_nonneg (by positivity) hlw.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hk]

example : rosserSecondBoundary326 pairSieve326 4 20 = 1 / 4 := by
  have hpf : pairSieve326.prodPrimes.primeFactors = {2, 3} := by
    norm_num [pairSieve326, Nat.primeFactors]
  have hn2 : pairSieve326.nu 2 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  have hn3 : pairSieve326.nu 3 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  rw [rosserSecondBoundary_eq_pairs326 _ _ _ (by norm_num)]
  simp only [hpf]
  norm_num [Finset.filter_insert, Finset.filter_singleton, hn2, hn3]

example : rosserIntervalBoundary326 pairSieve326 2 4 = 3 / 4 := by
  have hpf : pairSieve326.prodPrimes.primeFactors = {2, 3} := by
    norm_num [pairSieve326, Nat.primeFactors]
  have hn2 : pairSieve326.nu 2 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  have hn3 : pairSieve326.nu 3 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  rw [rosserIntervalBoundary_eq_sub326 _ _ _ (by norm_num)]
  simp only [rosserPrefixProduct326, hpf]
  norm_num [Finset.filter_insert, Finset.filter_singleton, hn2, hn3]

example : rosserSecondModel326 4 = 0 := by
  unfold rosserSecondModel326
  norm_num

example : (∫ t in (2 : ℝ)..4, rosserIntervalBoundary326 pairSieve326 t 4) = 1 / 4 := by
  have hh := rosser_boundary_integral326 pairSieve326 2 4 (by norm_num)
    (fun _ => (1 : ℝ)) intervalIntegrable_const
  simp only [one_mul] at hh
  rw [hh]
  have hpf : pairSieve326.prodPrimes.primeFactors = {2, 3} := by
    norm_num [pairSieve326, Nat.primeFactors]
  have hn2 : pairSieve326.nu 2 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  have hn3 : pairSieve326.nu 3 = 1 / 2 := by
    norm_num [pairSieve326, ArithmeticFunction.prodPrimeFactors]
  simp only [hpf]
  norm_num [Finset.filter_insert, Finset.filter_singleton, hn2, hn3]

example : pairSieve326.siftedSum = 1 := by
  norm_num [BoundingSieve.siftedSum, pairSieve326, Finset.filter_insert, Finset.filter_singleton]

/-- Nonempty positive density data satisfy all four supply leaf domains
at levels z, z squared and z to the fourth. The upper ratios are one
and four. Derived nonvacuity check for BJS pp. 4 to 5 equations 4 to 6. -/
theorem supply_hypotheses_instance326 :
    ∃ (s : BoundingSieve) (K z : ℝ), 0 < K ∧ 2 ≤ z ∧
      max 8 (exp (K + 2)) < z ∧ LinearDensity s K ∧
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) ∧
      s.totalMass = 2 ∧ s.prodPrimes = 2 ∧
      log z / log z = 1 ∧ log (z ^ 2) / log z = 2 ∧ log (z ^ 4) / log z = 4 := by
  obtain ⟨s, hP, hmass, hnu, hden, hsift, hrem1, hrem2⟩ := single_prime_density_instance
  let K : ℝ := log 2
  let z : ℝ := max 8 (exp (K + 2)) + 1
  have hK : 0 < K := log_pos (by norm_num)
  have hz8 : 8 < z := by dsimp [z]; linarith [le_max_left (8 : ℝ) (exp (K + 2))]
  have hlog : log z ≠ 0 := (log_pos (by linarith : 1 < z)).ne'
  refine ⟨s, K, z, hK, by linarith, by dsimp [z]; linarith, hden, ?_,
    hmass, hP, div_self hlog, ?_, ?_⟩
  · intro p hp
    rw [hP, Nat.prime_two.primeFactors] at hp
    have hp2 : p = 2 := Finset.mem_singleton.mp hp
    subst p
    norm_num
    linarith
  · rw [log_pow]
    field_simp
    norm_num
  · rw [log_pow]
    field_simp
    norm_num

end LeanLab.AlmostPrimeSums.Decomp1527b
