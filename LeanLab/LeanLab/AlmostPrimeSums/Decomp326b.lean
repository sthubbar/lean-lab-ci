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

/-! ### Helpers for `jr_lower_second326`

Private helper theorems only (nothing new is declared at type level).
The second stopping term of the lower linear sieve, normalised by the sieve
product, is evaluated against the density hypothesis by summation by parts on
a geometric grid, giving the continuous second coefficient
`rosserSecondModel326` plus an explicit `(1+K)^3 (log D)^(-1/3)` error.
Nathanson pp. 245 to 246 and pp. 251 to 253; BJS p. 11.
-/

/-- The second continuous coefficient is the `dt/t` integral of the
increasing weight `(4t-u)/(t(u-t))` over the stopping range `[u/4,1]`.
This is the change of variables used in the discrete-to-integral step of the
second stopping term (Nathanson p. 246 and pp. 251 to 252), written as a
standalone calculus identity. -/
private theorem second_model_eq_tail_integral326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    rosserSecondModel326 u =
      ∫ t in (u / 4)..(1 : ℝ), 3 / (t * (u - t)) - 1 / t ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hle : u / 4 ≤ (1 : ℝ) := by linarith
  have hq : 0 < u / 4 := by linarith
  let F : ℝ → ℝ := fun t => (3 / u) * (log t - log (u - t)) + 1 / t
  have hderiv : ∀ t ∈ Set.uIcc (u / 4) (1 : ℝ),
      HasDerivAt F (3 / (t * (u - t)) - 1 / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have ht0 : t ≠ 0 := by
      have : 0 < t := by linarith [ht.1]
      exact this.ne'
    have htu : u - t ≠ 0 := by
      have : t < u := by linarith [ht.2]
      linarith
    have hlogt : HasDerivAt log (1 / t) t := by
      simpa only [one_div] using hasDerivAt_log ht0
    have hlogu : HasDerivAt (fun y : ℝ => log (u - y)) (1 / (u - t) * (-1)) t := by
      have h := ((hasDerivAt_const t u).sub (hasDerivAt_id t)).log htu
      rw [show ((fun x : ℝ => u) - id) = fun y : ℝ => u - y from rfl] at h
      have h2 : (0 - 1) / (u - t) = 1 / (u - t) * (-1) := by ring
      simpa only [h2, id_eq] using h
    have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(t ^ 2)⁻¹) t := by
      simpa only [one_div] using hasDerivAt_inv ht0
    have hmain : HasDerivAt F ((3 / u) * (1 / t - 1 / (u - t) * (-1)) + -(t ^ 2)⁻¹) t := by
      have h1 : HasDerivAt (fun y : ℝ => (3 / u) * (log y - log (u - y)))
          ((3 / u) * (1 / t - 1 / (u - t) * (-1))) t :=
        (hlogt.sub hlogu).const_mul (3 / u)
      exact h1.add hinv
    convert hmain using 1
    field_simp [ht0, htu]
    ring
  have hcont : ContinuousOn (fun t : ℝ => 3 / (t * (u - t)) - 1 / t ^ 2)
      (Set.uIcc (u / 4) (1 : ℝ)) := by
    apply ContinuousOn.sub
    · apply continuousOn_const.div
        (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have htu : u - t ≠ 0 := by linarith [ht.2]
      exact mul_ne_zero ht0 htu
    · apply continuousOn_const.div (continuousOn_id.pow 2)
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      exact pow_ne_zero 2 ht0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hF1 : F 1 = (3 / u) * (-log (u - 1)) + 1 := by
    dsimp [F]
    norm_num
  have hFq : F (u / 4) = (3 / u) * (-log 3) + 4 / u := by
    dsimp [F]
    have h1 : u - u / 4 = 3 * u / 4 := by ring
    have h2 : log (u / 4) - log (3 * u / 4) = -log 3 := by
      have hqr : u / 4 = (1 / 3) * (3 * u / 4) := by ring
      rw [hqr, log_mul (by norm_num : (1 : ℝ) / 3 ≠ 0) (by positivity),
        log_div (by norm_num) (by norm_num), log_one]
      ring
    rw [h1, h2]
    field_simp
  rw [hF1, hFq]
  unfold rosserSecondModel326
  field_simp
  ring


/-- The weight `(4t-u)/(t(u-t))` is nonnegative and increasing on the stopping
range `[u/4,1]`, and it vanishes at the lower endpoint.  This is the weight
that the second stopping sum produces after the two density estimates, and it
is the weight whose `dt/t` integral is the continuous second coefficient. -/
private theorem psi_nonneg326 {u t : ℝ} (hu : 2 ≤ u) (h1 : u / 4 ≤ t) (h2 : t ≤ 1) :
    0 ≤ (4 * t - u) / (t * (u - t)) := by
  have hu0 : 0 < u := by linarith
  have ht : 0 < t := by linarith
  have htu : 0 < u - t := by linarith
  apply div_nonneg _ (by positivity)
  linarith

/-- The stopping weight vanishes exactly at `t = u/4`. -/
private theorem psi_endpoint326 {u : ℝ} (hu : 0 < u) :
    (4 * (u / 4) - u) / ((u / 4) * (u - u / 4)) = 0 := by
  have h : 4 * (u / 4) - u = 0 := by ring
  rw [h, zero_div]

/-- The stopping weight is increasing on `[u/4,1]`. -/
private theorem psi_mono326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) {t₁ t₂ : ℝ}
    (h1 : u / 4 ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ 1) :
    (4 * t₁ - u) / (t₁ * (u - t₁)) ≤ (4 * t₂ - u) / (t₂ * (u - t₂)) := by
  have hu0 : 0 < u := by linarith
  have ht1 : 0 < t₁ := by linarith
  have ht2 : 0 < t₂ := by linarith
  have hu1 : 0 < u - t₁ := by linarith
  have hu2 : 0 < u - t₂ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : (4 * t₂ - u) * (t₁ * (u - t₁)) - (4 * t₁ - u) * (t₂ * (u - t₂)) =
      (t₂ - t₁) * ((u - t₁) * (u - t₂) + 3 * t₁ * t₂) := by ring
  have hpos : 0 ≤ (t₂ - t₁) * ((u - t₁) * (u - t₂) + 3 * t₁ * t₂) := by positivity
  linarith

/-- The stopping weight also satisfies `4t-u ≤ 4t` and `u-t ≥ u-1`, the two
crude bounds used to compare it with its values at the endpoints. -/
private theorem psi_le_endpoint326 {u t : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) (h1 : u / 4 ≤ t)
    (h2 : t ≤ 1) :
    (4 * t - u) / (t * (u - t)) ≤ (4 - u) / (u - 1) + 0 := by
  have h := psi_mono326 hu hu4 (t₁ := t) (t₂ := 1) h1 h2 le_rfl
  have h1' : (4 * 1 - u) / (1 * (u - 1)) = (4 - u) / (u - 1) := by norm_num
  rw [h1'] at h
  linarith

/-- The staircase of increments of an increasing function dominates it: for
`x` in `[a,1)` and the grid `a + i d` with `n d = 1 - a`, `F x` is at most the
sum of the grid increments over the grid points below `x`. -/
private theorem step_le_sum326 {F : ℝ → ℝ} {a d : ℝ} {n : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : (n : ℝ) * d = 1 - a)
    (hFmono : ∀ x ∈ Set.Icc a 1, ∀ y ∈ Set.Icc a 1, x ≤ y → F x ≤ F y)
    (hFa : F a = 0) {x : ℝ} (hx1 : a ≤ x) (hx2 : x < 1) :
    F x ≤ ∑ i ∈ Finset.range n, (F (a + ((i : ℝ) + 1) * d) - F (a + (i : ℝ) * d)) *
      (if a + (i : ℝ) * d ≤ x then 1 else 0) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℕ → ℝ := fun i => a + (i : ℝ) * d with hs
  have hs0 : s 0 = a := by simp [hs]
  have hsn : s n = 1 := by
    have : a + (n : ℝ) * d = 1 := by rw [hnd]; ring
    simpa only [hs] using this
  have hsmono : Monotone s := by
    intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    simp only [hs]
    nlinarith

  have hsmem : ∀ i ≤ n, s i ∈ Set.Icc a 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have h := hsmono (Nat.zero_le i)
      rwa [hs0] at h
    · have h := hsmono hi
      rwa [hsn] at h
  set J : Finset ℕ := (Finset.range (n + 1)).filter (fun i => s i ≤ x) with hJdef
  have hJ0 : 0 ∈ J := by
    simp only [hJdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.succ_pos n, by rwa [hs0]⟩
  have hJne : J.Nonempty := ⟨0, hJ0⟩
  set i₀ : ℕ := J.max' hJne with hi₀def
  have hi₀mem : i₀ ∈ J := Finset.max'_mem J hJne
  have hi₀le : i₀ ≤ n := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hi₀mem).1
    omega
  have hsi₀ : s i₀ ≤ x := (Finset.mem_filter.mp hi₀mem).2
  have hi₀lt : i₀ < n := by
    rcases lt_or_eq_of_le hi₀le with h | h
    · exact h
    · exfalso
      rw [h] at hsi₀
      rw [hsn] at hsi₀
      linarith
  have hsnext : x < s (i₀ + 1) := by
    by_contra hcon
    push_neg at hcon
    have hmem : i₀ + 1 ∈ J := by
      simp only [hJdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.succ_lt_succ hi₀lt, hcon⟩
    have hle := Finset.le_max' J (i₀ + 1) hmem
    omega
  have hind : ∀ i ∈ Finset.range n,
      (if s i ≤ x then (1 : ℝ) else 0) = (if i ≤ i₀ then 1 else 0) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    by_cases h : i ≤ i₀
    · have hsix : s i ≤ x := le_trans (hsmono h) hsi₀
      simp only [hsix, h, if_true, ite_true]
    · have hnsx : ¬ (s i ≤ x) := by
        intro hcon
        have hmem : i ∈ J := by
          simp only [hJdef, Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_lt hin, hcon⟩
        have hle := Finset.le_max' J i hmem
        omega
      simp only [hnsx, h, ite_false]
  have hiff : ∀ i ∈ Finset.range n, (s i ≤ x ↔ i ≤ i₀) := by
    intro i hi
    have hh := hind i hi
    by_cases h : s i ≤ x
    · have h' : i ≤ i₀ := by
        by_contra hc
        rw [if_pos h, if_neg hc] at hh
        norm_num at hh
      exact ⟨fun _ => h', fun _ => h⟩
    · have h' : ¬ (i ≤ i₀) := by
        by_contra hc
        rw [if_neg h, if_pos hc] at hh
        norm_num at hh
      exact ⟨fun hc => absurd hc h, fun hc => absurd hc h'⟩
  have hsum : ∑ i ∈ Finset.range n, (F (a + ((i : ℝ) + 1) * d) - F (a + (i : ℝ) * d)) *
      (if a + (i : ℝ) * d ≤ x then 1 else 0) =
      ∑ i ∈ Finset.range (i₀ + 1), (F (s (i + 1)) - F (s i)) := by
    have h2 : ∀ i : ℕ, a + ((i : ℝ) + 1) * d = s (i + 1) := by
      intro i
      simp only [hs, Nat.cast_add, Nat.cast_one]
    have h1 : ∀ i : ℕ, a + (i : ℝ) * d = s i := fun i => rfl
    have hstep : ∀ i ∈ Finset.range n,
        (F (s (i + 1)) - F (s i)) * (if s i ≤ x then (1 : ℝ) else 0) =
          (if s i ≤ x then (F (s (i + 1)) - F (s i)) else 0) := by
      intro i _
      split_ifs <;> simp
    calc ∑ i ∈ Finset.range n, (F (a + ((i : ℝ) + 1) * d) - F (a + (i : ℝ) * d)) *
          (if a + (i : ℝ) * d ≤ x then 1 else 0)
        = ∑ i ∈ Finset.range n,
            (F (s (i + 1)) - F (s i)) * (if s i ≤ x then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [h1 i, h2 i]
      _ = ∑ i ∈ Finset.range n, (if s i ≤ x then (F (s (i + 1)) - F (s i)) else 0) :=
          Finset.sum_congr rfl hstep
      _ = ∑ i ∈ (Finset.range n).filter (fun i => s i ≤ x), (F (s (i + 1)) - F (s i)) := by
          rw [Finset.sum_filter]
      _ = ∑ i ∈ (Finset.range n).filter (fun i => i ≤ i₀), (F (s (i + 1)) - F (s i)) := by
          congr 1
          exact Finset.filter_congr hiff
      _ = ∑ i ∈ Finset.range (i₀ + 1), (F (s (i + 1)) - F (s i)) := by
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
  have htel : ∑ i ∈ Finset.range (i₀ + 1), (F (s (i + 1)) - F (s i)) =
      F (s (i₀ + 1)) - F (s 0) := by
    simpa only using Finset.sum_range_sub (fun i => F (s i)) (i₀ + 1)
  rw [hsum, htel]
  have hlast : F (s 0) = 0 := by rw [hs0]; exact hFa
  rw [hlast, sub_zero]
  exact hFmono x ⟨hx1, hx2.le⟩ (s (i₀ + 1)) (hsmem _ (Nat.succ_le_of_lt hi₀lt)) hsnext.le

/-- Strict monotonicity of the geometric grid `i ↦ a * rho^i`. -/
private theorem grid_lt326 {a rho : ℝ} (hrho : 1 < rho) (ha : 0 < a) (i : ℕ) :
    a * rho ^ i < a * rho ^ (i + 1) := by
  have hpos : 0 < a * rho ^ i := by positivity
  simp only [pow_succ]
  nlinarith [hpos, hrho]

/-- The ratio of two consecutive grid points is `rho`. -/
private theorem grid_ratio326 {a rho : ℝ} (hrho : 1 < rho) (ha : 0 < a) (i : ℕ) :
    a * rho ^ (i + 1) / (a * rho ^ i) = rho := by
  have hpos : 0 < a * rho ^ i := by positivity
  simp only [pow_succ]
  field_simp

/-- Discrete-to-integral comparison for an increasing weight against the
interval mass bound of the linear sieve.  The grid is geometric,
`s i = a * rho^i` with `rho^n = 1/a`, so every grid step has the same
logarithmic length `log rho`; this is what makes the logarithm telescope
without any derivative computation.  The error terms are one grid step
`log (1/a)/n` and `n` times the density slack `K/(s log z)`. -/
private theorem sum_le_integral326 (F : ℝ → ℝ) (K L a rho : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 < a) (ha1 : a < 1) (hL : 1 ≤ L) (hK : 0 ≤ K)
    (hrho : 1 < rho) (hrhon : rho ^ n = 1 / a)
    (hFmono : ∀ x ∈ Set.Icc a 1, ∀ y ∈ Set.Icc a 1, x ≤ y → F x ≤ F y)
    (hFcont : ContinuousOn F (Set.Icc a 1))
    (hFa : F a = 0)
    (P : Finset ℕ) (ν : ℕ → ℝ) (tt : ℕ → ℝ)
    (hν : ∀ p ∈ P, 0 ≤ ν p)
    (hta : ∀ p ∈ P, a ≤ tt p) (ht1 : ∀ p ∈ P, tt p < 1)
    (hmass : ∀ s s' : ℝ, a ≤ s → s < s' → s' ≤ 1 →
      ∑ p ∈ P.filter (fun p => s ≤ tt p ∧ tt p < s'), ν p ≤ Real.log (s' / s) + K / (s * L)) :
    ∑ p ∈ P, ν p * F (tt p) ≤
      (∫ x in a..(1 : ℝ), F x / x) +
        F 1 * (Real.log (1 / a) / (n : ℝ) + (n : ℝ) * K / (a * L)) := by
  classical
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr1 : 0 < rho := by linarith
  have hd : Real.log rho = Real.log (1 / a) / (n : ℝ) := by
    have := congrArg Real.log hrhon
    rw [Real.log_pow] at this
    field_simp at this ⊢
    linarith
  set d : ℝ := Real.log rho with hddef
  have hdpos : 0 < d := Real.log_pos hrho
  have hdv : d = Real.log (1 / a) / (n : ℝ) := by
    rw [hddef]; exact hd
  have hnd : (n : ℝ) * d = Real.log (1 / a) := by
    rw [hdv]; field_simp
  set s : ℕ → ℝ := fun i => a * rho ^ i with hs
  have hs0 : s 0 = a := by simp [hs]
  have hsn : s n = 1 := by
    simp only [hs, hrhon]
    field_simp
  have hsmono : Monotone s := by
    refine monotone_nat_of_le_succ (fun i => ?_)
    simp only [hs]
    exact (grid_lt326 hrho ha i).le
  have hsmem : ∀ i ≤ n, s i ∈ Set.Icc a 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · have h := hsmono (Nat.zero_le i)
      rwa [hs0] at h
    · have h := hsmono hi
      rwa [hsn] at h
  have hFnonneg : ∀ x ∈ Set.Icc a 1, 0 ≤ F x := by
    intro x hx
    have h := hFmono a ⟨le_rfl, ha1.le⟩ x hx hx.1
    rwa [hFa] at h
  -- `F` positive and continuous on every grid block, hence integrable there
  have hcont : ContinuousOn (fun x : ℝ => F x / x) (Set.Icc a 1) :=
    hFcont.div continuousOn_id (fun x hx => (by linarith [hx.1] : (0:ℝ) < x).ne')
  have hint : ∀ i < n, IntervalIntegrable (fun x : ℝ => F x / x)
      MeasureTheory.volume (s i) (s (i + 1)) := by
    intro i hi
    have h1 : a ≤ s i := (hsmem i (le_of_lt hi)).1
    have h2 : a ≤ s (i + 1) := (hsmem (i + 1) (Nat.succ_le_of_lt hi)).1
    have h3 : s i ≤ 1 := (hsmem i (le_of_lt hi)).2
    have h4 : s (i + 1) ≤ 1 := (hsmem (i + 1) (Nat.succ_le_of_lt hi)).2
    rcases le_total (s i) (s (i + 1)) with h | h
    · exact (hcont.mono (fun x hx => ⟨h1.trans hx.1, hx.2.trans h4⟩)).intervalIntegrable_of_Icc h
    · exact ((hcont.mono (fun x hx => ⟨h2.trans hx.1, hx.2.trans h3⟩)).intervalIntegrable_of_Icc h).symm
  -- each summand is dominated by the block sum at its block end point
  have hpt : ∀ p ∈ P, ν p * F (tt p) ≤
      ∑ i ∈ Finset.range n,
        (if s i ≤ tt p ∧ tt p < s (i + 1) then ν p * F (s (i + 1)) else 0) := by
    intro p hp
    have hpa : a ≤ tt p := hta p hp
    have hp1 : tt p < 1 := ht1 p hp
    set J : Finset ℕ := (Finset.range (n + 1)).filter (fun i => s i ≤ tt p) with hJdef
    have hJ0 : 0 ∈ J := by
      simp only [hJdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.succ_pos n, by rw [hs0]; exact hpa⟩
    have hJne : J.Nonempty := ⟨0, hJ0⟩
    set j : ℕ := J.max' hJne with hjdef
    have hjmem : j ∈ J := Finset.max'_mem J hJne
    have hjle : j ≤ n := by
      have h := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
      omega
    have hsj : s j ≤ tt p := (Finset.mem_filter.mp hjmem).2
    have hjlt : j < n := by
      rcases lt_or_eq_of_le hjle with h | h
      · exact h
      · exfalso
        rw [h] at hsj
        rw [hsn] at hsj
        linarith
    have hsnext : tt p < s (j + 1) := by
      by_contra hcon
      push_neg at hcon
      have hmem : j + 1 ∈ J := by
        simp only [hJdef, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.succ_lt_succ hjlt, hcon⟩
      have := Finset.le_max' J (j + 1) hmem
      omega
    have hsingle : ∀ i ∈ Finset.range n,
        (if s i ≤ tt p ∧ tt p < s (i + 1) then ν p * F (s (i + 1)) else 0) =
          (if i = j then ν p * F (s (j + 1)) else 0) := by
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      by_cases h : i = j
      · subst h
        simp only [hsj, hsnext, and_self, ite_true]
      · have hnot : ¬ (s i ≤ tt p ∧ tt p < s (i + 1)) := by
          intro hc
          rcases lt_or_gt_of_ne h with hlt | hgt
          · exact (not_le_of_gt hc.2) (le_trans (hsmono (Nat.succ_le_of_lt hlt)) hsj)
          · have hmem : i ∈ J := by
              simp only [hJdef, Finset.mem_filter, Finset.mem_range]
              exact ⟨Nat.lt_succ_of_lt hin, hc.1⟩
            have := Finset.le_max' J i hmem
            omega
        simp only [hnot, h, ite_false]
    have hmemj : j ∈ Finset.range n := Finset.mem_range.mpr hjlt
    calc ν p * F (tt p)
        ≤ ν p * F (s (j + 1)) :=
          mul_le_mul_of_nonneg_left
            (hFmono _ ⟨hpa, hp1.le⟩ _ (hsmem _ (Nat.succ_le_of_lt hjlt)) hsnext.le) (hν p hp)
      _ = ∑ i ∈ Finset.range n,
            (if s i ≤ tt p ∧ tt p < s (i + 1) then ν p * F (s (i + 1)) else 0) := by
          rw [Finset.sum_congr rfl hsingle, Finset.sum_eq_single j]
          · simp only [ite_true]
          · intro b _ hb
            simp only [hb, ite_false]
          · intro hcon
            exact absurd hmemj hcon
  -- swap the order of summation
  have hswap : ∑ p ∈ P, ∑ i ∈ Finset.range n,
      (if s i ≤ tt p ∧ tt p < s (i + 1) then ν p * F (s (i + 1)) else 0) =
      ∑ i ∈ Finset.range n, F (s (i + 1)) *
        ∑ p ∈ P.filter (fun p => s i ≤ tt p ∧ tt p < s (i + 1)), ν p := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hblock : ∀ i ∈ Finset.range n, F (s (i + 1)) *
      ∑ p ∈ P.filter (fun p => s i ≤ tt p ∧ tt p < s (i + 1)), ν p ≤
      F (s (i + 1)) * (d + K / (s i * L)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hsa : a ≤ s i := (hsmem i (le_of_lt hin)).1
    have hslt : s i < s (i + 1) := by
      simp only [hs]; exact grid_lt326 hrho ha i
    have hsle : s (i + 1) ≤ 1 := (hsmem (i + 1) (Nat.succ_le_of_lt hin)).2
    have h := hmass (s i) (s (i + 1)) hsa hslt hsle
    have hlog : Real.log (s (i + 1) / s i) = d := by
      have hr : s (i + 1) / s i = rho := by
        simp only [hs]; exact grid_ratio326 hrho ha i
      rw [hr, hddef]
    rw [hlog] at h
    exact mul_le_mul_of_nonneg_left h (hFnonneg _ (hsmem _ (Nat.succ_le_of_lt hin)))
  -- the geometric step against the logarithmic integral
  have hfirst : ∑ i ∈ Finset.range n, F (s (i + 1)) * d ≤
      (∫ x in a..(1 : ℝ), F x / x) + F 1 * d := by
    have htel : ∑ i ∈ Finset.range n, (F (s (i + 1)) - F (s i)) = F 1 - F a := by
      have h := Finset.sum_range_sub (fun i => F (s i)) n
      rw [hsn, hs0] at h
      exact h
    have hsplit : ∑ i ∈ Finset.range n, F (s (i + 1)) * d =
        (∑ i ∈ Finset.range n, F (s i) * d) + (F 1 - F a) * d := by
      have hcongr : ∑ i ∈ Finset.range n, F (s (i + 1)) * d =
          ∑ i ∈ Finset.range n, (F (s i) * d + (F (s (i + 1)) - F (s i)) * d) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      have h2 : ∑ i ∈ Finset.range n, (F (s (i + 1)) - F (s i)) * d = (F 1 - F a) * d := by
        rw [← Finset.sum_mul, htel]
      rw [hcongr, Finset.sum_add_distrib, h2]
    have hleft : ∑ i ∈ Finset.range n, F (s i) * d ≤ ∫ x in a..(1 : ℝ), F x / x := by
      have hblocks : ∑ i ∈ Finset.range n, F (s i) * d ≤
          ∑ i ∈ Finset.range n, ∫ x in s i..s (i + 1), F x / x := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        have hsa : a ≤ s i := (hsmem i (le_of_lt hin)).1
        have hslt : s i < s (i + 1) := by
          simp only [hs]; exact grid_lt326 hrho ha i
        have hsle : s (i + 1) ≤ 1 := (hsmem (i + 1) (Nat.succ_le_of_lt hin)).2
        have hsa' : a ≤ s (i + 1) := (hsmem (i + 1) (Nat.succ_le_of_lt hin)).1
        have hdsi : d = ∫ x in s i..s (i + 1), 1 / x := by
          rw [integral_one_div_of_pos (by linarith) (by linarith)]
          have hr : s (i + 1) / s i = rho := by
            simp only [hs]; exact grid_ratio326 hrho ha i
          rw [hr, hddef]
        rw [hdsi, ← intervalIntegral.integral_const_mul]
        have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hslt.le
          (by
            apply ContinuousOn.intervalIntegrable_of_Icc hslt.le
            show ContinuousOn (fun x : ℝ => F (s i) / x) (Set.Icc (s i) (s (i + 1)))
            exact ContinuousOn.div continuousOn_const continuousOn_id (fun x hx => by
              have : 0 < x := by linarith [hx.1]
              exact this.ne'))
          (by simpa only [div_eq_mul_inv] using hint i hin)
          (by
            intro x hx
            have hx0 : (0 : ℝ) ≤ x⁻¹ := by
              have : 0 < x := by linarith [hx.1]
              positivity
            exact mul_le_mul_of_nonneg_right
              (hFmono (s i) (hsmem i (le_of_lt hin)) x ⟨hsa.trans hx.1, hx.2.trans hsle⟩ hx.1) hx0)
        simpa only [div_eq_mul_inv, one_mul, mul_one] using hmono
      refine hblocks.trans (le_of_eq ?_)
      have hall := intervalIntegral.sum_integral_adjacent_intervals
        (fun i (hi : i < n) => hint i hi)
      rw [hs0, hsn] at hall
      exact hall
    rw [hsplit]
    have hFa' : F a = 0 := hFa
    nlinarith [hleft]
  -- the density slack term
  have hsecond : ∑ i ∈ Finset.range n, F (s (i + 1)) * (K / (s i * L)) ≤
      (n : ℝ) * K / (a * L) * F 1 := by
    have hterm : ∀ i ∈ Finset.range n, F (s (i + 1)) * (K / (s i * L)) ≤ F 1 * (K / (a * L)) := by
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      have hsa : a ≤ s i := (hsmem i (le_of_lt hin)).1
      have hsle : F (s (i + 1)) ≤ F 1 :=
        hFmono _ (hsmem _ (Nat.succ_le_of_lt hin)) _ ⟨ha1.le, le_rfl⟩
          (hsmem _ (Nat.succ_le_of_lt hin)).2
      have hcoef : K / (s i * L) ≤ K / (a * L) := by
        apply div_le_div_of_nonneg_left hK (by positivity) (by nlinarith)
      calc F (s (i + 1)) * (K / (s i * L)) ≤ F 1 * (K / (s i * L)) :=
            mul_le_mul_of_nonneg_right hsle (by positivity)
        _ ≤ F 1 * (K / (a * L)) := mul_le_mul_of_nonneg_left hcoef (hFnonneg 1 ⟨ha1.le, le_rfl⟩)
    calc ∑ i ∈ Finset.range n, F (s (i + 1)) * (K / (s i * L))
        ≤ ∑ _i ∈ Finset.range n, F 1 * (K / (a * L)) := Finset.sum_le_sum hterm
      _ = (n : ℝ) * (F 1 * (K / (a * L))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (n : ℝ) * K / (a * L) * F 1 := by ring
  -- assemble
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [hswap]
  refine (Finset.sum_le_sum hblock).trans ?_
  have hsplit2 : ∑ i ∈ Finset.range n, F (s (i + 1)) * (d + K / (s i * L)) =
      (∑ i ∈ Finset.range n, F (s (i + 1)) * d) +
        ∑ i ∈ Finset.range n, F (s (i + 1)) * (K / (s i * L)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit2]
  have hFa' : F a = 0 := hFa
  have hdform : F 1 * d = F 1 * (Real.log (1 / a) / (n : ℝ)) := by rw [hdv]
  nlinarith [hfirst, hsecond]

/-- The moving prefix product normalised by the full sieve product is an
inverse interval product, hence is bounded by the density hypothesis at
`(p,z)`. -/
private theorem prefix_ratio_le326 (s : BoundingSieve) (K z : ℝ) (hden : LinearDensity s K)
    (hz : 2 ≤ z) (hP : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z)
    {p : ℕ} (hp : p ∈ s.prodPrimes.primeFactors) :
    rosserPrefixProduct326 s (p : ℝ) /
        ∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q) ≤
      Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ)) := by
  classical
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpz : (p : ℝ) < z := hP p hp
  set Pf := s.prodPrimes.primeFactors with hPf
  have hsplit : (∏ q ∈ Pf, (1 - s.nu q)) =
      (∏ q ∈ Pf.filter (fun q : ℕ => (q : ℝ) < (p : ℝ)), (1 - s.nu q)) *
        ∏ q ∈ Pf.filter (fun q : ℕ => ¬ (q : ℝ) < (p : ℝ)), (1 - s.nu q) :=
    (Finset.prod_filter_mul_prod_filter_not Pf (fun q : ℕ => (q : ℝ) < (p : ℝ))
      (fun q => 1 - s.nu q)).symm
  have hden' := hden (p : ℝ) z hp2 hpz
  have hfilter : Pf.filter (fun q : ℕ => (p : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < z) =
      Pf.filter (fun q : ℕ => ¬ (q : ℝ) < (p : ℝ)) := by
    ext q
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨hq, h1, -⟩; exact ⟨hq, h1⟩
    · rintro ⟨hq, h1⟩; exact ⟨hq, h1, hP q hq⟩
  have hposf : (0 : ℝ) < ∏ q ∈ Pf.filter (fun q : ℕ => ¬ (q : ℝ) < (p : ℝ)),
      (1 - s.nu q) :=
    Finset.prod_pos fun q hq => sub_pos.mpr
      (s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
        (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))
  have hposA : (0 : ℝ) < ∏ q ∈ Pf.filter (fun q : ℕ => (q : ℝ) < (p : ℝ)), (1 - s.nu q) :=
    Finset.prod_pos fun q hq => sub_pos.mpr
      (s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
        (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))
  have hpref : rosserPrefixProduct326 s (p : ℝ) =
      ∏ q ∈ Pf.filter (fun q : ℕ => (q : ℝ) < (p : ℝ)), (1 - s.nu q) := rfl
  rw [hpref, hsplit]
  have hcalc : (∏ q ∈ Pf.filter (fun q : ℕ => (q : ℝ) < (p : ℝ)), (1 - s.nu q)) /
      ((∏ q ∈ Pf.filter (fun q : ℕ => (q : ℝ) < (p : ℝ)), (1 - s.nu q)) *
        ∏ q ∈ Pf.filter (fun q : ℕ => ¬ (q : ℝ) < (p : ℝ)), (1 - s.nu q)) =
      (∏ q ∈ Pf.filter (fun q : ℕ => ¬ (q : ℝ) < (p : ℝ)), (1 - s.nu q))⁻¹ := by
    field_simp
  rw [hcalc, ← Finset.prod_inv_distrib, ← hfilter]
  exact hden'

/-- Pointwise comparison: every summand of the normalised second stopping term
is bounded by the product of the two density factors. -/
private theorem second_summand_le326 (s : BoundingSieve) (K z D : ℝ)
    (hden : LinearDensity s K) (hK : 0 ≤ K) (hz : 8 ≤ z) (hDz : z ^ 2 ≤ D)
    (hP : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z)
    {p : ℕ} (hp : p ∈ s.prodPrimes.primeFactors) :
    s.nu p * rosserIntervalBoundary326 s (Real.exp (Real.log (D / (p : ℝ)) / 3)) (p : ℝ) /
        ∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q) ≤
      s.nu p * (Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ))) *
        max 0 ((Real.log (p : ℝ) / Real.log (Real.exp (Real.log (D / (p : ℝ)) / 3))) *
          (1 + K / Real.log (Real.exp (Real.log (D / (p : ℝ)) / 3))) - 1) := by
  classical
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnu := (s.nu_pos_of_prime p hpprime (Nat.dvd_of_mem_primeFactors hp)).le
  have hV : (0 : ℝ) < ∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q) :=
    Finset.prod_pos fun q hq => sub_pos.mpr
      (s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors hq)
        (Nat.dvd_of_mem_primeFactors hq))
  have hpz : (p : ℝ) < z := hP p hp
  have hratio := prefix_ratio_le326 s K z hden (by linarith) hP hp
  have hratio0 : 0 ≤ rosserPrefixProduct326 s (p : ℝ) /
      ∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q) := by
    apply div_nonneg
    · exact Finset.prod_nonneg fun q hq => (sub_pos.mpr
        (s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
          (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))).le
    · exact hV.le
  set w := Real.exp (Real.log (D / (p : ℝ)) / 3) with hw
  have hw2 : 2 ≤ w := by
    have h8 : (8 : ℝ) ≤ D / (p : ℝ) := by
      rw [le_div_iff₀ hp0]
      calc 8 * (p : ℝ) ≤ 8 * z := by linarith
        _ ≤ z ^ 2 := by nlinarith
        _ ≤ D := hDz
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8
    rw [hlog8] at hh
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ w := Real.exp_le_exp.mpr (by linarith)
  by_cases hwp : w < (p : ℝ)
  · have hrel := rosserIntervalBoundary_eq_relative326 s w (p : ℝ) hwp.le
    have hbpos : (0 : ℝ) ≤ Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ)) := by
      have hp2' : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
      have h1 : (0 : ℝ) ≤ Real.log z / Real.log (p : ℝ) :=
        div_nonneg (Real.log_nonneg (by linarith)) hp2'.le
      have h2 : (0 : ℝ) ≤ 1 + K / Real.log (p : ℝ) := by
        have := div_nonneg hK hp2'.le
        linarith
      exact mul_nonneg h1 h2
    have hrel0 : rosserPrefixProduct326 s (p : ℝ) /
          (∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q)) *
          ((∏ q ∈ s.prodPrimes.primeFactors.filter
            (fun q : ℕ => w ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)), (1 - s.nu q)⁻¹) - 1) ≤
        (Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ))) *
          max 0 ((Real.log (p : ℝ) / Real.log w) * (1 + K / Real.log w) - 1) := by
      have hb := hden w (p : ℝ) hw2 hwp
      have hbracket : (∏ q ∈ s.prodPrimes.primeFactors.filter
            (fun q : ℕ => w ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)), (1 - s.nu q)⁻¹) - 1 ≤
          max 0 ((Real.log (p : ℝ) / Real.log w) * (1 + K / Real.log w) - 1) :=
        (sub_le_sub_right hb 1).trans (le_max_right _ _)
      calc rosserPrefixProduct326 s (p : ℝ) /
            (∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q)) *
              ((∏ q ∈ s.prodPrimes.primeFactors.filter
                (fun q : ℕ => w ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)), (1 - s.nu q)⁻¹) - 1)
          ≤ rosserPrefixProduct326 s (p : ℝ) /
              (∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q)) *
                max 0 ((Real.log (p : ℝ) / Real.log w) * (1 + K / Real.log w) - 1) :=
            mul_le_mul_of_nonneg_left hbracket hratio0
        _ ≤ (Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ))) *
              max 0 ((Real.log (p : ℝ) / Real.log w) * (1 + K / Real.log w) - 1) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
    calc s.nu p * rosserIntervalBoundary326 s w (p : ℝ) /
          (∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q))
        = s.nu p * (rosserPrefixProduct326 s (p : ℝ) /
            (∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q)) *
              ((∏ q ∈ s.prodPrimes.primeFactors.filter
                (fun q : ℕ => w ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)), (1 - s.nu q)⁻¹) - 1)) := by
          rw [hrel]; ring
      _ ≤ s.nu p * ((Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ))) *
            max 0 ((Real.log (p : ℝ) / Real.log w) * (1 + K / Real.log w) - 1)) :=
          mul_le_mul_of_nonneg_left hrel0 hnu
      _ = s.nu p * (Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ))) *
            max 0 ((Real.log (p : ℝ) / Real.log (Real.exp (Real.log (D / (p : ℝ)) / 3))) *
              (1 + K / Real.log (Real.exp (Real.log (D / (p : ℝ)) / 3))) - 1) := by
          rw [hw]; ring
  · have hzero : rosserIntervalBoundary326 s w (p : ℝ) = 0 :=
      rosserIntervalBoundary_eq_zero326 s w (p : ℝ) (le_of_not_gt hwp)
    rw [hzero, mul_zero, zero_div]
    have hb0 : (0 : ℝ) ≤ Real.log z / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ)) := by
      have hp2' : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
      have h1 : (0 : ℝ) ≤ Real.log z / Real.log (p : ℝ) :=
        div_nonneg (Real.log_nonneg (by linarith)) hp2'.le
      have h2 : (0 : ℝ) ≤ 1 + K / Real.log (p : ℝ) := by
        have := div_nonneg hK hp2'.le
        linarith
      exact mul_nonneg h1 h2
    exact mul_nonneg (mul_nonneg hnu hb0) (le_max_left _ _)

/-- Translation between the prime variable and `t = log p/log z` for `z > 1`:
`z^s ≤ p` is the same as `s ≤ log p/log z`. -/
private theorem rpow_le_iff_log_le326 {z t : ℝ} (hz1 : 1 < z) {p : ℕ} (hp : 0 < p) :
    z ^ t ≤ (p : ℝ) ↔ t ≤ Real.log (p : ℝ) / Real.log z := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos hz1
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hz0 t) hp0, Real.log_rpow hz0]
  constructor
  · intro h; rw [le_div_iff₀ hlz]; linarith
  · intro h; have := (le_div_iff₀ hlz).mp h; linarith

/-- The normalised second weight is dominated by the increasing weight
`(4t-u)/(t(u-t))` plus the `1/t` term, with the two relative losses
`4K/(a log D)` and `12K/((u-1) log D)`.  The factors `4` and `12` absorb the
`u ≤ 4` that the density hypothesis carries through `K/log p = uK/(t log D)`
and `K/log w_p = 3uK/((u-t) log D)`. -/
private theorem second_weight_le326 {K L u t : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hu : 2 ≤ u) (hu4 : u ≤ 4) (ht : u / 4 ≤ t) (ht1 : t ≤ 1) :
    (1 / t) * (1 + 4 * K / (t * L)) *
        max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1) ≤
      (1 + 4 * K / (u / 4 * L)) *
        ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
          12 * K / ((u - 1) * L) * (1 / t)) := by
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < t := by linarith
  have htu : 0 < u - t := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hRHS0 : (0 : ℝ) ≤ (1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (u - t)) +
      12 * K / ((u - 1) * L) := by
    have h1 : 0 ≤ (4 * t - u) / (u - t) := div_nonneg (by linarith) htu.le
    have h2 : 0 ≤ 12 * K / ((u - 1) * L) := by positivity
    have h3 : 0 ≤ 1 + 12 * K / ((u - 1) * L) := by linarith
    nlinarith
  have hstep : max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1) ≤
      (1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (u - t)) + 12 * K / ((u - 1) * L) := by
    have hd1 : 12 * K / ((u - t) * L) ≤ 12 * K / ((u - 1) * L) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have hb1 : 3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1 ≤
        (1 + 12 * K / ((u - 1) * L)) * (3 * t / (u - t)) - 1 := by
      have hmul : 3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) ≤
          3 * t / (u - t) * (1 + 12 * K / ((u - 1) * L)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hb2 : (1 + 12 * K / ((u - 1) * L)) * (3 * t / (u - t)) - 1 =
        (1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (u - t)) + 12 * K / ((u - 1) * L) := by
      field_simp
      ring
    exact max_le hRHS0 (hb1.trans hb2.le)
  have hbK : 1 + 4 * K / (t * L) ≤ 1 + 4 * K / (u / 4 * L) := by
    have h1 : 4 * K / (t * L) ≤ 4 * K / (u / 4 * L) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    linarith
  have hmain : (1 / t) * (1 + 4 * K / (t * L)) ≤ (1 / t) * (1 + 4 * K / (u / 4 * L)) :=
    mul_le_mul_of_nonneg_left hbK (by positivity)
  calc (1 / t) * (1 + 4 * K / (t * L)) *
        max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1)
      ≤ (1 / t) * (1 + 4 * K / (u / 4 * L)) *
          ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (u - t)) +
            12 * K / ((u - 1) * L)) := by
        apply mul_le_mul hmain hstep (by positivity) (by positivity)
    _ = (1 + 4 * K / (u / 4 * L)) *
          ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
            12 * K / ((u - 1) * L) * (1 / t)) := by
        have ht0' : t ≠ 0 := ht0.ne'
        have htu' : u - t ≠ 0 := htu.ne'
        have hu1' : u - 1 ≠ 0 := hu1.ne'
        have hL' : L ≠ 0 := hL.ne'
        have hinner : (1 / t) * ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (u - t)) +
            12 * K / ((u - 1) * L)) =
            (1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
              12 * K / ((u - 1) * L) * (1 / t) := by
          field_simp
        calc (1 / t) * (1 + 4 * K / (u / 4 * L)) *
              ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (u - t)) + 12 * K / ((u - 1) * L))
            = (1 + 4 * K / (u / 4 * L)) *
                ((1 / t) * ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (u - t)) +
                  12 * K / ((u - 1) * L))) := by ring
          _ = (1 + 4 * K / (u / 4 * L)) *
                ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
                  12 * K / ((u - 1) * L) * (1 / t)) := by rw [hinner]

/-- The stopping weight is at most two on the stopping range. -/
private theorem psi_le_two326 {u t : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) (h1 : u / 4 ≤ t) (h2 : t ≤ 1) :
    (4 * t - u) / (t * (u - t)) ≤ 2 := by
  have hu1 : 0 < u - 1 := by linarith
  have h := psi_le_endpoint326 hu hu4 h1 h2
  have h2' : (4 - u) / (u - 1) ≤ 2 := by
    rw [div_le_iff₀ hu1]
    linarith
  linarith

/-- The continuous second coefficient is bounded by four on the whole range. -/
private theorem second_model_le_four326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    rosserSecondModel326 u ≤ 4 := by
  have hu0 : 0 < u := by linarith
  have ha : 0 < u / 4 := by linarith
  have hle : u / 4 ≤ (1 : ℝ) := by linarith
  rw [second_model_eq_tail_integral326 hu hu4]
  have hcont1 : ContinuousOn (fun t : ℝ => 3 / (t * (u - t)) - 1 / t ^ 2)
      (Set.Icc (u / 4) 1) := by
    apply ContinuousOn.sub
    · apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      intro t ht
      have h1 : 0 < t := by linarith [ht.1, ha]
      have h2 : 0 < u - t := by linarith [ht.2, hu]
      exact mul_ne_zero h1.ne' h2.ne'
    · apply continuousOn_const.div (continuousOn_id.pow 2)
      intro t ht
      have h1 : 0 < t := by linarith [ht.1, ha]
      exact pow_ne_zero 2 h1.ne'
  have hcont2 : ContinuousOn (fun t : ℝ => 2 / t) (Set.Icc (u / 4) 1) := by
    apply continuousOn_const.div continuousOn_id
    intro t ht
    have h1 : 0 < t := by linarith [ht.1, ha]
    exact h1.ne'
  have hmono : (∫ t in (u / 4)..(1 : ℝ), (3 / (t * (u - t)) - 1 / t ^ 2)) ≤
      ∫ t in (u / 4)..(1 : ℝ), 2 / t := by
    refine intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle
      (hcont1.intervalIntegrable_of_Icc hle) (hcont2.intervalIntegrable_of_Icc hle) ?_
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have htu : 0 < u - t := by linarith [ht.2]
    have hid : 3 / (t * (u - t)) - 1 / t ^ 2 = ((4 * t - u) / (t * (u - t))) / t := by
      field_simp
      ring
    rw [hid]
    apply div_le_div_of_nonneg_right (psi_le_two326 hu hu4 ht.1 ht.2) ht0.le
  refine hmono.trans ?_
  have hval : (∫ t in (u / 4)..(1 : ℝ), 2 / t) = 2 * Real.log (1 / (u / 4)) := by
    have hv : (∫ t in (u / 4)..(1 : ℝ), 2 / t) = 2 * ∫ t in (u / 4)..(1 : ℝ), 1 / t := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      ring
    rw [hv, integral_one_div_of_pos ha (by norm_num)]
  have hlog : Real.log (1 / (u / 4)) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ ha]
    linarith
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [hval]
  linarith

/-- Below the sixteenth part of the level ratio the second weight vanishes:
the two density factors cannot both stay above the threshold.  This uses only
`K/log D ≤ 1/2`, which the cutoff `z > exp (K+2)` provides. -/
private theorem mid_weight_zero326 {K L u t : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hu : 2 ≤ u) (hu4 : u ≤ 4) (hKL : K / L ≤ 1 / 2) (ht0 : 0 < t) (ht : t ≤ u / 16) :
    3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1 ≤ 0 := by
  have htu : 0 < u - t := by linarith
  have hY0 : 0 ≤ 3 * t / (u - t) := by positivity
  have hY : 3 * t / (u - t) ≤ 1 / 5 := by
    rw [div_le_iff₀ htu]
    linarith
  have hK1 : K ≤ L / 2 := by
    rw [div_le_iff₀ hL] at hKL
    linarith
  have hZ : 12 * K / ((u - t) * L) ≤ 16 / 5 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (u - t) * L)]
    nlinarith
  have hprod : 3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) ≤ 1 / 5 * (1 + 16 / 5) := by
    apply mul_le_mul hY (by linarith) (by positivity) (by norm_num)
  linarith

/-- In the middle band the second weight is of order `K/log D`. -/
private theorem mid_weight_le326 {K L u t : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hu : 2 ≤ u) (hu4 : u ≤ 4) (hKL : K / L ≤ 1 / 2) (ht : u / 16 ≤ t) (ht2 : t < u / 4) :
    (1 / t) * (1 + 4 * K / (t * L)) *
        max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1) ≤
      64 * (K / L) * (1 + 32 * K / L) := by
  have ht0 : 0 < t := by linarith
  have htu : 0 < u - t := by linarith
  have ht8 : 1 / t ≤ 8 := by
    rw [div_le_iff₀ ht0]
    linarith
  have hKL0 : 0 ≤ K / L := div_nonneg hK.le hL.le
  -- the threshold factor is at most `8 K/L`
  have hc : max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1) ≤ 8 * (K / L) := by
    have hY1 : 3 * t / (u - t) ≤ 1 := by
      rw [div_le_iff₀ htu]
      linarith
    have hZ : 12 * K / ((u - t) * L) ≤ 8 * K / L := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (u - t) * L) (by positivity : (0 : ℝ) < L)]
      nlinarith [mul_pos hK hL, htu, hu]
    have h12 : 8 * K / L = 8 * (K / L) := by ring
    rw [h12] at hZ
    have h : 3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1 ≤ 8 * (K / L) := by
      have h1 : 3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) ≤
          1 * (1 + 12 * K / ((u - t) * L)) := by
        apply mul_le_mul hY1 (le_refl _) (by positivity) (by norm_num)
      linarith
    exact max_le (by positivity) h
  -- the prefactor is at most `8 (1 + 32K/L)`
  have hpre : (1 / t) * (1 + 4 * K / (t * L)) ≤ 8 * (1 + 32 * K / L) := by
    have hK2 : 4 * K / (t * L) ≤ 32 * K / L := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < t * L) (by positivity : (0 : ℝ) < L)]
      nlinarith [mul_pos hK hL, ht0, hu]
    have h12 : 32 * K / L = 32 * (K / L) := by ring
    rw [h12] at hK2
    have hprod : (1 / t) * (4 * K / (t * L)) ≤ 8 * (32 * (K / L)) := by
      apply mul_le_mul ht8 hK2 (by positivity) (by norm_num)
    have hsplit : (1 / t) * (1 + 4 * K / (t * L)) =
        1 / t + (1 / t) * (4 * K / (t * L)) := by ring
    rw [hsplit, h12]
    linarith
  calc (1 / t) * (1 + 4 * K / (t * L)) *
        max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1)
      ≤ 8 * (1 + 32 * K / L) * (8 * (K / L)) := by
        apply mul_le_mul hpre hc (by positivity) (by positivity)
    _ = 64 * (K / L) * (1 + 32 * K / L) := by ring

/-- In the main band the second weight is dominated by `8 (1+32K/L)` times the
form `(1+eps) psi(t) + eps/t`, whose `dt/t` integral is the continuous second
coefficient. -/
private theorem main_weight_le326 {K L u t : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hu : 2 ≤ u) (hu4 : u ≤ 4) (ht : u / 4 ≤ t) (ht1 : t ≤ 1) :
    (1 / t) * (1 + 4 * K / (t * L)) *
        max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1) ≤
      8 * (1 + 32 * K / L) *
        ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
          12 * K / ((u - 1) * L) * (1 / t)) := by
  have ht0 : 0 < t := by linarith
  have htu : 0 < u - t := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hbase := second_weight_le326 hK hL hu hu4 ht ht1
  have hA0 : (0 : ℝ) ≤ (1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
      12 * K / ((u - 1) * L) * (1 / t) := by
    have h1 : 0 ≤ (4 * t - u) / (t * (u - t)) := by
      apply div_nonneg (by linarith)
      positivity
    have h2 : 0 ≤ 12 * K / ((u - 1) * L) := by positivity
    have h3 : 0 ≤ 1 + 12 * K / ((u - 1) * L) := by linarith
    have h4 : 0 ≤ 1 / t := by positivity
    have := mul_nonneg h3 h1
    have := mul_nonneg h2 h4
    linarith
  have hdelta : 1 + 4 * K / (u / 4 * L) ≤ 1 + 32 * K / L := by
    have h1 : 4 * K / (u / 4 * L) ≤ 32 * K / L := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < u / 4 * L) (by positivity : (0 : ℝ) < L)]
      nlinarith [mul_nonneg hK hL.le, hu]
    linarith
  have h8 : (1 + 32 * K / L) ≤ 8 * (1 + 32 * K / L) := by
    have : (0 : ℝ) ≤ 1 + 32 * K / L := by positivity
    linarith
  have h1 : (1 + 4 * K / (u / 4 * L)) *
        ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
          12 * K / ((u - 1) * L) * (1 / t)) ≤
      (1 + 32 * K / L) *
        ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
          12 * K / ((u - 1) * L) * (1 / t)) :=
    mul_le_mul_of_nonneg_right hdelta hA0
  have h2 : (1 + 32 * K / L) *
        ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
          12 * K / ((u - 1) * L) * (1 / t)) ≤
      8 * (1 + 32 * K / L) *
        ((1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
          12 * K / ((u - 1) * L) * (1 / t)) := by
    have h0 : (0 : ℝ) ≤ (1 + 12 * K / ((u - 1) * L)) * ((4 * t - u) / (t * (u - t))) +
        12 * K / ((u - 1) * L) * (1 / t) := hA0
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 32 * K / L) h0]
  exact hbase.trans (h1.trans h2)

/-- The exponent that makes `z ^ s` equal a prescribed positive number. -/
private theorem rpow_log_div326 {z c : ℝ} (hz : 1 < z) (hc : 0 < c) :
    z ^ (Real.log c / Real.log z) = c := by
  have hz0 : 0 < z := by linarith
  have hlz : Real.log z ≠ 0 := (Real.log_pos hz).ne'
  rw [Real.rpow_def_of_pos hz0]
  have h : Real.log z * (Real.log c / Real.log z) = Real.log c := by field_simp
  rw [h, Real.exp_log hc]

/-- `z` raised to the lower end of the main band is at least two. -/
private theorem two_le_rpow_band326 {z u : ℝ} (hz : 1 < z) (hu : 2 ≤ u) :
    2 ≤ z ^ max (u / 16) (Real.log 2 / Real.log z) := by
  have h2 : z ^ (Real.log 2 / Real.log z) = 2 := rpow_log_div326 hz (by norm_num)
  have hle : Real.log 2 / Real.log z ≤ max (u / 16) (Real.log 2 / Real.log z) :=
    le_max_right _ _
  have := Real.rpow_le_rpow_of_exponent_le hz.le hle
  rw [h2] at this
  exact this

/-- Strict form of the prime/exponent correspondence. -/
private theorem rpow_lt_iff_log_lt326 {z t : ℝ} (hz : 1 < z) {p : ℕ} (hp : 0 < p) :
    (p : ℝ) < z ^ t ↔ Real.log (p : ℝ) / Real.log z < t := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [← Real.log_lt_log_iff hp0 (Real.rpow_pos_of_pos hz0 t), Real.log_rpow hz0]
  constructor
  · intro h; rw [div_lt_iff₀ hlz]; linarith
  · intro h; have hh := (div_lt_iff₀ hlz).mp h; linarith

/-- The interval mass bound of the linear sieve, transported to the variable
`log p / log z`.  This is the summation by parts input: the mass of a band of
primes between two powers of `z` is the logarithmic length of the band plus the
density slack. -/
private theorem mass_t_interval326 (s : BoundingSieve) (K z lo hi : ℝ) (hK : 0 ≤ K)
    (hden : LinearDensity s K) (hz : 1 < z) (hlohi : lo < hi) (hhi : hi ≤ 1)
    (h2 : 2 ≤ z ^ lo) :
    ∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => lo ≤ Real.log (p : ℝ) / Real.log z ∧
          Real.log (p : ℝ) / Real.log z < hi),
        s.nu p ≤ Real.log (hi / lo) + K / (lo * Real.log z) := by
  have hz0 : 0 < z := by linarith
  have hpos : z ^ lo < z ^ hi := Real.rpow_lt_rpow_of_exponent_lt hz hlohi
  have hset : s.prodPrimes.primeFactors.filter
      (fun p : ℕ => lo ≤ Real.log (p : ℝ) / Real.log z ∧
        Real.log (p : ℝ) / Real.log z < hi) =
      s.prodPrimes.primeFactors.filter
        (fun p : ℕ => z ^ lo ≤ (p : ℝ) ∧ (p : ℝ) < z ^ hi) := by
    apply Finset.filter_congr
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact ⟨fun h => ⟨(rpow_le_iff_log_le326 hz hpp.pos).mpr h.1,
        (rpow_lt_iff_log_lt326 hz hpp.pos).mpr h.2⟩,
      fun h => ⟨(rpow_le_iff_log_le326 hz hpp.pos).mp h.1,
        (rpow_lt_iff_log_lt326 hz hpp.pos).mp h.2⟩⟩
  rw [hset]
  have hh := linearDensity_interval_sum s K hK hden (z ^ lo) (z ^ hi) h2 hpos
  have e1 : Real.log (z ^ hi) / Real.log (z ^ lo) = hi / lo := by
    rw [Real.log_rpow hz0, Real.log_rpow hz0]
    have hlz : Real.log z ≠ 0 := (Real.log_pos hz).ne'
    have hlo0 : 0 < lo := by
      by_contra hc
      push_neg at hc
      have hle : z ^ lo ≤ z ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le hc
      rw [Real.rpow_zero] at hle
      linarith
    have hlo : lo ≠ 0 := hlo0.ne'
    field_simp
  have e2 : K / Real.log (z ^ lo) = K / (lo * Real.log z) := by
    rw [Real.log_rpow hz0]
  rw [e1, e2] at hh
  exact hh

/-- Parameter translation for the second stopping term: the density factors at
the prime `p` are dominated by `(1/t)(1+4K/(t log D))` and
`(1+12K/((u-t) log D))` in the variable `t = log p/log z`. -/
private theorem weight_le_G326 {K L lz u t lp : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hu : 2 ≤ u) (hu4 : u ≤ 4) (huL : L = u * lz) (ht : t = lp / lz)
    (ht1 : t ≤ 1) (hp : 0 < lp) (htu0 : 0 < u - t) :
    lz / lp * (1 + K / lp) *
        max 0 (lp / ((L - lp) / 3) * (1 + K / ((L - lp) / 3)) - 1) ≤
      (1 / t) * (1 + 4 * K / (t * L)) *
        max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1) := by
  have hlz : 0 < lz := by
    rcases lt_or_ge 0 lz with h | h
    · exact h
    · rw [huL] at hL
      nlinarith
  have ht0 : 0 < t := by
    rw [ht]
    positivity
  have hLp : L - lp = lz * (u - t) := by
    rw [huL, ht]; field_simp
  have e1 : lz / lp = 1 / t := by
    rw [ht]; field_simp
  have e2 : K / lp = u * K / (t * L) := by
    rw [ht, huL]; field_simp
  have e2' : u * K / (t * L) ≤ 4 * K / (t * L) :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have e3 : lp / ((L - lp) / 3) = 3 * t / (u - t) := by
    rw [hLp, ht]; field_simp
  have e4 : K / ((L - lp) / 3) = 3 * u * K / ((u - t) * L) := by
    rw [hLp, huL]; field_simp
  have e4' : 3 * u * K / ((u - t) * L) ≤ 12 * K / ((u - t) * L) :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have h1 : lz / lp * (1 + K / lp) ≤ (1 / t) * (1 + 4 * K / (t * L)) := by
    rw [e1, e2]
    have hb := e2'
    have h0 : (0 : ℝ) ≤ 1 / t := by positivity
    nlinarith
  have h2 : max 0 (lp / ((L - lp) / 3) * (1 + K / ((L - lp) / 3)) - 1) ≤
      max 0 (3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) - 1) := by
    rw [e3, e4]
    apply max_le_max (le_refl 0)
    have hb1 : 3 * t / (u - t) * (1 + 3 * u * K / ((u - t) * L)) ≤
        3 * t / (u - t) * (1 + 12 * K / ((u - t) * L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- The normalised second stopping term is bounded by the sum of the translated
density weights at the sifting primes. -/
private theorem second_sum_le_G326 (s : BoundingSieve) (K z D : ℝ) (hK : 0 < K)
    (hden : LinearDensity s K) (hz8 : 8 ≤ z) (hzD : z ^ 2 ≤ D) (hz4 : D ≤ z ^ 4)
    (hP : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z) :
    rosserSecondBoundary326 s z D / (∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q)) ≤
      ∑ p ∈ s.prodPrimes.primeFactors,
        s.nu p * ((1 / (Real.log (p : ℝ) / Real.log z)) *
          (1 + 4 * K / ((Real.log (p : ℝ) / Real.log z) * Real.log D)) *
          max 0 (3 * (Real.log (p : ℝ) / Real.log z) /
              (Real.log D / Real.log z - Real.log (p : ℝ) / Real.log z) *
            (1 + 12 * K / ((Real.log D / Real.log z - Real.log (p : ℝ) / Real.log z) *
              Real.log D)) - 1)) := by
  classical
  have hz1 : 1 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos hz1
  have hD : 0 < D := lt_of_lt_of_le (by positivity : (0:ℝ) < z ^ 2) hzD
  have hV : (0 : ℝ) < ∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q) :=
    Finset.prod_pos fun q hq => sub_pos.mpr
      (s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors hq)
        (Nat.dvd_of_mem_primeFactors hq))
  have hzf : s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) =
      s.prodPrimes.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact hP p hp
  rw [rosserSecondBoundary326, hzf, Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hlz' : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpp.one_lt)
  have hpz : (p : ℝ) < z := hP p hp
  have hlpz : Real.log (p : ℝ) < Real.log z := by
    have := Real.log_lt_log hp0 hpz
    linarith
  have ht1 : Real.log (p : ℝ) / Real.log z ≤ 1 := by
    rw [div_le_one hlz]; linarith
  have hu2 : (2 : ℝ) ≤ Real.log D / Real.log z := by
    rw [le_div_iff₀ hlz]
    have h := Real.log_le_log (by positivity : (0:ℝ) < z ^ 2) hzD
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hu4 : Real.log D / Real.log z ≤ 4 := by
    rw [div_le_iff₀ hlz]
    have h := Real.log_le_log hD hz4
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have huL : Real.log D = Real.log D / Real.log z * Real.log z := by
    field_simp
  have htu0 : 0 < Real.log D / Real.log z - Real.log (p : ℝ) / Real.log z := by
    have h2 : 1 < Real.log D / Real.log z := by linarith
    linarith
  have hlw : Real.log (Real.exp (Real.log (D / (p : ℝ)) / 3)) =
      (Real.log D - Real.log (p : ℝ)) / 3 := by
    rw [Real.log_exp, Real.log_div hD.ne' hp0.ne']
  have h1 := second_summand_le326 s K z D hden hK.le hz8 hzD hP hp
  rw [hlw] at h1
  refine h1.trans ?_
  have hnu : 0 ≤ s.nu p := (s.nu_pos_of_prime p hpp (Nat.dvd_of_mem_primeFactors hp)).le
  have hlogD : (0 : ℝ) < Real.log D := Real.log_pos (by nlinarith)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (weight_le_G326 (K := K) (L := Real.log D) (lz := Real.log z)
      (u := Real.log D / Real.log z) (t := Real.log (p : ℝ) / Real.log z)
      (lp := Real.log (p : ℝ)) hK.le hlogD hu2 hu4 huL rfl ht1 hlz' htu0) hnu

/-- Summation by parts for the main band: the `psi`-weighted prime mass is
bounded by the `dt/t` integral of `psi`, which is the continuous second
coefficient, plus the two grid errors.  The grid is geometric with
`n = ceil ((log D)^(1/3))` steps. -/
private theorem main_band_integral326 (s : BoundingSieve) (K z D u lz L : ℝ)
    (hK : 0 < K) (hden : LinearDensity s K) (hz8 : 8 ≤ z) (hD : 0 < D)
    (hlz : lz = Real.log z) (hL : L = Real.log D) (huL : L = u * lz)
    (hu2 : 2 ≤ u) (hu4 : u < 4) (hL1 : 1 ≤ L) (hDV : 2 ≤ D)
    (hP : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z) :
    ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz),
        s.nu p * ((4 * (Real.log (p : ℝ) / lz) - u) /
          ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz))) ≤
      rosserSecondModel326 u +
        2 * (Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) +
          (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L)) := by
  classical
  have hz1 : 1 < z := by linarith
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hlzp : 0 < Real.log z := Real.log_pos hz1
  have hlz' : 0 < lz := by rw [hlz]; exact hlzp
  have ha : 0 < u / 4 := by linarith
  have ha1 : u / 4 < 1 := by linarith
  set n : ℕ := Nat.ceil (L ^ ((1 : ℝ) / 3)) with hndef
  have hn : 0 < n := by
    rw [hndef]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL0 _)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hceil : L ^ ((1 : ℝ) / 3) ≤ (n : ℝ) := by
    rw [hndef]; exact Nat.le_ceil _
  have hlt : (n : ℝ) < L ^ ((1 : ℝ) / 3) + 1 := by
    rw [hndef]; exact Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hL0 _).le
  have hlam1 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 3) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    simpa using h
  set F : ℝ → ℝ := fun x => (4 * x - u) / (x * (u - x)) with hFdef
  have hFa : F (u / 4) = 0 := by
    simp only [hFdef]
    have h : 4 * (u / 4) - u = 0 := by ring
    rw [h, zero_div]
  have hFmono : ∀ x ∈ Set.Icc (u / 4) 1, ∀ y ∈ Set.Icc (u / 4) 1, x ≤ y → F x ≤ F y := by
    intro x hx y hy hxy
    simp only [hFdef]
    have hx0 : 0 < x := by linarith [hx.1]
    have hxu : 0 < u - x := by linarith [hx.2]
    have hy0 : 0 < y := by linarith [hy.1]
    have hyu : 0 < u - y := by linarith [hy.2]
    rw [div_le_div_iff₀ (mul_pos hx0 hxu) (mul_pos hy0 hyu)]
    have h1 : 0 ≤ y - x := by linarith
    have h2 : 0 ≤ u * u - u * x - u * y + 4 * (x * y) := by nlinarith [hxy, hx.2, hy.2]
    have h3 : 0 ≤ (y - x) * (u * u - u * x - u * y + 4 * (x * y)) := mul_nonneg h1 h2
    nlinarith [h3]
  have hFcont : ContinuousOn F (Set.Icc (u / 4) 1) := by
    simp only [hFdef]
    apply ContinuousOn.div
    · exact (continuousOn_const.mul continuousOn_id).sub continuousOn_const
    · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
    · intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hxu : 0 < u - x := by linarith [hx.2]
      exact mul_ne_zero hx0.ne' hxu.ne'
  -- the interval mass bound, in the form the abstract lemma wants
  have hmass : ∀ a' b' : ℝ, u / 4 ≤ a' → a' < b' → b' ≤ 1 →
      ∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz)).filter
          (fun p : ℕ => a' ≤ Real.log (p : ℝ) / lz ∧ Real.log (p : ℝ) / lz < b'),
        s.nu p ≤ Real.log (b' / a') + 4 * K / (a' * L) := by
    intro a' b' ha' hab' hb'
    have hset : (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz)).filter
          (fun p : ℕ => a' ≤ Real.log (p : ℝ) / lz ∧ Real.log (p : ℝ) / lz < b') =
        s.prodPrimes.primeFactors.filter
          (fun p : ℕ => a' ≤ Real.log (p : ℝ) / lz ∧ Real.log (p : ℝ) / lz < b') := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, ⟨h1, h2⟩⟩
    rw [hset, hlz]
    have h2 : 2 ≤ z ^ a' := by
      have hlog2 : Real.log 2 / Real.log z ≤ 1 / 2 := by
        rw [div_le_iff₀ hlzp]
        have h8 : Real.log (8 : ℝ) ≤ Real.log z := Real.log_le_log (by norm_num) hz8
        have h83 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
          convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
        rw [h83] at h8
        linarith
      calc (2 : ℝ) = z ^ (Real.log 2 / Real.log z) := (rpow_log_div326 hz1 (by norm_num)).symm
        _ ≤ z ^ a' := Real.rpow_le_rpow_of_exponent_le hz1.le (by linarith)
    have hm := mass_t_interval326 s K z a' b' hK.le hden hz1 hab' hb' h2
    have h1 : K / (a' * Real.log z) ≤ 4 * K / (a' * L) := by
      have ha0 : 0 < a' := by linarith
      rw [div_le_div_iff₀ (mul_pos ha0 hlzp) (mul_pos ha0 hL0)]
      have hlzeq : Real.log z = lz := hlz.symm
      rw [hlzeq, huL]
      have hpos : 0 < K * (a' * lz) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hu4.le hpos.le]
    linarith
  -- the required ingredients for the abstract summation lemma
  have hrho1 : (1 : ℝ) < (1 / (u / 4)) ^ ((n : ℝ)⁻¹) := by
    have hbase : (1 : ℝ) < 1 / (u / 4) := by
      rw [lt_div_iff₀ ha]
      linarith
    have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact Real.one_lt_rpow hbase (inv_pos.mpr hnr)
  have hrhon : ((1 / (u / 4)) ^ ((n : ℝ)⁻¹)) ^ n = 1 / (u / 4) := by
    have hbase : (0 : ℝ) ≤ 1 / (u / 4) := by positivity
    exact Real.rpow_inv_natCast_pow hbase hn.ne'
  have hnu0 : ∀ p ∈ s.prodPrimes.primeFactors.filter
      (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz), 0 ≤ s.nu p := by
    intro p hp
    exact (s.nu_pos_of_prime p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
  have hta0 : ∀ p ∈ s.prodPrimes.primeFactors.filter
      (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz), u / 4 ≤ Real.log (p : ℝ) / lz := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have ht10 : ∀ p ∈ s.prodPrimes.primeFactors.filter
      (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz), Real.log (p : ℝ) / lz < 1 := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hmem.1
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hltz : Real.log (p : ℝ) < Real.log z := Real.log_lt_log hp0 (hP p hmem.1)
    rw [hlz]
    exact (div_lt_one hlzp).mpr hltz
  have hmain := sum_le_integral326 F (4 * K) L (u / 4) ((1 / (u / 4)) ^ ((n : ℝ)⁻¹)) n hn
    ha ha1 hL1 (by positivity) hrho1 hrhon hFmono hFcont hFa
    (s.prodPrimes.primeFactors.filter (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz))
    s.nu (fun p : ℕ => Real.log (p : ℝ) / lz) hnu0 hta0 ht10 hmass
  -- identify the integral with the continuous coefficient and bound `F 1`
  have hint : (∫ x in (u / 4)..(1 : ℝ), F x / x) = rosserSecondModel326 u := by
    have heq : (∫ x in (u / 4)..(1 : ℝ), F x / x) =
        ∫ x in (u / 4)..(1 : ℝ), (3 / (x * (u - x)) - 1 / x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : u / 4 ≤ 1)] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have hxu : u - x ≠ 0 := by linarith [hx.2]
      simp only [hFdef]
      field_simp
      ring
    rw [heq, second_model_eq_tail_integral326 (by linarith) hu4.le]
  have hF1 : F 1 ≤ 2 := by
    simp only [hFdef]
    norm_num
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < u - 1)]
    linarith
  have hE0 : (0 : ℝ) ≤ Real.log (1 / (u / 4)) / (n : ℝ) +
      (n : ℝ) * (4 * K) / (u / 4 * L) := by
    have h1 : (0 : ℝ) ≤ Real.log (1 / (u / 4)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ ha]
      linarith
    have h2 : (0 : ℝ) ≤ Real.log (1 / (u / 4)) / (n : ℝ) :=
      div_nonneg h1 (by positivity)
    have h3 : (0 : ℝ) ≤ (n : ℝ) * (4 * K) / (u / 4 * L) := by
      apply div_nonneg _ (by positivity)
      positivity
    linarith
  have hgoal : (∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz),
      s.nu p * ((4 * (Real.log (p : ℝ) / lz) - u) /
        ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz)))) =
      ∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz),
      s.nu p * F (Real.log (p : ℝ) / lz) := rfl
  rw [hgoal, hint] at hmain
  refine hmain.trans ?_
  have h2 : F 1 * (Real.log (1 / (u / 4)) / (n : ℝ) +
      (n : ℝ) * (4 * K) / (u / 4 * L)) ≤
      2 * (Real.log (1 / (u / 4)) / (n : ℝ) +
        (n : ℝ) * (4 * K) / (u / 4 * L)) :=
    mul_le_mul_of_nonneg_right hF1 hE0
  linarith

set_option maxHeartbeats 4000000 in
/-- Arithmetic endgame for the second stopping term: the two relative losses,
the two grid errors and the middle band are all of size `(1+K)^3 L^{-1/3}`. -/
private theorem bound_total326 {K lr dl de E Y0 Btot : ℝ}
    (hK : 0 < K) (hlr0 : 0 ≤ lr) (hlr1 : lr ≤ 1)
    (hdl0 : 0 ≤ dl) (hde0 : 0 ≤ de) (hE0 : 0 ≤ E) (hY0 : 0 ≤ Y0)
    (hdl : dl ≤ 40 * K * lr) (hde : de ≤ 12 * K * lr)
    (hE : E ≤ (Real.log 2 + 16 * K) * lr)
    (hY : Y0 ≤ Real.log 2 + 8 * K * lr)
    (hB : Btot ≤ 64 * (1 + 32 * K) * (5 * K + K ^ 2 / Real.log 2) * lr)
    (hlog2 : 0 < Real.log 2) (hlog2gt : 1 / 2 ≤ Real.log 2) (hlog2le : Real.log 2 ≤ 1) :
    4 * dl + 4 * de + 4 * (dl * de) + (1 + dl) * (1 + de) * (2 * E) +
      8 * (1 + dl) * de * Y0 + Btot ≤ 1000000 * (1 + K) ^ 3 * lr := by
  have hK0 : (0 : ℝ) ≤ K := hK.le
  have hK1 : (0 : ℝ) ≤ 1 + K := by linarith
  have hl2 : (0 : ℝ) ≤ Real.log 2 := hlog2.le
  have hc : 1 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2]
    linarith
  -- pure arithmetic: the coefficient bounds used below
  have hp1 : (1 + 40 * K) * (1 + 12 * K) * (2 * (1 + 16 * K)) ≤ 40000 * (1 + K) ^ 3 := by
    have b1 : (1 + 40 * K) ≤ 41 * (1 + K) := by nlinarith
    have b2 : (1 + 12 * K) ≤ 13 * (1 + K) := by nlinarith
    have b3 : 2 * (1 + 16 * K) ≤ 34 * (1 + K) := by nlinarith
    have b12 : (1 + 40 * K) * (1 + 12 * K) ≤ (41 * (1 + K)) * (13 * (1 + K)) :=
      mul_le_mul b1 b2 (by positivity) (by positivity)
    have b123 : (1 + 40 * K) * (1 + 12 * K) * (2 * (1 + 16 * K)) ≤
        (41 * (1 + K)) * (13 * (1 + K)) * (34 * (1 + K)) :=
      mul_le_mul b12 b3 (by positivity) (by positivity)
    have he : (41 * (1 + K)) * (13 * (1 + K)) * (34 * (1 + K)) = 18122 * (1 + K) ^ 3 := by ring
    rw [he] at b123
    nlinarith [hK1, mul_nonneg (mul_nonneg hK1 hK1) hK1]
  have hp2 : 8 * ((1 + 40 * K) * (12 * K)) * (1 + 8 * K) ≤ 100000 * (1 + K) ^ 3 := by
    have b1 : (1 + 40 * K) ≤ 41 * (1 + K) := by nlinarith
    have b2 : 12 * K ≤ 12 * (1 + K) := by nlinarith
    have b3 : (1 + 8 * K) ≤ 9 * (1 + K) := by nlinarith
    have b12 : (1 + 40 * K) * (12 * K) ≤ (41 * (1 + K)) * (12 * (1 + K)) :=
      mul_le_mul b1 b2 (by positivity) (by positivity)
    have b123 : ((1 + 40 * K) * (12 * K)) * (1 + 8 * K) ≤
        ((41 * (1 + K)) * (12 * (1 + K))) * (9 * (1 + K)) :=
      mul_le_mul b12 b3 (by positivity) (by positivity)
    have h8 := mul_le_mul_of_nonneg_left b123 (by norm_num : (0:ℝ) ≤ 8)
    have he : 8 * (((41 * (1 + K)) * (12 * (1 + K))) * (9 * (1 + K))) = 35424 * (1 + K) ^ 3 := by
      ring
    rw [he] at h8
    nlinarith [h8, mul_nonneg (mul_nonneg hK1 hK1) hK1]
  have hp3 : 64 * (1 + 32 * K) * (5 * K + 2 * K ^ 2) ≤ 100000 * (1 + K) ^ 3 := by
    have b1 : (1 + 32 * K) ≤ 33 * (1 + K) := by nlinarith
    have b2 : 5 * K + 2 * K ^ 2 ≤ 7 * (1 + K) ^ 2 := by nlinarith [hK0]
    have b12 : (1 + 32 * K) * (5 * K + 2 * K ^ 2) ≤ (33 * (1 + K)) * (7 * (1 + K) ^ 2) :=
      mul_le_mul b1 b2 (by positivity) (by positivity)
    have he : 64 * ((33 * (1 + K)) * (7 * (1 + K) ^ 2)) = 14784 * (1 + K) ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left b12 (by norm_num : (0:ℝ) ≤ 64)]
  -- step 1: the two relative losses
  have hd1 : 4 * dl + 4 * de + 4 * (dl * de) ≤ 100000 * (1 + K) ^ 3 * lr := by
    have hmul : dl * de ≤ (40 * K * lr) * (12 * K * lr) :=
      mul_le_mul hdl hde hde0 (by positivity)
    have hlr2 : lr * lr ≤ lr := by nlinarith [hlr0, hlr1]
    have hprod : (40 * K * lr) * (12 * K * lr) ≤ 480 * K ^ 2 * lr := by
      nlinarith [hlr2, mul_nonneg hK0 hlr0, mul_nonneg (mul_nonneg hK0 hK0) hlr0, hlr0, hK0]
    have hk2 : K ^ 2 ≤ (1 + K) ^ 3 := by nlinarith [hK0]
    have hk1 : K ≤ (1 + K) ^ 3 := by nlinarith [hK0]
    have hq : 480 * K ^ 2 * lr ≤ 480 * (1 + K) ^ 3 * lr :=
      mul_le_mul_of_nonneg_right (by linarith [hk2]) hlr0
    have hq1 : 40 * K * lr ≤ 40 * (1 + K) ^ 3 * lr :=
      mul_le_mul_of_nonneg_right (by linarith [hk1]) hlr0
    have hq2 : 12 * K * lr ≤ 12 * (1 + K) ^ 3 * lr :=
      mul_le_mul_of_nonneg_right (by linarith [hk1]) hlr0
    nlinarith [hmul, hprod, hq, hq1, hq2, hlr0, hK0, mul_nonneg (mul_nonneg hK0 hK0) hlr0]
  -- step 2: the first grid error
  have hE1 : (1 + dl) * (1 + de) * (2 * E) ≤ 40000 * (1 + K) ^ 3 * lr := by
    have h1 : 1 + dl ≤ 1 + 40 * K * lr := by linarith
    have h2 : 1 + de ≤ 1 + 12 * K * lr := by linarith
    have h3 : (1 + dl) * (1 + de) ≤ (1 + 40 * K * lr) * (1 + 12 * K * lr) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : (1 + dl) * (1 + de) * (2 * E) ≤
        (1 + 40 * K * lr) * (1 + 12 * K * lr) * (2 * ((Real.log 2 + 16 * K) * lr)) :=
      mul_le_mul h3 (by linarith [hE]) (by positivity) (by positivity)
    have h5 : (1 + 40 * K * lr) ≤ (1 + 40 * K) := by nlinarith [hlr1, hK0]
    have h6 : (1 + 12 * K * lr) ≤ (1 + 12 * K) := by nlinarith [hlr1, hK0]
    have h7 : 2 * ((Real.log 2 + 16 * K) * lr) ≤ 2 * ((1 + 16 * K) * lr) := by
      nlinarith [hlog2le, hlr0]
    have h8 : (1 + 40 * K * lr) * (1 + 12 * K * lr) * (2 * ((Real.log 2 + 16 * K) * lr)) ≤
        (1 + 40 * K) * (1 + 12 * K) * (2 * ((1 + 16 * K) * lr)) := by
      have h56 : (1 + 40 * K * lr) * (1 + 12 * K * lr) ≤ (1 + 40 * K) * (1 + 12 * K) :=
        mul_le_mul h5 h6 (by positivity) (by positivity)
      exact mul_le_mul h56 h7 (by positivity) (by positivity)
    have h9 : (1 + 40 * K) * (1 + 12 * K) * (2 * ((1 + 16 * K) * lr)) ≤
        40000 * (1 + K) ^ 3 * lr := by
      have he : (1 + 40 * K) * (1 + 12 * K) * (2 * ((1 + 16 * K) * lr)) =
          ((1 + 40 * K) * (1 + 12 * K) * (2 * (1 + 16 * K))) * lr := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hp1 hlr0
    exact le_trans h4 (le_trans h8 h9)
  -- step 3: the `1/t` correction
  have hY1 : 8 * (1 + dl) * de * Y0 ≤ 100000 * (1 + K) ^ 3 * lr := by
    have h1 : 1 + dl ≤ 1 + 40 * K * lr := by linarith
    have hs1 : (1 + dl) * de ≤ (1 + 40 * K * lr) * (12 * K * lr) :=
      mul_le_mul h1 hde hde0 (by positivity)
    have h2 : 8 * ((1 + dl) * de) ≤ 8 * ((1 + 40 * K * lr) * (12 * K * lr)) :=
      mul_le_mul_of_nonneg_left hs1 (by norm_num)
    have h3 : 8 * (1 + dl) * de * Y0 =
        8 * ((1 + dl) * de) * Y0 := by ring
    rw [h3]
    have hY0' : (0 : ℝ) ≤ Real.log 2 + 8 * K * lr := by positivity
    have h4 : 8 * ((1 + dl) * de) * Y0 ≤
        8 * ((1 + 40 * K * lr) * (12 * K * lr)) * (Real.log 2 + 8 * K * lr) :=
      mul_le_mul h2 hY hY0 (by positivity)
    have hb1 : (1 + 40 * K * lr) ≤ (1 + 40 * K) := by nlinarith [hlr1, hK0]
    have hb3 : Real.log 2 + 8 * K * lr ≤ 1 + 8 * K := by nlinarith [hlog2le, hlr1, hK0]
    have hb2 : 12 * K * lr ≤ 12 * K * lr := le_rfl
    have h5 : ((1 + 40 * K * lr) * (12 * K * lr)) ≤ (1 + 40 * K) * (12 * K * lr) :=
      mul_le_mul hb1 hb2 (by positivity) (by positivity)
    have h6 : ((1 + 40 * K * lr) * (12 * K * lr)) * (Real.log 2 + 8 * K * lr) ≤
        ((1 + 40 * K) * (12 * K * lr)) * (1 + 8 * K) :=
      mul_le_mul h5 hb3 hY0' (by positivity)
    have h7 : 8 * ((1 + 40 * K * lr) * (12 * K * lr)) * (Real.log 2 + 8 * K * lr) ≤
        8 * ((1 + 40 * K) * (12 * K * lr)) * (1 + 8 * K) := by
      nlinarith [h6]
    have h8 : 8 * ((1 + 40 * K) * (12 * K * lr)) * (1 + 8 * K) =
        (8 * ((1 + 40 * K) * (12 * K)) * (1 + 8 * K)) * lr := by ring
    have h9 := mul_le_mul_of_nonneg_right hp2 hlr0
    calc 8 * ((1 + dl) * de) * Y0
        ≤ 8 * ((1 + 40 * K * lr) * (12 * K * lr)) * (Real.log 2 + 8 * K * lr) := h4
      _ ≤ 8 * ((1 + 40 * K) * (12 * K * lr)) * (1 + 8 * K) := h7
      _ = (8 * ((1 + 40 * K) * (12 * K)) * (1 + 8 * K)) * lr := h8
      _ ≤ 100000 * (1 + K) ^ 3 * lr := h9
  -- step 4: the middle band
  have hB1 : Btot ≤ 100000 * (1 + K) ^ 3 * lr := by
    have h0 : (0:ℝ) ≤ 4 * K + K ^ 2 / Real.log 2 := by positivity
    have h7 : K ^ 2 / Real.log 2 ≤ 2 * K ^ 2 := by
      rw [div_le_iff₀ hlog2]
      nlinarith [mul_nonneg hK0 hK0, hlog2le]
    have h6 : 5 * K + K ^ 2 / Real.log 2 ≤ 5 * K + 2 * K ^ 2 := by linarith
    have h8 : 64 * (1 + 32 * K) * (5 * K + K ^ 2 / Real.log 2) ≤
        64 * (1 + 32 * K) * (5 * K + 2 * K ^ 2) := by
      apply mul_le_mul_of_nonneg_left h6 (by positivity)
    have h9 : 64 * (1 + 32 * K) * (5 * K + K ^ 2 / Real.log 2) ≤ 100000 * (1 + K) ^ 3 :=
      le_trans h8 hp3
    have h10 := mul_le_mul_of_nonneg_right h9 hlr0
    linarith [hB]
  have hS1 : 4 * dl + 4 * de + 4 * (dl * de) ≤ (100000:ℝ) * (1 + K) ^ 3 * lr := hd1
  have hS2 : (1 + dl) * (1 + de) * (2 * E) ≤ (40000:ℝ) * (1 + K) ^ 3 * lr := hE1
  have hS3 : 8 * (1 + dl) * de * Y0 ≤ (100000:ℝ) * (1 + K) ^ 3 * lr := hY1
  have hS4 : Btot ≤ (100000:ℝ) * (1 + K) ^ 3 * lr := hB1
  have hc0 : (0:ℝ) ≤ (1 + K) ^ 3 * lr := by positivity
  nlinarith [hS1, hS2, hS3, hS4, hc0]

/-- The mass of the main band `u/4 ≤ log p/log z` is the logarithmic length of
`[z^{u/4}, z]` plus the density slack. -/
private theorem mass_band326 (s : BoundingSieve) (K z D u lz L : ℝ) (hK : 0 < K)
    (hden : LinearDensity s K) (hz8 : 8 ≤ z) (hDV : 2 ≤ D) (hlz : lz = Real.log z)
    (hL : L = Real.log D) (huL : L = u * lz) (hu2 : 2 ≤ u) (hu4 : u < 4)
    (hP : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z) :
    ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz),
        s.nu p ≤ Real.log (1 / (u / 4)) + 4 * K / (u / 4 * L) := by
  classical
  have hz1 : 1 < z := by linarith
  have hlzp : 0 < Real.log z := Real.log_pos hz1
  have hlz' : 0 < lz := by rw [hlz]; exact hlzp
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have ha : 0 < u / 4 := by linarith
  have ha1 : u / 4 < 1 := by linarith
  rw [hlz]
  have h2 : 2 ≤ z ^ (u / 4) := by
    have hlog2 : Real.log 2 / Real.log z ≤ 1 / 2 := by
      rw [div_le_iff₀ hlzp]
      have h8 : Real.log (8 : ℝ) ≤ Real.log z := Real.log_le_log (by norm_num) hz8
      have h83 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
      rw [h83] at h8
      linarith
    calc (2 : ℝ) = z ^ (Real.log 2 / Real.log z) := (rpow_log_div326 hz1 (by norm_num)).symm
      _ ≤ z ^ (u / 4) := Real.rpow_le_rpow_of_exponent_le hz1.le (by linarith)
  have hfil : s.prodPrimes.primeFactors.filter (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / Real.log z) =
      s.prodPrimes.primeFactors.filter
        (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / Real.log z ∧
          Real.log (p : ℝ) / Real.log z < 1) := by
    apply Finset.filter_congr
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hltz : Real.log (p : ℝ) < Real.log z := Real.log_lt_log hp0 (hP p hp)
    constructor
    · intro h; exact ⟨h, (div_lt_one hlzp).mpr hltz⟩
    · rintro ⟨h, -⟩; exact h
  have hm := mass_t_interval326 s K z (u / 4) 1 hK.le hden hz1 ha1 le_rfl h2
  rw [hfil]
  have h1 : K / (u / 4 * Real.log z) ≤ 4 * K / (u / 4 * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [huL]
    have hpos : 0 < K * (u / 4 * lz) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hu4.le hpos.le]
  linarith

/-- The main band costs its continuous coefficient plus the two grid errors,
and the `1/t` correction is bounded by eight times the band mass. -/
private theorem region_C_le326 (s : BoundingSieve) (K z D u lz L : ℝ) (hK : 0 < K)
    (hden : LinearDensity s K) (hz8 : 8 ≤ z) (hDV : 2 ≤ D) (hL1 : 1 ≤ L)
    (hlz : lz = Real.log z)
    (hL : L = Real.log D) (huL : L = u * lz) (hu2 : 2 ≤ u) (hu4 : u < 4)
    (hP : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z) :
    ∑ p ∈ (s.prodPrimes.primeFactors.filter
        (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
        (fun p : ℕ => ¬ Real.log (p : ℝ) / lz < u / 4),
      s.nu p * ((1 / (Real.log (p : ℝ) / lz)) *
        (1 + 4 * K / ((Real.log (p : ℝ) / lz) * L)) *
        max 0 (3 * (Real.log (p : ℝ) / lz) /
            (u - Real.log (p : ℝ) / lz) *
          (1 + 12 * K / ((u - Real.log (p : ℝ) / lz) * L)) - 1)) ≤
      (1 + 4 * K / (u / 4 * L)) *
        ((1 + 12 * K / ((u - 1) * L)) *
            (rosserSecondModel326 u +
              2 * (Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) +
                (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L))) +
          (12 * K / ((u - 1) * L)) *
            (8 * (Real.log (1 / (u / 4)) + 4 * K / (u / 4 * L)))) := by
  classical
  have hz1 : 1 < z := by linarith
  have hlzp : 0 < Real.log z := Real.log_pos hz1
  have hlz' : 0 < lz := by rw [hlz]; exact hlzp
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hu4le : u ≤ 4 := hu4.le
  have hu1 : 0 < u - 1 := by linarith
  set P2 := s.prodPrimes.primeFactors.filter (fun p : ℕ => u / 4 ≤ Real.log (p : ℝ) / lz)
    with hP2def
  set Cre := (s.prodPrimes.primeFactors.filter
      (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
      (fun p : ℕ => ¬ Real.log (p : ℝ) / lz < u / 4) with hCredef
  have hsub : Cre ⊆ P2 := by
    intro p hp
    rw [hCredef, Finset.mem_filter] at hp
    rw [hP2def, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hp.1).1, not_lt.mp hp.2⟩
  -- the pointwise weight bound
  have hpt : ∀ p ∈ Cre, s.nu p * ((1 / (Real.log (p : ℝ) / lz)) *
        (1 + 4 * K / ((Real.log (p : ℝ) / lz) * L)) *
        max 0 (3 * (Real.log (p : ℝ) / lz) /
            (u - Real.log (p : ℝ) / lz) *
          (1 + 12 * K / ((u - Real.log (p : ℝ) / lz) * L)) - 1)) ≤
      s.nu p * ((1 + 4 * K / (u / 4 * L)) *
        ((1 + 12 * K / ((u - 1) * L)) *
            ((4 * (Real.log (p : ℝ) / lz) - u) /
              ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz))) +
          (12 * K / ((u - 1) * L)) * (1 / (Real.log (p : ℝ) / lz)))) := by
    intro p hp
    rw [hCredef, Finset.mem_filter] at hp
    have hmem : p ∈ s.prodPrimes.primeFactors := (Finset.mem_filter.mp hp.1).1
    have hpp := Nat.prime_of_mem_primeFactors hmem
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hltz : Real.log (p : ℝ) < Real.log z := Real.log_lt_log hp0 (hP p hmem)
    have htt1 : Real.log (p : ℝ) / lz < 1 := by
      rw [hlz]; exact (div_lt_one hlzp).mpr hltz
    have htu : u / 4 ≤ Real.log (p : ℝ) / lz := not_lt.mp hp.2
    have hnu : 0 ≤ s.nu p := (s.nu_pos_of_prime p hpp
      (Nat.dvd_of_mem_primeFactors hmem)).le
    exact mul_le_mul_of_nonneg_left
      (second_weight_le326 hK.le hL0 hu2 hu4le htu htt1.le) hnu
  -- the two band sums
  have hpsi : ∑ p ∈ Cre, s.nu p * ((4 * (Real.log (p : ℝ) / lz) - u) /
      ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz))) ≤
      rosserSecondModel326 u +
        2 * (Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) +
          (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L)) := by
    have h1 : ∑ p ∈ Cre, s.nu p * ((4 * (Real.log (p : ℝ) / lz) - u) /
        ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz))) ≤
        ∑ p ∈ P2, s.nu p * ((4 * (Real.log (p : ℝ) / lz) - u) /
          ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hmem := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hmem.1
      have hpsi0 : 0 ≤ (4 * (Real.log (p : ℝ) / lz) - u) /
          ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz)) := by
        have hp1 : (0 : ℝ) < Real.log (p : ℝ) / lz := by
          apply div_pos (Real.log_pos (by exact_mod_cast hpp.one_lt)) hlz'
        have htt1 : Real.log (p : ℝ) / lz < 1 := by
          have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
          have hltz : Real.log (p : ℝ) < Real.log z := Real.log_lt_log hp0 (hP p hmem.1)
          rw [hlz]
          exact (div_lt_one hlzp).mpr hltz
        have hpu : 0 < u - Real.log (p : ℝ) / lz := by linarith
        exact div_nonneg (by linarith [hmem.2]) (by positivity)
      exact mul_nonneg (s.nu_pos_of_prime p hpp (Nat.dvd_of_mem_primeFactors hmem.1)).le hpsi0
    refine h1.trans ?_
    rw [hP2def]
    exact main_band_integral326 s K z D u lz L hK hden hz8 (by linarith) hlz hL huL hu2
      hu4 hL1 hDV hP
  have hY0 : ∑ p ∈ Cre, s.nu p * (1 / (Real.log (p : ℝ) / lz)) ≤
      8 * (Real.log (1 / (u / 4)) + 4 * K / (u / 4 * L)) := by
    have hpt2 : ∀ p ∈ Cre, s.nu p * (1 / (Real.log (p : ℝ) / lz)) ≤ 8 * s.nu p := by
      intro p hp
      have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
      have hpp := Nat.prime_of_mem_primeFactors hmem.1
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have ht0 : 0 < Real.log (p : ℝ) / lz :=
        div_pos (Real.log_pos (by exact_mod_cast hpp.one_lt)) hlz'
      have htge : u / 4 ≤ Real.log (p : ℝ) / lz := not_lt.mp (Finset.mem_filter.mp hp).2
      have h8 : 1 / (Real.log (p : ℝ) / lz) ≤ 8 := by
        rw [div_le_iff₀ ht0]
        linarith
      calc s.nu p * (1 / (Real.log (p : ℝ) / lz)) ≤ s.nu p * 8 :=
            mul_le_mul_of_nonneg_left h8 (s.nu_pos_of_prime p hpp
              (Nat.dvd_of_mem_primeFactors hmem.1)).le
        _ = 8 * s.nu p := by ring
    have h2 : ∑ p ∈ Cre, s.nu p * (1 / (Real.log (p : ℝ) / lz)) ≤ ∑ p ∈ Cre, 8 * s.nu p :=
      Finset.sum_le_sum hpt2
    have h3 : ∑ p ∈ Cre, s.nu p ≤ ∑ p ∈ P2, s.nu p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hmemP : p ∈ s.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
      exact (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hmemP)
        (Nat.dvd_of_mem_primeFactors hmemP)).le
    have h4 : ∑ p ∈ P2, s.nu p ≤ Real.log (1 / (u / 4)) + 4 * K / (u / 4 * L) := by
      rw [hP2def]
      exact mass_band326 s K z D u lz L hK hden hz8 hDV hlz hL huL hu2 hu4 hP
    have h5 : ∑ p ∈ Cre, 8 * s.nu p = 8 * ∑ p ∈ Cre, s.nu p := by
      rw [Finset.mul_sum]
    rw [h5] at h2
    nlinarith [h2, h3, h4]
  -- assemble
  have hden' : (0 : ℝ) ≤ 1 + 4 * K / (u / 4 * L) := by positivity
  have heps0 : (0 : ℝ) ≤ 1 + 12 * K / ((u - 1) * L) := by positivity
  have hd0 : (0 : ℝ) ≤ 12 * K / ((u - 1) * L) := by positivity
  calc ∑ p ∈ Cre, s.nu p * ((1 / (Real.log (p : ℝ) / lz)) *
        (1 + 4 * K / ((Real.log (p : ℝ) / lz) * L)) *
        max 0 (3 * (Real.log (p : ℝ) / lz) / (u - Real.log (p : ℝ) / lz) *
          (1 + 12 * K / ((u - Real.log (p : ℝ) / lz) * L)) - 1))
      ≤ ∑ p ∈ Cre, s.nu p * ((1 + 4 * K / (u / 4 * L)) *
          ((1 + 12 * K / ((u - 1) * L)) *
              ((4 * (Real.log (p : ℝ) / lz) - u) /
                ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz))) +
            (12 * K / ((u - 1) * L)) * (1 / (Real.log (p : ℝ) / lz)))) :=
        Finset.sum_le_sum hpt
    _ = (1 + 4 * K / (u / 4 * L)) *
          ∑ p ∈ Cre, s.nu p * ((1 + 12 * K / ((u - 1) * L)) *
              ((4 * (Real.log (p : ℝ) / lz) - u) /
                ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz))) +
            (12 * K / ((u - 1) * L)) * (1 / (Real.log (p : ℝ) / lz))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ = (1 + 4 * K / (u / 4 * L)) *
          ((1 + 12 * K / ((u - 1) * L)) *
              (∑ p ∈ Cre, s.nu p * ((4 * (Real.log (p : ℝ) / lz) - u) /
                ((Real.log (p : ℝ) / lz) * (u - Real.log (p : ℝ) / lz)))) +
            (12 * K / ((u - 1) * L)) *
              (∑ p ∈ Cre, s.nu p * (1 / (Real.log (p : ℝ) / lz)))) := by
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ ≤ (1 + 4 * K / (u / 4 * L)) *
          ((1 + 12 * K / ((u - 1) * L)) *
              (rosserSecondModel326 u +
                2 * (Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) +
                  (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L))) +
            (12 * K / ((u - 1) * L)) *
              (8 * (Real.log (1 / (u / 4)) + 4 * K / (u / 4 * L)))) := by
        apply mul_le_mul_of_nonneg_left _ hden'
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hpsi heps0
        · exact mul_le_mul_of_nonneg_left hY0 hd0

/-! ### 5. The assembly of `jr_lower_second326` -/

/-- `1/(u/4) ≤ 2` on the model range. -/
private theorem inv_four_div326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    1 / (u / 4) ≤ 2 := by
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < u / 4)]
  linarith

/-- The band factor is at most `log 2`. -/
private theorem log_inv_four_div_le326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    Real.log (1 / (u / 4)) ≤ Real.log 2 :=
  Real.log_le_log (by positivity) (inv_four_div326 hu hu4)

/-- The band factor is nonnegative. -/
private theorem log_inv_four_div_nonneg326 {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) :
    0 ≤ Real.log (1 / (u / 4)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < u / 4)]
  linarith

/-- The mass of the middle band `u/16 ≤ log p/log z < u/4` is `log 4` plus the
density slack. -/
private theorem mid_mass326 (s : BoundingSieve) (K z D u lz L : ℝ) (hK : 0 < K)
    (hden : LinearDensity s K) (hz8 : 8 ≤ z) (hzD : z ^ 2 ≤ D)
    (hlzdef : lz = Real.log z) (hLdef : L = Real.log D) (huL : L = u * lz)
    (hu2 : 2 ≤ u) (hu4 : u < 4)
    (hP : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z) :
    ∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => u / 16 ≤ Real.log (p : ℝ) / lz ∧ Real.log (p : ℝ) / lz < u / 4),
        s.nu p ≤ Real.log 4 + 16 * K / L := by
  have hz1 : 1 < z := by linarith
  have hlzp : 0 < Real.log z := Real.log_pos hz1
  have hD1 : (1 : ℝ) < D := by nlinarith [hzD, hz8]
  have hL0 : 0 < L := by rw [hLdef]; exact Real.log_pos hD1
  have hlz' : 0 < lz := by rw [hlzdef]; exact hlzp
  have hL4s : 4 * Real.log 2 < L := by
    have h2 : 2 * Real.log z ≤ L := by
      rw [hLdef]
      have h := Real.log_le_log (by positivity : (0 : ℝ) < z ^ 2) hzD
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hlog4 : Real.log 4 < Real.log z := Real.log_lt_log (by norm_num) (by linarith : (4 : ℝ) < z)
    have h44 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  set lo := max (u / 16) (Real.log 2 / Real.log z) with hlodef
  have hlo2 : 2 ≤ z ^ lo := by
    rw [hlodef]
    exact two_le_rpow_band326 hz1 hu2
  have hlo_lt : lo < u / 4 := by
    rw [hlodef]
    apply max_lt
    · linarith
    · rw [div_lt_iff₀ hlzp]
      have huz : u / 4 * Real.log z = L / 4 := by
        rw [← hlzdef, huL]
        field_simp
        try ring
      linarith [hL4s]
  have hset : s.prodPrimes.primeFactors.filter
        (fun p : ℕ => u / 16 ≤ Real.log (p : ℝ) / lz ∧ Real.log (p : ℝ) / lz < u / 4) =
      s.prodPrimes.primeFactors.filter
        (fun p : ℕ => lo ≤ Real.log (p : ℝ) / lz ∧ Real.log (p : ℝ) / lz < u / 4) := by
    apply Finset.filter_congr
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
    have htge : Real.log 2 / Real.log z ≤ Real.log (p : ℝ) / lz := by
      rw [hlzdef]
      exact div_le_div_of_nonneg_right hlog hlzp.le
    rw [hlodef]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨max_le h1 htge, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨le_trans (le_max_left _ _) h1, h2⟩
  have hm := mass_t_interval326 s K z lo (u / 4) hK.le hden hz1 hlo_lt (by linarith) hlo2
  rw [← hlzdef] at hm
  rw [hset]
  have hlog : Real.log ((u / 4) / lo) ≤ Real.log 4 := by
    apply Real.log_le_log (by positivity)
    rw [hlodef]
    rcases le_total (Real.log 2 / Real.log z) (u / 16) with hle | hle
    · rw [max_eq_left hle]
      have heq : (u / 4) / (u / 16) = 4 := by
        field_simp
        ring
      rw [heq]
    · rw [max_eq_right hle]
      have heL : u / 16 ≤ Real.log 2 / Real.log z := hle
      have hL16 : L ≤ 16 * Real.log 2 := by
        rw [le_div_iff₀ hlzp] at heL
        rw [huL]
        nlinarith [heL, hlzp]
      have heq : (u / 4) / (Real.log 2 / Real.log z) = L / (4 * Real.log 2) := by
        rw [← hlzdef, huL]
        field_simp
        try ring
      rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log 2)]
      linarith [hL16]
  have hslack : K / (lo * Real.log z) ≤ 16 * K / L := by
    have hlo : u / 16 ≤ lo := by rw [hlodef]; exact le_max_left _ _
    have h1 : u / 16 * Real.log z ≤ lo * Real.log z :=
      mul_le_mul_of_nonneg_right hlo hlzp.le
    have h2 : L / 16 ≤ lo * Real.log z := by
      have huz : u / 16 * Real.log z = L / 16 := by
        rw [← hlzdef, huL]
        field_simp
        try ring
      linarith [h1]
    have := div_le_div_of_nonneg_left hK.le (by linarith : (0 : ℝ) < L / 16) h2
    have h3 : K / (L / 16) = 16 * K / L := by
      field_simp
      try ring
    linarith [this, h3.le, h3.ge]
  rw [← hlzdef] at hslack
  linarith [hm, hlog, hslack]

set_option maxHeartbeats 2000000 in
/-- Arithmetic endgame for the second stopping term, with deliberately generous
constants: every piece of the error budget is `O((1+K)^3 (log D)^(-1/3))`. -/
private theorem bound_total_loose326 {K lr dl de E Y0 Btot : ℝ}
    (hK : 0 < K) (hlr0 : 0 ≤ lr) (hlr1 : lr ≤ 1)
    (hdl0 : 0 ≤ dl) (hde0 : 0 ≤ de) (hE0 : 0 ≤ E) (hY0 : 0 ≤ Y0)
    (hdl : dl ≤ 40 * K * lr) (hde : de ≤ 12 * K * lr)
    (hE : E ≤ (Real.log 2 + 16 * K) * lr)
    (hY : Y0 ≤ Real.log 2 + 16 * K)
    (hB : Btot ≤ 64 * (1 + 32 * K) * (2 * K + 16 * K ^ 2) * lr)
    (hlog2 : 0 < Real.log 2) (hlog2le : Real.log 2 ≤ 1) :
    4 * dl + 4 * de + 4 * (dl * de) + (1 + dl) * (1 + de) * (2 * E) +
      8 * (1 + dl) * de * Y0 + Btot ≤ 1000000 * (1 + K) ^ 3 * lr := by
  have hK0 : (0 : ℝ) ≤ K := hK.le
  have hK1 : (0 : ℝ) ≤ 1 + K := by linarith
  have hcube : (0 : ℝ) ≤ (1 + K) ^ 3 := by positivity
  have hKc : K ≤ (1 + K) ^ 3 := by nlinarith [hK0, sq_nonneg K, mul_nonneg hK0 (sq_nonneg K)]
  have hK2c : K ^ 2 ≤ (1 + K) ^ 3 := by
    have h1 : (0 : ℝ) ≤ K := hK0
    nlinarith [hKc, sq_nonneg K, mul_nonneg h1 h1, hcube, hK1]
  have h1c : (1 : ℝ) ≤ (1 + K) ^ 3 := by nlinarith [hK0, sq_nonneg K, hcube]
  -- each piece is at most its constant times `(1+K)^3 lr`
  have hlrun : (1 + K) ^ 3 * lr ≤ (1 + K) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hlr1 hcube
    linarith [h]
  have b1 : 4 * dl ≤ 160 * (1 + K) ^ 3 * lr := by
    have h : 4 * dl ≤ 160 * K * lr := by nlinarith [hdl, hK0]
    have h2 : 160 * K * lr ≤ 160 * (1 + K) ^ 3 * lr := by
      have h5 : 160 * K ≤ 160 * (1 + K) ^ 3 := by nlinarith [hKc]
      exact mul_le_mul_of_nonneg_right h5 hlr0
    linarith
  have b2 : 4 * de ≤ 48 * (1 + K) ^ 3 * lr := by
    have h : 4 * de ≤ 48 * K * lr := by nlinarith [hde, hK0]
    have h2 : 48 * K * lr ≤ 48 * (1 + K) ^ 3 * lr := by
      have h5 : 48 * K ≤ 48 * (1 + K) ^ 3 := by nlinarith [hKc]
      exact mul_le_mul_of_nonneg_right h5 hlr0
    linarith
  have b3 : 4 * (dl * de) ≤ 1920 * (1 + K) ^ 3 * lr := by
    have hdlK : dl ≤ 40 * K * lr := hdl
    have hdeK : de ≤ 12 * K * lr := hde
    have h1 : dl * de ≤ (40 * K * lr) * (12 * K * lr) :=
      mul_le_mul hdlK hdeK hde0 (by positivity)
    have he1 : (40 * K * lr) * (12 * K * lr) = 480 * K ^ 2 * lr * lr := by ring
    have hlr2 : lr * lr ≤ lr := by nlinarith [hlr0, hlr1]
    have h2 : 480 * K ^ 2 * lr * lr ≤ 480 * K ^ 2 * lr := by
      have h0 : (0 : ℝ) ≤ 480 * K ^ 2 := by positivity
      nlinarith [hlr2, h0]
    have h3 : 480 * K ^ 2 * lr ≤ 480 * (1 + K) ^ 3 * lr := by
      have h5 : 480 * K ^ 2 ≤ 480 * (1 + K) ^ 3 := by nlinarith [hK2c]
      exact mul_le_mul_of_nonneg_right h5 hlr0
    have h4 : 4 * (dl * de) ≤ 1920 * (1 + K) ^ 3 * lr := by nlinarith [h1, he1.le, he1.ge, h2, h3]
    exact h4
  have b4 : (1 + dl) * (1 + de) * (2 * E) ≤ 18122 * (1 + K) ^ 3 * lr := by
    have hA : 1 + dl ≤ 41 * (1 + K) := by nlinarith [hdl, hlr1, hK0]
    have hB : 1 + de ≤ 13 * (1 + K) := by nlinarith [hde, hlr1, hK0]
    have hC : 2 * E ≤ 34 * (1 + K) * lr := by
      have h1 : 2 * E ≤ 2 * ((Real.log 2 + 16 * K) * lr) := by linarith [hE]
      have h4 : 2 * (Real.log 2 + 16 * K) ≤ 34 * (1 + K) := by nlinarith [hlog2le, hK0]
      have h5 : 2 * ((Real.log 2 + 16 * K) * lr) ≤ 34 * (1 + K) * lr := by
        rw [show 2 * ((Real.log 2 + 16 * K) * lr) = (2 * (Real.log 2 + 16 * K)) * lr by ring]
        exact mul_le_mul_of_nonneg_right h4 hlr0
      linarith [h1, h5]
    have hAB : (1 + dl) * (1 + de) ≤ (41 * (1 + K)) * (13 * (1 + K)) :=
      mul_le_mul hA hB (by linarith) (by linarith)
    have h0 : (0 : ℝ) ≤ 2 * E := by linarith
    have hstep : (1 + dl) * (1 + de) * (2 * E) ≤
        ((41 * (1 + K)) * (13 * (1 + K))) * (34 * (1 + K) * lr) :=
      mul_le_mul hAB hC h0 (by positivity)
    have he : (41 * (1 + K)) * (13 * (1 + K)) * (34 * (1 + K) * lr) =
        18122 * (1 + K) ^ 3 * lr := by ring
    linarith [hstep, he.le, he.ge]
  have b5 : 8 * (1 + dl) * de * Y0 ≤ 66912 * (1 + K) ^ 3 * lr := by
    have hA : 1 + dl ≤ 41 * (1 + K) := by nlinarith [hdl, hlr1, hK0]
    have hY2 : Y0 ≤ 17 * (1 + K) := by nlinarith [hY, hlog2le, hK0]
    have s1 : 8 * (1 + dl) ≤ 8 * (41 * (1 + K)) := by nlinarith [hA]
    have s2 : 8 * (1 + dl) * de ≤ (8 * (41 * (1 + K))) * (12 * K * lr) :=
      mul_le_mul s1 hde hde0 (by positivity)
    have s3 : 8 * (1 + dl) * de * Y0 ≤
        ((8 * (41 * (1 + K))) * (12 * K * lr)) * (17 * (1 + K)) := by
      have h0 : (0 : ℝ) ≤ (8 * (41 * (1 + K))) * (12 * K * lr) := by positivity
      exact (mul_le_mul_of_nonneg_right s2 hY0).trans (mul_le_mul_of_nonneg_left hY2 h0)
    have he : ((8 * (41 * (1 + K))) * (12 * K * lr)) * (17 * (1 + K)) =
        66912 * K * (1 + K) ^ 2 * lr := by ring
    have h2 : 66912 * K * (1 + K) ^ 2 * lr ≤ 66912 * (1 + K) ^ 3 * lr := by
      have h0 : (0 : ℝ) ≤ 66912 * (1 + K) ^ 2 * lr := by positivity
      nlinarith [hK1]
    linarith [s3, he.le, he.ge, h2]
  have b6 : Btot ≤ 38016 * (1 + K) ^ 3 * lr := by
    have hA : 1 + 32 * K ≤ 33 * (1 + K) := by nlinarith [hK0]
    have hC : 2 * K + 16 * K ^ 2 ≤ 18 * K * (1 + K) := by
      nlinarith [hK0, sq_nonneg K, mul_nonneg hK0 hK0]
    have hA0' : (0 : ℝ) ≤ 1 + 32 * K := by positivity
    have hC0' : (0 : ℝ) ≤ 2 * K + 16 * K ^ 2 := by positivity
    have s1 : 64 * (1 + 32 * K) ≤ 64 * (33 * (1 + K)) := by nlinarith [hA]
    have s2 : 64 * (1 + 32 * K) * (2 * K + 16 * K ^ 2) ≤
        64 * (33 * (1 + K)) * (18 * K * (1 + K)) :=
      mul_le_mul s1 hC hC0' (by positivity)
    have s3 : 64 * (1 + 32 * K) * (2 * K + 16 * K ^ 2) * lr ≤
        64 * (33 * (1 + K)) * (18 * K * (1 + K)) * lr :=
      mul_le_mul_of_nonneg_right s2 hlr0
    have he : 64 * (33 * (1 + K)) * (18 * K * (1 + K)) * lr =
        38016 * K * (1 + K) ^ 2 * lr := by ring
    have h2 : 38016 * K * (1 + K) ^ 2 * lr ≤ 38016 * (1 + K) ^ 3 * lr := by
      have h0 : (0 : ℝ) ≤ 38016 * (1 + K) ^ 2 * lr := by positivity
      nlinarith [hK1]
    linarith [s3, he.le, he.ge, h2]
  have htot : 4 * dl + 4 * de + 4 * (dl * de) + (1 + dl) * (1 + de) * (2 * E) +
      8 * (1 + dl) * de * Y0 + Btot ≤
      (160 + 48 + 1920 + 18122 + 66912 + 38016) * (1 + K) ^ 3 * lr := by
    nlinarith [b1, b2, b3, b4, b5, b6]
  have hconst : (160 + 48 + 1920 + 18122 + 66912 + 38016 : ℝ) ≤ 1000000 := by norm_num
  have hfin : (160 + 48 + 1920 + 18122 + 66912 + 38016) * (1 + K) ^ 3 * lr ≤
      1000000 * (1 + K) ^ 3 * lr := by
    have h0 : (0:ℝ) ≤ (1 + K) ^ 3 * lr := by positivity
    nlinarith [hconst, h0]
  linarith [htot, hfin]

set_option maxHeartbeats 4000000 in
/-- The normalised second stopping term is bounded by the continuous second
coefficient plus `1000000 (1+K)^3 (log D)^(-1/3)`.  This is the analytic content
of `jr_lower_second326`, with the constant made explicit. -/
private theorem second_bound_main326 (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ),
      2 ≤ z → max 8 (Real.exp (K + 2)) < z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      rosserSecondBoundary326 s z D / (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤
        rosserSecondModel326 (Real.log D / Real.log z) + C * Real.log D ^ (-(1 / 3 : ℝ)) := by
  classical
  refine ⟨1000000 * (1 + K) ^ 3, by positivity, ?_⟩
  intro s z D hz2 hzB hzD2 hz4 hP hden
  have hz8 : 8 ≤ z := le_trans (le_max_left (8 : ℝ) (Real.exp (K + 2))) hzB.le
  have hz1 : 1 < z := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity : (0 : ℝ) < z ^ 2) hzD2
  have hDV : 2 ≤ D := by nlinarith
  have hlog2gt : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  set lz := Real.log z with hlzdef
  have hlz : 0 < lz := by rw [hlzdef]; exact Real.log_pos hz1
  set L := Real.log D with hLdef
  have hL : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h3 := Real.exp_one_lt_three
    have he : Real.exp 1 ≤ D := by nlinarith
    have hh := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at hh
  have hL2 : 2 * lz ≤ L := by
    rw [hlzdef, hLdef]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < z ^ 2) hzD2
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  set u := L / lz with hudef
  have huL : L = u * lz := by rw [hudef]; field_simp
  have hu2 : 2 ≤ u := by
    rw [hudef, le_div_iff₀ hlz]
    linarith
  have hu4 : u ≤ 4 := by
    rw [hudef, div_le_iff₀ hlz, hLdef, hlzdef]
    have h := Real.log_le_log hDpos hz4
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hu1 : 0 < u - 1 := by linarith
  have hzK : K + 2 < lz := by
    rw [hlzdef]
    have h2 : Real.exp (K + 2) < z :=
      lt_of_le_of_lt (le_max_right (8 : ℝ) (Real.exp (K + 2))) hzB
    have h := Real.log_lt_log (Real.exp_pos (K + 2)) h2
    rwa [Real.log_exp] at h
  have hKL : K / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]
    nlinarith [hzK, hL2]
  by_cases hu4eq : u = 4
  · -- the endpoint `D = z^4`: the stopping term vanishes
    have hDeq : D = z ^ 4 := by
      have h1 : Real.log D = Real.log (z ^ 4) := by
        rw [Real.log_pow]
        push_cast
        rw [← hLdef, ← hlzdef, ← hu4eq]
        exact huL
      have h2 := congrArg Real.exp h1
      rwa [Real.exp_log hDpos, Real.exp_log (by positivity)] at h2
    have hzero : rosserSecondBoundary326 s z D = 0 :=
      rosserSecondBoundary_eq_zero326 s z D hz2 (le_of_eq hDeq.symm)
    have hmodel : rosserSecondModel326 u = 0 := by
      rw [hu4eq]; exact rosserSecondModel_four326
    rw [hzero, zero_div, hmodel]
    have hrp : (0 : ℝ) ≤ 1000000 * (1 + K) ^ 3 * L ^ (-(1 / 3 : ℝ)) :=
      mul_nonneg (by positivity) (Real.rpow_pos_of_pos hL _).le
    linarith
  · have hu4' : u < 4 := lt_of_le_of_ne hu4 hu4eq
    -- the weight of a single prime
    set S : ℕ → ℝ := fun p => s.nu p *
      ((1 / (Real.log (p : ℝ) / lz)) * (1 + 4 * K / ((Real.log (p : ℝ) / lz) * L)) *
        max 0 (3 * (Real.log (p : ℝ) / lz) / (u - Real.log (p : ℝ) / lz) *
          (1 + 12 * K / ((u - Real.log (p : ℝ) / lz) * L)) - 1)) with hSdef
    have hS_eq : ∀ p : ℕ, S p = s.nu p *
        ((1 / (Real.log (p : ℝ) / lz)) * (1 + 4 * K / ((Real.log (p : ℝ) / lz) * L)) *
          max 0 (3 * (Real.log (p : ℝ) / lz) / (u - Real.log (p : ℝ) / lz) *
            (1 + 12 * K / ((u - Real.log (p : ℝ) / lz) * L)) - 1)) := fun p => rfl
    -- step 1: the normalised second stopping term is such a sum
    have hstep1 : rosserSecondBoundary326 s z D /
        (∏ q ∈ s.prodPrimes.primeFactors, (1 - s.nu q)) ≤
        ∑ p ∈ s.prodPrimes.primeFactors, S p := by
      have h := second_sum_le_G326 s K z D hK hden hz8 hzD2 hz4 hP
      rw [← hlzdef, ← hLdef, ← hudef] at h
      refine h.trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro p _
      rw [hS_eq p]
    -- band A: `log p/log z ≤ u/16`, the weight vanishes
    have hA0 : ∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => Real.log (p : ℝ) / lz ≤ u / 16), S p = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hmem.1
      have htp0 : 0 < Real.log (p : ℝ) / lz :=
        div_pos (Real.log_pos (by exact_mod_cast hpp.one_lt)) hlz
      have hz0 : 3 * (Real.log (p : ℝ) / lz) / (u - Real.log (p : ℝ) / lz) *
          (1 + 12 * K / ((u - Real.log (p : ℝ) / lz) * L)) - 1 ≤ 0 :=
        mid_weight_zero326 hK hL hu2 hu4 hKL htp0 hmem.2
      rw [hS_eq p, max_eq_left hz0]
      ring
    -- band B: `u/16 ≤ log p/log z < u/4`
    have hBband : ∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4), S p ≤
        64 * (K / L) * (1 + 32 * K / L) * (Real.log 4 + 16 * K / L) := by
      have hsub : (s.prodPrimes.primeFactors.filter
            (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
            (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4) ⊆
          s.prodPrimes.primeFactors.filter
            (fun p : ℕ => u / 16 ≤ Real.log (p : ℝ) / lz ∧
              Real.log (p : ℝ) / lz < u / 4) := by
        intro p hp
        have h1 := (Finset.mem_filter.mp hp).1
        have h2 := (Finset.mem_filter.mp hp).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h1).1,
          le_of_lt (not_le.mp (Finset.mem_filter.mp h1).2), h2⟩
      have hpt : ∀ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4),
          S p ≤ (64 * (K / L) * (1 + 32 * K / L)) * s.nu p := by
        intro p hp
        have hmem := Finset.mem_filter.mp hp
        have hmemPf := Finset.mem_filter.mp hmem.1
        have hpp := Nat.prime_of_mem_primeFactors hmemPf.1
        have ht16 : u / 16 ≤ Real.log (p : ℝ) / lz := le_of_lt (not_le.mp hmemPf.2)
        have hw := mid_weight_le326 hK hL hu2 hu4 hKL ht16 hmem.2
        have hnu : 0 ≤ s.nu p := (s.nu_pos_of_prime p hpp
          (Nat.dvd_of_mem_primeFactors hmemPf.1)).le
        rw [hS_eq p]
        refine (mul_le_mul_of_nonneg_left hw hnu).trans_eq ?_
        ring
      have hmass : ∑ p ∈ (s.prodPrimes.primeFactors.filter
            (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
            (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4), s.nu p ≤
          Real.log 4 + 16 * K / L :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
          (s.nu_pos_of_dvd_prodPrimes
            (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le)).trans
          (mid_mass326 s K z D u lz L hK hden hz8 hzD2 hlzdef hLdef huL hu2 hu4' hP)
      calc ∑ p ∈ (s.prodPrimes.primeFactors.filter
            (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
            (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4), S p
          ≤ ∑ p ∈ (s.prodPrimes.primeFactors.filter
            (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
            (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4),
            (64 * (K / L) * (1 + 32 * K / L)) * s.nu p := Finset.sum_le_sum hpt
        _ = 64 * (K / L) * (1 + 32 * K / L) *
            ∑ p ∈ (s.prodPrimes.primeFactors.filter
              (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
              (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4), s.nu p := by
            rw [Finset.mul_sum]
        _ ≤ 64 * (K / L) * (1 + 32 * K / L) * (Real.log 4 + 16 * K / L) := by
            apply mul_le_mul_of_nonneg_left hmass
            have h0 : (0 : ℝ) ≤ K / L := div_nonneg hK.le hL.le
            have h1 : (0 : ℝ) ≤ 1 + 32 * K / L := by positivity
            positivity
    -- band C: `u/4 ≤ log p/log z`, the main band
    have hCband : ∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz < u / 4), S p ≤
        (1 + 4 * K / (u / 4 * L)) *
          ((1 + 12 * K / ((u - 1) * L)) *
              (rosserSecondModel326 u +
                2 * (Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) +
                  (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L))) +
            (12 * K / ((u - 1) * L)) *
              (8 * (Real.log (1 / (u / 4)) + 4 * K / (u / 4 * L)))) :=
      region_C_le326 (s := s) (K := K) (z := z) (D := D) (u := u) (lz := lz) (L := L)
        hK hden hz8 hDV hL1 hlzdef hLdef huL hu2 hu4' hP
    -- the arithmetic endgame
    set dl := 4 * K / (u / 4 * L) with hdl_def
    set de := 12 * K / ((u - 1) * L) with hde_def
    set Er := Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) +
      (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L) with hEr_def
    set Y0 := Real.log (1 / (u / 4)) + 4 * K / (u / 4 * L) with hY0_def
    set Btot := 64 * (K / L) * (1 + 32 * K / L) * (Real.log 4 + 16 * K / L) with hB_def
    have hBband' : ∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4), S p ≤ Btot := by
      rw [hB_def]; exact hBband
    have hCband' : ∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz < u / 4), S p ≤
        (1 + dl) * ((1 + de) * (rosserSecondModel326 u + 2 * Er) + de * (8 * Y0)) := by
      rw [hdl_def, hde_def, hEr_def, hY0_def]; exact hCband
    have hdl0 : 0 ≤ dl := by rw [hdl_def]; positivity
    have hde0 : 0 ≤ de := by rw [hde_def]; positivity
    have hY0nn : 0 ≤ Y0 := by
      rw [hY0_def]
      have h1 := log_inv_four_div_nonneg326 hu2 hu4
      have h2 : 0 ≤ 4 * K / (u / 4 * L) := by positivity
      linarith
    have hEr0 : 0 ≤ Er := by
      rw [hEr_def]
      have h1 := log_inv_four_div_nonneg326 hu2 hu4
      have hn : (0 : ℝ) ≤ (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) := by positivity
      have h2 : 0 ≤ Real.log (1 / (u / 4)) /
          (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) := div_nonneg h1 hn
      have h3 : 0 ≤ (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L) :=
        div_nonneg (mul_nonneg hn (by positivity)) (by positivity)
      linarith
    have hlr0 : (0 : ℝ) ≤ L ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos hL _).le
    have hlr1 : L ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num : -(1 / 3 : ℝ) ≤ 0)
    have hinvL : L⁻¹ ≤ L ^ (-(1 / 3 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (-(1 : ℝ)) ≤ -(1 / 3 : ℝ))
      rwa [Real.rpow_neg_one] at h
    have hdl : dl ≤ 40 * K * L ^ (-(1 / 3 : ℝ)) := by
      have h1 : dl = 16 * K / (u * L) := by
        rw [hdl_def]
        field_simp
        ring
      have h2 : 16 * K / (u * L) ≤ 8 * K * L⁻¹ := by
        have h16 : 16 * K / (u * L) ≤ 16 * K / (2 * L) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [hL, hu2]
        have he : 16 * K / (2 * L) = 8 * K * L⁻¹ := by
          field_simp
          ring
        linarith [h16, he.le, he.ge]
      have h3 : 8 * K * L⁻¹ ≤ 8 * K * L ^ (-(1 / 3 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hinvL (by positivity : (0 : ℝ) ≤ 8 * K)
        linarith [this]
      have h5 : 8 * K * L ^ (-(1 / 3 : ℝ)) ≤ 40 * K * L ^ (-(1 / 3 : ℝ)) := by
        nlinarith [mul_nonneg hK.le hlr0]
      linarith [h1, h2, h3, h5]
    have hde : de ≤ 12 * K * L ^ (-(1 / 3 : ℝ)) := by
      have h2 : 12 * K / ((u - 1) * L) ≤ 12 * K * L⁻¹ := by
        have h12 : 12 * K / ((u - 1) * L) ≤ 12 * K / (1 * L) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [hL, hu1]
        have he : 12 * K / (1 * L) = 12 * K * L⁻¹ := by
          field_simp
          try ring
        linarith [h12, he.le, he.ge]
      have h3 : 12 * K * L⁻¹ ≤ 12 * K * L ^ (-(1 / 3 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hinvL (by positivity : (0 : ℝ) ≤ 12 * K)
        linarith [this]
      rw [hde_def]
      exact h2.trans h3
    have hceil : L ^ ((1 : ℝ) / 3) ≤ (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) := Nat.le_ceil _
    have hL13 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 3) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL1
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
      simpa using h
    have hceil1 : (1 : ℝ) ≤ (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) := by linarith [hL13, hceil]
    have hceil2 : (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) ≤ 2 * L ^ ((1 : ℝ) / 3) := by
      have h3 := Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hL ((1 : ℝ) / 3)).le
      have h4 : L ^ ((1 : ℝ) / 3) + 1 ≤ 2 * L ^ ((1 : ℝ) / 3) := by linarith [hL13]
      linarith [h3, h4]
    have hE : Er ≤ (Real.log 2 + 16 * K) * L ^ (-(1 / 3 : ℝ)) := by
      rw [hEr_def]
      have hfirst : Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) ≤
          Real.log 2 * L ^ (-(1 / 3 : ℝ)) := by
        have hinv : (1 : ℝ) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) ≤ L ^ (-(1 / 3 : ℝ)) := by
          have hrw : L ^ (-(1 / 3 : ℝ)) = (L ^ ((1 : ℝ) / 3))⁻¹ :=
            Real.rpow_neg hL.le (1 / 3)
          rw [hrw, ← one_div]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _) hceil
        have h1 := log_inv_four_div_le326 hu2 hu4
        have h2 := log_inv_four_div_nonneg326 hu2 hu4
        calc Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ)
            = Real.log (1 / (u / 4)) * (1 / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ)) := by ring
          _ ≤ Real.log 2 * L ^ (-(1 / 3 : ℝ)) :=
              mul_le_mul h1 hinv (by positivity) (by linarith)
      have hsecond : (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L) ≤
          16 * K * L ^ (-(1 / 3 : ℝ)) := by
        have hstep : (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L) ≤
            (2 * L ^ ((1 : ℝ) / 3)) * (4 * K) / (u / 4 * L) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hceil2 (by positivity)
        have hstep2 : (2 * L ^ ((1 : ℝ) / 3)) * (4 * K) / (u / 4 * L) ≤
            16 * K * L ^ (-(1 / 3 : ℝ)) := by
          have hpos : (0 : ℝ) < u / 4 := by linarith
          have h23 : L ^ (-(2 / 3 : ℝ)) ≤ L ^ (-(1 / 3 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          have hsplit : (2 * L ^ ((1 : ℝ) / 3)) * (4 * K) / (u / 4 * L) =
              8 * K * (L ^ ((1 : ℝ) / 3) / L) * (1 / (u / 4)) := by
            field_simp
            ring
          have hrw2 : L ^ ((1 : ℝ) / 3) / L = L ^ (-(2 / 3 : ℝ)) := by
            have h2 : L ^ ((1 : ℝ) / 3 - 1) = L ^ ((1 : ℝ) / 3) / L := by
              have h3 := Real.rpow_sub hL ((1 : ℝ) / 3) 1
              rwa [Real.rpow_one] at h3
            rw [← h2]
            norm_num
          rw [hsplit, hrw2]
          have hinv4 : (1 : ℝ) / (u / 4) ≤ 2 := inv_four_div326 hu2 hu4
          have hnn : (0 : ℝ) ≤ 8 * K * L ^ (-(2 / 3 : ℝ)) := by positivity
          have hstep3 : 8 * K * L ^ (-(2 / 3 : ℝ)) * (1 / (u / 4)) ≤
              8 * K * L ^ (-(1 / 3 : ℝ)) * 2 := by
            have hA' : 8 * K * L ^ (-(2 / 3 : ℝ)) * (1 / (u / 4)) ≤
                8 * K * L ^ (-(2 / 3 : ℝ)) * 2 :=
              mul_le_mul_of_nonneg_left hinv4 hnn
            have hB' : 8 * K * L ^ (-(2 / 3 : ℝ)) * 2 ≤
                8 * K * L ^ (-(1 / 3 : ℝ)) * 2 := by
              have h16 : (0 : ℝ) ≤ 16 * K := by positivity
              have hm := mul_le_mul_of_nonneg_left h23 h16
              calc 8 * K * L ^ (-(2 / 3 : ℝ)) * 2 = (16 * K) * L ^ (-(2 / 3 : ℝ)) := by ring
                _ ≤ (16 * K) * L ^ (-(1 / 3 : ℝ)) := hm
                _ = 8 * K * L ^ (-(1 / 3 : ℝ)) * 2 := by ring
            linarith [hA', hB']
          calc 8 * K * L ^ (-(2 / 3 : ℝ)) * (1 / (u / 4))
              ≤ 8 * K * L ^ (-(1 / 3 : ℝ)) * 2 := hstep3
            _ = 16 * K * L ^ (-(1 / 3 : ℝ)) := by ring
        exact hstep.trans hstep2
      have hsum := add_le_add hfirst hsecond
      calc Real.log (1 / (u / 4)) / (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) +
            (Nat.ceil (L ^ ((1 : ℝ) / 3)) : ℝ) * (4 * K) / (u / 4 * L)
          ≤ Real.log 2 * L ^ (-(1 / 3 : ℝ)) + 16 * K * L ^ (-(1 / 3 : ℝ)) := hsum
        _ = (Real.log 2 + 16 * K) * L ^ (-(1 / 3 : ℝ)) := by ring
    have hY : Y0 ≤ Real.log 2 + 16 * K := by
      rw [hY0_def]
      have h1 := log_inv_four_div_le326 hu2 hu4
      have h2 : 4 * K / (u / 4 * L) ≤ 16 * K := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < u / 4 * L)]
        have hge : (1 : ℝ) ≤ u / 4 * L := by nlinarith [hu2, hL1]
        have := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ 16 * K)
        nlinarith [this]
      linarith
    have hB : Btot ≤ 64 * (1 + 32 * K) * (2 * K + 16 * K ^ 2) * L ^ (-(1 / 3 : ℝ)) := by
      rw [hB_def]
      have h1 : K / L ≤ K * L ^ (-(1 / 3 : ℝ)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinvL hK.le
      have h2 : 1 + 32 * K / L ≤ 1 + 32 * K := by
        have h32 : 32 * K / L ≤ 32 * K := by
          rw [div_le_iff₀ hL]
          have := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 32 * K)
          nlinarith [this]
        linarith
      have h3 : Real.log 4 + 16 * K / L ≤ 2 + 16 * K := by
        have hlog4 : Real.log 4 ≤ 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          push_cast
          nlinarith [hlog2le]
        have h4 : 16 * K / L ≤ 16 * K := by
          rw [div_le_iff₀ hL]
          have := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 16 * K)
          nlinarith [this]
        linarith
      have hA : (0 : ℝ) ≤ 1 + 32 * K / L := by positivity
      have hA2 : (0 : ℝ) ≤ 1 + 32 * K := by positivity
      have hC : (0 : ℝ) ≤ Real.log 4 + 16 * K / L := by
        have h5 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
        have h6 : (0 : ℝ) ≤ 16 * K / L := by positivity
        linarith
      have hC2 : (0 : ℝ) ≤ 2 + 16 * K := by positivity
      have hlr := hlr0
      have s1 : 64 * (K / L) ≤ 64 * (K * L ^ (-(1 / 3 : ℝ))) := by nlinarith [h1, hlr]
      have s2 : 64 * (K / L) * (1 + 32 * K / L) ≤
          64 * (K * L ^ (-(1 / 3 : ℝ))) * (1 + 32 * K / L) :=
        mul_le_mul_of_nonneg_right s1 hA
      have s3 : 64 * (K / L) * (1 + 32 * K / L) ≤
          64 * (K * L ^ (-(1 / 3 : ℝ))) * (1 + 32 * K) := by
        refine s2.trans ?_
        apply mul_le_mul_of_nonneg_left h2
        have h0 : (0 : ℝ) ≤ K * L ^ (-(1 / 3 : ℝ)) := mul_nonneg hK.le hlr0
        positivity
      have s4 : 64 * (K / L) * (1 + 32 * K / L) * (Real.log 4 + 16 * K / L) ≤
          64 * (K * L ^ (-(1 / 3 : ℝ))) * (1 + 32 * K) * (Real.log 4 + 16 * K / L) :=
        mul_le_mul_of_nonneg_right s3 hC
      have s5 : 64 * (K * L ^ (-(1 / 3 : ℝ))) * (1 + 32 * K) * (Real.log 4 + 16 * K / L) ≤
          64 * (K * L ^ (-(1 / 3 : ℝ))) * (1 + 32 * K) * (2 + 16 * K) := by
        apply mul_le_mul_of_nonneg_left h3
        have h0 : (0 : ℝ) ≤ K * L ^ (-(1 / 3 : ℝ)) := mul_nonneg hK.le hlr0
        positivity
      have he : 64 * (K * L ^ (-(1 / 3 : ℝ))) * (1 + 32 * K) * (2 + 16 * K) =
          64 * (1 + 32 * K) * (2 * K + 16 * K ^ 2) * L ^ (-(1 / 3 : ℝ)) := by ring
      calc 64 * (K / L) * (1 + 32 * K / L) * (Real.log 4 + 16 * K / L)
          ≤ 64 * (K * L ^ (-(1 / 3 : ℝ))) * (1 + 32 * K) * (2 + 16 * K) := s4.trans s5
        _ = 64 * (1 + 32 * K) * (2 * K + 16 * K ^ 2) * L ^ (-(1 / 3 : ℝ)) := he
    have hstep2 : 4 * dl + 4 * de + 4 * (dl * de) + (1 + dl) * (1 + de) * (2 * Er) +
        8 * (1 + dl) * de * Y0 + Btot ≤
        1000000 * (1 + K) ^ 3 * L ^ (-(1 / 3 : ℝ)) :=
      bound_total_loose326 (K := K) (lr := L ^ (-(1 / 3 : ℝ))) (dl := dl) (de := de)
        (E := Er) (Y0 := Y0) (Btot := Btot)
        hK hlr0 hlr1 hdl0 hde0 hEr0 hY0nn hdl hde hE hY hB
        (Real.log_pos (by norm_num)) hlog2le
    -- insert the two band bounds and expand
    have hmodel4 : rosserSecondModel326 u ≤ 4 := second_model_le_four326 hu2 hu4
    have hexp : (1 + dl) * ((1 + de) * (rosserSecondModel326 u + 2 * Er) + de * (8 * Y0)) =
        (1 + dl) * (1 + de) * rosserSecondModel326 u +
          ((1 + dl) * (1 + de) * (2 * Er) + (1 + dl) * de * (8 * Y0)) := by ring
    have hexp2 : (1 + dl) * (1 + de) * rosserSecondModel326 u =
        rosserSecondModel326 u + (dl + de + dl * de) * rosserSecondModel326 u := by ring
    have hcoef0 : (0 : ℝ) ≤ dl + de + dl * de := by positivity
    have hquad : (dl + de + dl * de) * rosserSecondModel326 u ≤
        4 * dl + 4 * de + 4 * (dl * de) := by
      have h := mul_le_mul_of_nonneg_left hmodel4 hcoef0
      nlinarith [h]
    have hband : ∑ p ∈ s.prodPrimes.primeFactors.filter
          (fun p : ℕ => Real.log (p : ℝ) / lz ≤ u / 16), S p +
        ((∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4), S p) +
        (∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz < u / 4), S p)) ≤
        Btot + (1 + dl) * ((1 + de) * (rosserSecondModel326 u + 2 * Er) + de * (8 * Y0)) := by
      have h1 : (∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => Real.log (p : ℝ) / lz < u / 4), S p) ≤ Btot := hBband'
      have h2 : (∑ p ∈ (s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16)).filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz < u / 4), S p) ≤
          (1 + dl) * ((1 + de) * (rosserSecondModel326 u + 2 * Er) + de * (8 * Y0)) := hCband'
      linarith [hA0, h1, h2]
    have hbr : Btot + ((1 + dl) * ((1 + de) * (rosserSecondModel326 u + 2 * Er) + de * (8 * Y0))) ≤
        rosserSecondModel326 u + (4 * dl + 4 * de + 4 * (dl * de)) +
          ((1 + dl) * (1 + de) * (2 * Er) + (1 + dl) * de * (8 * Y0)) + Btot := by
      linarith [hexp, hexp2, hquad]
    have hbud : 4 * dl + 4 * de + 4 * (dl * de) + (1 + dl) * (1 + de) * (2 * Er) +
        (1 + dl) * de * (8 * Y0) + Btot =
        4 * dl + 4 * de + 4 * (dl * de) + (1 + dl) * (1 + de) * (2 * Er) +
          8 * (1 + dl) * de * Y0 + Btot := by ring
    have hfin : ∑ p ∈ s.prodPrimes.primeFactors, S p ≤
        rosserSecondModel326 u + 1000000 * (1 + K) ^ 3 * L ^ (-(1 / 3 : ℝ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := s.prodPrimes.primeFactors)
        (p := fun p : ℕ => Real.log (p : ℝ) / lz ≤ u / 16) (f := S)]
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := s.prodPrimes.primeFactors.filter
          (fun p : ℕ => ¬ Real.log (p : ℝ) / lz ≤ u / 16))
        (p := fun p : ℕ => Real.log (p : ℝ) / lz < u / 4) (f := S)]
      linarith [hband, hbr, hstep2, hbud]
    exact hstep1.trans hfin

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
        rosserSecondModel326 (log D / log z) + C * log D ^ (-(1 / 3 : ℝ)) := second_bound_main326 K hK

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
