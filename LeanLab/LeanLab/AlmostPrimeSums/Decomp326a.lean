import LeanLab.AlmostPrimeSums.RosserBounded
import LeanLab.AlmostPrimeSums.RosserFirst

/-!
AI wrote this Lean code for CODEX task326. Goldbach is open.
This supply unit separates bounded cutoffs from the two explicit upper
sieve function ranges. The original declarations stay in Decomp1527b.
Sources: Nathanson, Additive Number Theory, The Classical Bases,
pp. 242 to 244 equations 9.10 and 9.11 and p. 256 Theorem 9.6.
Heath Brown, Lectures on sieves, pp. 34 to 35,
https://arxiv.org/abs/math/0209360.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b
open Finset Real BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a

/-- The sieve product with a moving internal cutoff. Nathanson p. 241,
the definition of V used in equation 9.9. -/
noncomputable def rosserPrefixProduct326 (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (1 - s.nu p)

/-- The first stopping boundary inside a moving prime prefix. Nathanson
p. 241 equation 9.9 and p. 245 equation 9.13. Unlike the existing full
boundary, this expression excludes primes at or above its upper cutoff. -/
noncomputable def rosserIntervalBoundary326 (s : BoundingSieve) (w z : ℝ) : ℝ :=
  ∑ p ∈ s.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
    s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)

/-- The internal boundary telescopes to the difference of prefix products.
Nathanson pp. 241 to 242 equation 9.9. This finite identity requires no
density estimate and works with primes above the upper cutoff present. -/
theorem rosserIntervalBoundary_eq_sub326 (s : BoundingSieve) (w z : ℝ) (hwz : w ≤ z) :
    rosserIntervalBoundary326 s w z =
      rosserPrefixProduct326 s w - rosserPrefixProduct326 s z := by
  classical
  have hdiff : rosserIntervalBoundary326 s w z =
      rosserFirstBoundary s w - rosserFirstBoundary s z := by
    unfold rosserIntervalBoundary326 rosserFirstBoundary
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hw : w ≤ (p : ℝ)
    · by_cases hz : z ≤ (p : ℝ)
      · simp [hw, not_lt.mpr hz, hz]
      · simp [hw, lt_of_not_ge hz, hz]
    · have hz : ¬z ≤ (p : ℝ) := by linarith
      simp [hw, hz]
  rw [hdiff, rosserFirstBoundary_eq_product_sub, rosserFirstBoundary_eq_product_sub]
  unfold rosserPrefixProduct326
  ring

/-- If the internal lower cutoff exceeds the upper one, the stopping
boundary is zero. Derived empty interval case of Nathanson equation 9.9. -/
theorem rosserIntervalBoundary_eq_zero326 (s : BoundingSieve) (w z : ℝ) (hzw : z ≤ w) :
    rosserIntervalBoundary326 s w z = 0 := by
  classical
  unfold rosserIntervalBoundary326
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨_, hpw, hpz⟩ := Finset.mem_filter.mp hp
  exfalso
  linarith

/-- The product difference formula for an internal boundary includes the
empty interval case by taking the minimum cutoff. Derived endpoint form
of Nathanson pp. 241 to 242 equation 9.9. -/
theorem rosserIntervalBoundary_eq_min326 (s : BoundingSieve) (w z : ℝ) :
    rosserIntervalBoundary326 s w z =
      rosserPrefixProduct326 s (min w z) - rosserPrefixProduct326 s z := by
  by_cases hwz : w ≤ z
  · rw [min_eq_left hwz]
    exact rosserIntervalBoundary_eq_sub326 s w z hwz
  · rw [min_eq_right (le_of_not_ge hwz), sub_self]
    exact rosserIntervalBoundary_eq_zero326 s w z (le_of_not_ge hwz)

/-- The moving prefix stopping boundary is nonnegative. Nathanson p. 242,
the positivity of T one in Lemma 9.3. -/
theorem rosserIntervalBoundary_nonneg326 (s : BoundingSieve) (w z : ℝ) :
    0 ≤ rosserIntervalBoundary326 s w z := by
  apply Finset.sum_nonneg
  intro p hp
  have hpP := (Finset.mem_filter.mp hp).1
  apply mul_nonneg (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
    (Nat.dvd_of_mem_primeFactors hpP)).le
  exact Finset.prod_nonneg fun q hq =>
    (sub_pos.mpr (s.nu_lt_one_of_prime q
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))).le

/-- The moving boundary normalized by the upper prefix product is the
inverse interval product minus one. Nathanson pp. 241 to 242 equation 9.9,
combined with the finite product factorization defining V. -/
theorem rosserIntervalBoundary_eq_relative326 (s : BoundingSieve) (w z : ℝ)
    (hwz : w ≤ z) :
    rosserIntervalBoundary326 s w z = rosserPrefixProduct326 s z *
      ((∏ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - s.nu p)⁻¹) - 1) := by
  classical
  let P := s.prodPrimes.primeFactors
  let Q := P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hlo : (P.filter (fun p : ℕ => (p : ℝ) < z)).filter
      (fun p : ℕ => (p : ℝ) < w) = P.filter (fun p : ℕ => (p : ℝ) < w) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans_le hwz⟩, h.2⟩
  have hhi : (P.filter (fun p : ℕ => (p : ℝ) < z)).filter
      (fun p : ℕ => ¬(p : ℝ) < w) = Q := by
    ext p
    simp only [Q, Finset.mem_filter, not_lt]
    tauto
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (P.filter (fun p : ℕ => (p : ℝ) < z)) (fun p : ℕ => (p : ℝ) < w)
    (fun p => 1 - s.nu p)
  rw [hlo, hhi] at hsplit
  have hQ : (∏ p ∈ Q, (1 - s.nu p)) ≠ 0 :=
    (Finset.prod_pos fun p hp => sub_pos.mpr
      (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
        (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1))).ne'
  rw [rosserIntervalBoundary_eq_sub326 s w z hwz]
  unfold rosserPrefixProduct326
  change _ = _ * ((∏ p ∈ Q, (1 - s.nu p)⁻¹) - 1)
  rw [Finset.prod_inv_distrib, ← hsplit]
  field_simp [hQ]
  dsimp [P]
  ring

/-- The density condition bounds a boundary within any moving prime
prefix. It does not require every prime of P below the upper cutoff.
Derived local input for Nathanson p. 245 equation 9.14 and BJS p. 11. -/
theorem rosserIntervalBoundary_le_density326 (s : BoundingSieve) (K w z : ℝ)
    (hden : LinearDensity s K) (hw : 2 ≤ w) (hwz : w < z) :
    rosserIntervalBoundary326 s w z ≤ rosserPrefixProduct326 s z *
      (log z / log w * (1 + K / log w) - 1) := by
  rw [rosserIntervalBoundary_eq_relative326 s w z hwz.le]
  apply mul_le_mul_of_nonneg_left (sub_le_sub_right (hden w z hw hwz) 1)
  exact Finset.prod_nonneg fun p hp =>
    (sub_pos.mpr (s.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1))).le

/-- A weighted internal boundary integral is a finite sum of primitive
integrals at the stopping primes. This is the finite partial summation
step behind Nathanson pp. 251 to 252 Lemma 9.8. Only interval
integrability of the weight is needed. No density estimate is used. -/
theorem rosser_boundary_integral326 (s : BoundingSieve) (a b : ℝ) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ t in a..b, f t * rosserIntervalBoundary326 s t b) =
      ∑ p ∈ s.prodPrimes.primeFactors.filter
          (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b),
        (s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)) *
          ∫ t in a..(p : ℝ), f t := by
  classical
  let S := s.prodPrimes.primeFactors.filter
    (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b)
  let m : ℕ → ℝ := fun p =>
    s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)
  have hboundary : ∀ t ∈ Set.Icc a b, rosserIntervalBoundary326 s t b =
      ∑ p ∈ S, if t ≤ (p : ℝ) then m p else 0 := by
    intro t ht
    unfold rosserIntervalBoundary326 S
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpb : (p : ℝ) < b
    · by_cases htp : t ≤ (p : ℝ)
      · have hap : a ≤ (p : ℝ) := ht.1.trans htp
        simp [hpb, htp, hap, m]
      · simp [hpb, htp]
    · simp [hpb]
  have hpoint : ∀ t ∈ Set.Icc a b,
      f t * rosserIntervalBoundary326 s t b =
        ∑ p ∈ S, m p * Set.indicator {t : ℝ | t ≤ (p : ℝ)} f t := by
    intro t ht
    rw [hboundary t ht, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases htp : t ≤ (p : ℝ) <;> simp [htp, mul_comm]
  calc
    _ = ∫ t in a..b, ∑ p ∈ S, m p * Set.indicator {t : ℝ | t ≤ (p : ℝ)} f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hpoint t ht
    _ = ∑ p ∈ S, ∫ t in a..b, m p * Set.indicator {t : ℝ | t ≤ (p : ℝ)} f t := by
      apply intervalIntegral.integral_finsetSum
      intro p hp
      apply IntervalIntegrable.const_mul
      apply intervalIntegrable_iff.mpr
      exact hf.def'.indicator measurableSet_Iic
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpmem := (Finset.mem_filter.mp hp).2
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_indicator ⟨hpmem.1, hpmem.2.le⟩]

/-- Multiplying a moving stopping boundary by an interval integrable
weight preserves interval integrability. Derived finite step function
fact in the partial summation proof of Nathanson pp. 251 to 252. -/
theorem rosser_boundary_intervalIntegrable326 (s : BoundingSieve) (a b : ℝ)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun t => f t * rosserIntervalBoundary326 s t b)
      MeasureTheory.volume a b := by
  classical
  let Q := s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < b)
  let m : ℕ → ℝ := fun p =>
    s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)
  have heq : (fun t => f t * rosserIntervalBoundary326 s t b) =
      fun t => ∑ p ∈ Q, m p * Set.indicator {t : ℝ | t ≤ (p : ℝ)} f t := by
    funext t
    unfold rosserIntervalBoundary326 Q
    simp_rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpb : (p : ℝ) < b <;> by_cases htp : t ≤ (p : ℝ) <;>
      simp [hpb, htp, m, mul_comm]
  rw [heq]
  have hsum := IntervalIntegrable.sum Q
    (f := fun p t => m p * Set.indicator {t : ℝ | t ≤ (p : ℝ)} f t)
    (fun p hp => (intervalIntegrable_iff.mpr
      (hf.def'.indicator measurableSet_Iic)).const_mul (m p))
  convert hsum using 1
  funext t
  simp only [Finset.sum_apply]

/-- Partial summation with the actual lab density loss bounds a weighted
prime stopping sum by a single explicit integral. This is a derived
version of Nathanson pp. 251 to 252 Lemma 9.8 that retains K over log t.
The weight is continuous and nonnegative on the integration interval. -/
theorem rosser_weighted_boundary_le_density326 (s : BoundingSieve) (K a b : ℝ)
    (hK : 0 ≤ K) (hden : LinearDensity s K) (ha : 2 ≤ a) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hf0 : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    (∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b),
      (s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)) *
        ∫ t in a..(p : ℝ), f t) ≤
      rosserPrefixProduct326 s b *
        ∫ t in a..b, f t * (log b / log t * (1 + K / log t) - 1) := by
  have hfi : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have hlog : ContinuousOn (fun t : ℝ => log t) (Set.Icc a b) :=
    continuousOn_id.log (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hlnz : ∀ t ∈ Set.Icc a b, log t ≠ 0 := fun t ht =>
    (log_pos (by linarith [ht.1] : 1 < t)).ne'
  have hci : IntervalIntegrable
      (fun t => f t * (log b / log t * (1 + K / log t) - 1))
      MeasureTheory.volume a b :=
    (hf.mul (((continuousOn_const.div hlog hlnz).mul
      (continuousOn_const.add (continuousOn_const.div hlog hlnz))).sub
        continuousOn_const)).intervalIntegrable_of_Icc hab
  rw [← rosser_boundary_integral326 s a b hab f hfi,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab
    (rosser_boundary_intervalIntegrable326 s a b f hfi) (hci.const_mul _)
  intro t ht
  have htb : t ≤ b := ht.2
  have ht2 : 2 ≤ t := ha.trans ht.1
  have hpoint : rosserIntervalBoundary326 s t b ≤ rosserPrefixProduct326 s b *
      (log b / log t * (1 + K / log t) - 1) := by
    rcases eq_or_lt_of_le htb with he | he
    · subst t
      rw [rosserIntervalBoundary_eq_zero326 s b b le_rfl]
      have hV : 0 ≤ rosserPrefixProduct326 s b :=
        Finset.prod_nonneg fun p hp => (sub_pos.mpr
          (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1))).le
      have hlb : 0 < log b := log_pos (by linarith)
      rw [div_self hlb.ne']
      exact mul_nonneg hV (by simpa using div_nonneg hK hlb.le)
    · exact rosserIntervalBoundary_le_density326 s K t b hden ht2 he
  have hh := mul_le_mul_of_nonneg_left hpoint (hf0 t ht)
  nlinarith only [hh]

/-- The first stopping term already has a vanishing logarithmic error.
The remaining upper stopping terms start at order three. The main
coefficient here is max of zero and three over s minus one.
Derived from the T one calculation in Nathanson p. 245 equation 9.13
and BJS p. 11, with the lab density parameter K. -/
theorem rosserFirstBoundary_le_log_error326 (s : BoundingSieve) (K z D : ℝ)
    (hK : 0 ≤ K) (hden : LinearDensity s K) (hz : 2 ≤ z) (hzD : z ≤ D)
    (hD : 8 ≤ D) (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    rosserFirstBoundary s (exp (log D / 3)) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (max 0 (3 / (log D / log z) - 1) + 9 * K * log D ^ (-(1 / 3 : ℝ))) := by
  have hD1 : 1 < D := by linarith
  have hld : 0 < log D := log_pos hD1
  have hlz : 0 < log z := log_pos (by linarith)
  have hu : 1 ≤ log D / log z := (le_div_iff₀ hlz).mpr
    (by simpa using log_le_log (by linarith : 0 < z) hzD)
  have hu0 : 0 < log D / log z := by linarith
  have hlog1 : 1 ≤ log D := by
    have hex : exp 1 < D := exp_one_lt_three.trans_le (by linarith)
    have hh := log_lt_log (exp_pos 1) hex
    simpa only [log_exp] using hh.le
  have hlog8 : log (8 : ℝ) = 3 * log 2 := by
    convert log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have hw : 2 ≤ exp (log D / 3) := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 8) hD
    rw [hlog8] at hh
    calc
      (2 : ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
      _ ≤ exp (log D / 3) := exp_le_exp.mpr (by linarith)
  have hV : 0 ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_nonneg fun p hp => (sub_pos.mpr
      (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp))).le
  have herr : 0 ≤ 9 * K * log D ^ (-(1 / 3 : ℝ)) := by positivity
  by_cases hwz : exp (log D / 3) < z
  · have hh := rosserFirstBoundary_le_three_div s K z D hden hz hD1 hw hwz hP
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ hV)
    have hthree : 3 / (log D / log z) ≤ 3 :=
      (div_le_iff₀ hu0).mpr (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hthree
      (div_nonneg (show 0 ≤ 3 * K by positivity) hld.le)
    have hrpow : (log D)⁻¹ ≤ log D ^ (-(1 / 3 : ℝ)) := by
      rw [← rpow_neg_one]
      exact rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have he := mul_le_mul_of_nonneg_left hrpow (show 0 ≤ 9 * K by positivity)
    have hbase := le_max_right 0 (3 / (log D / log z) - 1)
    have hmul' : 3 / (log D / log z) * (3 * K / log D) ≤ 9 * K / log D :=
      hmul.trans_eq (by ring)
    have he' : 9 * K / log D ≤ 9 * K * log D ^ (-(1 / 3 : ℝ)) := by
      simpa only [div_eq_mul_inv] using he
    nlinarith only [hmul', he', hbase]
  · rw [rosserFirstBoundary_eq_zero s _ (fun p hp =>
      (hP p hp).trans_le (le_of_not_gt hwz))]
    exact mul_nonneg hV (add_nonneg (le_max_left _ _) herr)

/-- The two thirds logarithmic cutoff makes the density loss explicit.
It is a derived small prime separation input for Nathanson p. 253
Theorem 9.5 and the varying logarithmic error on Heath Brown p. 35.
This estimates only interval products above the cutoff. -/
theorem linearDensity_twoThirds_cutoff326 (s : BoundingSieve) (K D : ℝ)
    (hK : 0 ≤ K) (hden : LinearDensity s K) (hD : 1 ≤ log D)
    (w w' : ℝ) (hw : exp (log D ^ ((2 : ℝ) / 3)) ≤ w) (hww' : w < w') :
    (∏ p ∈ s.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'), (1 - s.nu p)⁻¹) ≤
      log w' / log w * (1 + K / log D ^ ((2 : ℝ) / 3)) := by
  have ha : 0 < log D ^ ((2 : ℝ) / 3) := rpow_pos_of_pos (by linarith) _
  have hw0 : 2 ≤ exp (log D ^ ((2 : ℝ) / 3)) :=
    exp_one_gt_two.le.trans (exp_le_exp.mpr (one_le_rpow hD (by norm_num)))
  apply linearDensity_uniform_above s K (K / log D ^ ((2 : ℝ) / 3))
    (exp (log D ^ ((2 : ℝ) / 3))) hden (div_nonneg hK ha.le) hw0
  · rw [log_exp, div_mul_cancel₀ K ha.ne']
  · exact hw
  · exact hww'

/-- The level cost of the two thirds logarithmic cutoff is exactly the
one third logarithmic error scale. Derived parameter identity for the
small prime separation in the linear sieve on Heath Brown p. 35. -/
theorem twoThirds_cutoff_level_cost326 (D : ℝ) (hD : 1 < D) :
    log (exp (log D ^ ((2 : ℝ) / 3))) / log D = log D ^ (-(1 / 3 : ℝ)) := by
  rw [log_exp, ← rpow_sub_one (log_pos hD).ne']
  norm_num

/-- For fixed K the explicit density loss above the two thirds cutoff
tends to zero. This is only the density parameter, not the unresolved
stopping series estimate. Derived limit for Nathanson p. 253 Theorem 9.5. -/
theorem twoThirds_density_loss_tendsto326 (K : ℝ) :
    Filter.Tendsto (fun D : ℝ => K / log D ^ ((2 : ℝ) / 3))
      Filter.atTop (nhds 0) := by
  have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    tendsto_log_atTop).const_mul K
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with D hD
  simp only [Function.comp_apply, rpow_neg (log_pos hD).le, div_eq_mul_inv]

/-- On a fixed bounded cutoff range, both Rosser defect moments satisfy
the logarithmic error bound for levels between z and z to the fifth.
The constant depends on K and B. Derived compact range reduction of
Nathanson p. 256 Theorem 9.6 using the finite identity on p. 242. -/
theorem rosser_defect_log_bounded (K B : ℝ) (hK : 0 ≤ K) (hB : 2 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ),
      2 ≤ z → z ≤ B → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∀ upper : Bool,
        (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) ≤
          C * log D ^ (-(1 / 3 : ℝ)) := by
  classical
  let M : ℕ := ⌈B⌉₊
  let A : ℝ := 2 ^ M * (log (B + 1) / log 2 * (1 + K / log 2))
  let e : ℝ := log (B ^ 5) ^ (-(1 / 3 : ℝ))
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hB1 : 1 < B := by linarith
  have he : 0 < e := rpow_pos_of_pos (log_pos (one_lt_pow₀ hB1 (by norm_num))) _
  have hA : 0 < A := by
    dsimp [A]
    have : 0 ≤ K / log 2 := div_nonneg hK hlog2.le
    exact mul_pos (by positivity) (mul_pos (div_pos (log_pos (by linarith)) hlog2)
      (by linarith))
  refine ⟨A / e, div_pos hA he, ?_⟩
  intro s z D hz hzB hzD hDz hP hden upper
  have hcard : s.prodPrimes.primeFactors.card ≤ M := by
    have hsub : s.prodPrimes.primeFactors ⊆ Finset.range M := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr ((hP p hp).trans_le hzB))
    simpa using Finset.card_le_card hsub
  have hcoarse : (∑ n ∈ s.prodPrimes.divisors,
      s.selbergTerms n * rosserDefect D upper n) ≤ A := by
    refine (rosser_defect_moment_le_coarse s K D z hK hz hP hden upper).trans ?_
    apply mul_le_mul
    · exact pow_le_pow_right₀ (by norm_num) hcard
    · exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (log_le_log (by linarith) (by linarith)) hlog2.le) (by positivity)
    · have hlogz : 0 ≤ log (z + 1) := log_nonneg (by linarith)
      positivity
    · positivity
  have hD1 : 1 < D := by linarith
  have hDB : D ≤ B ^ 5 := hDz.trans (pow_le_pow_left₀ (by linarith) hzB 5)
  have heD : e ≤ log D ^ (-(1 / 3 : ℝ)) :=
    rpow_le_rpow_of_nonpos (log_pos hD1)
      (log_le_log (by linarith) hDB) (by norm_num)
  calc
    _ ≤ A := hcoarse
    _ = A / e * e := (div_mul_cancel₀ A he.ne').symm
    _ ≤ A / e * log D ^ (-(1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left heD (div_pos hA he).le

/-- LEAF. The higher odd stopping moment on the first explicit F range after
removing bounded cutoffs. This is only the range one through three,
with positive K and z above the fixed K dependent cutoff.
The explicitly bounded first stopping term is subtracted.
Nathanson pp. 242 to 244 equation 9.10 and p. 256 Theorem 9.6,
with the explicit F formula on pp. 266 to 267 Theorem 9.8.
Derived varying error subproblem of Heath Brown p. 35 Theorem 5.1. -/
theorem jr_upper_small_ratio326 (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ),
      2 ≤ z → max 8 (exp (K + 2)) < z → z ≤ D → D ≤ z ^ 5 →
      log D / log z ≤ 3 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D true n) -
          rosserFirstBoundary s (exp (log D / 3)) /
            (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤
        (2 * exp eulerMascheroniConstant - 3) / (log D / log z) +
          C * log D ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- LEAF. The upper stopping moment on the integral F range after removing
bounded cutoffs. This is only the range strictly above three through five,
with positive K and z above the fixed K dependent cutoff.
Nathanson pp. 242 to 244 equation 9.10 and p. 256 Theorem 9.6,
with the explicit F formula on pp. 266 to 267 Theorem 9.8.
Derived varying error subproblem of Heath Brown p. 35 Theorem 5.1. -/
theorem jr_upper_integral_ratio326 (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ),
      2 ≤ z → max 8 (exp (K + 2)) < z → z ≤ D → D ≤ z ^ 5 →
      3 < log D / log z →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D true n) ≤
        2 * exp eulerMascheroniConstant / (log D / log z) *
          (1 + ∫ t in (2 : ℝ)..(log D / log z - 1), log (t - 1) / t) - 1 +
          C * log D ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- Exact supply for jr_mainSum_upper from the two smaller range leaves
and the proved bounded cutoff estimate. The positive K and large cutoff
restrictions occur only in the leaves. This assembly keeps the original
unrestricted conclusion. CONDITIONAL ON the two open range estimates.
Nathanson p. 256 Theorem 9.6 and Heath Brown p. 35. -/
theorem jr_mainSum_upper_supply326 (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      s.mainSum (rosserWeight D true) ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))) := by
  by_cases hzero : K = 0
  · subst K
    exact jr_mainSum_upper_zero
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hzero)
  obtain ⟨Cb, hCb, hb⟩ := rosser_defect_log_bounded K (max 8 (exp (K + 2))) hK
    (by linarith [le_max_left (8 : ℝ) (exp (K + 2))])
  obtain ⟨C1, hC1, h1⟩ := jr_upper_small_ratio326 K hKpos
  obtain ⟨C2, hC2, h2⟩ := jr_upper_integral_ratio326 K hKpos
  refine ⟨Cb + C1 + C2 + 9 * K, by positivity, ?_⟩
  intro s z D hz hzD hDz hP hden
  have hld : 0 < log D := log_pos (by linarith)
  have hlz : 0 < log z := log_pos (by linarith)
  have herr : 0 ≤ log D ^ (-(1 / 3 : ℝ)) := (rpow_pos_of_pos hld _).le
  have hspos : 0 < log D / log z := div_pos hld hlz
  have hs5 : log D / log z ≤ 5 := by
    apply (div_le_iff₀ hlz).mpr
    have hh := log_le_log (by linarith : 0 < D) hDz
    rw [log_pow] at hh
    norm_num at hh
    linarith
  apply (rosser_upper_mainSum_iff_defect s D _).mpr
  by_cases hzB : z ≤ max 8 (exp (K + 2))
  · have hh := hb s z D hz hzB hzD hDz hP hden true
    have hf := one_lt_Fsieve _ hspos hs5
    nlinarith [mul_nonneg hC1.le herr, mul_nonneg hC2.le herr,
      mul_nonneg (show 0 ≤ 9 * K by positivity) herr]
  · have hlarge := lt_of_not_ge hzB
    by_cases hs3 : log D / log z ≤ 3
    · have hh := h1 s z D hz hlarge hzD hDz hs3 hP hden
      have hV : 0 < ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
        Finset.prod_pos fun p hp => sub_pos.mpr
          (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
            (Nat.dvd_of_mem_primeFactors hp))
      have ht0 := rosserFirstBoundary_le_log_error326 s K z D hK hden hz hzD
        (by have := le_max_left (8 : ℝ) (exp (K + 2)); linarith) hP
      have ht : rosserFirstBoundary s (exp (log D / 3)) /
          (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤
          max 0 (3 / (log D / log z) - 1) + 9 * K * log D ^ (-(1 / 3 : ℝ)) :=
        (div_le_iff₀ hV).mpr (by simpa only [mul_comm] using ht0)
      have hu : 0 < log D / log z := div_pos hld hlz
      have hbase : 0 ≤ 3 / (log D / log z) - 1 := by
        have ht3 : 1 ≤ 3 / (log D / log z) :=
          (le_div_iff₀ hu).mpr (by simpa using hs3)
        linarith
      rw [max_eq_right hbase] at ht
      rw [Fsieve, ite_eq_left hs3]
      have hc : (2 * exp eulerMascheroniConstant - 3) / (log D / log z) +
          (3 / (log D / log z) - 1) =
          2 * exp eulerMascheroniConstant / (log D / log z) - 1 := by ring
      nlinarith [mul_nonneg hCb.le herr, mul_nonneg hC2.le herr]
    · have hh := h2 s z D hz hlarge hzD hDz (lt_of_not_ge hs3) hP hden
      rw [Fsieve, ite_eq_right hs3]
      nlinarith [mul_nonneg hCb.le herr, mul_nonneg hC1.le herr,
        mul_nonneg (show 0 ≤ 9 * K by positivity) herr]

end LeanLab.AlmostPrimeSums.Decomp1527b
