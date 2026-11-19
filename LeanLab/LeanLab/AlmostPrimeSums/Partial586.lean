import LeanLab.AlmostPrimeSums.Decomp326a
import Mathlib

/-!
AI wrote this Lean code for CODEX task586. Goldbach is open.
The smooth weighted partial summation input for the primary Rosser proof.
Source: Iwaniec, Rosser's sieve, p. 198 Lemma 21 equation 8.2,
https://doi.org/10.4064/aa-36-2-171-202.
-/
open Finset Real MeasureTheory intervalIntegral
namespace LeanLab.AlmostPrimeSums.Decomp1527b

/-- LEAF. The logarithmic density profile has the exact smooth
partial summation error at most two K times the terminal B value
divided by log a. Derived calculus normalization for Iwaniec p. 198
Lemma 21 equation 8.2 at dimension one. -/
theorem log_profile_bound586 (K a b : ℝ) (hK : 0 ≤ K) (ha : 2 ≤ a) (hab : a ≤ b)
    (B H H' : ℝ → ℝ) (hB : ContinuousOn B (Set.Icc a b))
    (hH' : ContinuousOn H' (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt H (H' t) t)
    (hnorm : ∀ t ∈ Set.Icc a b, H t = log t / log b * B t)
    (hB0 : ∀ t ∈ Set.Icc a b, 0 ≤ B t)
    (hBup : ∀ t ∈ Set.Icc a b, B t ≤ B b) :
    H a * (log b / log a * (1 + K / log a) - 1) +
      (∫ t in a..b, H' t * (log b / log t * (1 + K / log t) - 1)) ≤
        (∫ t in a..b, B t * (t⁻¹ / log t)) + 2 * K * B b / log a := by
  have ha1 : 1 < a := by linarith
  have hb1 : 1 < b := by linarith
  have hlb : log b ≠ 0 := (log_pos hb1).ne'
  have htn : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hln : ∀ t ∈ Set.Icc a b, log t ≠ 0 := fun t ht =>
    (log_pos (by linarith [ht.1] : 1 < t)).ne'
  have hlog : ContinuousOn (fun t : ℝ => log t) (Set.Icc a b) :=
    continuousOn_id.log htn
  have hker (k : ℕ) : ContinuousOn (fun t : ℝ => t⁻¹ / log t ^ k) (Set.Icc a b) :=
    (continuousOn_id.inv₀ htn).div (hlog.pow k) (fun t ht => pow_ne_zero _ (hln t ht))
  let R := fun t : ℝ => log b / log t * (1 + K / log t) - 1
  let R' := fun t : ℝ => -log b * (t⁻¹ / log t ^ 2) -
    2 * K * log b * (t⁻¹ / log t ^ 3)
  have hRc : ContinuousOn R (Set.Icc a b) := by
    dsimp [R]
    exact ((continuousOn_const.div hlog hln).mul
      (continuousOn_const.add (continuousOn_const.div hlog hln))).sub continuousOn_const
  have hR'c : ContinuousOn R' (Set.Icc a b) :=
    ((hker 2).const_mul _).sub ((hker 3).const_mul _)
  have hRd : ∀ t ∈ Set.Icc a b, HasDerivAt R (R' t) t := by
    intro t ht
    have hd := Real.hasDerivAt_log (htn t ht)
    convert (((hasDerivAt_const t (log b)).div hd (hln t ht)).mul
      ((hasDerivAt_const t 1).add ((hasDerivAt_const t K).div hd (hln t ht)))).sub_const 1 using 1
    dsimp [R']
    field_simp [htn t ht, hln t ht]
    ring
  have hHc : ContinuousOn H (Set.Icc a b) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hP := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (by simpa only [Set.uIcc_of_le hab] using hHc)
    (by simpa only [Set.uIcc_of_le hab] using hRc)
    (fun t ht => by
      rw [min_eq_left hab, max_eq_right hab] at ht
      exact hderiv t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      rw [min_eq_left hab, max_eq_right hab] at ht
      exact hRd t ⟨ht.1.le, ht.2.le⟩)
    (hH'.intervalIntegrable_of_Icc hab) (hR'c.intervalIntegrable_of_Icc hab)
  have hI : IntervalIntegrable (fun t => H' t * R t) volume a b :=
    (hH'.mul hRc).intervalIntegrable_of_Icc hab
  have hJ : IntervalIntegrable (fun t => H t * R' t) volume a b :=
    (hHc.mul hR'c).intervalIntegrable_of_Icc hab
  have h1 : IntervalIntegrable (fun t => B t * (t⁻¹ / log t)) volume a b := by
    have hc : ContinuousOn (fun t => B t * (t⁻¹ / log t)) (Set.Icc a b) := by
      convert hB.mul (hker 1) using 1
      funext t
      simp only [Pi.mul_apply, pow_one]
    exact hc.intervalIntegrable_of_Icc hab
  have h2 : IntervalIntegrable (fun t => B t * (t⁻¹ / log t ^ 2)) volume a b :=
    (hB.mul (hker 2)).intervalIntegrable_of_Icc hab
  have hJval : (∫ t in a..b, H t * R' t) =
      -(∫ t in a..b, B t * (t⁻¹ / log t)) -
        2 * K * (∫ t in a..b, B t * (t⁻¹ / log t ^ 2)) := by
    calc
      _ = ∫ t in a..b, -(B t * (t⁻¹ / log t)) -
          (2 * K) * (B t * (t⁻¹ / log t ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        dsimp only
        rw [hnorm t ht]
        dsimp [R']
        field_simp [htn t ht, hln t ht, hlb]
      _ = _ := by
        rw [intervalIntegral.integral_sub
          (f := fun t => -(B t * (t⁻¹ / log t)))
          (g := fun t => (2 * K) * (B t * (t⁻¹ / log t ^ 2))) h1.neg (h2.const_mul (2 * K)),
          intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hI hJ, hJval] at hP
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hBend : H b * R b = K * B b / log b := by
    rw [hnorm b hbmem]
    dsimp [R]
    field_simp [hlb]
    ring
  rw [hBend] at hP
  have herr := intervalIntegral.integral_mono_on hab h2
    (((hker 2).const_mul (B b)).intervalIntegrable_of_Icc hab) (by
      intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      exact mul_le_mul_of_nonneg_right (hBup t ht)
        (div_nonneg (inv_nonneg.mpr ht0) (sq_nonneg _)))
  rw [intervalIntegral.integral_const_mul, integral_inv_div_log_sq ha1 hb1] at herr
  have hscaled := mul_le_mul_of_nonneg_left herr (by positivity : (0 : ℝ) ≤ 2 * K)
  have hbound : K * B b / log b +
      (∫ t in a..b, B t * (t⁻¹ / log t)) +
      2 * K * (B b * ((log a)⁻¹ - (log b)⁻¹)) =
      (∫ t in a..b, B t * (t⁻¹ / log t)) + 2 * K * B b / log a -
        K * B b / log b := by simp only [div_eq_mul_inv]; ring
  have hnonneg : 0 ≤ K * B b / log b := by
    exact div_nonneg (mul_nonneg hK (hB0 b hbmem)) (log_pos hb1).le
  change H a * R a + _ ≤ _
  calc
    _ = K * B b / log b + (∫ t in a..b, B t * (t⁻¹ / log t)) +
        2 * K * (∫ t in a..b, B t * (t⁻¹ / log t ^ 2)) := by linarith
    _ ≤ K * B b / log b + (∫ t in a..b, B t * (t⁻¹ / log t)) +
        2 * K * (B b * ((log a)⁻¹ - (log b)⁻¹)) := by linarith
    _ ≤ _ := by rw [hbound]; exact sub_le_self _ hnonneg

/-- LEAF. Smooth weighted partial summation at dimension one, with the
exact lab density loss. The normalized weight H is continuously
differentiable with nonnegative derivative on the interval. The nonnegative B is
continuous and bounded by its terminal value. This is a derived smooth
case of Iwaniec p. 198 Lemma 21 equation 8.2. -/
theorem linearDensity_weighted_log_prime_C1_586 (s : BoundingSieve)
    (K a b : ℝ) (hK : 0 ≤ K) (hden : LinearDensity s K) (ha : 2 ≤ a) (hab : a ≤ b)
    (B H H' : ℝ → ℝ) (hB : ContinuousOn B (Set.Icc a b))
    (hH' : ContinuousOn H' (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt H (H' t) t)
    (hnorm : ∀ t ∈ Set.Icc a b, H t = log t / log b * B t)
    (hB0 : ∀ t ∈ Set.Icc a b, 0 ≤ B t)
    (hBup : ∀ t ∈ Set.Icc a b, B t ≤ B b)
    (hH'0 : ∀ t ∈ Set.Icc a b, 0 ≤ H' t) :
    (∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b),
      (s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)) *
        (log (p : ℝ) / log b) * B p) ≤
      rosserPrefixProduct326 s b *
        ((∫ t in a..b, B t * (t⁻¹ / log t)) + 2 * K * B b / log a) := by
  classical
  let Q := s.prodPrimes.primeFactors.filter
    (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b)
  let m : ℕ → ℝ := fun p => s.nu p *
    ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)
  let V := rosserPrefixProduct326 s b
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hla : 0 < log a := log_pos (by linarith)
  have hlb : 0 < log b := log_pos (by linarith)
  have hHc : ContinuousOn H (Set.Icc a b) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have hprim : ∀ p ∈ Q, (∫ t in a..(p : ℝ), H' t) = H p - H a := by
    intro p hp
    have hband := (Finset.mem_filter.mp hp).2
    have hsub : Set.Icc a (p : ℝ) ⊆ Set.Icc a b := fun t ht =>
      ⟨ht.1, ht.2.trans hband.2.le⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hband.1 (hHc.mono hsub)
      (fun t ht => hderiv t ⟨ht.1.le, ht.2.le.trans hband.2.le⟩)
      ((hH'.mono hsub).intervalIntegrable_of_Icc hband.1)
  have hHa : 0 ≤ H a := by
    rw [hnorm a haI]
    exact mul_nonneg (div_nonneg hla.le hlb.le) (hB0 a haI)
  have hV : 0 ≤ V := by
    apply Finset.prod_nonneg
    intro p hp
    exact (sub_pos.mpr (s.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1))).le
  have hboundary : rosserIntervalBoundary326 s a b ≤
      V * (log b / log a * (1 + K / log a) - 1) := by
    rcases eq_or_lt_of_le hab with he | he
    · subst b
      rw [rosserIntervalBoundary_eq_zero326 s a a le_rfl, div_self hla.ne']
      exact mul_nonneg hV (by simpa using div_nonneg hK hla.le)
    · exact rosserIntervalBoundary_le_density326 s K a b hden ha he
  have hweighted := rosser_weighted_boundary_le_density326 s K a b hK hden ha hab
    H' hH' hH'0
  change (∑ p ∈ Q, m p * (log (p : ℝ) / log b) * B p) ≤ _
  calc
    _ = ∑ p ∈ Q, m p * H p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hnorm p ⟨(Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2.le⟩]
      ring
    _ = H a * rosserIntervalBoundary326 s a b +
        ∑ p ∈ Q, m p * (∫ t in a..(p : ℝ), H' t) := by
      rw [rosserIntervalBoundary326, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hprim p hp]
      ring
    _ ≤ H a * (V * (log b / log a * (1 + K / log a) - 1)) +
        V * (∫ t in a..b, H' t * (log b / log t * (1 + K / log t) - 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hboundary hHa) hweighted
    _ = V * (H a * (log b / log a * (1 + K / log a) - 1) +
        (∫ t in a..b, H' t * (log b / log t * (1 + K / log t) - 1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (log_profile_bound586 K a b hK ha hab B H H' hB hH' hderiv hnorm hB0 hBup) hV

/-- A nonempty sieve with positive constant B satisfies the smooth
partial summation hypotheses. Derived instance of Iwaniec p. 198
Lemma 21 equation 8.2 on the interval from two to four. -/
theorem smooth_partial_instance586 :
    ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ LinearDensity s (log 2) ∧
      (∑ p ∈ s.prodPrimes.primeFactors.filter
          (fun p : ℕ => (2 : ℝ) ≤ p ∧ (p : ℝ) < 4),
        (s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)) *
          (log (p : ℝ) / log 4)) ≤
        rosserPrefixProduct326 s 4 *
          ((∫ t in (2 : ℝ)..4, t⁻¹ / log t) + 2 * log 2 / log 2) := by
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  refine ⟨s, hP, hden, ?_⟩
  have hl4 : 0 < log 4 := log_pos (by norm_num)
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹ / log 4) (Set.Icc 2 4) :=
    (continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])).div_const _
  have h := linearDensity_weighted_log_prime_C1_586 s (log 2) 2 4
    (log_pos (by norm_num)).le hden (by norm_num) (by norm_num)
    (fun _ => 1) (fun t => log t / log 4) (fun t => t⁻¹ / log 4)
    continuousOn_const hcont
    (fun t ht => (Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)).div_const _)
    (by intro t ht; simp) (by intro t ht; exact zero_le_one)
    (by intro t ht; exact le_rfl) (by
      intro t ht
      exact div_nonneg (inv_nonneg.mpr (by linarith [ht.1])) hl4.le)
  simpa only [mul_one, one_mul] using h

end LeanLab.AlmostPrimeSums.Decomp1527b
