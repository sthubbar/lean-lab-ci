/-
Jia 1996 page 262 Lemma 21 and page 261 displays 40 and 41.
Source https://doi.org/10.4064/aa-77-3-207-287.
Separate the prime number theorem base range from the cited rough range.
The original source leaf stays sealed. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Sieve565
import LeanLab.Languasco2004.Buchstab578
import LeanLab.Languasco2004.Decomp588e

namespace LeanLab.Languasco2004.Decomp588a
open Real Finset intervalIntegral
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 262 Lemma 21 support: above the square root cutoff the rough interval is exactly primes. -/
theorem rough_eq_primes {t z : ℝ} (ht : 1 ≤ t) (hzt : z ≤ t) (hsq : 2 * t < z ^ 2)
    (hz : 0 < z) :
    Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z =
      (Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter Nat.Prime := by
  ext a
  simp only [Sieve565.sieved, mem_filter]
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    have hta : t < (a : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp ha).1
    have ha0 : 0 < a := by exact_mod_cast (lt_trans (by linarith : (0 : ℝ) < t) hta)
    have ha1 : a ≠ 1 := by intro h; subst a; norm_num at hta; linarith
    by_contra hnp
    have hp := Nat.minFac_prime ha1
    have hsqA : (a.minFac : ℝ) ^ 2 ≤ (a : ℝ) := by
      exact_mod_cast Nat.minFac_sq_le_self ha0 hnp
    have hau : (a : ℝ) ≤ 2 * t :=
      (Nat.cast_le.mpr (mem_Ioc.mp ha).2).trans (Nat.floor_le (by linarith))
    have hpf : (a.minFac : ℝ) < z := by
      have hnonneg : (0 : ℝ) ≤ a.minFac := Nat.cast_nonneg _
      nlinarith
    exact hs a.minFac hp hpf (by simpa using hp.not_dvd_one) (Nat.minFac_dvd a)
  · rintro ⟨ha, hp⟩
    refine ⟨ha, ?_⟩
    intro p hpp hpz _ hpa
    have hpa' : p = a := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hpa
    subst p
    have hta : t < (a : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp ha).1
    linarith

/-- Page 262 Lemma 21 support: the Buchstab main term in the prime range is t over log t. -/
theorem prime_range_main_term (w : ℝ → ℝ)
    (hi : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    {t z : ℝ} (hz : 1 < z) (hzt : z ≤ t) (hsq : 2 * t < z ^ 2) :
    w (log t / log z) * (t / log z) = t / log t := by
  have ht : 1 < t := hz.trans_le hzt
  have hlz := Real.log_pos hz
  have hlt := Real.log_pos ht
  have hlogzt : log z ≤ log t := Real.log_le_log (by linarith) hzt
  have htz : t < z ^ 2 := by
    have : 0 < t := by linarith
    linarith
  have hlogsq : log t < 2 * log z := by
    have h := Real.log_lt_log (by linarith : 0 < t) htz
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  rw [hi _ ((le_div_iff₀ hlz).mpr (by simpa using hlogzt))
    ((div_le_iff₀ hlz).mpr hlogsq.le)]
  field_simp

/-- LEAF. Jia page 262 Lemma 21 prime number theorem base case.
This is the dyadic short interval prime number theorem, with an arbitrary relative tolerance.
Only primes occur. No Buchstab recurrence is asserted. -/
theorem dyadic_prime_number_theorem :
    ∀ η : ℝ, 0 < η → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
      |(((Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter Nat.Prime).card : ℝ) - t / log t| ≤
        η * (t / log t) := by
  exact Decomp588e.dyadic_prime_number_theorem

/-- LEAF. Jia page 262 Lemma 21, only the range below the square root cutoff.
The source cites Lemma 5 of reference 9. The omitted prime range is supplied separately.
The recurrence is display 41 on page 261. This input still needs its uniform induction proof. -/
theorem rough_below_square_root :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ η : ℝ, 0 < η → ∃ T Z : ℝ, 1 < T ∧ 1 < Z ∧
      ∀ t z : ℝ, T ≤ t → Z ≤ z → z ≤ t → z ^ 2 ≤ 2 * t →
        |((Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) -
            w (log t / log z) * (t / log z)| ≤ η * (t / log z) := by sorry

/-- Jia page 262 Lemma 21: exact assembly of the two proper ranges.
CONDITIONAL ON the below square root rough input. The prime case is proved.
This theorem has the exact statement of the sealed rough asymptotic. -/
theorem lemma21_from_ranges :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ η : ℝ, 0 < η → ∃ T Z : ℝ, 1 < T ∧ 1 < Z ∧
      ∀ t z : ℝ, T ≤ t → Z ≤ z → z ≤ t →
        |((Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) -
            w (log t / log z) * (t / log z)| ≤ η * (t / log z) := by
  intro w hw hi hr η hη
  obtain ⟨TP, hTP, hP⟩ := dyadic_prime_number_theorem η hη
  obtain ⟨TR, Z, hTR, hZ, hR⟩ := rough_below_square_root w hw hi hr η hη
  refine ⟨max TP TR, Z, hTP.trans_le (le_max_left _ _), hZ, ?_⟩
  intro t z ht hz hzt
  by_cases hsq : z ^ 2 ≤ 2 * t
  · exact hR t z ((le_max_right _ _).trans ht) hz hzt hsq
  · have htP := (le_max_left TP TR).trans ht
    have hz1 := hZ.trans_le hz
    have ht1 : 1 < t := hTP.trans_le htP
    rw [rough_eq_primes ht1.le hzt (lt_of_not_ge hsq) (by linarith),
      prime_range_main_term w hi hz1 hzt (lt_of_not_ge hsq)]
    refine (hP t htP).trans (mul_le_mul_of_nonneg_left ?_ hη.le)
    exact div_le_div_of_nonneg_left (by linarith) (Real.log_pos hz1)
      (Real.log_le_log (by linarith) hzt)

/-- Page 262 Lemma 21 support: no fixed positive power cutoff covers its uniform domain.
This records the scope obstruction to reusing estimates restricted by z at least t^c. -/
theorem no_fixed_power_cutoff (c T Z : ℝ) (hc : 0 < c) :
    ∃ t z : ℝ, 1 < z ∧ T ≤ t ∧ Z ≤ z ∧ z ≤ t ∧ z < t ^ c := by
  let z := max 2 Z
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hc).eventually (Filter.eventually_gt_atTop z))
  refine ⟨max N (max T z), z, hz1, ?_, le_max_right _ _, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact hN _ (le_max_left _ _)

#print axioms no_fixed_power_cutoff
#print axioms rough_eq_primes
#print axioms prime_range_main_term
#print axioms dyadic_prime_number_theorem
#print axioms rough_below_square_root
#print axioms lemma21_from_ranges
end
end LeanLab.Languasco2004.Decomp588a
