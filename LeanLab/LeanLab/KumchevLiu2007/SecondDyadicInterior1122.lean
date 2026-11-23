/-
BURST 2026-11-22, session S81, burst-20261122, second step. Proves the LEAFs
SecondDyadicCases1122.case1_interior from Prep1122KLLemma31Cases.lemma31, Lemma 3.1,
and SecondDyadicCases1122.case2_interior from Prep1122KLLemma31Cases.lemma32, Lemma 3.2
of P0088 page 10 as printed, by the method of Case 2 of the proof of Lemma 3.4 on
page 11: the variable d of the dyadic block D with coefficient mu of d on d free of
prime factors at least z1, and the variable k = n / d with coefficient the number
of primes p of the block M dividing k, at most tau of k. Kumchev and Liu 2007,
P0088, arXiv 0801.0130.

* coeff_eq, PROVED: the block coefficient of display 52 is the Dirichlet
  convolution of the two coefficients above.
* reindex2, PROVED: the change of variables n = d k with two coefficients.
* case2_interior_of_lemma32, PROVED from lemma32: the exact statement of the LEAF,
  split at Y/2, x = Y/4 and x = Y/2, as in Split1122KLLemma34M1.
* Case 1: bC is the convolution b_r over p d = r, bC_bound gives |b_r| at most tau of r,
  coeff1_eq and coeff1_split write the block coefficient as the sum of b_r over the
  divisors r of n in the two dyadic blocks M D and 2 M D, integrand1 and piece_eq pass
  to the form of Lemma 3.1, and case1_interior_of_lemma31, PROVED from lemma31 with
  B / 2 in place of B for the slack 2 M D at most x^(1/4) (log x)^(-B/2).

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SecondDyadicCases1122
import LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases
import LeanLab.KumchevLiu2007.Split1122KLLemma34M1

namespace LeanLab.KumchevLiu2007.SecondDyadicInterior1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The coefficient of d in Case 2: mu of d when every prime factor of d is below z1. -/
noncomputable def amC (z1 : ℝ) (d : ℕ) : ℂ :=
  if (∀ r : ℕ, r.Prime → r ∣ d → (r : ℝ) < z1) then ((ArithmeticFunction.moebius d : ℤ) : ℂ)
  else 0

/-- The block prime set of display 52 for k. -/
noncomputable def primeSet (z1 z0 M : ℝ) (k : ℕ) : Finset ℕ :=
  ((Finset.range (k + 1)).filter (fun p : ℕ => p.Prime ∧
    z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ k)).filter
    (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M)

/-- The coefficient of k in Case 2: the number of primes of the block dividing k. -/
noncomputable def bkC (z1 z0 M : ℝ) (k : ℕ) : ℂ := ((primeSet z1 z0 M k).card : ℂ)

/-- PROVED. amC is at most tau to the power one. -/
theorem amC_bound (z1 : ℝ) (m : ℕ) (hm : m ≠ 0) :
    ‖amC z1 m‖ ≤ (m.divisors.card : ℝ) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have h1 : (1 : ℝ) ≤ m.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
  unfold amC
  split_ifs
  · refine le_trans ?_ h1
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- PROVED. bkC is at most tau to the power one: the block primes dividing k are
divisors of k. -/
theorem bkC_bound (z1 z0 M : ℝ) (k : ℕ) (hk : k ≠ 0) :
    ‖bkC z1 z0 M k‖ ≤ (k.divisors.card : ℝ) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  unfold bkC
  rw [Complex.norm_natCast]
  exact_mod_cast Finset.card_le_card (fun p hp => by
    obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, -, -, hpk⟩ := Finset.mem_filter.mp hp1
    exact Nat.mem_divisors.mpr ⟨hpk, hk⟩)

/-- PROVED. P0088 page 11, Case 2: the block coefficient of display 52 is the
convolution of amC on the block D and bkC. -/
theorem coeff_eq (z1 z0 M D : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ p ∈ ((Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧
        z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ n)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      ∑ d ∈ ((n / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < z1)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D)),
      amC z1 d * bkC z1 z0 M (n / d) := by
  have e1 : ∀ d : ℕ, amC z1 d * bkC z1 z0 M (n / d) =
      if (∀ r : ℕ, r.Prime → r ∣ d → (r : ℝ) < z1) then
        ∑ _p ∈ primeSet z1 z0 M (n / d), ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0 := by
    intro d
    unfold amC bkC
    split_ifs
    · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    · rw [zero_mul]
  simp_rw [e1]
  rw [← Finset.sum_filter]
  refine Finset.sum_comm' fun p d => ?_
  unfold primeSet
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  constructor
  · rintro ⟨⟨⟨hpn1, hpr, hz1, hz0, hpn⟩, hM1, hM2⟩, ⟨⟨hd, hnp⟩, hsm⟩, hD1, hD2⟩
    have hpd : p * d ∣ n := (Nat.dvd_div_iff_mul_dvd hpn).mp hd
    have hdn : d ∣ n := dvd_trans (dvd_mul_left d p) hpd
    have hdp : d * p ∣ n := by rwa [mul_comm]
    have hpnd : p ∣ n / d := (Nat.dvd_div_iff_mul_dvd hdn).mpr hdp
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn0
    have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn0 hdn) hd0
    exact ⟨⟨⟨Nat.lt_succ_of_le (Nat.le_of_dvd hnd hpnd), hpr, hz1, hz0, hpnd⟩, hM1, hM2⟩,
      ⟨⟨⟨hdn, hn⟩, Nat.lt_succ_of_le (Nat.le_floor (by linarith)), hD1, hD2⟩, hsm⟩⟩
  · rintro ⟨⟨⟨-, hpr, hz1, hz0, hpnd⟩, hM1, hM2⟩, ⟨⟨⟨hdn, -⟩, -, hD1, hD2⟩, hsm⟩⟩
    have hdp : d * p ∣ n := (Nat.dvd_div_iff_mul_dvd hdn).mp hpnd
    have hpn : p ∣ n := dvd_trans (dvd_mul_left p d) hdp
    have hpd : p * d ∣ n := by rwa [mul_comm]
    have hd : d ∣ n / p := (Nat.dvd_div_iff_mul_dvd hpn).mpr hpd
    have hp0 : 0 < p := hpr.pos
    have hnp : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp0).ne'
    exact ⟨⟨⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn0 hpn), hpr, hz1, hz0, hpn⟩, hM1, hM2⟩,
      ⟨⟨hd, hnp⟩, hsm⟩, hD1, hD2⟩

/-- PROVED. The change of variables n = m k of pages 10 and 11 with two
coefficients. -/
theorem reindex2 (R : Finset ℕ) (N : ℕ) (am bk g : ℕ → ℂ) (P : ℕ → Prop)
    (hR : ∀ r ∈ R, r ≠ 0) (hP : ∀ n, P n → n ≠ 0 ∧ n ≤ N) :
    ∑ r ∈ R, ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => P (r * k)),
        am r * bk k * g (r * k) =
      ∑ n ∈ (Finset.range (N + 1)).filter P,
        (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ R), am d * bk (n / d)) * g n := by
  have hin : ∀ r ∈ R, ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => P (r * k)),
      am r * bk k * g (r * k) =
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => P n ∧ r ∣ n),
        am r * bk (n / r) * g n := by
    intro r hr
    have hr0 : 0 < r := Nat.pos_of_ne_zero (hR r hr)
    refine Finset.sum_nbij' (fun k => r * k) (fun n => n / r) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨_, hPk⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hP _ hPk).2),
        hPk, dvd_mul_right r k⟩
    · intro n hn
      obtain ⟨hnr, hPn, hdvd⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact lt_of_le_of_lt (Nat.div_le_self n r) (Finset.mem_range.mp hnr)
      · show P (r * (n / r))
        rw [Nat.mul_div_cancel' hdvd]
        exact hPn
    · intro k _
      exact Nat.mul_div_cancel_left k hr0
    · intro n hn
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2.2
    · intro k _
      simp only [Nat.mul_div_cancel_left k hr0]
  rw [Finset.sum_congr rfl hin]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_comm' fun r n => ?_
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨hr, hn, hPn, hd⟩
    exact ⟨⟨⟨hd, (hP n hPn).1⟩, hr⟩, hn, hPn⟩
  · rintro ⟨⟨⟨hd, _⟩, hr⟩, hn, hPn⟩
    exact ⟨hr, hn, hPn, hd⟩


/-- The coefficient of d in Case 1: mu of d on d in the block D free of primes at
least z1. -/
noncomputable def amD (z1 D : ℝ) (d : ℕ) : ℂ :=
  if (∀ r : ℕ, r.Prime → r ∣ d → (r : ℝ) < z1) ∧ (D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D) then
    ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0

/-- The convolution b_r of Case 1, the sum over p d = r of the block prime
indicator times amD of d. -/
noncomputable def bC (z1 z0 M D : ℝ) (r : ℕ) : ℂ :=
  ∑ p ∈ primeSet z1 z0 M r, amD z1 D (r / p)

/-- PROVED. P0088 page 11, Case 1: b_r is at most tau of r. -/
theorem bC_bound (z1 z0 M D : ℝ) (r : ℕ) (hr : r ≠ 0) :
    ‖bC z1 z0 M D r‖ ≤ (r.divisors.card : ℝ) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  unfold bC
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ p ∈ primeSet z1 z0 M r, ‖amD z1 D (r / p)‖ ≤ 1 := by
    intro p _
    unfold amD
    split_ifs
    · rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · simp
  refine (Finset.sum_le_card_nsmul _ _ 1 h1).trans ?_
  rw [nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card (fun p hp => by
    unfold primeSet at hp
    obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, -, -, hpk⟩ := Finset.mem_filter.mp hp1
    exact Nat.mem_divisors.mpr ⟨hpk, hr⟩)

/-- PROVED. P0088 page 11, Case 1: the block coefficient of display 52 at n is the
sum over the divisors r of n of the convolution b_r. -/
theorem coeff1_eq (z1 z0 M D : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ p ∈ ((Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧
        z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ n)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      ∑ d ∈ ((n / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < z1)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ r ∈ n.divisors, bC z1 z0 M D r := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have s1 : ∀ p ∈ ((Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧
        z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ n)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      (∑ d ∈ ((n / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < z1)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      ∑ r ∈ n.divisors.filter (fun r : ℕ => p ∣ r), amD z1 D (r / p) := by
    intro p hp
    obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpr, -, -, hpn⟩ := Finset.mem_filter.mp hp1
    have hp0 : 0 < p := hpr.pos
    rw [Finset.filter_filter, Finset.sum_filter]
    refine Finset.sum_nbij' (fun d => p * d) (fun r => r / p) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, dvd_mul_right p d⟩
      exact (Nat.dvd_div_iff_mul_dvd hpn).mp hd'.1
    · intro r hr
      obtain ⟨hr1, hpr'⟩ := Finset.mem_filter.mp hr
      have hr1' := Nat.mem_divisors.mp hr1
      refine Nat.mem_divisors.mpr ⟨?_, (Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp0).ne'⟩
      obtain ⟨c, rfl⟩ := hpr'
      rw [Nat.mul_div_cancel_left c hp0]
      exact (Nat.dvd_div_iff_mul_dvd hpn).mpr hr1'.1
    · intro d _
      exact Nat.mul_div_cancel_left d hp0
    · intro r hr
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hr).2
    · intro d _
      simp only [Nat.mul_div_cancel_left d hp0]
      unfold amD
      rfl
  rw [Finset.sum_congr rfl s1]
  unfold bC primeSet
  refine Finset.sum_comm' fun p r => ?_
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨-, hpr, hz1, hz0, hpn⟩, hM1, hM2⟩, ⟨hrn, -⟩, hpr'⟩
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrn hn0
    exact ⟨⟨⟨Nat.lt_succ_of_le (Nat.le_of_dvd hr0 hpr'), hpr, hz1, hz0, hpr'⟩, hM1, hM2⟩,
      hrn, hn⟩
  · rintro ⟨⟨⟨-, hpr, hz1, hz0, hpr'⟩, hM1, hM2⟩, hrn, -⟩
    have hpn : p ∣ n := dvd_trans hpr' hrn
    exact ⟨⟨⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn0 hpn), hpr, hz1, hz0, hpn⟩, hM1, hM2⟩,
      ⟨hrn, hn⟩, hpr'⟩


/-- PROVED. b_r vanishes outside M D at most r below 4 M D. -/
theorem bC_support (z1 z0 M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D) (r : ℕ)
    (h : bC z1 z0 M D r ≠ 0) : M * D ≤ (r : ℝ) ∧ (r : ℝ) < 2 * (2 * (M * D)) := by
  unfold bC at h
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  unfold primeSet at hp
  obtain ⟨hp1, hM1, hM2⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, -, -, -, hpr⟩ := Finset.mem_filter.mp hp1
  have hc : (∀ r' : ℕ, r'.Prime → r' ∣ r / p → (r' : ℝ) < z1) ∧
      (D ≤ ((r / p : ℕ) : ℝ) ∧ ((r / p : ℕ) : ℝ) < 2 * D) := by
    by_contra hc
    exact hne (by unfold amD; rw [if_neg hc])
  have hr : (r : ℝ) = (p : ℝ) * ((r / p : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hpr]
  rw [hr]
  obtain ⟨-, hD1, hD2⟩ := hc
  constructor
  · exact mul_le_mul hM1 hD1 hD (le_trans hM hM1)
  · calc (p : ℝ) * ((r / p : ℕ) : ℝ) < (2 * M) * (2 * D) :=
          mul_lt_mul'' hM2 hD2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = 2 * (2 * (M * D)) := by ring

/-- PROVED. The sum of b_r over the divisors r of n is the sum over the two dyadic
blocks M D and 2 M D. -/
theorem coeff1_split (z1 z0 M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D) (n : ℕ) :
    ∑ r ∈ n.divisors, bC z1 z0 M D r =
      ∑ r ∈ n.divisors.filter (fun r : ℕ => r ∈ (Finset.range (⌊2 * (M * D)⌋₊ + 1)).filter (fun m : ℕ => M * D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (M * D))), bC z1 z0 M D r +
      ∑ r ∈ n.divisors.filter (fun r : ℕ => r ∈ (Finset.range (⌊2 * (2 * (M * D))⌋₊ + 1)).filter (fun m : ℕ => 2 * (M * D) ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (2 * (M * D)))), bC z1 z0 M D r := by
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors
    (fun r : ℕ => r ∈ (Finset.range (⌊2 * (M * D)⌋₊ + 1)).filter (fun m : ℕ => M * D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (M * D)))]
  congr 1
  refine (Finset.sum_subset ?_ ?_).symm
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
    refine ⟨hr.1, ?_⟩
    intro h
    linarith [h.2.2, hr.2.2.1]
  · intro r hr hr2
    by_contra hne
    obtain ⟨h1, h2⟩ := bC_support z1 z0 M D hM hD r hne
    simp only [Finset.mem_filter, Finset.mem_range, not_and, not_lt] at hr hr2
    obtain ⟨hrd, hr1⟩ := hr
    have hge : 2 * (M * D) ≤ (r : ℝ) := by
      by_contra hlt
      push Not at hlt
      exact absurd (hr1 (Nat.lt_succ_of_le (Nat.le_floor (by linarith))) h1) (not_le.mpr hlt)
    exact absurd h2 (not_lt.mpr (hr2 hrd (Nat.lt_succ_of_le (Nat.le_floor (by linarith))) hge))

theorem norm_add_sq_le2 (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_add_le u v
  have h2 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- PROVED. Case 1 on t: the windowless n sum of display 52 is the sum of the two
dyadic pieces in r. -/
theorem integrand1 {x H t z1 z0 M D α : ℝ} (hx : 0 < x) (hHx : H ≤ x) (ht : x ≤ t)
    (ht2 : t ≤ 2 * x) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    (∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ p ∈ ((Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧
          z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ n)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        ∑ d ∈ ((n / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
            (r : ℝ) < z1)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
    (∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (M * D)⌋₊ + 1)).filter (fun m : ℕ => M * D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (M * D))), bC z1 z0 M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) + (∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (2 * (M * D))⌋₊ + 1)).filter (fun m : ℕ => 2 * (M * D) ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (2 * (M * D)))), bC z1 z0 M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H := by
    simp only [Finset.mem_filter] at hn
    exact hn.2
  have hn0 := (Prep1122KLLemma31Cases.window_n_bound hx hHx ht ht2 n hn').1
  rw [coeff1_eq z1 z0 M D n hn0, coeff1_split z1 z0 M D hM hD n, add_mul]

/-- PROVED. One dyadic piece in the double sum form of Lemma 3.1. -/
theorem piece_eq {x H t z1 z0 M D α E : ℝ} (hx : 0 < x) (hHx : H ≤ x) (ht : x ≤ t)
    (ht2 : t ≤ 2 * x) (hE : 0 < E) :
    (∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * E⌋₊ + 1)).filter
          (fun m : ℕ => E ≤ (m : ℝ) ∧ (m : ℝ) < 2 * E)), bC z1 z0 M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
    ∑ m ∈ (Finset.range (⌊2 * E⌋₊ + 1)).filter
        (fun m : ℕ => E ≤ (m : ℝ) ∧ (m : ℝ) < 2 * E),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + H),
      bC z1 z0 M D m * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  have hR : ∀ r ∈ (Finset.range (⌊2 * E⌋₊ + 1)).filter
      (fun m : ℕ => E ≤ (m : ℝ) ∧ (m : ℝ) < 2 * E), r ≠ 0 := by
    intro r hr
    obtain ⟨_, hDr, _⟩ := Finset.mem_filter.mp hr
    rintro rfl
    norm_num at hDr
    linarith
  have e := Prep1122KLLemma31Cases.reindex_mul ((Finset.range (⌊2 * E⌋₊ + 1)).filter
      (fun m : ℕ => E ≤ (m : ℝ) ∧ (m : ℝ) < 2 * E)) ⌊Real.sqrt (3 * x)⌋₊
    (bC z1 z0 M D) (fun n : ℕ => fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))
    (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H) hR
    (fun n hn => Prep1122KLLemma31Cases.window_n_bound hx hHx ht ht2 n hn)
  refine Eq.trans ?_ (e.symm.trans ?_)
  · refine Finset.sum_congr (by ext n; simp only [Finset.mem_filter]) fun n _ => ?_
    congr 1
  · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr ?_ fun k _ => rfl
    ext k
    simp only [Finset.mem_filter]

/-- PROVED. P0088 page 11, Case 2: on t in x to 2x, the windowed sum in the
variable n is the double sum of Lemma 3.2 with am = amC z1 on the block D and
bk = bkC. -/
theorem integrand2 {x H t z1 z0 M D α : ℝ} (hx : 0 < x) (hHx : H ≤ x) (ht : x ≤ t)
    (ht2 : t ≤ 2 * x) (hD : 0 < D) :
    (∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ p ∈ ((Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧
          z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ n)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        ∑ d ∈ ((n / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
            (r : ℝ) < z1)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
    ∑ m ∈ (Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + H),
      amC z1 m * bkC z1 z0 M k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  have hR : ∀ r ∈ (Finset.range (⌊2 * D⌋₊ + 1)).filter
      (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D), r ≠ 0 := by
    intro r hr
    obtain ⟨_, hDr, _⟩ := Finset.mem_filter.mp hr
    rintro rfl
    norm_num at hDr
    linarith
  have e := reindex2 ((Finset.range (⌊2 * D⌋₊ + 1)).filter
      (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D)) ⌊Real.sqrt (3 * x)⌋₊
    (amC z1) (bkC z1 z0 M) (fun n : ℕ => fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))
    (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H) hR
    (fun n hn => Prep1122KLLemma31Cases.window_n_bound hx hHx ht ht2 n hn)
  refine Eq.trans ?_ (e.symm.trans ?_)
  · refine Finset.sum_congr (by ext n; simp only [Finset.mem_filter]) fun n hn => ?_
    have hn' : t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H := by
      simp only [Finset.mem_filter] at hn
      exact hn.2
    have hn0 := (Prep1122KLLemma31Cases.window_n_bound hx hHx ht ht2 n hn').1
    rw [coeff_eq z1 z0 M D n hn0]
  · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr ?_ fun k _ => rfl
    ext k
    simp only [Finset.mem_filter]

theorem case2_interior_of_lemma32 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, Real.log X ^ B < D →
        D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
        (∫ t in windowY X ε / 4..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, hlem⟩ := Prep1122KLLemma31Cases.lemma32 A 1 hA one_pos
  refine ⟨max B1 1, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hB)
  obtain ⟨C, x0, hC, -, hL⟩ := hlem B hBB1
  obtain ⟨X1, hX1, hbig⟩ := Split1122KLLemma34M1.block_large_X B ε x0 hBpos hε (by linarith)
  refine ⟨2 * (C * 2 ^ A), X1, by positivity, hX1, ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD1 hD2
  obtain ⟨hL1, hP2, hgap, hhalf, hx0⟩ := hbig X hX
  have hX2 : 2 ≤ X := hX1.trans hX
  have hYge : X ^ (7 / 12 : ℝ) ≤ windowY X ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hYX : windowY X ε ≤ X := by
    have : windowY X ε ≤ X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rwa [Real.rpow_one] at this
  have hLX : 0 < Real.log X := by linarith
  have hPB : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hLX B
  have hD0 : 0 < D := hPB.trans hD1
  have key : ∀ x : ℝ, windowY X ε / 4 ≤ x → x ≤ windowY X ε / 2 →
      (∫ t in x..2 * x,
          ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (x))⌋₊ + 1)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ C * 2 ^ A * H ^ 2 / Real.log X ^ A := by
    intro x hx1 hx2
    obtain ⟨hsx, hHx, hq1, hq2, hdir, -, -, -, -, hlx0, hlogx⟩ :=
      Split1122KLLemma34M1.block_hyps B ε X H x 0 α q a hBpos hε (by linarith) hX2 hL1 hP2
        hgap hhalf hlo hhi hqP hqQ hclose (Real.rpow_nonneg hY0.le _) hx1 (by linarith)
    have hx0' : 0 < x := by linarith
    have hlxX : Real.log x ≤ Real.log X := Real.log_le_log hx0' (by linarith)
    have hPx : Real.log x ^ B ≤ Real.log X ^ B := Real.rpow_le_rpow hlx0.le hlxX hBpos.le
    have hPx0 : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hlx0 B
    have hDlo : Real.log x ^ B ≤ D := by linarith
    have hDhi : D ≤ H / Real.sqrt x / Real.log x ^ B := by
      rw [div_div]
      refine hD2.trans (div_le_div_of_nonneg_left (by linarith [Real.sqrt_nonneg x])
        (mul_pos (Real.sqrt_pos.mpr hx0') hPx0)
        (mul_le_mul (Real.sqrt_le_sqrt (by linarith)) hPx hPx0.le (Real.sqrt_nonneg _)))
    have hmain := hL x H (by linarith) hsx hHx α q a hcop hq1 hq2 hdir
      (amC (windowY X ε ^ (1 / 6 + ε / 2))) (bkC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M)
      (fun m hm => amC_bound _ m hm) (fun k hk => bkC_bound _ _ _ k hk) D hDlo hDhi
    refine le_trans (le_of_eq ?_) (hmain.trans
      (Split1122KLLemma34M1.log_saving_conv C H _ _ A hC.le hA hLX hlx0 hlogx))
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [integrand2 hx0' hHx ht.1 ht.2 hD0]
  obtain ⟨-, -, -, -, -, -, hsY, hH4, -, -, -⟩ :=
    Split1122KLLemma34M1.block_hyps B ε X H (windowY X ε / 4) 0 α q a hBpos hε (by linarith)
      hX2 hL1 hP2 hgap hhalf hlo hhi hqP hqQ hclose (Real.rpow_nonneg hY0.le _) le_rfl
      (by linarith)
  have hH0 : 0 < H := lt_of_lt_of_le (Real.sqrt_pos.mpr hY0) hsY
  have hint := fun (S : Finset ℕ) (u v : ℝ) => short_sum_sq_intervalIntegrable S
      (fun m : ℕ => (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H u v
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (squareWindow (windowY X ε)) (windowY X ε / 4) (windowY X ε / 2))
    (hint (squareWindow (windowY X ε)) (windowY X ε / 2) (windowY X ε - 2 * H))]
  have k1 := key (windowY X ε / 4) le_rfl (by linarith)
  rw [show 2 * (windowY X ε / 4) = windowY X ε / 2 by ring] at k1
  have k2 := key (windowY X ε / 2) (by linarith) le_rfl
  rw [show 2 * (windowY X ε / 2) = windowY X ε by ring] at k2
  have p1 : (∫ t in windowY X ε / 4..windowY X ε / 2,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ C * 2 ^ A * H ^ 2 / Real.log X ^ A := by
    refine le_trans (le_of_eq ?_) k1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [Split1122KLLemma34M1.window_filter_eq (windowY X ε) (windowY X ε / 4) t H le_rfl ht.1
      (by linarith [ht.2]) hH4 (by linarith [ht.2])]
  have p2 : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ C * 2 ^ A * H ^ 2 / Real.log X ^ A := by
    have hc : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) = (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
          ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (windowY X ε / 2))⌋₊ + 1)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [Split1122KLLemma34M1.window_filter_eq (windowY X ε) (windowY X ε / 2) t H
        (by linarith) ht.1 (by linarith [ht.2]) (by linarith) (by linarith [ht.2])]
    rw [hc]
    refine le_trans ?_ k2
    exact intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => by simp only [Pi.zero_apply]; positivity))
      (hint _ _ _)
  have e : 2 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A =
      C * 2 ^ A * H ^ 2 / Real.log X ^ A + C * 2 ^ A * H ^ 2 / Real.log X ^ A := by ring
  rw [e]
  exact add_le_add p1 p2

example : type_of% @SecondDyadicCases1122.case2_interior := case2_interior_of_lemma32


set_option maxHeartbeats 1000000 in
theorem case1_interior_of_lemma31 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, hlem⟩ := Prep1122KLLemma31Cases.lemma31 A 1 hA one_pos
  refine ⟨max (2 * B1) 1, lt_max_of_lt_right one_pos, fun B hB ε hε hε' => ?_⟩
  have hBB1 : B1 ≤ B / 2 := by linarith [le_max_left (2 * B1) 1]
  have hBpos : 0 < B := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hB)
  obtain ⟨C, x0, hC, -, hL⟩ := hlem (B / 2) hBB1
  obtain ⟨X1, hX1, hbig⟩ := Split1122KLLemma34M1.block_large_X B ε x0 hBpos hε (by linarith)
  obtain ⟨X2, -, hbig2⟩ := Split1122KLLemma34M1.block_large_X (B / 4) ε 0 (by linarith) hε
    (by linarith)
  refine ⟨8 * (C * 2 ^ A), max X1 X2, by positivity, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD1 hD2
  obtain ⟨hL1, hP2, hgap, hhalf, hx0⟩ := hbig X ((le_max_left _ _).trans hX)
  obtain ⟨-, hQ2, -, -, -⟩ := hbig2 X ((le_max_right _ _).trans hX)
  have hX2 : 2 ≤ X := hX1.trans ((le_max_left _ _).trans hX)
  have hYge : X ^ (7 / 12 : ℝ) ≤ windowY X ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hYX : windowY X ε ≤ X := by
    have : windowY X ε ≤ X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rwa [Real.rpow_one] at this
  have hLX : 0 < Real.log X := by linarith
  have hPB : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hLX B
  have hQ : Real.log X ^ (B / 2) = Real.log X ^ (B / 4) * Real.log X ^ (B / 4) := by
    rw [← Real.rpow_add hLX]; ring_nf
  have hPQ : Real.log X ^ B = Real.log X ^ (B / 2) * Real.log X ^ (B / 2) := by
    rw [← Real.rpow_add hLX]; ring_nf
  have hQ4 : 4 ≤ Real.log X ^ (B / 2) := by
    rw [hQ]
    have := mul_le_mul hQ2 hQ2 (by norm_num) (by linarith)
    linarith
  have hQ0 : 0 < Real.log X ^ (B / 2) := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hy4 : 0 < windowY X ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hY0 _
  have hw : (Real.log X ^ B) ^ (-2 : ℤ) * (Real.log X ^ B * Real.log X ^ B) = 1 := by
    rw [zpow_neg, zpow_two]; field_simp
  have hMP : M * Real.log X ^ B * Real.log X ^ B < windowY X ε ^ (1 / 4 : ℝ) := by
    have := mul_lt_mul_of_pos_right htop (mul_pos hPB hPB)
    calc M * Real.log X ^ B * Real.log X ^ B = M * (Real.log X ^ B * Real.log X ^ B) := by ring
      _ < _ := this
      _ = windowY X ε ^ (1 / 4 : ℝ) *
          ((Real.log X ^ B) ^ (-2 : ℤ) * (Real.log X ^ B * Real.log X ^ B)) := by ring
      _ = _ := by rw [hw, mul_one]
  have key : ∀ x : ℝ, windowY X ε / 4 ≤ x → x ≤ windowY X ε / 2 →
      (∫ t in x..2 * x,
          ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (x))⌋₊ + 1)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ 4 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A := by
    intro x hx1 hx2
    obtain ⟨hsx, hHx, hq1, hq2, hdir, -, -, -, -, hlx0, hlogx⟩ :=
      Split1122KLLemma34M1.block_hyps B ε X H x 0 α q a hBpos hε (by linarith) hX2 hL1 hP2
        hgap hhalf hlo hhi hqP hqQ hclose (Real.rpow_nonneg hY0.le _) hx1 (by linarith)
    have hx0' : 0 < x := by linarith
    have hH0 : 0 ≤ H := le_trans (Real.sqrt_nonneg x) hsx
    have hlxX : Real.log x ≤ Real.log X := Real.log_le_log hx0' (by linarith)
    have hPx : Real.log x ^ (B / 2) ≤ Real.log X ^ (B / 2) :=
      Real.rpow_le_rpow hlx0.le hlxX (by linarith)
    have hPhalf : Real.log X ^ (B / 2) ≤ Real.log X ^ B := by
      rw [hPQ]; exact le_mul_of_one_le_right hQ0.le (by linarith)
    have hPx0 : 0 < Real.log x ^ (B / 2) := Real.rpow_pos_of_pos hlx0 _
    have hq1' : Real.log x ^ (B / 2) ≤ (q : ℝ) := (hPx.trans hPhalf).trans hqP.le
    have hq2' : (q : ℝ) ≤ H / Real.log x ^ (B / 2) :=
      hqQ.trans (div_le_div_of_nonneg_left hH0 hPx0 (hPx.trans hPhalf))
    have hx4 : windowY X ε ^ (1 / 4 : ℝ) / 2 ≤ x ^ (1 / 4 : ℝ) := by
      have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      have := Real.rpow_le_rpow (by positivity) (show windowY X ε / 16 ≤ x by linarith)
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [Real.div_rpow hY0.le (by norm_num), h16] at this
    have hMD : 2 * (M * D) ≤ x ^ (1 / 4 : ℝ) / Real.log x ^ (B / 2) := by
      rw [le_div_iff₀ hPx0]
      have a1 : M * D ≤ M * Real.log X ^ B := mul_le_mul_of_nonneg_left hD2 hM0
      have a2 : 2 * (M * D) * Real.log x ^ (B / 2) ≤
          2 * (M * Real.log X ^ B) * Real.log X ^ (B / 2) :=
        mul_le_mul (by linarith) hPx hPx0.le (by positivity)
      have a3 : 4 * Real.log X ^ (B / 2) ≤ Real.log X ^ B := by
        rw [hPQ]; exact mul_le_mul_of_nonneg_right hQ4 hQ0.le
      have a4 : 2 * (M * Real.log X ^ B) * Real.log X ^ (B / 2) * 4 ≤
          2 * (M * Real.log X ^ B) * Real.log X ^ B := by
        have h0 : 0 ≤ 2 * (M * Real.log X ^ B) := by positivity
        have := mul_le_mul_of_nonneg_left a3 h0
        linarith
      linarith
    have hMD1 : 1 ≤ M * D := one_le_mul_of_one_le_of_one_le hM hD1
    have hm1 := hL x H (by linarith) hsx hHx α q a hcop hq1' hq2' hdir
      (bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D) (fun m hm => bC_bound _ _ _ _ m hm) (M * D) hMD1
      (by linarith)
    have hm2 := hL x H (by linarith) hsx hHx α q a hcop hq1' hq2' hdir
      (bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D) (fun m hm => bC_bound _ _ _ _ m hm) (2 * (M * D))
      (by linarith) hMD
    have i0 := short_sum_sq_intervalIntegrable (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)) (fun m : ℕ => (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H x (2 * x)
    have i1 := short_sum_sq_intervalIntegrable (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)) (fun n : ℕ => (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (M * D)⌋₊ + 1)).filter (fun m : ℕ => M * D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (M * D))),
        bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) * fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H x (2 * x)
    have i2 := short_sum_sq_intervalIntegrable (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)) (fun n : ℕ => (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (2 * (M * D))⌋₊ + 1)).filter (fun m : ℕ => 2 * (M * D) ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (2 * (M * D)))),
        bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) * fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H x (2 * x)
    have hMDp : 0 < M * D := by linarith
    have b1 : (∫ t in x..2 * x, ‖(∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (M * D)⌋₊ + 1)).filter (fun m : ℕ => M * D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (M * D))), bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))‖ ^ 2) ≤ C * 2 ^ A * H ^ 2 / Real.log X ^ A := by
      refine le_trans (le_of_eq ?_) (hm1.trans
        (Split1122KLLemma34M1.log_saving_conv C H _ _ A hC.le hA hLX hlx0 hlogx))
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      beta_reduce
      rw [piece_eq hx0' hHx ht.1 ht.2 hMDp]
    have b2 : (∫ t in x..2 * x, ‖(∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (2 * (M * D))⌋₊ + 1)).filter (fun m : ℕ => 2 * (M * D) ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (2 * (M * D)))), bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))‖ ^ 2) ≤ C * 2 ^ A * H ^ 2 / Real.log X ^ A := by
      refine le_trans (le_of_eq ?_) (hm2.trans
        (Split1122KLLemma34M1.log_saving_conv C H _ _ A hC.le hA hLX hlx0 hlogx))
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      beta_reduce
      rw [piece_eq hx0' hHx ht.1 ht.2 (by linarith)]
    calc _ ≤ ∫ t in x..2 * x, (2 * ‖(∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (M * D)⌋₊ + 1)).filter (fun m : ℕ => M * D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (M * D))), bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))‖ ^ 2 +
          2 * ‖(∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (2 * (M * D))⌋₊ + 1)).filter (fun m : ℕ => 2 * (M * D) ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (2 * (M * D)))), bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))‖ ^ 2) :=
          intervalIntegral.integral_mono_on (by linarith) i0
            ((i1.const_mul 2).add (i2.const_mul 2)) (fun t ht => by
              beta_reduce
              rw [integrand1 hx0' hHx ht.1 ht.2 hM0 hD0]
              exact norm_add_sq_le2 _ _)
      _ = 2 * (∫ t in x..2 * x, ‖(∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (M * D)⌋₊ + 1)).filter (fun m : ℕ => M * D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (M * D))), bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))‖ ^ 2) + 2 * (∫ t in x..2 * x, ‖(∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
      (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ (Finset.range (⌊2 * (2 * (M * D))⌋₊ + 1)).filter (fun m : ℕ => 2 * (M * D) ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (2 * (M * D)))), bC (windowY X ε ^ (1 / 6 + ε / 2)) (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M D d) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))‖ ^ 2) := by
          rw [intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ 2 * (C * 2 ^ A * H ^ 2 / Real.log X ^ A) + 2 * (C * 2 ^ A * H ^ 2 / Real.log X ^ A) :=
          add_le_add (mul_le_mul_of_nonneg_left b1 (by norm_num))
            (mul_le_mul_of_nonneg_left b2 (by norm_num))
      _ = 4 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A := by ring
  obtain ⟨-, -, -, -, -, -, hsY, hH4, -, -, -⟩ :=
    Split1122KLLemma34M1.block_hyps B ε X H (windowY X ε / 4) 0 α q a hBpos hε (by linarith)
      hX2 hL1 hP2 hgap hhalf hlo hhi hqP hqQ hclose (Real.rpow_nonneg hY0.le _) le_rfl
      (by linarith)
  have hH0 : 0 < H := lt_of_lt_of_le (Real.sqrt_pos.mpr hY0) hsY
  have hint := fun (S : Finset ℕ) (u v : ℝ) => short_sum_sq_intervalIntegrable S
      (fun m : ℕ => (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H u v
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (squareWindow (windowY X ε)) (windowY X ε / 4) (windowY X ε / 2))
    (hint (squareWindow (windowY X ε)) (windowY X ε / 2) (windowY X ε - 2 * H))]
  have k1 := key (windowY X ε / 4) le_rfl (by linarith)
  rw [show 2 * (windowY X ε / 4) = windowY X ε / 2 by ring] at k1
  have k2 := key (windowY X ε / 2) (by linarith) le_rfl
  rw [show 2 * (windowY X ε / 2) = windowY X ε by ring] at k2
  have p1 : (∫ t in windowY X ε / 4..windowY X ε / 2,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ 4 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A := by
    refine le_trans (le_of_eq ?_) k1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [Split1122KLLemma34M1.window_filter_eq (windowY X ε) (windowY X ε / 4) t H le_rfl ht.1
      (by linarith [ht.2]) hH4 (by linarith [ht.2])]
  have p2 : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ 4 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A := by
    have hc : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) = (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
          ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (windowY X ε / 2))⌋₊ + 1)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [Split1122KLLemma34M1.window_filter_eq (windowY X ε) (windowY X ε / 2) t H
        (by linarith) ht.1 (by linarith [ht.2]) (by linarith) (by linarith [ht.2])]
    rw [hc]
    refine le_trans ?_ k2
    exact intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => by simp only [Pi.zero_apply]; positivity))
      (hint _ _ _)
  have e : 8 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A =
      4 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A + 4 * (C * 2 ^ A) * H ^ 2 / Real.log X ^ A := by
    ring
  rw [e]
  exact add_le_add p1 p2

example : type_of% @SecondDyadicCases1122.case1_interior := case1_interior_of_lemma31

end LeanLab.KumchevLiu2007.SecondDyadicInterior1122

#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.amC_bound
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.bkC_bound
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.coeff_eq
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.reindex2
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.bC_bound
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.coeff1_eq
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.integrand2
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.case2_interior_of_lemma32
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.bC_support
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.coeff1_split
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.integrand1
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.piece_eq
#print axioms LeanLab.KumchevLiu2007.SecondDyadicInterior1122.case1_interior_of_lemma31
