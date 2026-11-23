/-
BURST 2026-11-22, session S39, unit P1122-0141, second step. Splits the leaf
Prep1122KLRoughLemma34.lemma34_unit, Lemma 3.4 of P0088 page 11 in the case
M = 1 and a_1 = 1, along the proof printed on pages 11 and 12. Kumchev and Liu
2007, P0088, arXiv 0801.0130.

* moebius_rough, PROVED: the first display of the proof, Phi of k and z
  is the sum of mu of d over the divisors d of k that divide Pi of z.
* case_one, case_two, case_three, LEAF HARD: display 42 for one dyadic range
  d at least D and below 2D, in the three cases of pages 11 and 12, D at most
  L^B, D from L^B to y x^(-1/2) L^(-B), and D at least y x^(-1/2) L^(-B). The
  sum over m and k of display 42 with M = 1 is written with n = kd, so the
  coefficient of e of alpha n^2 is the sum of mu of d over the admissible
  divisors d of n. CITED-LEFT: case one is Lemma 3.1, case two is Lemma 3.2,
  case three is Lemma 3.3 followed by Lemma 3.2; the paper omits the proofs
  of Lemmas 3.1 and 3.2 and cites Kumchev reference 14, and cites Lemma 3.3
  to Kumchev reference 12 Lemma 2.7.
* lemma34_unit_of_cases, no sorry of its own: the exact statement of
  lemma34_unit. The divisors are cut into J dyadic ranges, J at most 3 log x,
  and Cauchy's inequality costs J^2, paid for by taking A + 2 in the cases.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34

namespace LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED. P0088 page 11, first display of the proof of Lemma 3.4, with Phi of
k and z from page 4 display 10: for k at least 1, Phi of k and z is the sum of
mu of d over the divisors d of k with d dividing Pi of z, the product of the
primes below z; d divides Pi of z exactly when d is squarefree with every prime
factor below z. Class MEDIUM, proved here. -/
theorem moebius_rough (z : ℝ) {k : ℕ} (hk : k ≠ 0) :
    roughWeight z k = ∑ d ∈ k.divisors.filter
        (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = k.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = ∏ p ∈ P, p := ⟨_, rfl⟩
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => by
    rw [hP] at hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => (hPprime p hp).ne_zero
  have hgpf : g.primeFactors = P := by
    rw [hg]
    exact Nat.primeFactors_prod hPprime
  have hgk : g ∣ k := by
    rw [hg, hP]
    exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd k)
  have hsub : k.divisors.filter
      (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z) ⊆ g.divisors := by
    intro d hd
    obtain ⟨hdk, hsq, hpz⟩ := Finset.mem_filter.mp hd
    rw [Nat.mem_divisors] at hdk ⊢
    refine ⟨?_, hg0⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq, hg]
    refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    rw [hP]
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hdk.1, hk⟩,
      hpz p hpp hpd⟩
  have hsum : ∑ d ∈ k.divisors.filter
      (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
        (ArithmeticFunction.moebius d : ℤ) =
      ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℤ) := by
    refine Finset.sum_subset hsub fun d hdg hdS => ?_
    by_contra hne
    apply hdS
    have hsq : Squarefree d := by
      by_contra hns
      exact hne (ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns)
    have hdg' := Nat.mem_divisors.mp hdg
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdg'.1.trans hgk, hk⟩, hsq,
      fun p hp hpd => ?_⟩
    have hpg : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdg'.1, hg0⟩
    rw [hgpf, hP] at hpg
    exact (Finset.mem_filter.mp hpg).2
  have hmob : ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℤ) = if g = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ => f g)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    exact h
  have hiff : g = 1 ↔ ∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ) := by
    constructor
    · intro h1 p hp hpk
      by_contra hlt
      push_neg at hlt
      have hpP : p ∈ P := by
        rw [hP]
        exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpk, hk⟩, hlt⟩
      have hpg : p ∣ g := by
        rw [hg]
        exact Finset.dvd_prod_of_mem _ hpP
      rw [h1] at hpg
      exact hp.not_dvd_one hpg
    · intro h
      have hPe : P = ∅ := by
        rw [hP, Finset.filter_eq_empty_iff]
        intro p hp hlt
        have hpk := Nat.mem_primeFactors.mp hp
        exact absurd (h p hpk.1 hpk.2.1) (not_le.mpr hlt)
      rw [hg, hPe, Finset.prod_empty]
  rw [← Int.cast_sum, hsum, hmob]
  unfold roughWeight
  by_cases hc : ∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ)
  · rw [if_pos hc, if_pos (hiff.mpr hc)]
    simp
  · rw [if_neg hc, if_neg (mt hiff.mp hc)]
    simp

/-- LEAF: P0088 page 11, display 42 in Case 1, D at most L^B, for M = 1 and
a_1 = 1, with n = kd. The paper derives it from Lemma 3.1 with the convolution
b_r of the sum of a_m mu of d over dm = r, d near D, d dividing Pi of z. Class
HARD. CITED-LEFT on Lemma 3.1, proof omitted in the paper, Kumchev reference 14. -/
theorem case_one (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log x ^ B →
        (∫ t in x..2 * x,
          ‖∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
            fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  sorry

/-- LEAF: P0088 page 11, display 42 in Case 2, D from L^B to y x^(-1/2) L^(-B),
for M = 1 and a_1 = 1, with n = kd. The paper derives it from Lemma 3.2 with the
coefficients mu of d on d near D, d dividing Pi of z, and b_r = 1. Class HARD.
CITED-LEFT on Lemma 3.2, proof omitted in the paper, Kumchev reference 14. -/
theorem case_two (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        ∀ D : ℝ, Real.log x ^ B ≤ D → D ≤ y / Real.sqrt x / Real.log x ^ B →
        (∫ t in x..2 * x,
          ‖∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
            fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  sorry

/-- LEAF: P0088 pages 11 and 12, display 42 in Case 3, D at least
V = y x^(-1/2) L^(-B), for M = 1 and a_1 = 1, with n = kd. The paper factors
d = p1 ... pr, picks the unique s with L^B at most z^(-1) V at most p1 ... ps at
most V at most p1 ... ps+1, removes the conditions p' below p, pp'd1d2 near D
and d1pp' at least V by Lemma 3.3, and ends with Lemma 3.2 in u = mkp'd2 and
v = pd1. Class HARD. CITED-LEFT on Lemma 3.3, Kumchev reference 12 Lemma 2.7,
and on Lemma 3.2, proof omitted in the paper, Kumchev reference 14. -/
theorem case_three (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        ∀ D : ℝ, y / Real.sqrt x / Real.log x ^ B ≤ D →
        (∫ t in x..2 * x,
          ‖∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
            fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  sorry

/-- Parameter step of P0088 page 11: for x at least 3 there is J at most 3 log x
with x below 2^J, the number of dyadic ranges of d. -/
theorem dyadic_count {x : ℝ} (hx : 3 ≤ x) :
    ∃ J : ℕ, x < (2 : ℝ) ^ J ∧ (J : ℝ) ≤ 3 * Real.log x := by
  have hX1 : 1 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  refine ⟨⌊Real.logb 2 x⌋₊ + 1, ?_, ?_⟩
  · have h1 : Real.logb 2 x < ((⌊Real.logb 2 x⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at h2
  · push_cast
    have hlb : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hX1.le
    have h1 : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := Nat.floor_le hlb
    have h2 : Real.logb 2 x ≤ 2 * Real.log x := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith [Real.log_two_gt_d9]
    linarith

/-- P0088 page 11: every divisor d of an n in the sum is positive and below 2^J
when x is below 2^J, since n is at most the square root of 3x, at most x. -/
theorem divisor_lt_pow {x : ℝ} (hx : 3 ≤ x) {J n d : ℕ} (hJ : x < (2 : ℝ) ^ J)
    (hn : n < ⌊Real.sqrt (3 * x)⌋₊ + 1) (hn0 : n ≠ 0) (hd : d ∈ n.divisors) :
    d ≠ 0 ∧ d < 2 ^ J := by
  have hdn : d ≤ n := Nat.divisor_le hd
  refine ⟨(Nat.pos_of_mem_divisors hd).ne', ?_⟩
  have h1 : (n : ℝ) ≤ Real.sqrt (3 * x) :=
    (Nat.cast_le.mpr (Nat.le_of_lt_succ hn)).trans (Nat.floor_le (Real.sqrt_nonneg _))
  have h2 : Real.sqrt (3 * x) ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h3 : (d : ℝ) < (2 : ℝ) ^ J :=
    lt_of_le_of_lt ((Nat.cast_le.mpr hdn).trans (h1.trans h2)) hJ
  exact_mod_cast h3

set_option maxHeartbeats 800000 in
/-- The exact statement of Prep1122KLRoughLemma34.lemma34_unit, from moebius_rough
and the three cases with A + 2, by the dyadic cut of d. No sorry of its own. -/
theorem lemma34_unit_of_cases (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        (∫ t in x..2 * x,
          ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
            roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  obtain ⟨B1, hB1, h1⟩ := case_one (A + 2) (by linarith)
  obtain ⟨B2, hB2, h2⟩ := case_two (A + 2) (by linarith)
  obtain ⟨B3, hB3, h3⟩ := case_three (A + 2) (by linarith)
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, fun B hB => ?_⟩
  obtain ⟨C1, x1, hC1, hx1, k1⟩ := h1 B ((le_max_left _ _).trans hB)
  obtain ⟨C2, x2, hC2, hx2, k2⟩ :=
    h2 B (((le_max_left _ _).trans (le_max_right _ _)).trans hB)
  obtain ⟨C3, x3, hC3, hx3, k3⟩ :=
    h3 B (((le_max_right _ _).trans (le_max_right _ _)).trans hB)
  refine ⟨9 * max C1 (max C2 C3), max (max x1 (max x2 x3)) 3,
    by positivity, hx1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro x y hx hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz
  have hxa : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxb : x2 ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx
  have hxc : x3 ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  obtain ⟨J, hJ1, hJ2⟩ := dyadic_count hx3
  -- the Moebius expansion and the dyadic cut, inside the integral
  have hrw : (∫ t in x..2 * x,
      ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
          (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
        roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      ∫ t in x..2 * x,
      ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
          (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
        (∑ j ∈ Finset.range J, ∑ d ∈ (k.divisors.filter
            (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    refine congrArg (fun s : ℂ => ‖s‖ ^ 2) (Finset.sum_congr rfl fun k hk => ?_)
    obtain ⟨hkr, hkt, _⟩ := Finset.mem_filter.mp hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : (0 : ℝ) < t := lt_of_lt_of_le hx0 ht.1
      norm_num at hkt
      linarith
    rw [moebius_rough z hk0, dyadic_partition _ J _ fun d hd =>
      divisor_lt_pow hx3 hJ1 (Finset.mem_range.mp hkr) hk0 (Finset.mem_filter.mp hd).1]
  rw [hrw]
  have hLA2 : 0 < Real.log x ^ (A + 2) := Real.rpow_pos_of_pos hL _
  have hmax : ∀ c : ℝ, c ≤ max C1 (max C2 C3) →
      c * y ^ 2 / Real.log x ^ (A + 2) ≤ max C1 (max C2 C3) * y ^ 2 / Real.log x ^ (A + 2) :=
    fun c hc => (div_le_div_iff_of_pos_right hLA2).mpr
      (mul_le_mul_of_nonneg_right hc (sq_nonneg y))
  refine (dyadic_mean_square_le ((Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1))) J
    (fun j k => ∑ d ∈ (k.divisors.filter
        (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (fun k : ℕ => (fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    y x (2 * x) (max C1 (max C2 C3) * y ^ 2 / Real.log x ^ (A + 2)) (by linarith)
    (fun j _ => ?_)).trans ?_
  · have hD : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    by_cases c1 : (2 : ℝ) ^ j ≤ Real.log x ^ B
    · exact (k1 x y hxa hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz _ hD c1).trans
        (hmax C1 (le_max_left _ _))
    by_cases c2 : (2 : ℝ) ^ j ≤ y / Real.sqrt x / Real.log x ^ B
    · exact (k2 x y hxb hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz _
        (le_of_lt (not_le.mp c1)) c2).trans
        (hmax C2 ((le_max_left _ _).trans (le_max_right _ _)))
    · exact (k3 x y hxc hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz _
        (le_of_lt (not_le.mp c2))).trans
        (hmax C3 ((le_max_right _ _).trans (le_max_right _ _)))
  · have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL A
    have hpow : Real.log x ^ (A + 2) = Real.log x ^ A * Real.log x ^ 2 := by
      rw [Real.rpow_add hL, Real.rpow_two]
    rw [hpow]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log x ^ 2 := by nlinarith
    have hK : 0 ≤ max C1 (max C2 C3) * y ^ 2 / (Real.log x ^ A * Real.log x ^ 2) :=
      div_nonneg (mul_nonneg (hC1.le.trans (le_max_left _ _)) (sq_nonneg y))
        (mul_pos hLA (pow_pos hL 2)).le
    calc
      _ ≤ 9 * Real.log x ^ 2 *
          (max C1 (max C2 C3) * y ^ 2 / (Real.log x ^ A * Real.log x ^ 2)) :=
        mul_le_mul_of_nonneg_right hJsq hK
      _ = 9 * max C1 (max C2 C3) * y ^ 2 / Real.log x ^ A := by
        field_simp

example : type_of% @Prep1122KLRoughLemma34.lemma34_unit := lemma34_unit_of_cases

end LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases

#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases.moebius_rough
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases.dyadic_count
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases.divisor_lt_pow
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases.lemma34_unit_of_cases
