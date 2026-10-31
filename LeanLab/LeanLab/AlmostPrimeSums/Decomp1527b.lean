/-
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176. Unit U-1527, run 20261025T2003Z-426, type
DECOMPOSE, file b of three.

The linear sieve machinery behind Chen's theorem, part 2: Rosser's weights of level `D` with
`β = 2` (Iwaniec-Kowalski (6.30), Section 6.4; Friedlander-Iwaniec, Opera de Cribro, ch. 6 and
11), the upper and lower bound sieve inequalities they satisfy, the remainder bookkeeping, the
Jurkat-Richert / Iwaniec main term bounds with `F(s)`, `f(s)` (Iwaniec-Kowalski Theorem 11.13,
Halberstam-Richert ch. 8 Theorem 8.3 and 8.4), and the fundamental lemma (Iwaniec-Kowalski
Lemma 6.3 and Theorem 6.9). Sieve problems are Mathlib's `BoundingSieve`
(`Mathlib/NumberTheory/SelbergSieve.lean`): `X = totalMass`, `g = nu`, `r_d = rem d`,
`S(A, P) = siftedSum`, `V = ∏_{p ∣ P} (1 - g(p))`.

The two main-term leaves `jr_mainSum_upper`, `jr_mainSum_lower` are the deep ones; the
assemblies `jr_upper`, `jr_lower` derive the Jurkat-Richert sieve bounds from the leaves with
no sorry of their own.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.AlmostPrimeSums.Decomp1527a
import LeanLab.PNTSieve.BrunBlocksRel

namespace LeanLab.AlmostPrimeSums.Decomp1527b
open Finset Real ArithmeticFunction BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a
open LeanLab.PNTSieve.Bonferroni
attribute [local instance] Classical.propDecidable

/-- The prime factors of `d` in decreasing order `p₁ > p₂ > ⋯ > p_r`. -/
noncomputable def decPrimes (d : ℕ) : List ℕ := d.primeFactors.sort (· ≥ ·)

/-- Rosser's weights with `β = 2` and level `D`: `λ_d = μ(d)` if `d = p₁⋯p_r` is squarefree,
`p₁ > ⋯ > p_r`, and `p₁⋯p_{m-1} p_m³ < D` for every `m` odd (upper, `upper = true`) or every
`m` even (lower, `upper = false`); else `0`. In the code `m` is 0-indexed, so "odd `m`" is
`m % 2 = 0`. Iwaniec-Kowalski (6.30). -/
noncomputable def rosserWeight (D : ℝ) (upper : Bool) (d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ m < (decPrimes d).length, (upper = true ↔ m % 2 = 0) →
      (((decPrimes d).take m).prod : ℝ) * ((decPrimes d).getD m 0 : ℝ) ^ 3 < D
  then (ArithmeticFunction.moebius d : ℝ) else 0

/-- The linear sieve density condition `Ω₁(K)`: for `2 ≤ w < w'`,
`∏_{p ∣ P, w ≤ p < w'} (1 - g(p))⁻¹ ≤ (log w'/log w)(1 + K/log w)`.
Iwaniec-Kowalski (6.34) with `κ = 1`; Halberstam-Richert `(Ω₂(1))`, `(Ω₂(κ))` p. 142. -/
def LinearDensity (s : BoundingSieve) (K : ℝ) : Prop :=
  ∀ w w' : ℝ, 2 ≤ w → w < w' →
    ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'),
      (1 - s.nu p)⁻¹ ≤ log w' / log w * (1 + K / log w)

/-- The density condition bounds each local inverse factor by its limiting
short interval bound. Derived from IK equation 6.34 and HR p. 142. -/
theorem linearDensity_prime_factor_bound (s : BoundingSieve) (K : ℝ) (hK : 0 ≤ K) (h : LinearDensity s K)
    {p : ℕ} (hp : p ∈ s.prodPrimes.primeFactors) :
    (1 - s.nu p)⁻¹ ≤ 1 + K / Real.log (p : ℝ) := by
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
  have hplog : 0 < Real.log (p : ℝ) := log_pos (by linarith)
  have hnu0 := s.nu_pos_of_prime p hpprime hpd
  have hnu1 := s.nu_lt_one_of_prime p hpprime hpd
  let A : ℝ := (1 - s.nu p)⁻¹
  let B : ℝ := 1 + K / Real.log (p : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  by_contra hc
  have hBA : B < A := lt_of_not_ge hc
  let t : ℝ := (A / B + 1) / 2
  have ht : 1 < t := by
    have hab : 1 < A / B := (lt_div_iff₀ hB).mpr (by simpa using hBA)
    dsimp [t]
    linarith
  have htB : t * B < A := by
    have he : t * B = (A + B) / 2 := by dsimp [t]; field_simp
    rw [he]
    linarith
  let w : ℝ := exp (Real.log (p : ℝ) * t)
  have hpw : (p : ℝ) < w := by
    calc
      (p : ℝ) = exp (Real.log (p : ℝ)) := (exp_log (by linarith)).symm
      _ < w := exp_lt_exp.mpr (by nlinarith)
  have hden := h (p : ℝ) w hp2 hpw
  have hmem : p ∈ s.prodPrimes.primeFactors.filter (fun q : ℕ => (p : ℝ) ≤ q ∧ (q : ℝ) < w) :=
    Finset.mem_filter.mpr ⟨hp, le_rfl, hpw⟩
  have hfactor : A ≤ ∏ q ∈ s.prodPrimes.primeFactors.filter
      (fun q : ℕ => (p : ℝ) ≤ q ∧ (q : ℝ) < w), (1 - s.nu q)⁻¹ := by
    have hfac : ∀ q ∈ s.prodPrimes.primeFactors.filter
        (fun q : ℕ => (p : ℝ) ≤ q ∧ (q : ℝ) < w), 1 ≤ (1 - s.nu q)⁻¹ := by
      intro q hq
      have hqmem := (Finset.mem_filter.mp hq).1
      have hqprime := Nat.prime_of_mem_primeFactors hqmem
      have hqd := Nat.dvd_of_mem_primeFactors hqmem
      apply (one_le_inv₀ (by linarith [s.nu_lt_one_of_prime q hqprime hqd])).mpr
      linarith [s.nu_pos_of_prime q hqprime hqd]
    rw [← Finset.mul_prod_erase _ _ hmem]
    have hrest : 1 ≤ ∏ q ∈ (s.prodPrimes.primeFactors.filter
        (fun q : ℕ => (p : ℝ) ≤ q ∧ (q : ℝ) < w)).erase p, (1 - s.nu q)⁻¹ :=
      by simpa only [Finset.prod_const_one] using
        (Finset.prod_le_prod₀ (fun _ _ => (show (0 : ℝ) ≤ 1 by norm_num))
          (fun q hq => hfac q (Finset.mem_of_mem_erase hq)))
    have ha : 0 ≤ A := by dsimp [A]; positivity
    change A ≤ A * _
    nlinarith
  have hratio : log w / Real.log (p : ℝ) * (1 + K / Real.log (p : ℝ)) = t * B := by
    dsimp [w, B]
    rw [log_exp]
    field_simp
  rw [hratio] at hden
  exact (not_lt_of_ge (hfactor.trans hden)) htB

/-- The density condition at K equal to zero permits no sifting primes.
Derived boundary case of IK equation 6.34 and HR p. 142. -/
theorem linearDensity_zero_prodPrimes (s : BoundingSieve) (h : LinearDensity s 0) : s.prodPrimes = 1 := by
  have hempty : s.prodPrimes.primeFactors = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hbound := linearDensity_prime_factor_bound s 0 le_rfl h hp
    simp only [zero_div, add_zero] at hbound
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hnu0 := s.nu_pos_of_prime p hprime hpd
    have hnu1 := s.nu_lt_one_of_prime p hprime hpd
    have hh := (inv_le_one₀ (by linarith : 0 < 1 - s.nu p)).mp hbound
    linarith
  have hh := Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree
  simpa only [hempty, Finset.prod_empty] using hh.symm

/-- Taking logarithms of the density product bounds the sum of local densities
on a prime interval. Derived block input from IK equation 6.34 and HR p. 142. -/
theorem linearDensity_interval_sum (s : BoundingSieve) (K : ℝ) (hK : 0 ≤ K) (h : LinearDensity s K)
    (w w' : ℝ) (hw : 2 ≤ w) (hww' : w < w') :
    ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'), s.nu p ≤
      Real.log (Real.log w' / Real.log w) + K / Real.log w := by
  let Q := s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w')
  have hfac : ∀ p ∈ Q, 0 < 1 - s.nu p := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    exact sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp')
      (Nat.dvd_of_mem_primeFactors hp'))
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlw' : 0 < Real.log w' := Real.log_pos (by linarith)
  have hratio : 0 < Real.log w' / Real.log w := div_pos hlw' hlw
  have hfactor : 0 < 1 + K / Real.log w := by positivity
  calc
    (∑ p ∈ Q, s.nu p) ≤ ∑ p ∈ Q, Real.log (1 - s.nu p)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Real.log_inv]
      have hh := Real.log_le_sub_one_of_pos (hfac p hp)
      linarith
    _ = Real.log (∏ p ∈ Q, (1 - s.nu p)⁻¹) :=
      (Real.log_prod (fun p hp => inv_ne_zero (ne_of_gt (hfac p hp)))).symm
    _ ≤ Real.log (Real.log w' / Real.log w * (1 + K / Real.log w)) := by
      apply Real.log_le_log (Finset.prod_pos fun p hp => inv_pos.mpr (hfac p hp))
      exact h w w' hw hww'
    _ = Real.log (Real.log w' / Real.log w) + Real.log (1 + K / Real.log w) :=
      Real.log_mul hratio.ne' hfactor.ne'
    _ ≤ Real.log (Real.log w' / Real.log w) + K / Real.log w := by
      have hh := Real.log_le_sub_one_of_pos hfactor
      linarith

/-- `|λ_d| ≤ 1` for Rosser's weights. -/
theorem abs_rosserWeight_le_one (D : ℝ) (b : Bool) (d : ℕ) : |rosserWeight D b d| ≤ 1 := by
  unfold rosserWeight
  split_ifs
  · exact_mod_cast abs_moebius_le_one
  · simp

/-- Adding a new least prime appends it to the decreasing factor list.
Derived first exit bookkeeping for IK equations 6.24 to 6.30 and BJS p. 10 equation 28. -/
theorem decPrimes_mul_smallest {d p : ℕ} (hd : Squarefree d) (hp : p.Prime)
    (hmin : ∀ q ∈ d.primeFactors, p < q) :
    decPrimes (d * p) = decPrimes d ++ [p] := by
  have hnot : p ∉ d.primeFactors := by intro h; exact (lt_irrefl p) (hmin p h)
  have hnodup : (decPrimes d ++ [p]).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.sort_nodup _ _, by simp, ?_⟩
    intro a ha b hb hab
    have hbp : b = p := by simpa using hb
    subst b
    subst a
    exact hnot (by simpa [decPrimes] using ha)
  have hpair : (decPrimes d ++ [p]).Pairwise (· ≥ ·) := by
    simp only [List.pairwise_append, List.pairwise_singleton, true_and ]
    refine ⟨Finset.pairwise_sort _ _, ?_⟩
    intro q hq r hr
    have : r = p := by simpa using hr
    subst r
    exact (hmin q (by simpa [decPrimes] using hq)).le
  have hset : (decPrimes d ++ [p]).toFinset = (d * p).primeFactors := by
    simp [decPrimes, Nat.primeFactors_mul hd.ne_zero hp.ne_zero, hp.primeFactors]
  change (d * p).primeFactors.sort (· ≥ ·) = _
  rw [← hset]
  exact (List.toFinset_sort (· ≥ ·) hnodup).mpr hpair

/-- Pair squarefree divisors by adding or removing a fixed prime divisor.
Derived finite cancellation for IK equations 6.24 to 6.27 and BJS p. 10 equation 28. -/
theorem sum_divisors_pair_of_squarefree_support (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n)
    (f : ℕ → ℝ) (hf : ∀ d, ¬Squarefree d → f d = 0) :
    ∑ d ∈ n.divisors, f d =
      ∑ d ∈ n.divisors.filter (fun d => ¬p ∣ d), (f d + f (d * p)) := by
  classical
  have hid : ∑ d ∈ n.divisors.filter (fun d => p ∣ d), f d =
      ∑ d ∈ n.divisors.filter (fun d => ¬p ∣ d), f (d * p) := by
    apply Finset.sum_bij_ne_zero (fun d _ _ => d / p)
    · intro d hd hfd
      obtain ⟨hdn, hpd⟩ := Finset.mem_filter.mp hd
      have hsq : Squarefree d := by by_contra h; exact hfd (hf d h)
      have hcop : (d / p).Coprime p := Nat.coprime_of_squarefree_mul (by
        rwa [Nat.div_mul_cancel hpd])
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨(Nat.div_dvd_of_dvd hpd).trans (Nat.mem_divisors.mp hdn).1, hn⟩,
        hp.coprime_iff_not_dvd.mp hcop.symm⟩
    · intro a ha hfa b hb hfb hab
      have hpa := (Finset.mem_filter.mp ha).2
      have hpb := (Finset.mem_filter.mp hb).2
      calc
        a = a / p * p := (Nat.div_mul_cancel hpa).symm
        _ = b / p * p := by rw [hab]
        _ = b := Nat.div_mul_cancel hpb
    · intro d hd hfd
      obtain ⟨hdn, hpd⟩ := Finset.mem_filter.mp hd
      have hcop := (hp.coprime_iff_not_dvd.mpr hpd).symm
      have hdp : d * p ∈ n.divisors.filter (fun x => p ∣ x) := by
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨hcop.mul_dvd_of_dvd_of_dvd (Nat.mem_divisors.mp hdn).1 hpn, hn⟩,
          dvd_mul_left p d⟩
      exact ⟨d * p, hdp, hfd, Nat.mul_div_cancel d hp.pos⟩
    · intro d hd hfd
      rw [Nat.div_mul_cancel (Finset.mem_filter.mp hd).2]
  rw [Finset.sum_add_distrib, ← hid]
  exact (Finset.sum_filter_add_sum_filter_not n.divisors (fun d => p ∣ d) f).symm.trans
    (add_comm _ _)

/-- Appending the least prime adds only the last cutoff condition.
Derived first exit bookkeeping for IK equation 6.30 and BJS p. 10 equation 28. -/
theorem rosserWeight_mul_smallest (D : ℝ) (b : Bool) {d p : ℕ} (hd : Squarefree d) (hp : p.Prime)
    (hmin : ∀ q ∈ d.primeFactors, p < q) :
    rosserWeight D b (d * p) =
      if ((b = true ↔ (decPrimes d).length % 2 = 0) → (d : ℝ) * (p : ℝ) ^ 3 < D)
      then -rosserWeight D b d else 0 := by
  have hnot : ¬p ∣ d := by
    intro hpd
    exact (lt_irrefl p) (hmin p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd.ne_zero⟩))
  have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hnot).symm
  have hdp : Squarefree (d * p) := (Nat.squarefree_mul_iff.mpr ⟨hcop, hd, hp.squarefree⟩)
  have hmu : (moebius (d * p) : ℝ) = -(moebius d : ℝ) := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]
    push_cast
    ring
  have hprod : (decPrimes d).prod = d := by
    exact (Finset.sort_perm_toList _ _).prod_eq.trans
      ((Finset.prod_toList _).trans (Nat.prod_primeFactors_of_squarefree hd))
  let A : List ℕ → Prop := fun l => ∀ m < l.length,
    (b = true ↔ m % 2 = 0) → ((l.take m).prod : ℝ) * (l.getD m 0 : ℝ) ^ 3 < D
  have hiff : A (decPrimes d ++ [p]) ↔ A (decPrimes d) ∧
      ((b = true ↔ (decPrimes d).length % 2 = 0) → (d : ℝ) * (p : ℝ) ^ 3 < D) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro m hm hb
        have hh := h m (by simp; omega) hb
        simpa only [List.take_append_of_le_length hm.le, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hm] using hh
      · intro hb
        have hh := h (decPrimes d).length (by simp) hb
        simpa [List.take_left, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), hprod] using hh
    · rintro ⟨h, hc⟩ m hm hb
      by_cases hml : m < (decPrimes d).length
      · simpa only [List.take_append_of_le_length hml.le, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hml] using h m hml hb
      · have he : m = (decPrimes d).length := by simp only [List.length_append, List.length_singleton] at hm; omega
        subst m
        simpa [List.take_left, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), hprod] using hc hb
  change (if Squarefree (d * p) ∧ A (decPrimes (d * p)) then (moebius (d * p) : ℝ) else 0) =
    if _ then -(if Squarefree d ∧ A (decPrimes d) then (moebius d : ℝ) else 0) else 0
  simp only [decPrimes_mul_smallest hd hp hmin, hiff, hmu]
  by_cases ha : A (decPrimes d) <;>
    by_cases hc : ((b = true ↔ (decPrimes d).length % 2 = 0) → (d : ℝ) * (p : ℝ) ^ 3 < D) <;>
    simp [hdp, hd, ha, hc]

/-- Each least prime pair has nonnegative upper sum and nonpositive lower sum.
Derived cancellation for IK equations 6.24 to 6.30 and BJS p. 10 equation 28. -/
theorem rosserWeight_smallest_pair_sign (D : ℝ) {d p : ℕ} (hp : p.Prime)
    (hmin : ∀ q ∈ d.primeFactors, p < q) :
    0 ≤ rosserWeight D true d + rosserWeight D true (d * p) ∧
    rosserWeight D false d + rosserWeight D false (d * p) ≤ 0 := by
  by_cases hd : Squarefree d
  · have hcard : cardFactors d = (decPrimes d).length := by
      have hh := (cardDistinctFactors_eq_cardFactors_iff_squarefree hd.ne_zero).mpr hd
      rw [← hh]
      simp only [decPrimes, Finset.length_sort, ← Nat.toFinset_factors,
        List.card_toFinset, cardDistinctFactors_apply]
    have hmu : (moebius d : ℝ) = (-1 : ℝ) ^ (decPrimes d).length := by
      rw [moebius_apply_of_squarefree hd]
      push_cast
      rw [hcard]
    rw [rosserWeight_mul_smallest D true hd hp hmin,
      rosserWeight_mul_smallest D false hd hp hmin]
    by_cases heven : (decPrimes d).length % 2 = 0
    · have hmu1 : (moebius d : ℝ) = 1 := by
        rw [hmu, neg_one_pow_eq_pow_mod_two, heven, pow_zero]
      simp only [heven, Bool.false_eq_true, false_iff, not_true_eq_false,
        false_implies, ite_true, add_neg_cancel, le_refl, and_true]
      split_ifs
      · simp
      · have hw : 0 ≤ rosserWeight D true d := by
          unfold rosserWeight
          split_ifs <;> simp_all
        simpa using hw
    · have hodd : (decPrimes d).length % 2 = 1 := by omega
      have hmu1 : (moebius d : ℝ) = -1 := by
        rw [hmu, neg_one_pow_eq_pow_mod_two, hodd, pow_one]
      simp only [true_iff, heven, Bool.false_eq_true,
        false_implies, ite_true, add_neg_cancel, le_refl, true_and]
      split_ifs
      · simp
      · have hw : rosserWeight D false d ≤ 0 := by
          unfold rosserWeight
          split_ifs <;> simp_all
        simpa using hw
  · have hdp : ¬Squarefree (d * p) := fun hh => hd (hh.squarefree_of_dvd (dvd_mul_right d p))
    simp [rosserWeight, hd, hdp]

/-- LEAF. Rosser's upper weights are an upper bound sieve: `Σ_{d ∣ n} λ⁺_d ≥ [n = 1]` for all
`n`. Proof: the support is closed under deleting the smallest prime, so
`Σ_{d∣n} μ(d) = Σ_{d∣n} λ⁺_d − Σ_{b first exit} [b ∣ n][(n/b, P(p_r)) = 1]`, every first
exit `b = p₁⋯p_r` has `r` odd and `μ(b) = −1`. Iwaniec-Kowalski (6.24) to (6.27) and Section 6.4.
Unit U-1527. -/
theorem rosser_upper_isUpperMoebius (D : ℝ) : IsUpperMoebius (rosserWeight D true) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp [rosserWeight, decPrimes]
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  rw [sum_divisors_pair_of_squarefree_support n n.minFac hn0 hp
    (Nat.minFac_dvd n) _ (fun d hd => by simp [rosserWeight, hd])]
  rw [ite_eq_right hn1]
  apply Finset.sum_nonneg
  intro d hd
  obtain ⟨hdn, hpd⟩ := Finset.mem_filter.mp hd
  apply (rosserWeight_smallest_pair_sign D hp ?_).1
  intro q hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hqn := (Nat.dvd_of_mem_primeFactors hq).trans (Nat.mem_divisors.mp hdn).1
  have hle := Nat.minFac_le_of_dvd hqprime.two_le hqn
  have hne : n.minFac ≠ q := by
    intro he
    exact hpd (he ▸ Nat.dvd_of_mem_primeFactors hq)
  exact lt_of_le_of_ne hle hne

/-- LEAF. Rosser's lower weights are a lower bound sieve: `Σ_{d ∣ n} λ⁻_d ≤ [n = 1]` for all
`n`; first exits have `r` even and `μ(b) = +1`. Iwaniec-Kowalski (6.24) to (6.27) and
Section 6.4. Unit U-1527. -/
theorem rosser_lower_le (D : ℝ) (n : ℕ) :
    ∑ d ∈ n.divisors, rosserWeight D false d ≤ if n = 1 then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp [rosserWeight, decPrimes]
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  rw [sum_divisors_pair_of_squarefree_support n n.minFac hn0 hp
    (Nat.minFac_dvd n) _ (fun d hd => by simp [rosserWeight, hd])]
  rw [ite_eq_right hn1]
  apply Finset.sum_nonpos
  intro d hd
  obtain ⟨hdn, hpd⟩ := Finset.mem_filter.mp hd
  apply (rosserWeight_smallest_pair_sign D hp ?_).2
  intro q hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hqn := (Nat.dvd_of_mem_primeFactors hq).trans (Nat.mem_divisors.mp hdn).1
  have hle := Nat.minFac_le_of_dvd hqprime.two_le hqn
  have hne : n.minFac ≠ q := by
    intro he
    exact hpd (he ▸ Nat.dvd_of_mem_primeFactors hq)
  exact lt_of_le_of_ne hle hne

/-- LEAF. Lower bound sieve inequality, the mirror of Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius`: if `Σ_{d∣n} λ_d ≤ [n=1]` for all `n` then
`S ≥ X Σ_{d∣P} λ_d g(d) − Σ_{d∣P} |λ_d||r_d|`. Iwaniec-Kowalski (6.17), (6.18).
Unit U-1527. -/
theorem siftedSum_ge_of_lower (s : BoundingSieve) (lam : ℕ → ℝ)
    (h : ∀ n : ℕ, ∑ d ∈ n.divisors, lam d ≤ if n = 1 then 1 else 0) :
    s.totalMass * s.mainSum lam - s.errSum lam ≤ s.siftedSum := by
  have hsum : (∑ d ∈ s.prodPrimes.divisors, lam d * s.multSum d) ≤ s.siftedSum := by
    calc
      (∑ d ∈ s.prodPrimes.divisors, lam d * s.multSum d) =
          ∑ n ∈ s.support, s.weights n *
            ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, lam d := by
        calc
          _ = ∑ n ∈ s.support, ∑ d ∈ s.prodPrimes.divisors,
                if d ∣ n then s.weights n * lam d else 0 := by
            rw [Finset.sum_comm]
            simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, Finset.mul_sum, mul_comm]
          _ = _ := by
            simp_rw [Finset.mul_sum, ← Finset.sum_filter]
            congr with n
            congr 1
            rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
              (Nat.gcd_dvd_left _ _)]
            ext x
            simp +contextual [Nat.dvd_gcd_iff]
      _ ≤ s.siftedSum := by
        rw [s.siftedSum_eq_sum_support_mul_ite]
        exact Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_left (h _) (s.weights_nonneg n)
  have herr : -s.errSum lam ≤ ∑ d ∈ s.prodPrimes.divisors, lam d * s.rem d := by
    rw [BoundingSieve.errSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← abs_mul]
    exact neg_abs_le _
  have hid : (∑ d ∈ s.prodPrimes.divisors, lam d * s.multSum d) =
      s.totalMass * s.mainSum lam + ∑ d ∈ s.prodPrimes.divisors, lam d * s.rem d := by
    rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr with d
    rw [BoundingSieve.rem]
    ring
  linarith

/-- A decreasing positive list has product at most a prefix product times the cube
of its next entry when at most two entries remain. Derived support bookkeeping
for BJS arXiv 2207.09452 p. 10 equation 28 and IK Section 6.4. -/
theorem prod_le_prefix_cube (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) (m : ℕ)
    (hm : m < l.length) (hnear : l.length ≤ m + 2)
    (hpos : ∀ p ∈ l, 1 ≤ p) :
    l.prod ≤ (l.take m).prod * (l.getD m 0) ^ 3 := by
  have hlen : (l.drop m).length = l.length - m := List.length_drop
  have hsorted : (l.drop m).Pairwise (· ≥ ·) := hl.drop
  have hget : (l.drop m).headD 0 = l.getD m 0 := by
    rw [List.drop_eq_getElem_cons hm]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  have hbnd : (l.drop m).prod ≤ (l.getD m 0) ^ 3 := by
    rcases hd : l.drop m with _ | ⟨p, t⟩
    · simp [hd] at hlen
      omega
    · rw [hd] at hlen hsorted hget
      have hp : 1 ≤ p := hpos p (List.mem_of_mem_drop (by rw [hd]; simp))
      have hmax : ∀ x ∈ p :: t, x ≤ p := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact (List.pairwise_cons.mp hsorted).1 x hx
      calc
        (p :: t).prod ≤ p ^ (p :: t).length := List.prod_le_pow_length _ _ hmax
        _ ≤ p ^ 3 := Nat.pow_le_pow_right hp (by simp only [List.length_cons] at hlen ⊢; omega)
        _ = _ := by simpa only [List.headD_cons] using congrArg (fun x : ℕ => x ^ 3) hget
  calc
    l.prod = (l.take m).prod * (l.drop m).prod := (List.prod_take_mul_prod_drop _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hbnd

/-- LEAF. Support of Rosser's weights: for `D > 1`, `λ^±_d ≠ 0` implies `d < D` or `d` prime
(only the lower weights reach the primes `p ≥ D^{1/3}`). For `r ≥ 2` use the condition at the
last or second to last index and `p_r < p_{r-1}`. Iwaniec-Kowalski Section 6.4, below (6.30).
Unit U-1527. -/
theorem rosserWeight_support (D : ℝ) (hD : 1 < D) (b : Bool) (d : ℕ)
    (h : rosserWeight D b d ≠ 0) : (d : ℝ) < D ∨ d.Prime := by
  have hadm : Squarefree d ∧ ∀ m < (decPrimes d).length,
      (b = true ↔ m % 2 = 0) →
      (((decPrimes d).take m).prod : ℝ) * ((decPrimes d).getD m 0 : ℝ) ^ 3 < D := by
    by_contra hh
    exact h (by unfold rosserWeight; rw [ite_eq_right hh])
  have hprod : (decPrimes d).prod = d := by
    calc
      _ = ∏ p ∈ d.primeFactors, p := by
        exact (Finset.sort_perm_toList _ _).prod_eq.trans (by simp)
      _ = d := Nat.prod_primeFactors_of_squarefree hadm.1
  by_cases hlen : 2 ≤ (decPrimes d).length
  · obtain ⟨m, hm, hnear, hpar⟩ : ∃ m : ℕ,
        m < (decPrimes d).length ∧ (decPrimes d).length ≤ m + 2 ∧
        (b = true ↔ m % 2 = 0) := by
      cases b <;> by_cases heven : ((decPrimes d).length - 1) % 2 = 0
      · exact ⟨(decPrimes d).length - 2, by omega, by omega, by simp; omega⟩
      · exact ⟨(decPrimes d).length - 1, by omega, by omega, by simp; omega⟩
      · exact ⟨(decPrimes d).length - 1, by omega, by omega, by simp; omega⟩
      · exact ⟨(decPrimes d).length - 2, by omega, by omega, by simp; omega⟩
    have hbnd := prod_le_prefix_cube (decPrimes d)
      (Finset.pairwise_sort _ _) m hm hnear (by
        intro p hp
        exact (Nat.prime_of_mem_primeFactors (by simpa [decPrimes] using hp)).one_lt.le)
    left
    have hbndR : (d : ℝ) ≤ (((decPrimes d).take m).prod : ℝ) *
        ((decPrimes d).getD m 0 : ℝ) ^ 3 := by
      exact_mod_cast (hprod ▸ hbnd)
    exact hbndR.trans_lt (hadm.2 m hm hpar)
  · rcases hl : decPrimes d with _ | ⟨p, t⟩
    · left
      have hd : d = 1 := by simpa [hl] using hprod.symm
      simpa [hd] using hD
    · have ht : t = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [hl, List.length_cons] at hlen
        omega
      subst t
      right
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (by
        have : p ∈ decPrimes d := by simp [hl]
        simpa [decPrimes] using this)
      have hd : d = p := by simpa [hl] using hprod.symm
      simpa [hd] using hp

/-- LEAF. Remainder bookkeeping: if every prime of `P` is `< z ≤ D`, then
`Σ_{d∣P} |λ^±_d||r_d| ≤ Σ_{d∣P, d<D} |r_d|`, by `rosserWeight_support` and `|λ| ≤ 1`.
Iwaniec-Kowalski (6.18), Theorem 11.13 remainder `R(D)`. Unit U-1527. -/
theorem errSum_rosser_le (s : BoundingSieve) (z D : ℝ) (hzD : z ≤ D) (hD : 1 < D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (b : Bool) :
    s.errSum (rosserWeight D b) ≤
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
  have hs_errSum : s.errSum (rosserWeight D b) = ∑ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d| := rfl
  rw [hs_errSum]
  have H : ∀ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d| ≤ if (d : ℝ) < D then |s.rem d| else 0 := by
    intro d hd
    by_cases hdD : (d : ℝ) < D
    · rw [ite_eq_left_iff.mpr (fun hh => False.elim (hh hdD))]
      have := abs_rosserWeight_le_one D b d
      nlinarith [abs_nonneg (s.rem d)]
    · rw [ite_eq_right_iff.mpr (fun hh => False.elim (hdD hh))]
      have h1 : rosserWeight D b d = 0 := by
        by_contra hc
        have := rosserWeight_support D hD b d hc
        rcases this with h_lt | h_prime
        · exact hdD h_lt
        · have hd_primeFactors : d ∈ s.prodPrimes.primeFactors := by
            rw [Nat.mem_primeFactors]
            exact ⟨h_prime, Nat.mem_divisors.mp hd |>.1, fun hh => by
              have hhh := s.prodPrimes_squarefree
              rw [hh] at hhh
              exact not_squarefree_zero hhh⟩
          have h_z := hP d hd_primeFactors
          linarith
      rw [h1]
      simp
  calc ∑ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d|
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) < D then |s.rem d| else 0 := Finset.sum_le_sum (fun d hd => H d hd)
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
      rw [Finset.sum_filter]

/-- Below D divided by z squared, no Rosser cutoff removes a coefficient whose
prime factors are at most z. Derived tail localization for IK equation 6.30
and BJS p. 10 equation 28. -/
theorem rosserWeight_eq_moebius_of_small (D z : ℝ) (hz : 0 ≤ z) (b : Bool) {d : ℕ}
    (hP : ∀ p ∈ d.primeFactors, (p : ℝ) ≤ z) (hsmall : (d : ℝ) * z ^ 2 < D) :
    rosserWeight D b d = (moebius d : ℝ) := by
  by_cases hd : Squarefree d
  · have hprod : (decPrimes d).prod = d := by
      exact (Finset.sort_perm_toList _ _).prod_eq.trans
        ((Finset.prod_toList _).trans (Nat.prod_primeFactors_of_squarefree hd))
    have hpos : ∀ p ∈ decPrimes d, 1 ≤ p := by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors (by simpa [decPrimes] using hp)).one_lt.le
    have hadm : ∀ m < (decPrimes d).length, (b = true ↔ m % 2 = 0) →
        (((decPrimes d).take m).prod : ℝ) * ((decPrimes d).getD m 0 : ℝ) ^ 3 < D := by
      intro m hm _
      have hprefix : ((decPrimes d).take (m + 1)).prod ≤ d := by
        exact ((List.take_sublist (m + 1) (decPrimes d)).prod_le_prod hpos).trans_eq hprod
      rw [List.prod_take_succ _ _ hm, ← List.getD_eq_getElem _ 0 hm] at hprefix
      have hprefixR : (((decPrimes d).take m).prod : ℝ) *
          ((decPrimes d).getD m 0 : ℝ) ≤ d := by exact_mod_cast hprefix
      have hpz : ((decPrimes d).getD m 0 : ℝ) ≤ z := by
        apply hP
        have hh : (decPrimes d).getD m 0 ∈ decPrimes d := by
          rw [List.getD_eq_getElem _ 0 hm]
          exact List.getElem_mem hm
        simpa [decPrimes] using hh
      have hpn : (0 : ℝ) ≤ (decPrimes d).getD m 0 := Nat.cast_nonneg _
      have hsq : ((decPrimes d).getD m 0 : ℝ) ^ 2 ≤ z ^ 2 := by nlinarith
      calc
        _ = ((((decPrimes d).take m).prod : ℝ) * ((decPrimes d).getD m 0 : ℝ)) *
              ((decPrimes d).getD m 0 : ℝ) ^ 2 := by ring
        _ ≤ (d : ℝ) * z ^ 2 := mul_le_mul hprefixR hsq (sq_nonneg _) (Nat.cast_nonneg _)
        _ < D := hsmall
    unfold rosserWeight
    exact ite_eq_left ⟨hd, hadm⟩
  · simp [rosserWeight, hd, moebius_eq_zero_of_not_squarefree hd]

/-- Discarding cancellation bounds the Rosser main term error by a positive
large divisor tail. This bound alone is weaker than the required uniform relative
error. Derived localization for IK equation 6.30 and BJS p. 10 equation 28. -/
theorem rosser_mainSum_error_le_tail (s : BoundingSieve) (z D : ℝ) (hz : 0 ≤ z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (b : Bool) :
    |s.mainSum (rosserWeight D b) - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => D ≤ (d : ℝ) * z ^ 2), s.nu d := by
  have hmu : s.mainSum (fun d => (moebius d : ℝ)) =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      s.nu s.nu_mult s.prodPrimes_squarefree).symm
  rw [← hmu, BoundingSieve.mainSum, BoundingSieve.mainSum, ← Finset.sum_sub_distrib,
    Finset.sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hdp := (Nat.mem_divisors.mp hd).1
  have hnu := s.nu_pos_of_dvd_prodPrimes hdp
  by_cases htail : D ≤ (d : ℝ) * z ^ 2
  · rw [ite_eq_left htail, ← sub_mul, abs_mul, abs_of_pos hnu]
    apply mul_le_of_le_one_left hnu.le
    have hdiff : |rosserWeight D b d - (moebius d : ℝ)| ≤ 1 := by
      unfold rosserWeight
      split_ifs
      · simp
      · simpa using (show |(moebius d : ℝ)| ≤ 1 by exact_mod_cast abs_moebius_le_one)
    exact hdiff
  · rw [ite_eq_right htail]
    have heq := rosserWeight_eq_moebius_of_small D z hz b
      (fun p hp => (hP p (Nat.primeFactors_mono hdp s.prodPrimes_ne_zero hp)).le)
      (lt_of_not_ge htail)
    rw [heq]
    simp

/-- A fixed positive error cannot be absorbed in a logarithmically decaying
error with a uniform constant. This records a limitation of using BJS p. 5
Theorem 6 at a fixed epsilon for the target main term estimate. It asserts no
paper error. Mathlib logarithm and power limits prove the obstruction. -/
theorem fixed_error_not_log_decay (eps : ℝ) (heps : 0 < eps) :
    ¬∃ C : ℝ, ∀ D : ℝ, 2 ≤ D → eps ≤ C * Real.log D ^ (-(1 / 3 : ℝ)) := by
  rintro ⟨C, hC⟩
  have hp : Filter.Tendsto (fun D : ℝ => Real.log D ^ (-(1 / 3 : ℝ))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp Real.tendsto_log_atTop
  have ht : Filter.Tendsto (fun D : ℝ => C * Real.log D ^ (-(1 / 3 : ℝ))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul hp
  obtain ⟨D, hD, hlt⟩ := ((Filter.eventually_ge_atTop (2 : ℝ)).and
    (ht.eventually_lt_const heps)).exists
  exact (not_lt_of_ge (hC D hD)) hlt

/-- The upper main term estimate at K equal to zero follows from the empty
prime set and the proved upper sieve function bound. Boundary case of the
linear sieve estimate on BJS p. 5 equation 5. -/
theorem jr_mainSum_upper_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s 0 →
      s.mainSum (rosserWeight D true) ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))) := by
  refine ⟨1, by norm_num, ?_⟩
  intro s z D hz hzD hDz hP hden
  have hprod := linearDensity_zero_prodPrimes s hden
  have hzpos : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hD1 : 1 < D := by linarith
  have hld : 0 < Real.log D := Real.log_pos hD1
  have hspos : 0 < Real.log D / Real.log z := div_pos hld hlz
  have hs5 : Real.log D / Real.log z ≤ 5 := by
    apply (div_le_iff₀ hlz).mpr
    have hh := Real.log_le_log (by linarith : 0 < D) hDz
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hf := LeanLab.AlmostPrimeSums.Decomp1527a.one_lt_Fsieve _ hspos hs5
  have hmain : s.mainSum (rosserWeight D true) = 1 := by
    simp [BoundingSieve.mainSum, hprod, rosserWeight, decPrimes, s.nu_mult.map_one]
  rw [hmain]
  simp only [hprod, Nat.primeFactors_one, Finset.prod_empty, one_mul]
  have herr : 0 ≤ Real.log D ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hld.le _
  linarith



/-- LEAF. Deep. Iwaniec's linear sieve, upper main term: given `K ≥ 0` there is `C > 0` such
that for every sieve problem with all primes of `P` below `z`, density `Ω₁(K)`, `2 ≤ z ≤ D ≤ z⁵`,
`Σ_{d∣P} λ⁺_d g(d) ≤ V(z)(F(s) + C (log D)^{-1/3})`, `s = log D / log z`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.4 (Jurkat-Richert form).
Unit U-1527. -/
theorem jr_mainSum_upper (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      s.mainSum (rosserWeight D true) ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))) := by
  sorry

/-- The lower main term estimate at K equal to zero follows from the empty
prime set and the proved lower sieve function bound. Boundary case of the
linear sieve estimate on BJS p. 5 equation 6. -/
theorem jr_mainSum_lower_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s 0 →
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))) ≤ s.mainSum (rosserWeight D false) := by
  refine ⟨1, by norm_num, ?_⟩
  intro s z D hz hzD hDz hP hden
  have hprod := linearDensity_zero_prodPrimes s hden
  have hzpos : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hzsq : z ≤ z ^ 2 := by nlinarith
  have hD1 : 1 < D := by linarith
  have hld : 0 < Real.log D := Real.log_pos hD1
  have hspos : 0 < Real.log D / Real.log z := div_pos hld hlz
  have hs4 : Real.log D / Real.log z ≤ 4 := by
    apply (div_le_iff₀ hlz).mpr
    have hh := Real.log_le_log (by linarith : 0 < D) hDz
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hf := LeanLab.AlmostPrimeSums.Decomp1527a.fsieve_lt_one _ hspos hs4
  have hmain : s.mainSum (rosserWeight D false) = 1 := by
    simp [BoundingSieve.mainSum, hprod, rosserWeight, decPrimes, s.nu_mult.map_one]
  rw [hmain]
  simp only [hprod, Nat.primeFactors_one, Finset.prod_empty, one_mul]
  have herr : 0 ≤ Real.log D ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hld.le _
  linarith



/-- LEAF. Deep. Iwaniec's linear sieve, lower main term: given `K ≥ 0` there is `C > 0` such
that for every sieve problem with all primes of `P` below `z`, density `Ω₁(K)`, `2 ≤ z`,
`z² ≤ D ≤ z⁴`, `Σ_{d∣P} λ⁻_d g(d) ≥ V(z)(f(s) − C (log D)^{-1/3})`, `s = log D / log z`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.3 (Jurkat-Richert form).
Unit U-1527. -/
theorem jr_mainSum_lower (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))) ≤ s.mainSum (rosserWeight D false) := by
  sorry

/-- Exact finite Moebius weights satisfy the support condition once the full sifting
product is below the level. This is a special case, not the uniform fundamental lemma.
Derived inclusion exclusion from BJS pp. 4 to 5 equations 3 and 11, and IK Lemma 6.3. -/
theorem exact_sieve_weights_of_prodPrimes_lt (s : BoundingSieve) (D : ℝ) (hD : (s.prodPrimes : ℝ) < D) :
    ∃ lam : ℕ → ℝ,
      (∀ d, |lam d| ≤ 1) ∧ lam 1 = 1 ∧
      (∀ d, lam d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
      IsUpperMoebius lam ∧
      (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lam d = if n = 1 then 1 else 0) ∧
      s.mainSum lam = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  let lam : ℕ → ℝ := fun d => if d ∣ s.prodPrimes then (moebius d : ℝ) else 0
  have hmu : ∀ n : ℕ, (∑ d ∈ n.divisors, (moebius d : ℝ)) = if n = 1 then 1 else 0 := by
    intro n
    have hh := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    rw [coe_mul_zeta_apply] at hh
    simpa only [intCoe_apply, one_apply] using hh
  have hsum : ∀ n : ℕ, n ≠ 0 →
      ∑ d ∈ n.divisors, lam d = if Nat.gcd s.prodPrimes n = 1 then 1 else 0 := by
    intro n hn
    calc
      _ = ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, (moebius d : ℝ) := by
        simp only [lam, Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.gcd_dvd_right _ _)]
        ext d
        simp +contextual [Nat.dvd_gcd_iff]
      _ = _ := hmu _
  refine ⟨lam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    dsimp [lam]
    split_ifs
    · exact_mod_cast abs_moebius_le_one
    · simp
  · simp [lam]
  · intro d hd
    have hdp : d ∣ s.prodPrimes := by by_contra hc; exact hd (by simp [lam, hc])
    exact ⟨hdp, lt_of_le_of_lt (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hdp) hD⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      simp
    rw [hsum n hn]
    by_cases hn1 : n = 1
    · simp [hn1]
    · simp only [hn1, ↓reduceIte]
      split_ifs <;> norm_num
  · intro n hnp
    have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hnp
    simp only [hsum n hn, Nat.gcd_eq_right hnp]
  · have heq : s.mainSum lam = s.mainSum (fun d => (moebius d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [show lam d = (moebius d : ℝ) by simp [lam, (Nat.mem_divisors.mp hd).1]]
    rw [heq]
    exact (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      s.nu s.nu_mult s.prodPrimes_squarefree).symm

/-- Restrict Rosser weights to divisors of P. All finite requirements in the
fundamental lemma hold. Their main sums are the original Rosser main sums.
The uniform analytic error remains separate. IK Lemma 6.3 and Theorem 6.9.
Derived finite construction with notation from BJS pp. 4 to 5 equations 3 and 11. -/
theorem rosser_fundamental_weights (s : BoundingSieve) (z D : ℝ) (hzD : z ≤ D) (hD : 1 < D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    ∃ lp lm : ℕ → ℝ,
      (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
      (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
      (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
      IsUpperMoebius lp ∧
      (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
      s.mainSum lp = s.mainSum (rosserWeight D true) ∧
      s.mainSum lm = s.mainSum (rosserWeight D false) := by
  let L : Bool → ℕ → ℝ := fun b d => if d ∣ s.prodPrimes then rosserWeight D b d else 0
  have hbound : ∀ b d, |L b d| ≤ 1 := by
    intro b d
    dsimp [L]
    split_ifs
    · exact abs_rosserWeight_le_one D b d
    · simp
  have hone : ∀ b, L b 1 = 1 := by intro b; simp [L, rosserWeight, decPrimes]
  have hsupp : ∀ b d, L b d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D := by
    intro b d hd
    have hdp : d ∣ s.prodPrimes := by by_contra hc; exact hd (by simp [L, hc])
    have hw : rosserWeight D b d ≠ 0 := by simpa [L, hdp] using hd
    refine ⟨hdp, ?_⟩
    rcases rosserWeight_support D hD b d hw with hlt | hprime
    · exact hlt
    · exact lt_of_lt_of_le (hP d (Nat.mem_primeFactors.mpr
        ⟨hprime, hdp, s.prodPrimes_ne_zero⟩)) hzD
  have hsum : ∀ b n, n ≠ 0 → ∑ d ∈ n.divisors, L b d =
      ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, rosserWeight D b d := by
    intro b n hn
    simp only [L, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.gcd_dvd_right _ _)]
    ext d
    simp +contextual [Nat.dvd_gcd_iff]
  have hmain : ∀ b, s.mainSum (L b) = s.mainSum (rosserWeight D b) := by
    intro b
    apply Finset.sum_congr rfl
    intro d hd
    simp only [L, (Nat.mem_divisors.mp hd).1, ite_true]
  refine ⟨L true, L false, fun d => ⟨hbound true d, hbound false d⟩,
    hone true, hone false, hsupp true, hsupp false, ?_, ?_, hmain true, hmain false⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      simp
    rw [hsum true n hn]
    have hu := rosser_upper_isUpperMoebius D (Nat.gcd s.prodPrimes n)
    by_cases hn1 : n = 1
    · simpa [hn1] using hu
    · have hi : (0 : ℝ) ≤ if Nat.gcd s.prodPrimes n = 1 then 1 else 0 := by split_ifs <;> norm_num
      exact (by simpa [hn1] using hi.trans hu)
  · intro n hnp
    have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hnp
    simpa only [hsum false n hn, Nat.gcd_eq_right hnp] using rosser_lower_le D n

/-- The fundamental lemma at the boundary parameter K equal to zero.
Density forces an empty prime set, so exact finite weights give zero error.
This is the boundary case of IK Lemma 6.3 and Theorem 6.9. -/
theorem fundamental_lemma_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s 0 →
      ∃ lp lm : ℕ → ℝ,
        (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
        (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        IsUpperMoebius lp ∧
        (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
        |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
        |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  refine ⟨1, by norm_num, ?_⟩
  intro s z D hz hDz hP hden
  have hprod : s.prodPrimes = 1 := linearDensity_zero_prodPrimes s hden
  have hzpow : (2 : ℝ) ^ 10 ≤ z ^ 10 := pow_le_pow_left₀ (by norm_num) hz 10
  have hD : (s.prodPrimes : ℝ) < D := by rw [hprod]; norm_num only [Nat.cast_one]; norm_num at hzpow; linarith
  obtain ⟨lam, hb, hone, hsupp, hup, hlow, hmain⟩ := exact_sieve_weights_of_prodPrimes_lt s D hD
  refine ⟨lam, lam, fun d => ⟨hb d, hb d⟩, hone, hone, hsupp, hsupp, hup, ?_, ?_, ?_⟩
  · intro n hn
    exact le_of_eq (hlow n hn)
  · rw [hmain, sub_self, abs_zero]
    simp only [hprod, Nat.primeFactors_one, Finset.prod_empty, mul_one, one_mul]
    exact Real.exp_nonneg _
  · rw [hmain, sub_self, abs_zero]
    simp only [hprod, Nat.primeFactors_one, Finset.prod_empty, mul_one, one_mul]
    exact Real.exp_nonneg _



/-- Reindex squarefree divisors by subsets of the sifting primes.
Mathlib supplies the squarefree divisor sum identity. This is the finite bridge
between the sieve notation on BJS p. 4 and the lab block main sums. -/
theorem sum_divisors_primeFactors_eq_powerset (s : BoundingSieve) (F : Finset ℕ → ℝ) :
    (∑ d ∈ s.prodPrimes.divisors, F d.primeFactors) =
      ∑ S ∈ s.prodPrimes.primeFactors.powerset, F S := by
  have hh := Nat.sum_divisors_filter_squarefree
    (f := fun d => F d.primeFactors) s.prodPrimes_ne_zero
  rw [Nat.divisors_filter_squarefree_of_squarefree s.prodPrimes_squarefree, Nat.factors_eq] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro S hS
  congr 1
  symm
  rw [Finset.prod_val]
  exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors
    ((Finset.mem_powerset.mp hS) hp)

/-- Multiplicativity identifies the divisor main sum with the block main sum.
Derived bridge between BJS p. 4 equation 3 and the lab block representation. -/
theorem mainSum_primeFactors_eq_block_main (s : BoundingSieve) (c : Finset ℕ → ℝ) :
    s.mainSum (fun d => c d.primeFactors) = wMain s.prodPrimes.primeFactors c s.nu := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors, c d.primeFactors *
        ∏ p ∈ d.primeFactors, s.nu p := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [s.prod_primeFactors_nu (Nat.mem_divisors.mp hd).1]
    _ = _ := by
      simpa only [wMain] using sum_divisors_primeFactors_eq_powerset s
        (fun S => c S * ∏ p ∈ S, s.nu p)

/-- Block evaluation equals the divisor sum restricted to multiples of the
subset product. Derived finite comparison from Heath Brown pp. 30 to 32. -/
theorem block_eval_eq_divisor_sum (s : BoundingSieve) (c : Finset ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ s.prodPrimes.divisors, if d ∣ n then c d.primeFactors else 0) =
      wEval s.prodPrimes.primeFactors c n := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors, c d.primeFactors *
        (if (∏ p ∈ d.primeFactors, p) ∣ n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hsq := s.prodPrimes_squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
      rw [Nat.prod_primeFactors_of_squarefree hsq]
      split_ifs <;> simp
    _ = _ := by
      simpa only [wEval, ind] using sum_divisors_primeFactors_eq_powerset s
        (fun S => c S * (if (∏ p ∈ S, p) ∣ n then 1 else 0))

/-- Adjacent even and odd block truncations keep the lower coefficients bounded
by one. This sharpens the general coefficient bound for the fundamental lemma
route. Derived from the lab Brun block recursion, with density source HR p. 142. -/
theorem block_lower_coeff_le_one_of_adjacent (Bs : List Block) (hadj : ∀ b ∈ Bs, b.2.2 = b.2.1 + 1) (S : Finset ℕ) :
    |cL Bs S| ≤ 1 := by
  induction Bs generalizing S with
  | nil => simp [cL, unitW]; split_ifs <;> norm_num
  | cons b Bs ih =>
    have hb : b.2.2 = b.2.1 + 1 := hadj b (by simp)
    have htail : ∀ c ∈ Bs, c.2.2 = c.2.1 + 1 := fun c hc => hadj c (by simp [hc])
    have hl := ih htail (S ∩ univB Bs)
    have hu := (coeff_bounds Bs (S ∩ univB Bs)).1
    simp only [cL, tens]
    by_cases hk : (S ∩ b.1).card ≤ b.2.1
    · have hk' : (S ∩ b.1).card ≤ b.2.2 := by omega
      simp only [tc, hk, hk', ite_true]
      have he : (-1 : ℝ) ^ (S ∩ b.1).card * cL Bs (S ∩ univB Bs) +
          (-1 : ℝ) ^ (S ∩ b.1).card * cU Bs (S ∩ univB Bs) -
          (-1 : ℝ) ^ (S ∩ b.1).card * cU Bs (S ∩ univB Bs) =
          (-1 : ℝ) ^ (S ∩ b.1).card * cL Bs (S ∩ univB Bs) := by ring
      rw [he, abs_mul]
      simpa using hl
    · by_cases hk' : (S ∩ b.1).card ≤ b.2.2
      · simp only [tc, hk, hk', ite_true, ite_false, zero_mul, zero_add, sub_zero, abs_mul]
        simpa using hu
      · simp [tc, hk, hk']

/-- Adjacent block truncations produce all finite weight requirements of the
fundamental lemma when the block level is below D. Their main sums are the lab
block main sums. The missing step is a quantitative choice of blocks.
Derived finite construction for IK Lemma 6.3 and Theorem 6.9, using the divisor
comparisons on Heath Brown pp. 30 to 32 and the lab Brun block recursion. -/
theorem block_fundamental_weights (s : BoundingSieve) (D : ℝ) (Bs : List Block) (hG : Good Bs)
    (hcover : univB Bs = s.prodPrimes.primeFactors)
    (hadj : ∀ b ∈ Bs, b.2.2 = b.2.1 + 1) (hlevel : (lev Bs : ℝ) < D) :
    ∃ lp lm : ℕ → ℝ,
      (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
      (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
      (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
      IsUpperMoebius lp ∧
      (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
      s.mainSum lp = wMain (univB Bs) (cU Bs) s.nu ∧
      s.mainSum lm = wMain (univB Bs) (cL Bs) s.nu := by
  let C : Bool → Finset ℕ → ℝ := fun b => if b then cU Bs else cL Bs
  let L : Bool → ℕ → ℝ := fun b d => if d ∣ s.prodPrimes then C b d.primeFactors else 0
  have hbound : ∀ b S, |C b S| ≤ 1 := by
    intro b S
    cases b
    · exact block_lower_coeff_le_one_of_adjacent Bs hadj S
    · exact (coeff_bounds Bs S).1
  have hempty : ∀ Ts : List Block, cU Ts ∅ = 1 ∧ cL Ts ∅ = 1 := by
    intro Ts
    induction Ts with
    | nil => simp [cU, cL, unitW]
    | cons t Ts ih => simp [cU, cL, tens, tc, ih.1, ih.2]
  have hone : ∀ b, L b 1 = 1 := by
    intro b
    cases b <;> simp [L, C, (hempty Bs).1, (hempty Bs).2]
  have hsupp : ∀ b d, L b d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D := by
    intro b d hd
    have hdp : d ∣ s.prodPrimes := by by_contra hc; exact hd (by simp [L, hc])
    have hC : C b d.primeFactors ≠ 0 := by simpa [L, hdp] using hd
    have hds := s.prodPrimes_squarefree.squarefree_of_dvd hdp
    have hsub : d.primeFactors ⊆ univB Bs := by
      rw [hcover]
      exact Nat.primeFactors_mono hdp s.prodPrimes_ne_zero
    have hne : cL Bs d.primeFactors ≠ 0 ∨ cU Bs d.primeFactors ≠ 0 := by
      cases b
      · exact Or.inl hC
      · exact Or.inr hC
    have hb := support_prod Bs hG d.primeFactors hsub hne
    rw [Nat.prod_primeFactors_of_squarefree hds] at hb
    exact ⟨hdp, lt_of_le_of_lt (by exact_mod_cast hb) hlevel⟩
  have hsum : ∀ b n, n ≠ 0 → ∑ d ∈ n.divisors, L b d =
      wEval s.prodPrimes.primeFactors (C b) n := by
    intro b n hn
    rw [← block_eval_eq_divisor_sum]
    have hleft : (∑ d ∈ n.divisors, L b d) =
        ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, C b d.primeFactors := by
      simp only [L, Finset.sum_ite, Finset.sum_const_zero, add_zero]
      congr 1
      rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.gcd_dvd_right _ _)]
      ext d
      simp +contextual [Nat.dvd_gcd_iff]
    rw [hleft]
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
    ext d
    simp +contextual [Nat.dvd_gcd_iff]
  have hmain : ∀ b, s.mainSum (L b) = wMain (univB Bs) (C b) s.nu := by
    intro b
    rw [hcover, ← mainSum_primeFactors_eq_block_main]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [L, (Nat.mem_divisors.mp hd).1, ite_true]
  refine ⟨L true, L false, fun d => ?_, hone true, hone false, hsupp true, hsupp false,
    ?_, ?_, hmain true, hmain false⟩
  · constructor <;> dsimp [L] <;> split_ifs <;> simp [hbound]
  · intro n
    by_cases hn : n = 0
    · subst n; simp
    by_cases hn1 : n = 1
    · subst n; simp [hone]
    rw [hsum true n hn]
    have hu := (blocks_pointwise Bs hG n).2
    rw [hcover] at hu
    simp only [hn1, ↓reduceIte]
    exact (xind_nonneg _ _).trans hu
  · intro n hnp
    have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hnp
    by_cases hn1 : n = 1
    · subst n; simp [hone]
    rw [hsum false n hn]
    have hl := (blocks_pointwise Bs hG n).1
    rw [hcover] at hl
    have hp := Nat.minFac_prime hn1
    have hpmem : n.minFac ∈ s.prodPrimes.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, (Nat.minFac_dvd n).trans hnp, s.prodPrimes_ne_zero⟩
    have hx : xind s.prodPrimes.primeFactors n = 0 := by
      apply ite_eq_right
      intro he
      have hh : n.minFac ∈ s.prodPrimes.primeFactors.filter (fun p => p ∣ n) :=
        Finset.mem_filter.mpr ⟨hpmem, Nat.minFac_dvd n⟩
      rw [he] at hh
      exact Finset.notMem_empty _ hh
    simpa [C, hx, hn1] using hl

/-- A block ratio sum at most one tenth gives relative main term error at most
five times that ratio sum. The global auxiliary density agrees with nu on the
sifting primes. Derived bridge from the lab relative block theorem to the
fundamental lemma route, with density source HR p. 142. -/
theorem block_mainSum_relative_error (s : BoundingSieve) (Bs : List Block) (hG : Good Bs)
    (hcover : univB Bs = s.prodPrimes.primeFactors) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1)
    (hagree : ∀ p ∈ s.prodPrimes.primeFactors, x p = s.nu p)
    (hrho : rhoSum x Bs ≤ 1 / 10) :
    |s.mainSum (fun d => cU Bs d.primeFactors) -
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
      5 * rhoSum x Bs * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
    |s.mainSum (fun d => cL Bs d.primeFactors) -
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
      5 * rhoSum x Bs * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  have hV : (∏ p ∈ univB Bs, (1 - x p)) =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
    rw [hcover]
    exact Finset.prod_congr rfl fun p hp => by rw [hagree p hp]
  have hmain : ∀ c : Finset ℕ → ℝ, s.mainSum (fun d => c d.primeFactors) =
      wMain (univB Bs) c x := by
    intro c
    rw [mainSum_primeFactors_eq_block_main, wMain, wMain, hcover]
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    exact Finset.prod_congr rfl fun p hp => (hagree p ((Finset.mem_powerset.mp hS) hp)).symm
  have hdev := blocks_rel_dev x hx0 hx1 Bs hG
  have hle := d_le_of_sum x hx0 (fun p => (hx1 p).le) Bs hrho
  have hr0 := rhoSum_nonneg x hx0 (fun p => (hx1 p).le) Bs
  have hV0 : 0 ≤ ∏ p ∈ univB Bs, (1 - x p) :=
    Finset.prod_nonneg fun p _ => sub_nonneg.mpr (hx1 p).le
  constructor
  · rw [hmain, ← hV]
    exact hdev.1.trans (mul_le_mul_of_nonneg_right (by linarith [hle.2.1]) hV0)
  · rw [hmain, ← hV]
    exact hdev.2.trans (mul_le_mul_of_nonneg_right hle.2.2.2 hV0)

/-- LEAF. Deep. Fundamental lemma of sieve theory, `κ = 1`: given `K ≥ 0` there is `C > 0`
such that whenever all primes of `P` are below `z`, `Ω₁(K)` holds, `z ≥ 2` and `D ≥ z^{10}`,
there are upper and lower bound sieve weights `λ^±` with `|λ^±_d| ≤ 1`, supported on `d ∣ P`,
`d < D`, `λ^±_1 = 1`, `Σ_{d∣n} λ⁺_d ≥ [n=1]` for all `n`,
`Σ_{d∣n} λ⁻_d ≤ [n=1]` for `n ∣ P`, and `|Σ_{d∣P} λ^±_d g(d) − V(z)| ≤ C e^{-s} V(z)`, `s = log D/log z`.
Iwaniec-Kowalski Lemma 6.3 and Theorem 6.9 (`D ≥ z^{9κ+1}`).
Unit U-1527. -/
theorem fundamental_lemma (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∃ lp lm : ℕ → ℝ,
        (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
        (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        IsUpperMoebius lp ∧
        (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
        |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
        |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  sorry

/-! ### Assemblies: the Jurkat-Richert linear sieve bounds, from the leaves -/

lemma one_lt_of_two_le {z D : ℝ} (hz : 2 ≤ z) (hzD : z ≤ D) : 1 < D := by linarith

/-- **Jurkat-Richert upper bound**, assembled from the leaves `rosser_upper_isUpperMoebius`,
`jr_mainSum_upper`, `errSum_rosser_le` and Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius`: for `X ≥ 0`, `2 ≤ z ≤ D ≤ z⁵`,
`S(A, P) ≤ X V(z)(F(s) + C (log D)^{-1/3}) + Σ_{d∣P, d<D} |r_d|`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.4. -/
theorem jr_upper (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K → 0 ≤ s.totalMass →
      s.siftedSum ≤ s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))))
        + ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
  obtain ⟨C, hC, hmain⟩ := jr_mainSum_upper K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hK' hX => ?_⟩
  have h1 := s.siftedSum_le_mainSum_errSum_of_upperMoebius _ (rosser_upper_isUpperMoebius D)
  have h2 := hmain s z D hz hzD hDz hP hK'
  have h3 := errSum_rosser_le s z D hzD (one_lt_of_two_le hz hzD) hP true
  have h4 : s.totalMass * s.mainSum (rosserWeight D true) ≤ s.totalMass *
      ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ)))) :=
    mul_le_mul_of_nonneg_left h2 hX
  linarith

/-- **Jurkat-Richert lower bound**, assembled from the leaves `rosser_lower_le`,
`siftedSum_ge_of_lower`, `jr_mainSum_lower`, `errSum_rosser_le`: for `X ≥ 0`, `2 ≤ z`,
`z² ≤ D ≤ z⁴`, `S(A, P) ≥ X V(z)(f(s) − C (log D)^{-1/3}) − Σ_{d∣P, d<D} |r_d|`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.3. -/
theorem jr_lower (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K → 0 ≤ s.totalMass →
      s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))))
        - ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| ≤ s.siftedSum := by
  obtain ⟨C, hC, hmain⟩ := jr_mainSum_lower K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hK' hX => ?_⟩
  have hz2 : z ≤ z ^ 2 := by nlinarith
  have hzD' : z ≤ D := hz2.trans hzD
  have h1 := siftedSum_ge_of_lower s _ (rosser_lower_le D)
  have h2 := hmain s z D hz hzD hDz hP hK'
  have h3 := errSum_rosser_le s z D hzD' (one_lt_of_two_le hz hzD') hP false
  have h4 : s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ)))) ≤
      s.totalMass * s.mainSum (rosserWeight D false) :=
    mul_le_mul_of_nonneg_left h2 hX
  linarith

/-! ### Vacuity -/

/-- A nonempty density instance with two equally weighted elements and one
sifting prime. Derived concrete model of BJS p. 4 equations 3 and 4. -/
theorem single_prime_density_instance : ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ s.totalMass = 2 ∧
    s.nu 2 = 1 / 2 ∧ LinearDensity s (Real.log 2) ∧ s.siftedSum = 1 ∧
    s.rem 1 = 0 ∧ s.rem 2 = 0 := by
  let s : BoundingSieve := {
    support := {1, 2}
    prodPrimes := 2
    prodPrimes_squarefree := Nat.squarefree_two
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := 2
    nu := ArithmeticFunction.prodPrimeFactors (fun _ => (1 / 2 : ℝ))
    nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
    nu_pos_of_prime := by
      intro p hp hpd
      have he : p = 2 := ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp hpd).symm
      subst p
      norm_num [ArithmeticFunction.prodPrimeFactors_apply, Nat.prime_two.primeFactors]
    nu_lt_one_of_prime := by
      intro p hp hpd
      have he : p = 2 := ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp hpd).symm
      subst p
      norm_num [ArithmeticFunction.prodPrimeFactors_apply, Nat.prime_two.primeFactors] }
  have hnu : s.nu 2 = 1 / 2 := by
    norm_num [s, ArithmeticFunction.prodPrimeFactors_apply, Nat.prime_two.primeFactors]
  have hden : LinearDensity s (Real.log 2) := by
    intro w w' hw hww'
    have hlw : 0 < Real.log w := Real.log_pos (by linarith)
    have hl : Real.log w ≤ Real.log w' := Real.log_le_log (by linarith) hww'.le
    have hratio : 1 ≤ Real.log w' / Real.log w := (le_div_iff₀ hlw).mpr (by simpa)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    change ∏ p ∈ (2 : ℕ).primeFactors.filter (fun p : ℕ => w ≤ p ∧ (p : ℝ) < w'),
      (1 - s.nu p)⁻¹ ≤ _
    rw [Nat.prime_two.primeFactors]
    by_cases hc : w ≤ 2 ∧ 2 < w'
    · have hw2 : w = 2 := le_antisymm hc.1 hw
      subst w
      simp only [Finset.filter_singleton, Nat.cast_ofNat, hc.2]
      norm_num [hnu]
      linarith
    · have he : ({2} : Finset ℕ).filter (fun p : ℕ => w ≤ p ∧ (p : ℝ) < w') = ∅ := by
        simp [Finset.filter_singleton, hc]
      rw [he, Finset.prod_empty]
      have hsecond : 1 ≤ 1 + Real.log 2 / Real.log w := by
        have : 0 ≤ Real.log 2 / Real.log w := div_nonneg hl2.le hlw.le
        linarith
      nlinarith
  refine ⟨s, rfl, rfl, hnu, hden, ?_, ?_, ?_⟩
  · change (∑ d ∈ ({1, 2} : Finset ℕ), if Nat.Coprime 2 d then (1 : ℝ) else 0) = 1
    rw [Finset.sum_insert (by norm_num : 1 ∉ ({2} : Finset ℕ))]
    norm_num
  · norm_num [BoundingSieve.rem, BoundingSieve.multSum, s,
      ArithmeticFunction.prodPrimeFactors_apply]
  · change (∑ n ∈ ({1, 2} : Finset ℕ), if 2 ∣ n then (1 : ℝ) else 0) - s.nu 2 * 2 = 0
    rw [Finset.sum_insert (by norm_num : 1 ∉ ({2} : Finset ℕ)), Finset.sum_singleton, hnu]
    norm_num

/-! Concrete instances for CODEX task192. AI wrote these Lean checks. -/

example : rosserWeight 2 false 3 = -1 := by
  norm_num [rosserWeight, decPrimes, Nat.prime_three.primeFactors, Nat.prime_three.squarefree, moebius_apply_prime Nat.prime_three]

example : rosserWeight 2 true 3 = 0 := by
  norm_num [rosserWeight, decPrimes, Nat.prime_three.primeFactors, Nat.prime_three.squarefree, moebius_apply_prime Nat.prime_three]

example : (3 : ℝ) < 2 ∨ Nat.Prime 3 :=
  rosserWeight_support 2 (by norm_num) false 3 (by
    norm_num [rosserWeight, decPrimes, Nat.prime_three.primeFactors, Nat.prime_three.squarefree, moebius_apply_prime Nat.prime_three])

example : rosserWeight 55 true 6 = (moebius 6 : ℝ) :=
  rosserWeight_eq_moebius_of_small 55 3 (by norm_num) true
    (by norm_num [Nat.primeFactors] ) (by norm_num)

example : [5, 3].prod ≤ ([5, 3].take 0).prod * ([5, 3].getD 0 0) ^ 3 := by
  apply prod_le_prefix_cube
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> norm_num

example : decPrimes (1 * 2) = decPrimes 1 ++ [2] :=
  decPrimes_mul_smallest squarefree_one Nat.prime_two (by simp)

example : 0 ≤ rosserWeight 2 true 1 + rosserWeight 2 true (1 * 2) ∧
    rosserWeight 2 false 1 + rosserWeight 2 false (1 * 2) ≤ 0 :=
  rosserWeight_smallest_pair_sign 2 Nat.prime_two (by simp)

example (s : BoundingSieve) : 0 ≤ s.siftedSum := by
  have hh := siftedSum_ge_of_lower s (fun _ => 0) (by
    intro n
    split_ifs <;> simp)
  simpa [BoundingSieve.mainSum, BoundingSieve.errSum] using hh

example : |cL [({2}, 0, 1)] {2}| ≤ 1 := by
  apply block_lower_coeff_le_one_of_adjacent
  intro b hb
  simp only [List.mem_singleton] at hb
  subst b
  norm_num

example : cL [({2}, 0, 1)] {2} = -1 := by
  norm_num [cL, cU, tens, tc, unitW, univB]

example : ¬∃ C : ℝ, ∀ D : ℝ, 2 ≤ D → (1 : ℝ) ≤ C * Real.log D ^ (-(1 / 3 : ℝ)) :=
  fixed_error_not_log_decay 1 (by norm_num)

example : ∃ (s : BoundingSieve) (lam : ℕ → ℝ), s.prodPrimes = 2 ∧
    (∀ d, |lam d| ≤ 1) ∧ lam 1 = 1 ∧
    s.mainSum lam = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  obtain ⟨lam, hb, h1, _, _, _, hm⟩ := exact_sieve_weights_of_prodPrimes_lt s 3 (by
    rw [hP]; norm_num)
  exact ⟨s, lam, hP, hb, h1, hm⟩

example : ∃ (s : BoundingSieve) (lp lm : ℕ → ℝ), s.prodPrimes = 2 ∧
    (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 := by
  obtain ⟨s, hP, _⟩ := single_prime_density_instance
  have hG : Good [({2}, 0, 1)] := by norm_num [Good, univB]
  have hcover : univB [({2}, 0, 1)] = s.prodPrimes.primeFactors := by
    rw [hP]; simp [univB, Nat.prime_two.primeFactors]
  obtain ⟨lp, lm, hb, h1, hm1, _⟩ := block_fundamental_weights s 3 [({2}, 0, 1)] hG hcover
    (by intro b hb; simp only [List.mem_singleton] at hb; subst b; norm_num) (by norm_num [lev])
  exact ⟨s, lp, lm, hP, hb, h1, hm1⟩


example : ∃ (s : BoundingSieve) (Bs : List Block) (x : ℕ → ℝ),
    s.prodPrimes = 2 ∧ Good Bs ∧ univB Bs = s.prodPrimes.primeFactors ∧
    (∀ p, 0 ≤ x p) ∧ (∀ p, x p < 1) ∧
    (∀ p ∈ s.prodPrimes.primeFactors, x p = s.nu p) ∧ rhoSum x Bs ≤ 1 / 10 := by
  obtain ⟨s, hP, _, hnu, _⟩ := single_prime_density_instance
  let Bs : List Block := [({2}, 4, 5)]
  let x : ℕ → ℝ := fun p => if p = 2 then 1 / 2 else 0
  refine ⟨s, Bs, x, hP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Bs, Good, univB]
  · rw [hP]; simp [Bs, univB, Nat.prime_two.primeFactors]
  · intro p; dsimp [x]; split_ifs <;> norm_num
  · intro p; dsimp [x]; split_ifs <;> norm_num
  · intro p hp
    rw [hP, Nat.prime_two.primeFactors] at hp
    have he : p = 2 := Finset.mem_singleton.mp hp
    subst p
    simpa [x] using hnu.symm
  · norm_num [Bs, x, rhoSum, rho, truncErr]

/-- The trivial sieve problem: empty support, `P = 1`, `g = ζ`. -/
noncomputable def trivialSieve : BoundingSieve where
  support := ∅
  prodPrimes := 1
  prodPrimes_squarefree := squarefree_one
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
  nu_mult := isMultiplicative_zeta.natCast
  nu_pos_of_prime := fun _p hp h => absurd (Nat.eq_one_of_dvd_one h) hp.ne_one
  nu_lt_one_of_prime := fun _p hp h => absurd (Nat.eq_one_of_dvd_one h) hp.ne_one

/-- Vacuity of `LinearDensity`: it holds for the trivial sieve with `K = 0`, and the
hypotheses of `jr_upper` hold at `z = D = 2`. -/
example : LinearDensity trivialSieve 0 ∧
    (∀ p ∈ trivialSieve.prodPrimes.primeFactors, (p : ℝ) < 2) := by
  refine ⟨fun w w' hw hww' => ?_, by simp [trivialSieve]⟩
  have hlw : 0 < log w := log_pos (by linarith)
  have hl : log w ≤ log w' := log_le_log (by linarith) hww'.le
  simp only [trivialSieve, Nat.primeFactors_one, Finset.filter_empty, Finset.prod_empty,
    zero_div, add_zero, mul_one]
  rw [le_div_iff₀ hlw]; linarith

end LeanLab.AlmostPrimeSums.Decomp1527b
