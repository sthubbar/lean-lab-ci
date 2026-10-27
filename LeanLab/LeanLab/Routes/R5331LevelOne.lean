/-
R-5331, CLOUD MANUAL-M3, unit U-7001, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The level-one ceiling route.  The sieve data of binary Goldbach are the counts
A_d = #{p < N prime : d ∣ N - p}.  Below level 1, parity blocks any main term
g(d)·X; at level 1 the data are the answer itself; and in between,
Friedlander-Granville irregularities break the main term at d ≈ N/(log N)^B.
* `eq_of_dvd_level_one`: if N ≤ 2d, 0 < p < N and d ∣ N - p then N - p = d;
  p = 0, N = 2d shows the hypothesis 0 < p is needed.
* `level_one_filter`: for N ≤ 2d < 2N the set of primes p < N with d ∣ N - p is
  {N - d} if N - d is prime and empty otherwise, so A_d = 1_P(N - d).
* `goldbach_iff_level_one`: Goldbach at N iff some prime d with N ≤ 2d < 2N has
  A_d ≠ 0: the data at level one are binary Goldbach itself.
* `dvd_sub_iff_dvd`: the Maier matrix step; if ℓ is prime, ℓ ∣ N, ℓ ∤ d and
  k d ≤ N then ℓ ∣ N - k d iff ℓ ∣ k.
* `rough_of_prime`: if every prime ℓ ≤ z divides N, d is coprime to N and
  N - k d is a prime above z, then k has no prime factor ≤ z.  So A_d counts
  z-rough k ≤ N/d only, which numerics/r5331_level_one.py shows moves A_d φ(d)/π(N)
  to 0.28 at N/d = 20 and 1.17 at N/d = 200 for N = P(23).
* `rough_side_condition`: vacuity check, N = 30, z = 5, d = 7, k = 4: N - k d = 2
  is prime, 2 ∣ k, and the side condition z < N - k d is what fails.
-/
import Mathlib

namespace LeanLab.Routes.R5331

open Finset

theorem eq_of_dvd_level_one {N d p : ℕ} (h2 : N ≤ 2 * d) (hp0 : 0 < p) (hp : p < N)
    (hd : d ∣ N - p) : N - p = d := by
  obtain ⟨c, hc⟩ := hd
  have hpos : 0 < N - p := Nat.sub_pos_of_lt hp
  rcases c with _ | _ | c
  · simp at hc; omega
  · simpa using hc
  · have : d * (c + 1 + 1) ≥ 2 * d := by nlinarith
    omega

theorem level_one_filter {N d : ℕ} (h2 : N ≤ 2 * d) (hdN : d < N) :
    (range N).filter (fun p => p.Prime ∧ d ∣ N - p) =
      if (N - d).Prime then {N - d} else ∅ := by
  ext p
  simp only [mem_filter, mem_range]
  split_ifs with hP
  · simp only [mem_singleton]
    constructor
    · rintro ⟨hp, hpr, hd⟩
      have := eq_of_dvd_level_one h2 hpr.pos hp hd
      omega
    · rintro rfl
      refine ⟨by omega, hP, ?_⟩
      rw [show N - (N - d) = d by omega]
  · simp only [Finset.notMem_empty, iff_false, not_and]
    intro hp hpr hd
    have := eq_of_dvd_level_one h2 hpr.pos hp hd
    exact hP (by rwa [show N - d = p by omega])

theorem level_one_card {N d : ℕ} (h2 : N ≤ 2 * d) (hdN : d < N) :
    ((range N).filter (fun p => p.Prime ∧ d ∣ N - p)).card =
      if (N - d).Prime then 1 else 0 := by
  rw [level_one_filter h2 hdN]; split_ifs <;> simp

theorem goldbach_iff_level_one (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N) ↔
      ∃ d, d.Prime ∧ N ≤ 2 * d ∧ d < N ∧ ∃ p, p.Prime ∧ p < N ∧ d ∣ N - p := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    rcases le_total p q with h | h
    · refine ⟨q, hq, by omega, by have := hp.two_le; omega, p, hp, by have := hq.two_le; omega, ?_⟩
      rw [show N - p = q by omega]
    · refine ⟨p, hp, by omega, by have := hq.two_le; omega, q, hq, by have := hp.two_le; omega, ?_⟩
      rw [show N - q = p by omega]
  · rintro ⟨d, hd, h2, hdN, p, hp, hpN, hdv⟩
    exact ⟨p, d, hp, hd, by have := eq_of_dvd_level_one h2 hp.pos hpN hdv; omega⟩

theorem dvd_sub_iff_dvd {ℓ N d k : ℕ} (hℓ : ℓ.Prime) (hN : ℓ ∣ N) (hd : ¬ ℓ ∣ d)
    (hk : k * d ≤ N) : ℓ ∣ N - k * d ↔ ℓ ∣ k := by
  constructor
  · intro h
    have h1 : ℓ ∣ k * d := by
      have := Nat.dvd_sub hN h
      rwa [Nat.sub_sub_self hk] at this
    rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h' | h'
    · exact h'
    · exact absurd h' hd
  · intro h
    exact Nat.dvd_sub hN (Dvd.dvd.mul_right h d)

theorem rough_of_prime {N d k z : ℕ} (hN : ∀ ℓ, ℓ.Prime → ℓ ≤ z → ℓ ∣ N)
    (hcop : Nat.Coprime d N) (hk : k * d ≤ N) (hP : (N - k * d).Prime)
    (hz : z < N - k * d) : ∀ ℓ, ℓ.Prime → ℓ ≤ z → ¬ ℓ ∣ k := by
  intro ℓ hℓ hℓz hdiv
  have hℓN := hN ℓ hℓ hℓz
  have hℓd : ¬ ℓ ∣ d := by
    intro h
    have h1 : ℓ ∣ Nat.gcd d N := Nat.dvd_gcd h hℓN
    rw [Nat.Coprime.gcd_eq_one hcop] at h1
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)
  have h1 : ℓ ∣ N - k * d := (dvd_sub_iff_dvd hℓ hℓN hℓd hk).mpr hdiv
  have h2 := (Nat.prime_dvd_prime_iff_eq hℓ hP).mp h1
  omega

theorem rough_side_condition :
    (30 - 4 * 7).Prime ∧ 2 ∣ 4 ∧ Nat.Coprime 7 30 ∧ ¬ (5 < 30 - 4 * 7) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Routes.R5331

#print axioms LeanLab.Routes.R5331.eq_of_dvd_level_one
#print axioms LeanLab.Routes.R5331.level_one_filter
#print axioms LeanLab.Routes.R5331.level_one_card
#print axioms LeanLab.Routes.R5331.goldbach_iff_level_one
#print axioms LeanLab.Routes.R5331.dvd_sub_iff_dvd
#print axioms LeanLab.Routes.R5331.rough_of_prime
#print axioms LeanLab.Routes.R5331.rough_side_condition
