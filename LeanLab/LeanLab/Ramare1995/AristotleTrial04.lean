/-
Aristotle trial 4, lean-aristotle 2026-10-27. Target from MOUNTAIN.md, folder Ramare1995,
file Decomp1526b.lean, OPEN leaf `oddFac_sq_eq_sum_divisors`: h(m)^2 = sum over d | m of g(d).
Statement and the definitions `oddFac` and `gfun` copied character for character from
Decomp1526b.lean on main, inlined here in their own namespace, unchanged. Proof written by
Aristotle, Harmonic, project 8ce564a0-a1b8-4046-b2d6-82f127507e3c, on Lean 4.28; checked by
lean-aristotle on Lean and Mathlib 4.35 standalone: builds, axioms propext, Classical.choice,
Quot.sound only, no banned token. This repo file itself is NOT yet built in the lane: the
lean-refresh merge rebuild is the trusted check; linking it to Decomp1526b's defs is
lean-refresh's call. AI wrote the Lean code.
-/
import Mathlib

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.Ramare1995.AristotleTrial04

def oddFac (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

def gfun (d : ℕ) : ℝ :=
  if Squarefree d ∧ ¬ Even d then
    ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2) else 0

lemma oddFac_factor_sq {p : ℕ} (hp : 2 < p) :
    (((p : ℝ) - 1) / ((p : ℝ) - 2)) ^ 2 = 1 + (2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2 := by
  have h : (p : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  field_simp
  ring

theorem oddFac_sq_eq_sum_divisors {m : ℕ} (hm : m ≠ 0) :
    oddFac m ^ 2 = ∑ d ∈ m.divisors, gfun d := by
  set S := m.primeFactors.filter (2 < ·) with hS
  set g : ℕ → ℝ := fun p => (2 * (p : ℝ) - 3) / ((p : ℝ) - 2) ^ 2 with hg
  have h1 : oddFac m ^ 2 = ∑ T ∈ S.powerset, ∏ p ∈ T, g p := by
    rw [oddFac, ← Finset.prod_pow, ← Finset.prod_one_add]
    refine Finset.prod_congr rfl fun p hp => ?_
    exact oddFac_factor_sq (Finset.mem_filter.1 hp).2
  have h2 : ∑ d ∈ m.divisors, gfun d =
      ∑ d ∈ m.divisors.filter (fun d => Squarefree d ∧ ¬ Even d), ∏ p ∈ d.primeFactors, g p := by
    rw [Finset.sum_filter]
    rfl
  rw [h1, h2]
  have hprime : ∀ T ∈ S.powerset, ∀ p ∈ T, p.Prime := fun T hT p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 (Finset.mem_powerset.1 hT hp)).1
  refine Finset.sum_bij' (fun T _ => ∏ p ∈ T, p) (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    have hTS := Finset.mem_powerset.1 hT
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hm⟩, ?_, ?_⟩
    · calc ∏ p ∈ T, p ∣ ∏ p ∈ m.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset _ _ _ (hTS.trans (Finset.filter_subset _ _))
        _ ∣ m := Nat.prod_primeFactors_dvd m
    · exact Finset.squarefree_prod_of_pairwise_isCoprime
        (fun a ha b hb hab => Nat.coprime_iff_isRelPrime.1
          ((Nat.coprime_primes (hprime T hT a ha) (hprime T hT b hb)).2 hab))
        (fun p hp => (hprime T hT p hp).squarefree)
    · rw [even_iff_two_dvd, Prime.dvd_finsetProd_iff Nat.prime_two.prime]
      rintro ⟨p, hp, h2p⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hprime T hT p hp)).1 h2p
      have := (Finset.mem_filter.1 (hTS hp)).2
      omega
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    rw [Finset.mem_powerset]
    intro p hp
    rw [Finset.mem_filter]
    refine ⟨Nat.primeFactors_mono hd.1.1 hm hp, ?_⟩
    have hpp := Nat.prime_of_mem_primeFactors hp
    rcases hpp.eq_two_or_odd' with h | h
    · subst h
      exact absurd (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp)) hd.2.2
    · have := hpp.two_le
      rcases Nat.lt_or_ge 2 p with h' | h'
      · exact h'
      · have : p = 2 := by omega
        subst this; exact absurd h (by decide)
  · intro T hT
    exact Nat.primeFactors_prod (hprime T hT)
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.prod_primeFactors_of_squarefree hd.2.1
  · intro T hT
    rw [Nat.primeFactors_prod (hprime T hT)]

end LeanLab.Ramare1995.AristotleTrial04

end
