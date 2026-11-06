/-
Jia 1996, pages 263 to 265, Lemma 22 and displays 49 to 51.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The two analytic inputs remain OPEN. The sealed leaf is not changed.
-/
import LeanLab.Languasco2004.Decomp279a

namespace LeanLab.Languasco2004.Decomp316a
open Finset Real Decomp279a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 208: delta is the cube root of epsilon. -/
def delta (ε : ℝ) : ℝ := ε ^ (1 / 3 : ℝ)

/-- Page 264 display 50: the low cutoff sifted count. -/
def lowSieve (N Y : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  sifted N Y n 1 (Y ^ delta ε)

/-- Page 263 display 49 with exact endpoints for the sealed strict sieve.
The lower endpoint is included and the upper endpoint is excluded. -/
def removed (N Y : ℝ) (n : ℕ) (z Z : ℝ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ z ≤ (p : ℝ) ∧ (p : ℝ) < Z),
    (sifted N Y n p p : ℝ)

/-- Page 262 display 45: the singular factor is nonnegative. -/
theorem singular_nonneg (n : ℕ) : 0 ≤ singular n := by
  unfold singular
  apply mul_nonneg
  · apply tprod_nonneg
    intro p
    split_ifs
    · positivity
    · have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
      have hs : 1 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hs
      linarith
  · apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity

/-- Page 262 display 44: the scale is nonnegative for N and Y at least one. -/
theorem scale_nonneg {N Y : ℝ} (n : ℕ) (hN : 1 ≤ N) (hY : 1 ≤ Y) :
    0 ≤ scale N Y n := by
  exact div_nonneg (mul_nonneg (singular_nonneg n) (by linarith))
    (mul_nonneg (Real.log_nonneg hY) (Real.log_nonneg hN))

/-- Page 263 display 49: assign a removed integer to its least offending prime.
This one sided form includes the lower cutoff and excludes the upper cutoff. -/
theorem sifted_le_add_removed (N Y : ℝ) (n : ℕ) (z Z : ℝ) :
    (sifted N Y n 1 z : ℝ) ≤ (sifted N Y n 1 Z : ℝ) + removed N Y n z Z := by
  let small := (Icc 1 n).filter (fun a => 1 ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a)
  let large := (Icc 1 n).filter (fun a => 1 ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < Z → ¬ p ∣ n → ¬ p ∣ a)
  let primes := (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ z ≤ (p : ℝ) ∧ (p : ℝ) < Z)
  let fibers := fun p : ℕ => (Icc 1 n).filter (fun a => p ∣ a ∧ (n - a).Prime ∧
    N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N ∧
    ∀ q : ℕ, q.Prime → (q : ℝ) < (p : ℝ) → ¬ q ∣ n → ¬ q ∣ a)
  have hsub : small ⊆ large ∪ primes.biUnion fibers := by
    intro a ha
    by_cases hal : a ∈ large
    · exact mem_union_left _ hal
    · obtain ⟨haI, _, hap, haL, haU, has⟩ := mem_filter.mp ha
      have hex : ∃ p : ℕ, p.Prime ∧ (p : ℝ) < Z ∧ ¬ p ∣ n ∧ p ∣ a := by
        by_contra h
        apply hal
        apply mem_filter.mpr
        refine ⟨haI, one_dvd a, hap, haL, haU, ?_⟩
        intro p hp hpZ hpn hpa
        exact h ⟨p, hp, hpZ, hpn, hpa⟩
      let p := Nat.find hex
      obtain ⟨hp, hpZ, hpn, hpa⟩ := Nat.find_spec hex
      have hpz : z ≤ (p : ℝ) := le_of_not_gt (fun h => has p hp h hpn hpa)
      have hpa' : p ≤ a := Nat.le_of_dvd (by have := mem_Icc.mp haI; omega) hpa
      have hpn' : p < n + 1 := by have := mem_Icc.mp haI; omega
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨p, mem_filter.mpr ⟨mem_range.mpr hpn', hp, hpz, hpZ⟩, ?_⟩
      apply mem_filter.mpr
      refine ⟨haI, hpa, hap, haL, haU, ?_⟩
      intro q hq hqp hqn hqa
      have hqp' : q < p := by exact_mod_cast hqp
      exact Nat.find_min hex hqp' ⟨hq, hqp.trans hpZ, hqn, hqa⟩
  have hc := (card_le_card hsub).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have hr : (small.card : ℝ) ≤ (large.card : ℝ) + ∑ p ∈ primes, ((fibers p).card : ℝ) := by
    exact_mod_cast hc
  exact hr

/-- LEAF. Page 264 display 50, from the linear sieve and Lemma 17.
Only the small cutoff count is estimated. The fixed tolerance is one quarter
of the numerical slack in the final printed lower bound. -/
theorem low_sieve_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => lowSieve N (localization N ε) n ε <
        (Real.exp (-Real.eulerMascheroniConstant) / delta ε - 0.00000025) *
          scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Pages 264 and 265 display 51 and Lemma 20.
Only the removed small prime terms are estimated. The main coefficient
135/16 times 0.5612 is 4.735125. Endpoint changes belong to this input. -/
theorem removed_upper :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        (Real.exp (-Real.eulerMascheroniConstant) / delta ε - 4.735125 + 0.00000025) *
          scale N (localization N ε) n <
        removed N (localization N ε) n ((localization N ε) ^ delta ε)
          ((localization N ε) ^ (16 / 135 : ℝ)))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Page 265: the two independent failure sets cover every initial failure.
CONDITIONAL ON low_sieve_lower and removed_upper. This has the exact
statement of the sealed initial_bound and has no admission of its own. -/
theorem initial_bound_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        initial N (localization N ε) n < 4.735124 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e₁, he₁, h₁⟩ := low_sieve_lower
  obtain ⟨e₂, he₂, h₂⟩ := removed_upper
  refine ⟨min e₁ e₂, lt_min he₁ he₂, ?_⟩
  intro ε B hε he hB
  obtain ⟨C₁, N₁, hC₁⟩ := h₁ ε B hε (he.trans_le (min_le_left _ _)) hB
  obtain ⟨C₂, N₂, hC₂⟩ := h₂ ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨C₁ + C₂, max (max N₁ N₂) 2, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  let bad₁ := (window N ε).filter (fun n => lowSieve N (localization N ε) n ε <
    (Real.exp (-Real.eulerMascheroniConstant) / delta ε - 0.00000025) *
      scale N (localization N ε) n)
  let bad₂ := (window N ε).filter (fun n =>
    (Real.exp (-Real.eulerMascheroniConstant) / delta ε - 4.735125 + 0.00000025) *
      scale N (localization N ε) n <
    removed N (localization N ε) n ((localization N ε) ^ delta ε)
      ((localization N ε) ^ (16 / 135 : ℝ)))
  have hsub : ((window N ε).filter (fun n =>
      initial N (localization N ε) n < 4.735124 * scale N (localization N ε) n)) ⊆
        bad₁ ∪ bad₂ := by
    intro n hn
    obtain ⟨hnw, hbad⟩ := mem_filter.mp hn
    by_contra h
    have hlow : (Real.exp (-Real.eulerMascheroniConstant) / delta ε - 0.00000025) *
        scale N (localization N ε) n ≤ lowSieve N (localization N ε) n ε := by
      apply le_of_not_gt
      intro hp
      exact h (mem_union_left _ (mem_filter.mpr ⟨hnw, hp⟩))
    have hremoved : removed N (localization N ε) n ((localization N ε) ^ delta ε)
        ((localization N ε) ^ (16 / 135 : ℝ)) ≤
        (Real.exp (-Real.eulerMascheroniConstant) / delta ε - 4.735125 + 0.00000025) *
          scale N (localization N ε) n := by
      apply le_of_not_gt
      intro hp
      exact h (mem_union_right _ (mem_filter.mpr ⟨hnw, hp⟩))
    have hs := scale_nonneg n (by linarith : 1 ≤ N)
      (Real.one_le_rpow (by linarith : 1 ≤ N) (by positivity :
        0 ≤ (7 / 12 : ℝ) + ε))
    change 0 ≤ scale N (localization N ε) n at hs
    have hc := sifted_le_add_removed N (localization N ε) n
      ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ))
    change lowSieve N (localization N ε) n ε ≤
      initial N (localization N ε) n + _ at hc
    nlinarith
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hcr : (((window N ε).filter (fun n =>
      initial N (localization N ε) n < 4.735124 * scale N (localization N ε) n)).card : ℝ) ≤
        (bad₁.card : ℝ) + bad₂.card := by exact_mod_cast hc
  have hb := add_le_add (hC₁ N hN₁) (hC₂ N hN₂)
  calc _ ≤ (bad₁.card : ℝ) + bad₂.card := hcr
       _ ≤ C₁ * windowLength N ε / Real.log N ^ B +
           C₂ * windowLength N ε / Real.log N ^ B := hb
       _ = _ := by ring

#print axioms singular_nonneg
#print axioms scale_nonneg
#print axioms sifted_le_add_removed
#print axioms low_sieve_lower
#print axioms removed_upper
#print axioms initial_bound_from_parts
end
end LeanLab.Languasco2004.Decomp316a
