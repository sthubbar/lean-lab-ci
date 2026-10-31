import LeanLab.MissingDigit.SingularSeries
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
Audit of a constant upper bound for the ordinary binary singular series.
This concerns all positive even arguments. It does not assert unboundedness
on a fixed digit set in the admissible intervals of Kim Theorem 1.2.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.MissingDigit.KimSeries

open Finset Filter

attribute [local instance] Classical.propDecidable

/-- An elementary finite product lower bound used to audit the Euler correction. -/
theorem one_add_sum_le_prod (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p ∈ s, 0 ≤ f p) :
    1 + ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 + f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hfa := hf a (mem_insert_self a s)
    have hfs : ∀ p ∈ s, 0 ≤ f p := fun p hp => hf p (mem_insert_of_mem hp)
    have hi := ih hfs
    have hs : 0 ≤ ∑ p ∈ s, f p := sum_nonneg hfs
    nlinarith [mul_nonneg hfa hs]

/-- Removing the prime 2 does not make the reciprocal prime series converge. -/
theorem not_summable_oddPrime_inv :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ 2 < p then (1 : ℝ) / p else 0) := by
  intro h
  apply not_summable_one_div_on_primes
  refine h.congr_atTop ?_
  filter_upwards [eventually_ge_atTop 3] with p hp
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hprime : p.Prime
  · simp [hprime, show 2 < p by omega]
  · simp [hprime]

/-- Finite sums of reciprocal odd primes exceed every real bound. -/
theorem exists_oddPrime_sum_gt (C : ℝ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ 2 < p) ∧ C < ∑ p ∈ s, (1 : ℝ) / p := by
  by_contra h
  push_neg at h
  apply not_summable_oddPrime_inv
  apply summable_of_sum_le (c := C)
  · intro p
    change (0 : ℝ) ≤ if p.Prime ∧ 2 < p then (1 : ℝ) / p else 0
    split_ifs <;> positivity
  · intro s
    rw [← Finset.sum_filter]
    exact h (s.filter (fun p => p.Prime ∧ 2 < p))
      (fun p hp => (Finset.mem_filter.mp hp).2)

/-- Prime divisors force a large finite correction in the Euler product. -/
theorem oddFactor_ge_prime_sum (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    {m : ℕ} (hm : m ≠ 0) (hd : ∀ p ∈ s, p ∣ m) :
    1 + ∑ p ∈ s, (1 : ℝ) / p ≤ oddFactor m := by
  have hsub : s ⊆ m.primeFactors.filter (2 < ·) := by
    intro p hp
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨(hs p hp).1, hd p hp, hm⟩,
      (hs p hp).2⟩
  calc
    1 + ∑ p ∈ s, (1 : ℝ) / p ≤ ∏ p ∈ s, (1 + (1 : ℝ) / p) :=
      one_add_sum_le_prod s _ (fun _ _ => by positivity)
    _ ≤ ∏ p ∈ s, (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
      apply prod_le_prod₀ (fun _ _ => by positivity)
      intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hs p hp).2
      have hden : (0 : ℝ) < p - 2 := by linarith
      have hrec : (1 : ℝ) / p ≤ 1 / ((p : ℝ) - 2) :=
        one_div_le_one_div_of_le hden (by linarith)
      have heq : ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := by
        field_simp
        ring
      rw [heq]
      linarith
    _ ≤ oddFactor m := by
      unfold oddFactor
      apply prod_le_prod_of_subset_of_one_le₀ hsub
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hs p hp).2
        exact div_nonneg (by linarith) (by linarith)
      · intro p hp _
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
        rw [le_div_iff₀ (by linarith)]
        linarith

/-- The ordinary binary singular series is unbounded on positive even integers. -/
theorem exists_even_series_gt (C : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ Even m ∧ C < series m := by
  obtain ⟨s, hs, hC⟩ := exists_oddPrime_sum_gt (C / (2 * LeanLab.ChenExplicit.twinC))
  let m := 2 * ∏ p ∈ s, p
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.mul_pos (by decide) (Finset.prod_pos (fun p hp => (hs p hp).1.pos))
  have he : Even m := even_two_mul _
  have hF := oddFactor_ge_prime_sum s hs hmpos.ne' (fun p hp => by
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hp) 2)
  have hFgt : C / (2 * LeanLab.ChenExplicit.twinC) < oddFactor m := by linarith
  refine ⟨m, hmpos, he, ?_⟩
  rw [series_even_eq hmpos he]
  have hpos : 0 < 2 * LeanLab.ChenExplicit.twinC := by
    exact mul_pos (by norm_num) LeanLab.ChenExplicit.twinC_pos
  have h := (div_lt_iff₀ hpos).mp hFgt
  nlinarith

/-- A constant upper bound on the series for all positive even arguments is false. -/
theorem not_uniform_series_upper :
    ¬ ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → Even m → series m ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm, he, hgt⟩ := exists_even_series_gt C
  exact (not_lt_of_ge (hC m hm he)) hgt

/-- Omitting all primes below a fixed threshold preserves reciprocal divergence. -/
theorem not_summable_prime_inv_above (B : ℕ) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ B < p then (1 : ℝ) / p else 0) := by
  intro h
  apply not_summable_one_div_on_primes
  refine h.congr_atTop ?_
  filter_upwards [eventually_ge_atTop (B + 1)] with p hp
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases hprime : p.Prime
  · simp [hprime, show B < p by omega]
  · simp [hprime]

/-- Large reciprocal prime sums can avoid every prime below a chosen bound. -/
theorem exists_prime_sum_gt_above (B : ℕ) (C : ℝ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ B < p) ∧ C < ∑ p ∈ s, (1 : ℝ) / p := by
  by_contra h
  push Not at h
  apply not_summable_prime_inv_above B
  apply summable_of_sum_le (c := C)
  · intro p
    change (0 : ℝ) ≤ if p.Prime ∧ B < p then (1 : ℝ) / p else 0
    split_ifs <;> positivity
  · intro s
    rw [← Finset.sum_filter]
    exact h (s.filter (fun p => p.Prime ∧ B < p))
      (fun p hp => (Finset.mem_filter.mp hp).2)

end LeanLab.MissingDigit.KimSeries
