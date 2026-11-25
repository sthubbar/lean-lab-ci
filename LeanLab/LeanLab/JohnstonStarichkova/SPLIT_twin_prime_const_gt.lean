/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3, page 3, the twin prime constant
C_2 = prod_{p>2} (1 - 1/(p-1)^2) inside U_N.
SPLIT of twin_prime_const_gt, ROUTE BURST S98 burst-20261122: finite product over
3 ≤ p ≤ 47, proved by exact rational arithmetic, times a tail over primes p > 50.
AI wrote this Lean code.
-/
import LeanLab.JohnstonStarichkova.SPLIT_sifted_count_lower_v3

namespace LeanLab.JohnstonStarichkova
open LeanLab.AlmostPrimes

/-- P0019 v3 page 3, the Euler product C_2 = prod_{p>2} (1 - 1/(p-1)^2)
converges; here its tail over primes p > 50: the sum of 1/(p-1)^2 is finite, so the
tail product is multipliable in ℝ. PROVED, burst S153, was the S98 LEAF. -/
theorem twin_prime_tail_multipliable :
    Multipliable (fun x : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}) =>
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2)) := by
  have hN : Summable (fun n : ℕ => ‖-(1 / ((n : ℝ) - 1) ^ 2)‖) := by
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) := by
      simp
    have h3 : Summable (fun n : ℕ => ‖-(1 / (((n + 1 : ℕ) : ℝ) - 1) ^ 2)‖) := by
      refine h2.congr (fun n => ?_)
      push_cast
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring_nf
    exact (summable_nat_add_iff 1).mp h3
  let T := ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p})
  have hinj : Function.Injective (fun x : T => (((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ))) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hS := hN.comp_injective hinj
  have := multipliable_one_add_of_summable (R := ℝ) (f := fun x : T =>
    -(1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2)) hS
  simpa [sub_eq_add_neg] using this

/-
Numerics: the tail prod over primes p > 50 of (1 - 1/(p-1)^2) is 0.99604627...,
computed to 10^7 with remainder factor above 1 - 6e-9; bound 0.996044 has margin 2.3e-6.
Partial product over 3 ≤ p ≤ 47 is 0.6627822807, and 0.6627822807 * 0.996044 =
0.66016029 > 0.66016.
-/
/-- LEAF: P0019 v3 page 3, tail of C_2: the product over primes p > 50 of
(1 - 1/(p-1)^2) is at least 0.996044, its value being 0.99604627; needs the
primes below about 10^5 explicitly plus a sum of 1/p^2 tail bound. Class MEDIUM. -/
theorem twin_prime_tail_ge :
    (0.996044 : ℝ) ≤ ∏' x : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}),
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2) := by
  sorry

theorem twin_prime_partial_eq :
    ∏ x ∈ (Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p),
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2) =
    ∏ n ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ),
      (1 - 1 / (((n : ℕ) : ℝ) - 1) ^ 2) := by
  have hf : (Finset.range 51).filter (fun p : ℕ => p.Prime ∧ 2 < p) =
      ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) := by
    decide +kernel
  rw [← hf, ← Finset.subtype_map, Finset.prod_map]
  rfl

theorem twin_prime_partial_ge : (0.6627822807 : ℝ) ≤ ∏ n ∈
    ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ),
    (1 - 1 / (((n : ℕ) : ℝ) - 1) ^ 2) := by
  rw [Finset.prod_eq_multiset_prod]
  simp only [Finset.insert_val, Finset.singleton_val]
  norm_num

theorem twin_prime_const_gt_split :
    (0.66016 : ℝ) < ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) := by
  have h := Multipliable.tprod_mul_tprod_compl
    (f := fun p : {p : ℕ // p.Prime ∧ 2 < p} => (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2))
    (Finset.multipliable _ _) twin_prime_tail_multipliable
  rw [← h, Finset.tprod_subtype' _
    (fun p : {p : ℕ // p.Prime ∧ 2 < p} => (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2)),
    twin_prime_partial_eq]
  have ht := twin_prime_tail_ge
  have hval := twin_prime_partial_ge
  calc (0.66016 : ℝ) < 0.6627822807 * 0.996044 := by norm_num
    _ ≤ _ := mul_le_mul hval ht (by norm_num) (le_trans (by norm_num) hval)
end LeanLab.JohnstonStarichkova
