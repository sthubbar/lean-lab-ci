import LeanLab.ChirreHagen2025.TailIntegral297
import LeanLab.ChirreHagen2025.Summability272

/-!
Prime index splitting for P0075 Lemma A.1, pages 13 and 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.PrimeSplit297
open TailIntegral297

/-- P0075 page 13, reindexing the convergent prime series by its zero-based index. -/
theorem prime_tsum_eq :
    (∑' p : Nat.Primes, weight p) = ∑' n : ℕ, weight (Nat.nth Nat.Prime n) := by
  let : Infinite {n : ℕ | Nat.Prime n} := Nat.infinite_setOfPred_prime.to_subtype
  let e : ℕ ≃ Nat.Primes := (Nat.Subtype.orderIsoOfNat {n | Nat.Prime n}).toEquiv
  have he (n : ℕ) : (e n : ℕ) = Nat.nth Nat.Prime n :=
    (Nat.nth_apply_eq_orderIsoOfNat Nat.infinite_setOfPred_prime n).symm
  simpa only [he] using (e.tsum_eq (fun p : Nat.Primes => weight p)).symm

/-- P0075 page 13, convergence is preserved when enumerating the primes. -/
theorem indexed_summable : Summable (fun n : ℕ => weight (Nat.nth Nat.Prime n)) := by
  let : Infinite {n : ℕ | Nat.Prime n} := Nat.infinite_setOfPred_prime.to_subtype
  let e : ℕ ≃ Nat.Primes := (Nat.Subtype.orderIsoOfNat {n | Nat.Prime n}).toEquiv
  have he (n : ℕ) : (e n : ℕ) = Nat.nth Nat.Prime n :=
    (Nat.nth_apply_eq_orderIsoOfNat Nat.infinite_setOfPred_prime n).symm
  have hs : Summable (fun p : Nat.Primes => weight p) := Summability272.part1_summable
  apply (e.summable_iff.mpr hs).congr
  intro n
  change weight (e n) = weight (Nat.nth Nat.Prime n)
  rw [he]

/-- P0075 page 13, the finite head is exactly the first N plus one zero-based primes. -/
theorem prime_head_eq (N : ℕ) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.nth Nat.Prime N)), weight p) =
      ∑ n ∈ Finset.range (N + 1), weight (Nat.nth Nat.Prime n) := by
  symm
  apply Finset.sum_bij (fun n _ => Nat.nth Nat.Prime n)
  · intro n hn
    have hp := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.one_lt.le, (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)⟩, hp⟩
  · intro n hn m hm h
    exact Nat.nth_injective Nat.infinite_setOfPred_prime h
  · intro p hp
    obtain ⟨hmem, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmem
    refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hprime⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mp
    simpa only [Nat.nth_count hprime] using h2
  · intro n hn
    rfl

/-- P0075 page 13, a Rosser lower bound implies the termwise tail comparison.
CONDITIONAL ON the lower bound supplied as hprime. -/
theorem prime_term_le_tail (N n : ℕ) (hN : 8 ≤ N) (hn : N < n)
    (hprime : (n : ℝ) * Real.log (n : ℝ) < (Nat.nth Nat.Prime n : ℝ)) :
    weight (Nat.nth Nat.Prime n) ≤ tailWeight n := by
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast (show 8 ≤ n by omega)
  have hl := one_le_log hn8
  have hx : Real.exp 2 ≤ (n : ℝ) * Real.log (n : ℝ) :=
    exp_two_lt_eight.le.trans (by nlinarith)
  exact weight_antitone hx (hx.trans hprime.le) hprime.le

/-- P0075 page 13, exact splitting followed by the Rosser tail comparison.
CONDITIONAL ON the prime lower bounds supplied as hprime. -/
theorem sum_split_of_lower_bound (N : ℕ) (hN : 8 ≤ N)
    (hprime : ∀ n : ℕ, N < n →
      (n : ℝ) * Real.log (n : ℝ) < (Nat.nth Nat.Prime n : ℝ)) :
    (∑' p : Nat.Primes, weight p) ≤
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.nth Nat.Prime N)), weight p) +
        ∑' n : ℕ, if N < n then tailWeight n else 0 := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := (tailWeight_antitone.mono (Set.Ici_subset_Ici.mpr hNr)).summable_of_integrableOn_Ioi
    (tailWeight_integrableOn hNr)
    (fun x hx => tailWeight_nonneg (hNr.trans hx.le))
  have hg : Summable (fun n : ℕ => if N < n then tailWeight n else 0) := by
    convert hs.indicator {n | N < n} using 1
    funext n
    simp [Set.indicator]
  have he := hg.sum_add_tsum_nat_add (N + 1)
  have hz : (∑ n ∈ Finset.range (N + 1), if N < n then tailWeight n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [show ¬ N < n by omega]
  rw [hz, zero_add] at he
  rw [prime_tsum_eq, prime_head_eq, ← indexed_summable.sum_add_tsum_nat_add (N + 1), ← he]
  refine add_le_add le_rfl ?_
  apply Summable.tsum_le_tsum
  · intro n
    have hn : N < n + (N + 1) := by omega
    rw [if_pos hn]
    exact prime_term_le_tail N _ hN hn (hprime _ hn)
  · exact (summable_nat_add_iff (f := fun n : ℕ => weight (Nat.nth Nat.Prime n)) (N + 1)).mpr indexed_summable
  · exact (summable_nat_add_iff (f := fun n : ℕ => if N < n then tailWeight n else 0) (N + 1)).mpr hg

/-- P0075 page 13, audit of the attempted elementary replacement for Rosser.
The linear lower bound from Mathlib alone does not imply the required logarithmic bound. -/
theorem linear_bound_insufficient :
    ¬ (∀ a : ℕ → ℕ, (∀ n : ℕ, n + 2 ≤ a n) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) * Real.log n < (a n : ℝ)) := by
  intro h
  have he := h (fun n => n + 2) (fun _ => le_rfl) 8 (by norm_num)
  have hl : (2 : ℝ) < Real.log 8 := by
    have hp : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9]
  norm_num at he
  linarith

end LeanLab.ChirreHagen2025.PrimeSplit297
