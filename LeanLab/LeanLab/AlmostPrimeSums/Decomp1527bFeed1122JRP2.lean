/-
P0002 J.-R. Chen 1973, unit U-1527 file b, burst-20261122 session S117 split of the MEDIUM leaf
`Decomp1527bFeed1122JR.rosser_mainSum_buchstab`, the Buchstab decomposition of a Rosser sum,
Iwaniec-Kowalski (6.6)-(6.8) and Opera de Cribro Section 6.3, into its two faithful steps:
the regrouping of the failing divisors `d = e f` by their first failure `e`, and the Euler
product `Σ_{f ∣ P(p)} μ(f) g(f) = V(p)`. The parent is proved here as
`rosser_mainSum_buchstab_of_leaves` with exactly the statement of the parent.

AI-written Lean code, Claude, 2026-11-23. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.AlmostPrimeSums.Decomp1527b

namespace LeanLab.AlmostPrimeSums.Decomp1527bFeed1122JRP2
open Finset Real ArithmeticFunction BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a
open LeanLab.AlmostPrimeSums.Decomp1527b
attribute [local instance] Classical.propDecidable

/-- LEAF: Iwaniec-Kowalski (6.6)-(6.7), Opera de Cribro Section 6.3, regrouping of the divisors
that fail the Rosser cut-off. Class MEDIUM, a finite combinatorial identity. Every `d ∣ P` with
`λ_d = 0` factors uniquely as `d = e f` with `e` its prefix of largest primes up to the first
failing prime, so `e ∈ B^b`, and `f ∣ P` having all prime factors below `p(e)`; conversely each
such `e f` fails. Hence `Σ_{d∣P} (μ(d) - λ^b_d) g(d) = Σ_{e ∈ B^b} μ(e) g(e) Σ_{f ∣ P(p(e))} μ(f) g(f)`. -/
theorem rosser_failure_regroup (s : BoundingSieve) (D : ℝ) (b : Bool) :
    ∑ d ∈ s.prodPrimes.divisors, ((ArithmeticFunction.moebius d : ℝ) - rosserWeight D b d) * s.nu d =
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (ArithmeticFunction.moebius e : ℝ) * s.nu e *
          ∑ f ∈ s.prodPrimes.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < e.minFac),
            (ArithmeticFunction.moebius f : ℝ) * s.nu f := by
  sorry

/-- LEAF: Iwaniec-Kowalski (6.8), the Euler product for the sifting function at `p`:
`Σ_{f ∣ P, all prime factors of f below p} μ(f) g(f) = ∏_{q ∣ P, q < p} (1 - g(q)) = V(p)`.
Class EASY, from multiplicativity of `g` and `Squarefree P`. -/
theorem sum_moebius_below_eq_prod (s : BoundingSieve) (p : ℕ) :
    ∑ f ∈ s.prodPrimes.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < p),
        (ArithmeticFunction.moebius f : ℝ) * s.nu f =
      ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q) := by
  set S := s.prodPrimes.primeFactors.filter (fun q => q < p) with hS
  have hSP : ∀ q ∈ S, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hnP : (∏ q ∈ S, q) ∣ s.prodPrimes := by
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hnsq : Squarefree (∏ q ∈ S, q) := s.prodPrimes_squarefree.squarefree_of_dvd hnP
  have hpf : (∏ q ∈ S, q).primeFactors = S := Nat.primeFactors_prod hSP
  have hdiv : (∏ q ∈ S, q).divisors =
      s.prodPrimes.divisors.filter (fun f => ∀ q ∈ f.primeFactors, q < p) := by
    ext f
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hf, hn0⟩
      refine ⟨⟨hf.trans hnP, hP0⟩, fun q hq => ?_⟩
      have : q ∈ (∏ q ∈ S, q).primeFactors := Nat.primeFactors_mono hf hn0 hq
      rw [hpf] at this
      exact (Finset.mem_filter.mp this).2
    · rintro ⟨⟨hfP, -⟩, hq⟩
      refine ⟨?_, hnsq.ne_zero⟩
      have hfsq : Squarefree f := s.prodPrimes_squarefree.squarefree_of_dvd hfP
      rw [← Nat.prod_primeFactors_of_squarefree hfsq]
      refine Finset.prod_dvd_prod_of_subset _ _ _ fun q hqf => ?_
      exact Finset.mem_filter.mpr ⟨Nat.primeFactors_mono hfP hP0 hqf, hq q hqf⟩
  have key := s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hnsq
  rw [hpf] at key
  rw [← hdiv, key]

/-- **Parent `Decomp1527bFeed1122JR.rosser_mainSum_buchstab`, assembled from the leaves**
`rosser_failure_regroup` and `sum_moebius_below_eq_prod`, with the full Euler product
`Σ_{d∣P} μ(d) g(d) = V(P)` from Mathlib. Same statement as the parent. -/
theorem rosser_mainSum_buchstab_of_leaves (s : BoundingSieve) (D : ℝ) (b : Bool) :
    s.mainSum (rosserWeight D b) = (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) -
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (ArithmeticFunction.moebius e : ℝ) * s.nu e *
          ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < e.minFac), (1 - s.nu q) := by
  have h1 := s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ s.prodPrimes_squarefree
  have h2 := rosser_failure_regroup s D b
  simp only [sum_moebius_below_eq_prod] at h2
  rw [h1, ← h2, ← Finset.sum_sub_distrib]
  unfold BoundingSieve.mainSum
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

end LeanLab.AlmostPrimeSums.Decomp1527bFeed1122JRP2
