/-
P0002 J.-R. Chen 1973, unit U-1527 file b, burst-20261122 feed1122 split of the two deep
main-term leaves `Decomp1527b.jr_mainSum_upper` and `Decomp1527b.jr_mainSum_lower`.

The split follows the proof of the linear sieve main term in Iwaniec-Kowalski, Section 6.4
equations (6.6)-(6.8) and Theorem 11.13, and Friedlander-Iwaniec, Opera de Cribro,
Section 6.3 and Chapter 11: the Rosser sum `Σ_{d∣P} λ^±_d g(d)` equals `V(z)` minus the
Buchstab tail `Σ_{e ∈ B^±} μ(e) g(e) V(p(e))`, where `B^±` is the set of first failures of the
Rosser cut-off and `p(e)` is the least prime factor of `e`; the sign of `μ(e)` on `B^±` is fixed
by the parity of the failing index; the analytic heart is the bound of the tail by
`V(z)(F(s) - 1 + O((log D)^{-1/3}))`, respectively `V(z)(1 - f(s) + O((log D)^{-1/3}))`.

This file imports `Decomp1527b`, which defines `rosserWeight` and `LinearDensity`, so the
original file cannot import it back; the parents are proved here as `jr_mainSum_upper_of_leaves`
and `jr_mainSum_lower_of_leaves`, with exactly the statements of the parents.

AI-written Lean code, Claude, 2026-11-22. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.AlmostPrimeSums.Decomp1527b

namespace LeanLab.AlmostPrimeSums.Decomp1527bFeed1122JR
open Finset Real ArithmeticFunction BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a
open LeanLab.AlmostPrimeSums.Decomp1527b
attribute [local instance] Classical.propDecidable

/-- LEAF: Iwaniec-Kowalski (6.6)-(6.8), Buchstab decomposition of a Rosser sum; Opera de Cribro
Section 6.3. Class MEDIUM, a finite combinatorial identity. For every level `D` and either
sign `b`, `Σ_{d∣P} λ^b_d g(d) = V(P) - Σ_{e ∈ B^b} μ(e) g(e) V(p(e))`, where `B^b` is the set of
divisors `e ∣ P` that fail the Rosser cut-off while `e / p(e)` passes it, `p(e) = e.minFac` is
the least prime factor, and `V(p) = ∏_{q ∣ P, q < p} (1 - g(q))`. Proof: every `d ∣ P` failing
the cut-off factors uniquely as `d = e f` with `e ∈ B^b` its prefix up to the first failing
prime and `f ∣ P(p(e))`, and `Σ_{f ∣ P(p)} μ(f) g(f) = V(p)`. -/
theorem rosser_mainSum_buchstab (s : BoundingSieve) (D : ℝ) (b : Bool) :
    s.mainSum (rosserWeight D b) = (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) -
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        (ArithmeticFunction.moebius e : ℝ) * s.nu e *
          ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < e.minFac), (1 - s.nu q) := by
  sorry

/-- LEAF: Iwaniec-Kowalski (6.30) and the remark after it, parity of the first failure of the
Rosser cut-off; Opera de Cribro Section 6.3. Class MEDIUM. If `e ∣ P` fails the cut-off while
`e / p(e)` passes it, the failing index is the last one, so the number of prime factors of `e`
is odd for the upper weights and even for the lower weights: `μ(e) = -1` for `b = true` and
`μ(e) = 1` for `b = false`. -/
theorem moebius_of_first_failure (s : BoundingSieve) (D : ℝ) (b : Bool) {e : ℕ}
    (he : e ∈ s.prodPrimes.divisors.filter
      (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0)) :
    (ArithmeticFunction.moebius e : ℝ) = if b = true then -1 else 1 := by
  sorry

/-- LEAF: Iwaniec-Kowalski Theorem 11.13 and its proof via the iterated
Buchstab bounds `T_n` and the delay differential equations for `F`, `f`; Halberstam-Richert
Theorem 8.4; Opera de Cribro Chapter 11. Class HARD. Upper Buchstab tail: given `K ≥ 0` there
is `C > 0` with `Σ_{e ∈ B^+} g(e) V(p(e)) ≤ V(z)(F(s) - 1 + C (log D)^{-1/3})`,
`s = log D / log z`, for every sieve problem with all primes of `P` below `z`, density
`Ω₁(K)` and `2 ≤ z ≤ D ≤ z⁵`. -/
theorem rosser_upper_tail_le (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D true e = 0 ∧ rosserWeight D true (e / e.minFac) ≠ 0),
        s.nu e * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < e.minFac), (1 - s.nu q)
      ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) - 1 + C * log D ^ (-(1 / 3 : ℝ))) := by
  sorry

/-- LEAF: Iwaniec-Kowalski Theorem 11.13 and its proof, lower half; Halberstam-Richert
Theorem 8.3; Opera de Cribro Chapter 11. Class HARD. Lower Buchstab tail: given `K ≥ 0` there
is `C > 0` with `Σ_{e ∈ B^-} g(e) V(p(e)) ≤ V(z)(1 - f(s) + C (log D)^{-1/3})`,
`s = log D / log z`, for every sieve problem with all primes of `P` below `z`, density
`Ω₁(K)`, `2 ≤ z` and `z² ≤ D ≤ z⁴`. -/
theorem rosser_lower_tail_le (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D false e = 0 ∧ rosserWeight D false (e / e.minFac) ≠ 0),
        s.nu e * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < e.minFac), (1 - s.nu q)
      ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (1 - fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))) := by
  sorry

/-- The Rosser sum in terms of the unsigned Buchstab tail, from the two combinatorial leaves. -/
theorem rosser_mainSum_eq_tail (s : BoundingSieve) (D : ℝ) (b : Bool) :
    s.mainSum (rosserWeight D b) = (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) -
      (if b = true then -1 else 1) *
      ∑ e ∈ s.prodPrimes.divisors.filter
          (fun e => rosserWeight D b e = 0 ∧ rosserWeight D b (e / e.minFac) ≠ 0),
        s.nu e * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < e.minFac), (1 - s.nu q) := by
  rw [rosser_mainSum_buchstab, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  rw [moebius_of_first_failure s D b he, mul_assoc]

/-- **Parent `Decomp1527b.jr_mainSum_upper`, assembled from the leaves** `rosser_mainSum_buchstab`,
`moebius_of_first_failure`, `rosser_upper_tail_le`. Same statement as the parent. -/
theorem jr_mainSum_upper_of_leaves (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      s.mainSum (rosserWeight D true) ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := rosser_upper_tail_le K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hden => ?_⟩
  have ht := h s z D hz hzD hDz hP hden
  rw [rosser_mainSum_eq_tail]
  simp only [if_true]
  linarith

/-- **Parent `Decomp1527b.jr_mainSum_lower`, assembled from the leaves** `rosser_mainSum_buchstab`,
`moebius_of_first_failure`, `rosser_lower_tail_le`. Same statement as the parent. -/
theorem jr_mainSum_lower_of_leaves (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))) ≤ s.mainSum (rosserWeight D false) := by
  obtain ⟨C, hC, h⟩ := rosser_lower_tail_le K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hden => ?_⟩
  have ht := h s z D hz hzD hDz hP hden
  rw [rosser_mainSum_eq_tail]
  simp only [Bool.false_eq_true, if_false]
  linarith

end LeanLab.AlmostPrimeSums.Decomp1527bFeed1122JR
