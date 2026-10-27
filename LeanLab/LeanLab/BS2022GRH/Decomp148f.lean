/- AI wrote this Lean code for CODEX task148.
Recovered from the recorded write commands. Fresh checks are required.
Journal Theorem 4, upper sieve at the selected table constants. Goldbach is open. -/
import LeanLab.BS2022GRH.ChenThresholdGRH
namespace LeanLab.BS2022GRH.Decomp148f
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- Finite sifting primes of Theorem 4 p. 1218. -/
def siftingPrimes (P : Set ℕ) (z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ (p : ℝ) < z)
/-- Finite sifted sum of Theorem 4. -/
def sifted (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ supp.filter (fun n => ∀ p ∈ siftingPrimes P z, ¬ p ∣ n), a n
/-- Main mass X of Theorem 4 p. 1219. -/
def mainMass (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (g : ℕ → ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ n ∈ supp, a n * ∏ p ∈ siftingPrimes P z, (1 - g n p)
/-- Divisor remainder r of Theorem 4. -/
def divisorError (supp : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (d : ℕ) : ℝ :=
  (∑ n ∈ supp.filter (fun n => d ∣ n), a n) -
    ∑ n ∈ supp, a n * ∏ p ∈ d.primeFactors, g n p
/-- Remainder R of Theorem 4, squarefree divisors represented by prime subsets. -/
def errorSum (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ) : ℝ :=
  ∑ T ∈ (siftingPrimes P z).powerset.filter
      (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D),
    |divisorError supp a g (∏ p ∈ T, p)|
/-- LEAF. Upper half of Theorem 4 p. 1218 on 1 ≤ s ≤ 3.
CITED source is Bordignon, Johnston and Starichkova, arXiv 2207.09452,
Theorem 6 and Table 1. The row at 6100 supplies constants 112 and 114.
This is the non-strict version already stated by LinearSieveT4. -/
theorem upper_sieve (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    sifted supp a P z ≤
      (2 * exp eulerMascheroniConstant / (log D / log z) +
        (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z +
      errorSum supp a P Q g z D := by
  sorry
end
end LeanLab.BS2022GRH.Decomp148f
#print axioms LeanLab.BS2022GRH.Decomp148f.upper_sieve
