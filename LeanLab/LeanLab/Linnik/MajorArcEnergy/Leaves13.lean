/-
Gallagher 1975 P0094 pp.128 to 131. Open leaves of the display 13 reduction.
Displays 3, 7, 9 and 11 are Gallagher's own derivations; display 5 and the two
singular series estimates in display 11 are cited from reference 10, Montgomery and
Vaughan 1975, and are CITED-LEFT walls, not split further.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.MajorArcEnergy.Defs

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries ramanujanSum)
open LeanLab.Linnik.U7204 (Sg)

/-- LEAF, OFF ROUTE: superseded by `major_arc_pair_expansion_of_steps` in Display3.lean, the same
statement PROVED. Gallagher 1975 p.128 display 3, Gallagher's own derivation from the first
character expansion of p.128 and S(alpha) at most a constant times N over log N:
the major arc integral equals the sum of J_n(chi, chi') over primitive chi, chi' to
conductors at most P, up to O(P^(5/2)). The expansion is the proved hypothesis shape. -/
theorem major_arc_pair_expansion
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ,
        ‖(∫ α in majorArcs N ((N : ℝ) ^ θ),
            ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) -
          ∑ x ∈ family ((N : ℝ) ^ θ), ∑ y ∈ family ((N : ℝ) ^ θ),
            pairSum N ((N : ℝ) ^ θ) n x y‖ ≤ K * ((N : ℝ) ^ θ) ^ (5 / 2 : ℝ) := by
  sorry

/-- LEAF, CITED-LEFT. Gallagher 1975 p.129 display 5, quoted from the evaluation in
reference 10, Montgomery and Vaughan 1975: for a character chi to modulus q and
conductor r, |c_n(chi)| is at most r^(1/2) phi(q)/phi(q_n) with q_n equal to q/(q, n),
and c_n(chi) vanishes unless r divides q_n and q_n/r is squarefree and prime to r.
Gallagher gives no proof; this is a citation wall and is not split. -/
theorem induced_cn_bound {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (n : ℤ) :
    ‖cn χ n‖ ≤ Real.sqrt χ.conductor * (q.totient : ℝ) /
        ((q / Nat.gcd q n.natAbs).totient : ℝ) ∧
      (cn χ n ≠ 0 → χ.conductor ∣ q / Nat.gcd q n.natAbs ∧
        Squarefree (q / Nat.gcd q n.natAbs / χ.conductor) ∧
        Nat.Coprime (q / Nat.gcd q n.natAbs / χ.conductor) χ.conductor) := by
  sorry

/-- LEAF, OFF ROUTE: superseded by `pair_weight_bound_of_cited` in Display7.lean, the same
statement proved from the CITED-LEFT display 5. Gallagher 1975 p.129 display 7 with its printed proof from display 5:
C_n(chi, chi') is at most a constant times n/phi(n), uniformly in the primitive
characters and in P. -/
theorem pair_weight_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ) (x y : PChar), n ≠ 0 →
      x.2.IsPrimitive → y.2.IsPrimitive → pairWeight P n x y ≤ K * totientWeight n := by
  sorry

/-- LEAF, OFF ROUTE: superseded by `principal_arc_integral_of_steps` in Display9.lean, the same
statement PROVED. Gallagher 1975 p.130 display 9, Gallagher's own derivation: partial summation
for T, the full period integral of |T|^2 e(n beta) equal to J(n), and J(n) at most
J(0) asymptotic to N/log^2 N give, for q at most P,
I_{n,q}(1, 1) equal to J(n) plus O(q Q L^(-2) + N^(1/2) L^(-1) ||R|| + ||R||^2). -/
theorem principal_arc_integral :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ,
        ∀ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
          ‖arcIntegral N ((N : ℝ) ^ θ) n q one one - (Jn N n : ℂ)‖ ≤
            K * (q * ((N : ℝ) / (N : ℝ) ^ θ) / Real.log N ^ 2 +
              Real.sqrt N / Real.log N * remNorm N ((N : ℝ) ^ θ) +
              remNorm N ((N : ℝ) ^ θ) ^ 2) := by
  sorry

/-- LEAF, CITED-LEFT. Gallagher 1975 p.130 before display 11, quoting reference 10,
equation 6.13: the singular series truncated at P differs from the full series by
O(n/phi(n) tau(n) P^(-1)). A citation wall, not split. -/
theorem singular_tail_cited :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ), 1 ≤ P → n ≠ 0 →
      ‖singTrunc P n - singSeries n‖ ≤
        K * totientWeight n * n.natAbs.divisors.card / P := by
  sorry

/-- LEAF, CITED-LEFT. Gallagher 1975 p.130 before display 11, quoting reference 10,
equation 6.14: the sum over q at most P of (mu(q)/phi(q))^2 |c_q(n)| q is
O(n/phi(n) tau(n) log P), and without the factor q it is O(n/phi(n)).
A citation wall, not split. -/
theorem singular_weighted_sums_cited :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ), 2 ≤ P → n ≠ 0 →
      (∑ q ∈ Icc 1 ⌊P⌋₊, ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 *
          ‖ramanujanSum q n‖ * q ≤
        K * totientWeight n * n.natAbs.divisors.card * Real.log P) ∧
      (∑ q ∈ Icc 1 ⌊P⌋₊, ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 *
          ‖ramanujanSum q n‖ ≤ K * totientWeight n) := by
  sorry

/-- LEAF, OFF ROUTE: superseded by `principal_pair_sum_of_leaves` in Display11.lean, which proves
the same statement from the three leaves named below; nothing on the route uses this one.
Gallagher 1975 p.130 display 11, Gallagher's own assembly of display 9, the
identity tau(1_q) equal to mu(q), c_n(1_q) equal to c_q(n), and the two cited estimates
`singular_tail_cited` and `singular_weighted_sums_cited`:
J_n(1, 1) equals J(n) S(n) plus
O(N L^(-2) n/phi(n) tau(n) log P / P + n/phi(n) (N^(1/2) L^(-1) ||R|| + ||R||^2)). -/
theorem principal_pair_sum :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ, n ≠ 0 →
        ‖pairSum N ((N : ℝ) ^ θ) n one one - (Jn N n : ℂ) * singSeries n‖ ≤
          K * totientWeight n *
            ((N : ℝ) / Real.log N ^ 2 * n.natAbs.divisors.card *
                (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) +
              Real.sqrt N / Real.log N * remNorm N ((N : ℝ) ^ θ) +
              remNorm N ((N : ℝ) ^ θ) ^ 2) := by
  sorry

end LeanLab.Linnik.MajorArcEnergy
