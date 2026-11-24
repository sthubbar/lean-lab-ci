/-
Feed split of `prime_supported_large_sieve_finset`, burst-20261122 session S107.
Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2:
Corollary 5.7 second bound, page 44, is "immediate from Prop. 5.1, Prop. 5.2 and Prop. 5.6".
The split below has two leaves:
* `prop52_finset`, Proposition 5.2 page 33, for finitely supported coefficients;
* `prop56`, Proposition 5.6 page 39, display (5.23).
The glue `prime_supported_large_sieve_finset_of_leaves` is sorry free.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp580a

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The restricted sum `G_q(R) = Σ_{r ≤ R, (r,q)=1} μ²(r)/φ(r)` of Helfgott 1312.7748v2,
page 33 display (5.5), equivalently page 32 display (5.2). -/
noncomputable def sieveG (q : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q),
    ((ArithmeticFunction.moebius r : ℝ)) ^ 2 / (Nat.totient r : ℝ)

/-- LEAF: Proposition 5.2, Helfgott 1312.7748v2 page 33, for finitely supported coefficients.
Class HARD. Coefficients supported on primes above `√x`, `Q₀ ≥ 1`, `δ₀ ≥ 1`,
`δ₀ Q₀² ≤ x/2`, `Q = √(x/2δ₀)`; the integral of `|S|²` over the arcs `M_{δ₀,Q₀}` of (3.5)
is at most the maximum over even `q ≤ 2Q₀` and `s ∈ [1, 2Q₀/q]` of
`G_q(2Q₀/sq)/G_q(2Q/sq)` times `Σ |a_n|²`. The maximum is passed as any upper bound `M`,
and `s` ranges over reals, which only strengthens the hypothesis. The proof in the paper is
the large sieve in Montgomery's dual form, pages 30 to 35. -/
theorem prop52_finset (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ₀ : 1 ≤ Q₀) (hsize : δ * Q₀ ^ 2 ≤ x / 2)
    (hsupport : ∀ n ∈ A, ¬n.Prime ∨ (n : ℝ) ≤ Real.sqrt x → a n = 0)
    (M : ℝ)
    (hM : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ 2 * Q₀ → Even q → ∀ s : ℝ, 1 ≤ s →
      s ≤ 2 * Q₀ / q →
        sieveG q (2 * Q₀ / (s * q)) / sieveG q (2 * Real.sqrt (x / (2 * δ)) / (s * q)) ≤ M) :
    (∫ α in majorArcs x δ Q₀ ∩ Set.Ioc (0 : ℝ) 1,
      ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2) ≤
      M * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  sorry

/-- LEAF: Proposition 5.6, Helfgott 1312.7748v2 page 39, display (5.23). Class HARD:
the proof ends in an interval arithmetic computation over all `q < 3.3·10⁹`, page 44.
For `Q ≥ 20000 Q₀`, `Q₀ ≥ 10⁵`, `ρ = log Q₀ / log Q ≤ 0.6`, `1 ≤ q ≤ Q₀` and
`s ∈ [1, Q₀/q]`, `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + c₊)/(log Q + c_E)` with `c₊ = 1.36`
and `c_E` the constant of display (5.14). The condition `ρ ≤ 0.6` is written multiplied out,
which is equivalent since `Q > 1`. -/
theorem prop56 (Q Q₀ : ℝ) (hQ₀ : 1e5 ≤ Q₀) (hQ : 20000 * Q₀ ≤ Q)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) (q : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q₀)
    (s : ℝ) (hs1 : 1 ≤ s) (hs : s ≤ Q₀ / q) :
    sieveG q (Q₀ / (s * q)) / sieveG q (Q / (s * q)) ≤
      (Real.log Q₀ + 1.36) / (Real.log Q + sieveConstant) := by
  sorry

/-- Corollary 5.7 second bound, Helfgott 1312.7748v2 page 44, for finitely supported
coefficients, from Proposition 5.2 and Proposition 5.6 applied with `2Q₀` and `2Q`.
This is the statement of `prime_supported_large_sieve_finset`, copied verbatim.
CONDITIONAL ON `prop52_finset` and `prop56`. -/
theorem prime_supported_large_sieve_finset_of_leaves (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ : 1e5 ≤ Q₀)
    (hsize : (20000 * Q₀) ^ 2 ≤ x / (2 * δ))
    (hpower : 2 * Q₀ ≤ (2 * Real.sqrt (x / (2 * δ))) ^ (0.6 : ℝ))
    (hsupport : ∀ n ∈ A, ¬n.Prime ∨ (n : ℝ) ≤ Real.sqrt x → a n = 0) :
    (∫ α in majorArcs x δ Q₀ ∩ Set.Ioc (0 : ℝ) 1,
      ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2) ≤
      ((Real.log (2 * Q₀) + 1.36) /
        (Real.log (2 * Real.sqrt (x / (2 * δ))) + sieveConstant)) *
          ∑ n ∈ A, ‖a n‖ ^ 2 := by
  have hδ0 : 0 < δ := by linarith
  have hQ0 : 0 < Q₀ := by norm_num at hQ; linarith
  have hsq : Q₀ ^ 2 ≤ x / (2 * δ) := by nlinarith [sq_nonneg Q₀]
  have hsize' : δ * Q₀ ^ 2 ≤ x / 2 := by
    rw [le_div_iff₀ (by positivity)] at hsq
    nlinarith
  have hroot : 20000 * Q₀ ≤ Real.sqrt (x / (2 * δ)) :=
    Real.le_sqrt_of_sq_le hsize
  apply prop52_finset A a x δ Q₀ hx hδ (by norm_num at hQ; linarith) hsize' hsupport
  intro q hq hqQ _ s hs1 hs
  have h2Q : 0 < 2 * Real.sqrt (x / (2 * δ)) := by nlinarith
  have hρ : Real.log (2 * Q₀) ≤ 0.6 * Real.log (2 * Real.sqrt (x / (2 * δ))) := by
    have h := Real.log_le_log (by positivity) hpower
    rwa [Real.log_rpow h2Q] at h
  exact prop56 (2 * Real.sqrt (x / (2 * δ))) (2 * Q₀) (by norm_num at hQ ⊢; linarith)
    (by linarith) hρ q hq hqQ s hs1 hs

end LeanLab.Ternary.Task580
