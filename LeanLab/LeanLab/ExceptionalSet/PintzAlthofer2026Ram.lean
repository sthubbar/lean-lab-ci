/-
# Pintz and Althöfer 2026, (4.15): the Ramanujan sum bound

Unit U-1125, T2 FRONTIER, idea I-0080, run 20261019T2303Z-16260.

arXiv 2610.15559v1 Section 4.3, (4.15) and the line after it: "use |c_q(n)| ≤ (q, n),
q/φ(q) ≪_δ q^δ, and (q, n) = Σ_{d | (q,n)} φ(d)". The lab's `c_q(n)` is
`HeathBrown1985.ramanujan q n = Σ_{d | (n,q)} d μ(q/d)`, equal to the exponential sum by
`PNTPort.Vinogradov.ramanujan_sum`.

* `ramanujan_abs_le_sigma`: `|c_q(n)| ≤ σ(gcd(n, q))`, the triangle inequality, every q, n.
* `ramanujan_abs_le_sigma_le`: `σ(g) ≤ g · τ(g)`, so `|c_q(n)| ≤ (q, n) τ((q, n))`, enough for
  every `≪ X^η` use in (4.15) since τ(m) ≪_η m^η.

The sharp `|c_q(n)| ≤ (q, n)` is not proved here. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.HeathBrown1985.Statements

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Ram

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

/-- `|c_q(n)| ≤ σ₁((n, q))`. -/
theorem ramanujan_abs_le_sigma (q n : ℕ) :
    |LeanLab.HeathBrown1985.ramanujan q n| ≤ (σ 1 (n.gcd q) : ℝ) := by
  unfold LeanLab.HeathBrown1985.ramanujan
  rw [ArithmeticFunction.sigma_one_apply]
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
  rw [abs_mul, Nat.abs_cast]
  have : |((μ (q / d) : ℤ) : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := q / d)
    exact_mod_cast h
  calc (d : ℝ) * |((μ (q / d) : ℤ) : ℝ)| ≤ (d : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)
    _ = d := mul_one _

/-- `σ₁(g) ≤ g · τ(g)`: every divisor is at most `g`. -/
theorem sigma_le_mul_card (g : ℕ) : σ 1 g ≤ g * g.divisors.card := by
  rw [ArithmeticFunction.sigma_one_apply, mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum fun d hd => Nat.divisor_le hd

/-- `|c_q(n)| ≤ (n, q) · τ((n, q))`. -/
theorem ramanujan_abs_le_gcd_mul_tau (q n : ℕ) :
    |LeanLab.HeathBrown1985.ramanujan q n| ≤ ((n.gcd q) * (n.gcd q).divisors.card : ℕ) :=
  (ramanujan_abs_le_sigma q n).trans (by exact_mod_cast sigma_le_mul_card _)

/-- Vacuity and a check: `c_6(4) = Σ_{d | 2} d μ(6/d) = μ 6 + 2 μ 3 = 1 − 2 = −1`. -/
example : LeanLab.HeathBrown1985.ramanujan 6 4 = -1 := by
  unfold LeanLab.HeathBrown1985.ramanujan
  have hd : (Nat.gcd 4 6).divisors = {1, 2} := by decide
  have h3 : μ 3 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h2 : μ 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h6 : μ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num), h2, h3]
    norm_num
  rw [hd, Finset.sum_pair (by norm_num)]
  norm_num [h6, h3]

end LeanLab.ExceptionalSet.PintzAlthofer2026Ram
