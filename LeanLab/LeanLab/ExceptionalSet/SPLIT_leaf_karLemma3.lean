/-
Split of the sealed statement `leaf_karLemma3` of `LeanLab.ExceptionalSet.KaracubaSplit`,
Karacuba's Lemma 3: for `U > 0`, `q ≥ 1`, `α = a/q + θ/q²` with `(a, q) = 1`, `|θ| ≤ 1`
and every real `β`,

  `Σ_{x=1}^{P} min(U, 1/‖(α x + β)‖) ≤ 6 (U + q log q) (P/q + 1)`,

`‖·‖` being `nint`, the distance to the nearest integer, and `P/q` the integer quotient.

The split keeps the conclusion and cuts the parameters into the four ranges that need
different arguments:

* `leaf_karLemma3_unit`, `q = 1`: `α x + β` is then an integer shift of `θ x + β`, so every
  summand is at most `U` and the right side is `6 U (P + 1)`; the trivial bound `U P` gives it.
* `leaf_karLemma3_few`, `2 ≤ q` and `P < q`: there are fewer than `q` summands and the right
  side is `6 (U + q log q)` because `P/q = 0`. For `0 < |x - x'| < q` the number `a (x - x')/q`
  is at least `1/q` from an integer, so the distances to the nearest integer are `(1/4q)`
  separated and a spacing bound on `P` points of the circle gives the result.
* `leaf_karLemma3_many_large_U`, `2 ≤ q ≤ P` and `q log q ≤ U`: the `U` term of the right side
  dominates, `6 (U + q log q) ≤ 12 U`, so counting the `x` with `‖α x + β‖ < 1/(2U)`, at most
  `4q` per residue class modulo `q`, finishes.
* `leaf_karLemma3_many_small_U`, `2 ≤ q ≤ P` and `U < q log q`: the log term dominates. Read
  `x = r + q j` with `1 ≤ r ≤ q`. Then `α x + β = a j + (a r/q + β) + θ (r + q j)/q²`, the
  integer `a j` drops out of the distance, the `θ` term moves the point by at most `P/q²`, and
  the `q` centres `a r/q + β` are `1/q` apart; the sum is `(P/q + 1)` times a lattice sum
  bounded by `2U + 2q(1 + log q)`.

`leaf_karLemma3_split` is the statement of `leaf_karLemma3`, from these four leaves, with no
`sorry` and without using `leaf_karLemma3`; `sorry` sits on the three remaining LEAF leaves
`leaf_karLemma3_few`, `leaf_karLemma3_many_large_U` and `leaf_karLemma3_many_small_U`.
`leaf_karLemma3_unit` is proved: every summand is at most `U`, so the sum is at most `U P`,
which the right side covers.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Leaves -/

/-- LEAF. The case `q = 1` of Lemma 3: `α = a + θ` and `a x` is an integer, so
`nint (α x + β) = nint (θ x + β)`, every summand `min U (1/nint ...)` is at most `U`, and the
right side `6 (U + 1 * log 1) (P/1 + 1) = 6 U (P + 1)` covers the trivial bound `U * P`. -/
theorem leaf_karLemma3_unit (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : q = 1) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  have hle : ∀ x ∈ Finset.Icc 1 P,
      min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β)) ≤ U :=
    fun x _ => min_le_left _ _
  subst hq
  have hcard : ((Finset.Icc 1 P).card : ℝ) = (P : ℝ) := by
    have h : (Finset.Icc 1 P).card = P := by simp
    rw [h]
  have h2 := Finset.sum_le_sum hle
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : ((Finset.Icc 1 P).card : ℝ) * U ≤ (P : ℝ) * U := by
    rw [hcard]
  have hP : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
  have hgoal : 6 * (U + (1 : ℕ) * Real.log ((1 : ℕ) : ℝ)) * (((P : ℕ) : ℝ) / ((1 : ℕ) : ℝ) + 1)
      = 6 * U * ((P : ℝ) + 1) := by
    norm_num [Real.log_one]
  rw [hgoal]
  nlinarith [h2, h3, hU, hP]

/-- LEAF. The case `2 ≤ q` and `P < q` of Lemma 3: few summands, `P/q = 0`, so the right side
is `6 (U + q log q)`. Every difference `x - x'` with `0 < |x - x'| < q` keeps `a (x - x')/q` at
distance at least `1/q` from an integer, while the `θ` term moves by less than `1/q`, so the
`P` points `α x + β` are `(1/4q)` separated on the circle; a spacing bound on separated points
bounds the sum by `2U + 2q (1 + log q)`. -/
theorem leaf_karLemma3_few (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hPq : P < q) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  sorry

/-- LEAF. The case `2 ≤ q ≤ P` of Lemma 3 where the `U` term dominates, `q log q ≤ U`: the
right side is at most `12 U (P/q + 1)`, and counting the `x` with `‖α x + β‖ < 1/(2U)` per
residue class modulo `q`, where there are at most `4q` of them, keeps the sum inside it. -/
theorem leaf_karLemma3_many_large_U (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hPq : q ≤ P) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1)
    (hLU : q * Real.log q ≤ U) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  sorry

/-- LEAF. The case `2 ≤ q ≤ P` of Lemma 3 where the log term dominates, `U < q log q`. Writing
`x = r + q j` with `1 ≤ r ≤ q`, each residue class has at most `P/q + 1` elements, the integer
`a j` drops out of the distance to the nearest integer, the `θ` term shifts by at most `P/q²`,
and the `q` centres `a r/q + β` are `1/q` apart; the lattice sum over the centres is at most
`2U + 2q (1 + log q)`, and `2U + 2q (1 + log q) ≤ 6 (U + q log q)` for `q ≥ 2`. -/
theorem leaf_karLemma3_many_small_U (U : ℝ) (P : ℕ) (a : ℤ) (q : ℕ) (θ β : ℝ)
    (hU : 0 < U) (hq : 2 ≤ q) (hPq : q ≤ P) (hgcd : Int.gcd a q = 1) (hθ : |θ| ≤ 1)
    (hUL : U < q * Real.log q) :
    ∑ x ∈ Finset.Icc 1 P, min U (1 / nint ((a / q + θ / (q : ℝ) ^ 2) * x + β))
      ≤ 6 * (U + q * Real.log q) * (P / q + 1) := by
  sorry

/-! ### Assembly -/

/-- The statement of `leaf_karLemma3` from the four leaves above, by cases on `q = 1`,
`P < q` and the two ranges of `U` against `q log q`. -/
theorem leaf_karLemma3_split : KarLemma3 := by
  intro U P a q θ β hU hq hgcd hθ
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · exact leaf_karLemma3_unit U P a q θ β hU hq1.symm hgcd hθ
  · have hq2' : 2 ≤ q := by omega
    rcases lt_or_ge P q with hPq | hPq
    · exact leaf_karLemma3_few U P a q θ β hU hq2' hPq hgcd hθ
    · rcases lt_trichotomy (q * Real.log q) U with hLU | hLU | hUL
      · exact leaf_karLemma3_many_large_U U P a q θ β hU hq2' hPq hgcd hθ hLU.le
      · exact leaf_karLemma3_many_large_U U P a q θ β hU hq2' hPq hgcd hθ hLU.le
      · exact leaf_karLemma3_many_small_U U P a q θ β hU hq2' hPq hgcd hθ hUL

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
