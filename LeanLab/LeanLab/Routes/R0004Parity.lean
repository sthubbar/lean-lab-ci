/-
R-0004 addendum, T3 MOONSHOT: binary Goldbach in 𝔽_q[T], the local obstruction over 𝔽₂. First written as R-0020 in an id clash; R-0004 is the existing route.

Over 𝔽₂ an irreducible polynomial of degree at least 2 has no root, so it takes the value 1 at
both 0 and 1. Hence a sum of two such polynomials vanishes at 0 and at 1, that is it is
divisible by T(T + 1): the 𝔽₂[T] analogue of "a sum of two odd primes is even". The two
degree 1 irreducibles T and T + 1 play the role of the prime 2.

* `eval_eq_one_of_irreducible`: `Irreducible p`, `2 ≤ natDegree p` over `ZMod 2` give
  `p.eval 0 = 1` and `p.eval 1 = 1`.
* `sum_two_irreducibles_even`: `(p + q).eval 0 = 0` and `(p + q).eval 1 = 0` for two such.

Python, same run: every monic f ∈ 𝔽₂[T] of degree 3 to 13 with f(0) = f(1) = 0 is P + Q with
P monic irreducible of degree deg f and Q irreducible of smaller degree, 0 exceptions in
4094 cases; degree 2 has the one exception T² + T. Over 𝔽₃, degrees 2 to 6, 5 exceptions in
1089, none at degrees 2, 5, 6. Prior art: Bender, arXiv 0809.4381, Mathematika, two
irreducibles for q large against the degree; Effinger-Hayes 1991 the ternary analogue.
KNOWN mathematics. AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1163.
Binary Goldbach is OPEN, and so is its 𝔽_q[T] analogue for fixed q and large degree as far as
the lab's one search found.
-/
import Mathlib

namespace LeanLab.Routes.R0004Parity
open Polynomial

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

/-- An irreducible polynomial of degree at least 2 over `𝔽₂` takes the value 1 at 0 and 1. -/
theorem eval_eq_one_of_irreducible {p : (ZMod 2)[X]} (hp : Irreducible p)
    (hd : 2 ≤ p.natDegree) : p.eval 0 = 1 ∧ p.eval 1 = 1 := by
  have key : ∀ a : ZMod 2, p.eval a ≠ 0 := by
    intro a ha
    have h1 := degree_eq_one_of_irreducible_of_root hp ha
    have : p.natDegree = 1 := natDegree_eq_of_degree_eq_some h1
    omega
  exact ⟨zmod2_eq_one_of_ne_zero (key 0), zmod2_eq_one_of_ne_zero (key 1)⟩

/-- **The parity of 𝔽₂[T]**: a sum of two irreducibles of degree at least 2 vanishes at 0 and
at 1, so it is divisible by `T (T + 1)`. -/
theorem sum_two_irreducibles_even {p q : (ZMod 2)[X]} (hp : Irreducible p)
    (hq : Irreducible q) (hdp : 2 ≤ p.natDegree) (hdq : 2 ≤ q.natDegree) :
    (p + q).eval 0 = 0 ∧ (p + q).eval 1 = 0 := by
  obtain ⟨p0, p1⟩ := eval_eq_one_of_irreducible hp hdp
  obtain ⟨q0, q1⟩ := eval_eq_one_of_irreducible hq hdq
  simp only [eval_add, p0, p1, q0, q1]
  exact ⟨rfl, rfl⟩

/-- Vacuity: `X² + X + 1` is irreducible of degree 2 over `𝔽₂`, so the hypotheses hold. -/
lemma natDegree_x2x1 : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!

theorem irreducible_x2x1 : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  have hd := natDegree_x2x1
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide) ?_
  intro x hx
  rw [IsRoot.def, eval_add, eval_add, eval_pow, eval_X, eval_one] at hx
  fin_cases x <;> revert hx <;> decide

example : ((X ^ 2 + X + 1 : (ZMod 2)[X]) + (X ^ 2 + X + 1)).eval 0 = 0 :=
  (sum_two_irreducibles_even irreducible_x2x1 irreducible_x2x1 natDegree_x2x1.ge
    natDegree_x2x1.ge).1

#print axioms eval_eq_one_of_irreducible
#print axioms sum_two_irreducibles_even
#print axioms irreducible_x2x1

end LeanLab.Routes.R0004Parity
