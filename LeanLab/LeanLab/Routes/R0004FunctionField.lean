/-
R-0004, T3 MOONSHOT: binary Goldbach over F_q[t] as a model case. Smallest lemma of the route:
the local obstruction in F₂[t], the analogue of "N must be even". Two irreducibles of degree at
least 2 over F₂ have no root, so each takes the value 1 at 0 and at 1, and their sum vanishes at
0 and at 1. So only a quarter of the polynomials can be such a sum. KNOWN mathematics.
Run 20261019T0403Z-4324, unit U-1023. AI-written Lean code, Claude. Checked only by the Lean
kernel. Nothing here is progress on Goldbach; Goldbach is open.
-/
import Mathlib

open Polynomial

namespace LeanLab.Routes.R0004

/-- An irreducible polynomial of degree at least 2 over a field has no root. -/
theorem eval_ne_zero_of_irreducible {K : Type*} [Field K] {p : K[X]} (hp : Irreducible p)
    (hd : 2 ≤ p.natDegree) (a : K) : p.eval a ≠ 0 := by
  intro h
  have := Polynomial.degree_eq_one_of_irreducible_of_root hp h
  have h1 : p.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some this
  omega

/-- In `ZMod 2`, a nonzero value is `1`. -/
theorem zmod2_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

/-- **Local obstruction in F₂[t].** A sum of two irreducibles of degree at least 2 vanishes at
both points of F₂. -/
theorem f2_local {F₁ F₂ : (ZMod 2)[X]} (h₁ : Irreducible F₁) (h₂ : Irreducible F₂)
    (d₁ : 2 ≤ F₁.natDegree) (d₂ : 2 ≤ F₂.natDegree) :
    (F₁ + F₂).eval 0 = 0 ∧ (F₁ + F₂).eval 1 = 0 := by
  have key : ∀ a : ZMod 2, (F₁ + F₂).eval a = 0 := by
    intro a
    rw [eval_add, zmod2_eq_one (eval_ne_zero_of_irreducible h₁ d₁ a),
      zmod2_eq_one (eval_ne_zero_of_irreducible h₂ d₂ a)]
    decide
  exact ⟨key 0, key 1⟩

end LeanLab.Routes.R0004
