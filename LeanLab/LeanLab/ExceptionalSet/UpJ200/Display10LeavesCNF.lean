import LeanLab.ExceptionalSet.UpJ200.Display10Leaves

/-!
# Split of the two class number formula leaves of `Display10Leaves`

Burst burst-20261122, Claude cloud session S132. AI wrote the Lean code. Binary Goldbach is open.

Each of `Display10Leaves.leaf_cnf_odd` and `Display10Leaves.leaf_cnf_even` is split into the
two halves of Davenport, Multiplicative Number Theory, chapter 6:

* the analytic half, Dirichlet's finite closed form for `L(1, χ)` from chapter 1 and the
  Gauss sum modulus `|τ(χ)| = √r` of chapter 2, stated in absolute value so the sign of the
  Gauss sum is not needed;
* the arithmetic half, Dirichlet's class number formula identifying the finite sum with
  `2 r h / w`, respectively `2 h log ε`.

`leaf_cnf_odd_of_leaves` and `leaf_cnf_even_of_leaves` prove the exact original statements
from the halves.  Both halves were checked numerically for many fundamental discriminants.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Display10LeavesCNF

open Real

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 1 and chapter 6, Dirichlet's closed
form for an odd primitive character, class MEDIUM. For a real primitive odd character `χ`
modulo `r`, `L(1, χ) = (π i τ(χ) / r²) ∑_{a < r} χ(a) a` up to the sign conventions, and with
`|τ(χ)| = √r` this gives `|L(1, χ)| = π / (r √r) · |∑_{a < r} χ(a) a|`. -/
theorem leaf_odd_finite : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = -1 →
    ‖χ.LFunction 1‖ = π / (r * Real.sqrt r) *
      ‖∑ a ∈ Finset.range r, χ a * (a : ℂ)‖ := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 6, the arithmetic class number
formula for an imaginary quadratic field of discriminant `-r`, class HARD:
`h = -(w / 2r) ∑_{a < r} χ(a) a`, so `|∑_{a < r} χ(a) a| = 2 r h / w` with class number
`h ≥ 1` and `w ∈ {2, 4, 6}` the number of roots of unity. -/
theorem leaf_odd_arith : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = -1 →
    ∃ (h w : ℕ), 1 ≤ h ∧ w ∈ ({2, 4, 6} : Finset ℕ) ∧
      ‖∑ a ∈ Finset.range r, χ a * (a : ℂ)‖ = 2 * r * h / w := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 1 and chapter 6, Dirichlet's closed
form for an even primitive character, class MEDIUM. For a real primitive even nonprincipal
character `χ` modulo `r`, `L(1, χ) = -(τ(χ) / r) ∑_{a < r} χ(a) log |1 - e(a/r)|`, and since
`|1 - e(a/r)| = 2 sin(π a / r)`, `∑ χ(a) = 0` and `|τ(χ)| = √r`, this gives
`|L(1, χ)| = |∑_{a < r} χ(a) log sin(π a / r)| / √r`. -/
theorem leaf_even_finite : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = 1 →
    ‖χ.LFunction 1‖ =
      ‖∑ a ∈ Finset.range r, χ a * (Real.log (Real.sin (π * a / r)) : ℂ)‖ / Real.sqrt r := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 6, the arithmetic class number
formula for a real quadratic field of discriminant `r`, class HARD:
`∑_{a < r} χ(a) log sin(π a / r) = -2 h log ε` with class number `h ≥ 1` and fundamental unit
`ε = (v + u √r)/2`, where `v, u` are positive integers with `v² - r u² = ±4`. -/
theorem leaf_even_arith : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = 1 →
    ∃ (h u v : ℕ), 1 ≤ h ∧ 1 ≤ u ∧ 1 ≤ v ∧
      ((v : ℤ) ^ 2 - r * u ^ 2 = 4 ∨ (v : ℤ) ^ 2 - r * u ^ 2 = -4) ∧
      ‖∑ a ∈ Finset.range r, χ a * (Real.log (Real.sin (π * a / r)) : ℂ)‖ =
        2 * h * Real.log ((v + u * Real.sqrt r) / 2) := by
  sorry

/-- Exact statement of `Display10Leaves.leaf_cnf_odd`, PROVED from the two odd halves. -/
theorem leaf_cnf_odd_of_leaves : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = -1 →
    ∃ (h w : ℕ), 1 ≤ h ∧ w ∈ ({2, 4, 6} : Finset ℕ) ∧
      ‖χ.LFunction 1‖ = 2 * π * h / (w * Real.sqrt r) := by
  intro r hr χ hp hsq hne hodd
  obtain ⟨h, w, hh, hw, hS⟩ := leaf_odd_arith r hr χ hp hsq hne hodd
  refine ⟨h, w, hh, hw, ?_⟩
  rw [leaf_odd_finite r hr χ hp hsq hne hodd, hS]
  have : NeZero r := hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hrpos : (0 : ℝ) < r := by positivity
  have hs0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hrpos).ne'
  have hw0 : (w : ℝ) ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> norm_num
  field_simp

/-- Exact statement of `Display10Leaves.leaf_cnf_even`, PROVED from the two even halves,
with the class number of the original leaf taken as twice the class number. -/
theorem leaf_cnf_even_of_leaves : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → χ (-1) = 1 →
    ∃ (h u v : ℕ), 1 ≤ h ∧ 1 ≤ u ∧ 1 ≤ v ∧
      ((v : ℤ) ^ 2 - r * u ^ 2 = 4 ∨ (v : ℤ) ^ 2 - r * u ^ 2 = -4) ∧
      ‖χ.LFunction 1‖ = h * Real.log ((v + u * Real.sqrt r) / 2) / Real.sqrt r := by
  intro r hr χ hp hsq hne hev
  obtain ⟨h, u, v, hh, hu, hv, hpell, hT⟩ := leaf_even_arith r hr χ hp hsq hne hev
  refine ⟨2 * h, u, v, by omega, hu, hv, hpell, ?_⟩
  rw [leaf_even_finite r hr χ hp hsq hne hev, hT]
  push_cast
  ring

end LeanLab.ExceptionalSet.UpJ200.Display10LeavesCNF

#print axioms LeanLab.ExceptionalSet.UpJ200.Display10LeavesCNF.leaf_cnf_odd_of_leaves
#print axioms LeanLab.ExceptionalSet.UpJ200.Display10LeavesCNF.leaf_cnf_even_of_leaves
