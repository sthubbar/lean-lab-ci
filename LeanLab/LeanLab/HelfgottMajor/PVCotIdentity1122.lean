import Mathlib
import LeanLab.HelfgottMajor.PVEvenTrunc1122

/-!
# HelfgottMajor cot identity, route burst S68, burst-20261122

Proof of the LEAF `PVEvenTrunc1122.cot_identity`, the exact finite cotangent expansion for even
primitive χ, Frolenkov arXiv 1107.0381 display 12 with M = 0 and display 17 before truncation:
`τ(χ⁻¹) (2 S(K) + χ(K)) = ∑_h χ⁻¹(h) cot(π h/q) sin(2π K h/q)`.

Route: for h ≠ 0, `cos_sum_cot` turns `cot(πh/q) sin(2πKh/q)` into
`2 ∑_{m<K} cos(2πmh/q) - 1 + cos(2πKh/q)`; the h = 0 term vanishes as χ⁻¹(0) = 0;
the constant sums to 0 over h since χ⁻¹ ≠ 1; each cosine sum is `χ(n) τ(χ⁻¹)` by
`PV420Split1122.gauss_twist_even` applied to χ⁻¹.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVCotIdentity1122

open Real Finset

/-- The cosine as an average of `stdAddChar` values. PROVED. -/
theorem cos_eq_stdAddChar {q : ℕ} [NeZero q] (n : ℕ) (h : ZMod q) :
    ((cos (2 * π * n * (h.val : ℝ) / q) : ℝ) : ℂ) =
      (ZMod.stdAddChar ((n : ZMod q) * h) + ZMod.stdAddChar (-((n : ZMod q) * h))) / 2 := by
  have e1 : (n : ZMod q) * h = (((n * h.val : ℕ) : ℤ) : ZMod q) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have e2 : -((n : ZMod q) * h) = ((-((n * h.val : ℕ) : ℤ) : ℤ) : ZMod q) := by
    rw [e1]; push_cast; ring
  rw [e2, e1, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, Complex.ofReal_cos, Complex.cos]
  push_cast
  congr 3 <;> ring_nf

/-- The cosine twisted Gauss sum: `∑_h χ⁻¹(h) cos(2π n h/q) = χ(n) τ(χ⁻¹)`. PROVED. -/
theorem cos_twist {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (heven : χ (-1) = 1) (n : ℕ) :
    ∑ h : ZMod q, χ⁻¹ h * ((cos (2 * π * n * (h.val : ℝ) / q) : ℝ) : ℂ) =
      χ (n : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχ' := LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ
  have heven' : χ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', heven, inv_one]
  have := LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_even hχ' heven' (n : ZMod q)
  rw [inv_inv] at this
  rw [this]
  exact sum_congr rfl fun h _ => by rw [cos_eq_stdAddChar]

/-- The sum of χ⁻¹ vanishes for χ primitive and q ≠ 1. PROVED. -/
theorem sum_inv_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) : ∑ h : ZMod q, χ⁻¹ h = 0 := by
  have hχ' := LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ
  refine MulChar.sum_eq_zero_of_ne_one fun h1 => hq ?_
  rw [DirichletCharacter.IsPrimitive, h1, DirichletCharacter.conductor_one] at hχ'
  exact hχ'.symm

/-- The termwise expansion: for every h, χ⁻¹(h) cot(πh/q) sin(2πKh/q) equals
χ⁻¹(h) (2 ∑_{m<K} cos(2πmh/q) - 1 + cos(2πKh/q)). PROVED. -/
theorem term_expand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q ≠ 1) (K : ℕ)
    (h : ZMod q) :
    χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) =
      χ⁻¹ h * (2 * ∑ m ∈ range K, ((cos (2 * π * m * (h.val : ℝ) / q) : ℝ) : ℂ) - 1 +
        ((cos (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)) := by
  by_cases h0 : h = 0
  · subst h0
    have : χ⁻¹ (0 : ZMod q) = 0 := by
      have : Nontrivial (ZMod q) := by
        rw [ZMod.nontrivial_iff]; exact hq
      exact MulChar.map_zero _
    rw [this, zero_mul, zero_mul]
  · congr 1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hv0 : 0 < h.val := by
      rcases Nat.eq_zero_or_pos h.val with hv | hv
      · exact absurd ((ZMod.val_eq_zero h).1 hv) h0
      · exact hv
    have hvq : h.val < q := ZMod.val_lt h
    have hsin : sin (π * (h.val : ℝ) / q) ≠ 0 := by
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      · have : (0 : ℝ) < h.val := by exact_mod_cast hv0
        positivity
      · rw [div_lt_iff₀ hq0]
        have : (h.val : ℝ) < q := by exact_mod_cast hvq
        nlinarith [pi_pos]
    have key := LeanLab.HelfgottMajor.PVEvenTrunc1122.cos_sum_cot _ hsin K
    have e : ∀ n : ℕ, (n : ℝ) * (2 * (π * (h.val : ℝ) / q)) = 2 * π * n * (h.val : ℝ) / q := by
      intro n; ring
    simp only [e] at key
    have key' : cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) =
        2 * ∑ m ∈ range K, cos (2 * π * m * (h.val : ℝ) / q) - 1 +
          cos (2 * π * K * (h.val : ℝ) / q) := by linarith
    rw [key']
    push_cast
    ring

/-- LEAF proved: the exact statement of `PVEvenTrunc1122.cot_identity`, Frolenkov display 12 with
M = 0 and display 17 before truncation. PROVED. -/
theorem cot_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (K : ℕ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * (2 * ∑ m ∈ range K, χ (m : ZMod q) + χ (K : ZMod q)) =
      ∑ h : ZMod q, χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) := by
  simp_rw [term_expand χ hq K]
  simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, mul_sum]
  rw [sum_inv_eq_zero hχ hq, cos_twist hχ heven K, sum_comm]
  have : ∀ m ∈ range K, ∑ h : ZMod q, χ⁻¹ h * (2 * ((cos (2 * π * m * (h.val : ℝ) / q) : ℝ) : ℂ))
      = 2 * (χ (m : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) := by
    intro m _
    rw [← cos_twist hχ heven m, mul_sum]
    exact sum_congr rfl fun h _ => by ring
  rw [sum_congr rfl this, sub_zero]
  congr 1
  · exact sum_congr rfl fun i _ => by ring
  · ring

example : type_of% @cot_identity =
    type_of% @LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_identity := rfl

end LeanLab.HelfgottMajor.PVCotIdentity1122

#print axioms LeanLab.HelfgottMajor.PVCotIdentity1122.cos_eq_stdAddChar
#print axioms LeanLab.HelfgottMajor.PVCotIdentity1122.cos_twist
#print axioms LeanLab.HelfgottMajor.PVCotIdentity1122.sum_inv_eq_zero
#print axioms LeanLab.HelfgottMajor.PVCotIdentity1122.term_expand
#print axioms LeanLab.HelfgottMajor.PVCotIdentity1122.cot_identity
