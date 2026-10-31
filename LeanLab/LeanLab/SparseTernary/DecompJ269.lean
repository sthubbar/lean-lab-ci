/-
Copyright (c) 2026 Lean Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI
-/
import Mathlib
import LeanLab.SparseTernary.Arc613FromSW
import LeanLab.SparseTernary.SWPartialSum
import LeanLab.SparseTernary.LocalFactors
import LeanLab.SparseTernary.RepAssembly
import LeanLab.SparseTernary.Section4
import LeanLab.SparseTernary.MajorArcs
import LeanLab.SparseTernary.Major618FromSW

open Finset Filter Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.DecompJ269

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Tail72Proof
open LeanLab.SparseTernary.SWInput
open LeanLab.SparseTernary.SWPartial LeanLab.SparseTernary.Arc613Proof
open LeanLab.SparseTernary.Major618SW

def Iu (u : ℝ) : Finset ℕ := Icc ⌈u⌉₊ ⌊2 * u⌋₊
def Stil_alias (u β : ℝ) : ℂ := ∑ k ∈ Iu u, (ArithmeticFunction.vonMangoldt k : ℂ) * ee (k * β)

/-- LEAF: the per-fraction approximation of display 6.10. -/
theorem per_fraction_approx (A B : ℕ) (hSW : SW (B + 5 * A + 1)) :
    PerFractionApprox (B + 5 * A) (12 * A) := by
  sorry

/-- LEAF: the expansion 5.3 of S over l and r. -/
theorem s_expansion (Z : ℕ) (u α : ℝ) :
    Sexp Z u α = (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q0 Z)) * Stil_alias u (α + ℓ / q0 Z) := by
  sorry

/-- LEAF: the cube expansion 6.11 to 6.12. -/
theorem s_cube_expansion (Z : ℕ) (u α : ℝ) :
    Sexp Z u α ^ 3 = (1 / (q0 Z : ℂ) ^ 3) * ∑ ℓ₁ ∈ range (q0 Z), ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range (q0 Z), ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range (q0 Z), ∑ r₃ ∈ R0 Z,
      ee (-((ℓ₁ * r₁ + ℓ₂ * r₂ + ℓ₃ * r₃ : ℝ) / q0 Z)) *
      Stil_alias u (α + ℓ₁ / q0 Z) * Stil_alias u (α + ℓ₂ / q0 Z) * Stil_alias u (α + ℓ₃ / q0 Z) := by
  rw [s_expansion Z u α, pow_three]
  sorry

/-- LEAF: disjointness of the major arcs. -/
theorem major_arcs_disjoint (Q : ℝ) :
    ∀ q₁ a₁ q₂ a₂ : ℕ, a₁ < q₁ → a₂ < q₂ → a₁.Coprime q₁ → a₂.Coprime q₂ →
      (q₁ : ℝ) ≤ Real.sqrt (Q / 2) → (q₂ : ℝ) ≤ Real.sqrt (Q / 2) →
      (q₁ ≠ q₂ ∨ a₁ ≠ a₂) →
      Disjoint (Set.Ioo ((a₁ : ℝ) / q₁ - 1 / Q) ((a₁ : ℝ) / q₁ + 1 / Q))
               (Set.Ioo ((a₂ : ℝ) / q₂ - 1 / Q) ((a₂ : ℝ) / q₂ + 1 / Q)) := by
  intro q1 a1 q2 a2 h_a1 h_a2 h_cop1 h_cop2 h_q1 h_q2 h_neq
  rw [Set.disjoint_iff_forall_ne]
  intro x hx y hy h_eq
  subst h_eq
  have hq1_pos : 0 < q1 := by linarith
  have hq2_pos : 0 < q2 := by linarith
  have hq1_pos' : (0 : ℝ) < q1 := by exact Nat.cast_pos.mpr hq1_pos
  have hq2_pos' : (0 : ℝ) < q2 := by exact Nat.cast_pos.mpr hq2_pos

  have h_dist : |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| < 2 / Q := by
    have h1 : |x - (a1 : ℝ) / q1| < 1 / Q := by
      rw [abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : |x - (a2 : ℝ) / q2| < 1 / Q := by
      rw [abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc
      |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| ≤ |(a1 : ℝ) / q1 - x| + |x - (a2 : ℝ) / q2| := abs_sub_le _ _ _
      _ = |x - (a1 : ℝ) / q1| + |x - (a2 : ℝ) / q2| := by rw [abs_sub_comm _ _]
      _ < 1 / Q + 1 / Q := add_lt_add h1 h2
      _ = 2 / Q := by ring

  have h_neq_rat : (a1 : ℝ) / q1 ≠ (a2 : ℝ) / q2 := by
    intro h
    have h1 : (a1 : ℝ) * q2 = (a2 : ℝ) * q1 := by
      calc
        (a1 : ℝ) * q2 = ((a1 : ℝ) / q1) * (q1 * q2) := by
          have : ((a1 : ℝ) / q1) * (q1 * q2) = ((a1 : ℝ) * q2) * (q1 / q1) := by ring
          rw [this, div_self hq1_pos'.ne', mul_one]
        _ = ((a2 : ℝ) / q2) * (q1 * q2) := by rw [h]
        _ = (a2 : ℝ) * q1 := by
          have : ((a2 : ℝ) / q2) * (q1 * q2) = ((a2 : ℝ) * q1) * (q2 / q2) := by ring
          rw [this, div_self hq2_pos'.ne', mul_one]
    have h2 : a1 * q2 = a2 * q1 := by exact_mod_cast h1
    have h3 : q1 ∣ q2 := by
      have : q1 ∣ a2 * q1 := dvd_mul_left _ _
      rw [←h2] at this
      exact h_cop1.symm.dvd_of_dvd_mul_left this
    have h4 : q2 ∣ q1 := by
      have : q2 ∣ a1 * q2 := dvd_mul_left _ _
      rw [h2] at this
      exact h_cop2.symm.dvd_of_dvd_mul_left this
    have hq_eq : q1 = q2 := Nat.dvd_antisymm h3 h4
    have ha_eq : a1 = a2 := by
      subst hq_eq
      have : a1 * q1 = a2 * q1 := h2
      exact (Nat.mul_right_cancel hq1_pos) this
    tauto

  have h_diff_ge : 1 / (q1 * q2 : ℝ) ≤ |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| := by
    have h_diff : (a1 : ℝ) / q1 - (a2 : ℝ) / q2 = (a1 * q2 - a2 * q1 : ℝ) / (q1 * q2 : ℝ) := by
      rw [div_sub_div _ _ hq1_pos'.ne' hq2_pos'.ne']
      ring_nf
    have h_abs_div : |(a1 * q2 - a2 * q1 : ℝ) / (q1 * q2 : ℝ)| = |(a1 * q2 - a2 * q1 : ℝ)| / |(q1 * q2 : ℝ)| := by
      rw [abs_div]
    have h_pos_prod : (0 : ℝ) < (q1 * q2 : ℝ) := by positivity
    have h_abs_denom : |(q1 * q2 : ℝ)| = (q1 * q2 : ℝ) := abs_of_pos h_pos_prod
    rw [h_diff, h_abs_div, h_abs_denom]
    have h_int_diff : (a1 * q2 : ℝ) - (a2 * q1 : ℝ) = ((a1 * q2 : ℤ) - (a2 * q1 : ℤ) : ℝ) := by push_cast; rfl
    rw [h_int_diff]
    have h_int_neq : (a1 * q2 : ℤ) - (a2 * q1 : ℤ) ≠ 0 := by
      intro h
      have h1 : (a1 * q2 : ℤ) = (a2 * q1 : ℤ) := sub_eq_zero.mp h
      have h2 : (a1 : ℝ) / q1 = (a2 : ℝ) / q2 := by
        rw [← sub_eq_zero]
        rw [h_diff]
        have h3 : (a1 * q2 : ℝ) - (a2 * q1 : ℝ) = 0 := by exact_mod_cast sub_eq_zero.mpr h1
        rw [h3, zero_div]
      exact h_neq_rat h2
    have h_int_ge : 1 ≤ |(a1 * q2 : ℤ) - (a2 * q1 : ℤ)| := by
      exact Int.one_le_abs h_int_neq
    have h_real_ge : (1 : ℝ) ≤ |((a1 * q2 : ℤ) - (a2 * q1 : ℤ) : ℝ)| := by exact_mod_cast h_int_ge
    have h_div_ge : 1 / (q1 * q2 : ℝ) ≤ |((a1 * q2 : ℤ) - (a2 * q1 : ℤ) : ℝ)| / (q1 * q2 : ℝ) := by
      exact div_le_div_of_nonneg_right h_real_ge h_pos_prod.le
    exact h_div_ge

  have hQ_pos2 : 0 ≤ Q / 2 := by
    by_cases h : 0 ≤ Q / 2
    · exact h
    · push Not at h
      have h_sqrt_zero : Real.sqrt (Q / 2) = 0 := Real.sqrt_eq_zero_of_nonpos h.le
      have h_prod_le_Q2 : (q1 : ℝ) * (q2 : ℝ) ≤ Real.sqrt (Q / 2) * Real.sqrt (Q / 2) :=
        mul_le_mul h_q1 h_q2 hq2_pos'.le (Real.sqrt_nonneg _)
      rw [h_sqrt_zero, mul_zero] at h_prod_le_Q2
      have : (0 : ℝ) < 0 := by linarith
      exact False.elim (lt_irrefl 0 this)

  have h_prod_le : (q1 * q2 : ℝ) ≤ Q / 2 := by
    calc
      (q1 * q2 : ℝ) = (q1 : ℝ) * (q2 : ℝ) := by ring_nf
      _ ≤ Real.sqrt (Q / 2) * Real.sqrt (Q / 2) := mul_le_mul h_q1 h_q2 hq2_pos'.le (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Q / 2)) ^ 2 := by ring
      _ = Q / 2 := Real.sq_sqrt hQ_pos2

  have h_diff_ge_2 : 2 / Q ≤ |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| := by
    calc
      2 / Q = 1 / (Q / 2) := by ring
      _ ≤ 1 / (q1 * q2 : ℝ) := by
        have ht : 0 < (q1 * q2 : ℝ) := by positivity
        exact one_div_le_one_div_of_le ht h_prod_le
      _ ≤ |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| := h_diff_ge

  linarith

/-- LEAF: integration over major arcs reaching 6.13. -/
theorem arc_integration_613 (A B : ℕ) (h_per_frac : PerFractionApprox (B + 5 * A) (12 * A))
    (h_s_exp : ∀ Z u α, Sexp Z u α = (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q0 Z)) * Stil_alias u (α + ℓ / q0 Z))
    (h_cube : ∀ Z u α, Sexp Z u α ^ 3 = (1 / (q0 Z : ℂ) ^ 3) * ∑ ℓ₁ ∈ range (q0 Z), ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range (q0 Z), ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range (q0 Z), ∑ r₃ ∈ R0 Z,
      ee (-((ℓ₁ * r₁ + ℓ₂ * r₂ + ℓ₃ * r₃ : ℝ) / q0 Z)) *
      Stil_alias u (α + ℓ₁ / q0 Z) * Stil_alias u (α + ℓ₂ / q0 Z) * Stil_alias u (α + ℓ₃ / q0 Z))
    (h_disjoint : ∀ Q : ℝ, ∀ q₁ a₁ q₂ a₂ : ℕ, a₁ < q₁ → a₂ < q₂ → a₁.Coprime q₁ → a₂.Coprime q₂ →
      (q₁ : ℝ) ≤ Real.sqrt (Q / 2) → (q₂ : ℝ) ≤ Real.sqrt (Q / 2) →
      (q₁ ≠ q₂ ∨ a₁ ≠ a₂) →
      Disjoint (Set.Ioo ((a₁ : ℝ) / q₁ - 1 / Q) ((a₁ : ℝ) / q₁ + 1 / Q))
               (Set.Ioo ((a₂ : ℝ) / q₂ - 1 / Q) ((a₂ : ℝ) / q₂ + 1 / Q))) :
    Arc613 A B := by
  sorry

theorem Arc613FromSWProp_assembly (A B : ℕ) : Arc613FromSWProp A B := by
  intro hSW
  have h1 := per_fraction_approx A B hSW
  have h2 := s_expansion
  have h3 := s_cube_expansion
  have h4 := major_arcs_disjoint
  exact arc_integration_613 A B h1 h2 h3 h4

end LeanLab.SparseTernary.DecompJ269
