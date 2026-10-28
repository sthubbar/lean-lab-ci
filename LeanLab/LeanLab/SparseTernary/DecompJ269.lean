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
  sorry

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
