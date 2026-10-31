/-
Copyright (c) 2026 Lean Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI
-/

import Mathlib
import LeanLab.SparseTernary.Major618FromSW
import LeanLab.SparseTernary.SWPartialSum
import LeanLab.SparseTernary.LocalFactors
import LeanLab.SparseTernary.RepAssembly

open Finset Filter Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Arc613Proof

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Tail72Proof
open LeanLab.SparseTernary.Major618SW LeanLab.SparseTernary.SWInput
open LeanLab.SparseTernary.SWPartial

/-- The total sum from `u` to `2u` with von Mangoldt weights. -/
def LambdaSum (u β : ℝ) (q a : ℕ) : ℂ :=
  ∑ k ∈ Iw u, (ArithmeticFunction.vonMangoldt k : ℂ) * ee (k * (a / q + β : ℝ))

/-- The per-fraction approximation. -/
def PerFractionApprox (N : ℕ) (K : ℝ) : Prop :=
  ∃ D u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log u ^ N →
    a.Coprime q → ∀ β : ℝ,
    ‖LambdaSum u β q a - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Tsum u β‖ ≤
      D * (1 + |β| * u) * u / Real.log u ^ K

/-- The main implication we want to prove. -/
def Arc613FromSWProp (A B : ℕ) : Prop := SW (B + 5 * A + 1) → Arc613 A B

end LeanLab.SparseTernary.Arc613Proof
