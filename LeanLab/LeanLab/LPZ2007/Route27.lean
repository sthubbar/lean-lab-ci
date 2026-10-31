/-
Route R-0027, T3 MOONSHOT barrier map, PC run 20261020T1203Z-6833, unit U-1232: how far the
Bessel-sup route of P0045 Section 3 can go.

`half_route`: even the best possible minor arc sup, square root cancellation `X^{1/2} L⁴`, gives
through `exceptional_of_sup` only `≪ X^0 L^{10}` exceptions, a power of log, never zero; and the
sup cannot be below `X^{1/2}` on average by Parseval. So the L² route alone cannot give every
large `N`. PROVED as an implication, CONDITIONAL ON `MinorBoundσ (1/2)`, which is NOT known.
Numerics: Lean Lab/LeanLab/LeanLab/LPZ2007/numerics/r0027.out.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LPZ2007.MinorBessel

namespace LeanLab.LPZ2007.Route27

open LeanLab.LPZ2007 LeanLab.LPZ2007.ExceptionalOfSup LeanLab.LPZ2007.MinorBessel

theorem half_route (h : MinorBoundσ (1 / 2)) :
    ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
      ((Exc7 k X P).card : ℝ) ≤ B * Lg X ^ 10 := by
  intro k hk
  obtain ⟨B, X0, H⟩ := exceptional_of_sup h k hk
  refine ⟨B, X0, fun X hX P hP => ?_⟩
  have e : (2 : ℝ) * (1 / 2) - 1 = 0 := by norm_num
  have := H X hX P hP
  rwa [e, Real.rpow_zero, mul_one] at this

end LeanLab.LPZ2007.Route27
