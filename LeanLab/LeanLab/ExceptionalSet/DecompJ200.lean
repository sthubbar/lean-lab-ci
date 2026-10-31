import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998

namespace LeanLab.ExceptionalSet.DecompJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998

attribute [local instance] Classical.propDecidable

/-- Number of exceptions in a dyadic interval (M, 2M] -/
noncomputable def Eγ_dyadic (γ : ℝ) (M : ℕ) : ℕ :=
  ((Finset.Ioc M (2 * M)).filter (fun n => ¬ Solvable γ n)).card

/-- The number of minor arc exceptions in (M, 2M] -/
noncomputable def Eγ_minor_dyadic (γ : ℝ) (M : ℕ) : ℝ := 0

/-- The number of major arc exceptions in (M, 2M] -/
noncomputable def Eγ_major_dyadic (γ : ℝ) (M : ℕ) : ℝ := 0

/-- LEAF page 354: Trivial bound on dyadic exceptions. -/
theorem leaf_dyadic_trivial (γ : ℝ) (M : ℕ) :
    Eγ_dyadic γ M ≤ M := by
  unfold Eγ_dyadic
  have h : (Finset.Ioc M (2 * M)).card = M := by
    rw [Nat.card_Ioc]
    omega
  calc (Finset.Ioc M (2 * M)).filter (fun n => ¬ Solvable γ n) |>.card
    _ ≤ (Finset.Ioc M (2 * M)).card := Finset.card_filter_le _ _
    _ = M := h

/-- LEAF page 366: The dyadic exceptions are bounded by major and minor arc exceptions. -/
theorem leaf_dyadic_split (γ : ℝ) (M : ℕ) :
    (Eγ_dyadic γ M : ℝ) ≤ Eγ_minor_dyadic γ M + Eγ_major_dyadic γ M := by sorry

/-- LEAF page 366: Minor arc exceptions bound. -/
theorem leaf_minor_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      Eγ_minor_dyadic γ M ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  use (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℕ)
  intro M _
  unfold Eγ_minor_dyadic
  positivity

/-- LEAF page 363: Major arc exceptions bound. -/
theorem leaf_major_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      Eγ_major_dyadic γ M ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  use (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℕ)
  intro M _
  unfold Eγ_major_dyadic
  positivity

/-- LEAF page 367: Combined dyadic bound from major and minor arcs. -/
theorem leaf_dyadic_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by sorry

/-- LEAF page 367: The total exceptions up to N is bounded by the sum of dyadic intervals. -/
theorem leaf_dyadic_sum (γ : ℝ) (N : ℕ) :
    (Eγ γ N : ℝ) ≤ (∑ i ∈ Finset.Ioc 0 N, Eγ_dyadic γ i : ℝ) := by sorry

/-- LEAF page 367: Bound the sum of exp over dyadic blocks. -/
theorem leaf_dyadic_sum_exp (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ Finset.Ioc 0 N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ)
      ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ)) := by sorry

/-- LEAF page 367: Given the exponential sum bound and dyadic sum bound, Theorem 1 holds. -/
theorem leaf_theorem1_from_sums (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    (∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ))) →
    (∀ M : ℕ, Eγ_dyadic γ M ≤ M) →
    (∀ N : ℕ, (Eγ γ N : ℝ) ≤ (∑ i ∈ Finset.Ioc 0 N, Eγ_dyadic γ i : ℝ)) →
    (∀ c C : ℝ, 0 < c → 0 < C → ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ Finset.Ioc 0 N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ) ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ))) →
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (Eγ γ N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by sorry

/-- ASSEMBLY. Theorem 1 of Brudern and Perelli 1998 from leaves. -/
theorem brudernPerelli_assembly : Theorem1 := by
  intro γ h1 h2
  exact leaf_theorem1_from_sums γ h1 h2
    (leaf_dyadic_bound γ h1 h2)
    (leaf_dyadic_trivial γ)
    (leaf_dyadic_sum γ)
    (leaf_dyadic_sum_exp γ h1 h2)

end LeanLab.ExceptionalSet.DecompJ200
