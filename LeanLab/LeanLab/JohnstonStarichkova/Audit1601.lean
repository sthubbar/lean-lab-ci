/-
Unit U-1601, statement audit of JohnstonStarichkova DecompJ274.sieveRange_of_thm42.
AI wrote this Lean code. Goldbach is open.
The leaf antecedent names exp (exp 7.9) but the conclusion SieveRange uses exp (exp 7.816).
Nothing here shows SieveRange false. These are the exact logical relations only.
-/
import Mathlib
import LeanLab.AlmostPrimes.Statements
import LeanLab.JohnstonStarichkova.Lemma34

namespace LeanLab.JohnstonStarichkova.Audit1601

open LeanLab.AlmostPrimes LeanLab.JohnstonStarichkova

/-- The threshold of the parameters named in the leaf. -/
noncomputable def X2v3 : ℝ := Real.exp (Real.exp 7.9)

/-- Repaired target: the sieve range at the threshold the leaf parameters support. -/
def SieveRange79 : Prop := ∀ N : ℕ, Even N → X2v3 ≤ N → PrimePlusAlmostPrime 39 N

/-- The word for word statement of sieveRange_of_thm42. -/
def LeafStatement : Prop :=
  (∃ Y0 α1 α2 C u0 δ α : ℝ, ∃ M : ℕ, ∃ X2 : ℝ,
    Y0 = 7.9 ∧ α1 = 7 ∧ α2 = 2 ∧ C = 3.98 ∧
    u0 = 400 ∧ δ = 1.3 ∧ α = 0.25 ∧ M = 40 ∧
    X2 = Real.exp (Real.exp 7.9)) →
  SieveRange

/-- The antecedent carries no content: the leaf is exactly SieveRange. -/
theorem leaf_iff_sieveRange : LeafStatement ↔ SieveRange :=
  ⟨fun h => h ⟨7.9, 7, 2, 3.98, 400, 1.3, 0.25, 40, Real.exp (Real.exp 7.9), by norm_num⟩,
    fun h _ => h⟩

/-- The sealed threshold is strictly below the threshold named in the leaf. -/
theorem X2_lt_X2v3 : X2 < X2v3 := by
  unfold X2 X2v3
  exact Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by norm_num))

/-- So the leaf demands strictly more than the repaired target. -/
theorem sieveRange79_of_sieveRange (h : SieveRange) : SieveRange79 :=
  fun N hN hX => h N hN (X2_lt_X2v3.le.trans hX)

/-- Vacuity instance: a natural number at the repaired threshold exists. -/
theorem sieveRange79_nonvacuous : ∃ N : ℕ, Even N ∧ X2v3 ≤ N := by
  obtain ⟨n, hn⟩ := exists_nat_ge X2v3
  refine ⟨2 * n, even_two_mul n, hn.trans ?_⟩
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end LeanLab.JohnstonStarichkova.Audit1601

#print axioms LeanLab.JohnstonStarichkova.Audit1601.leaf_iff_sieveRange
#print axioms LeanLab.JohnstonStarichkova.Audit1601.X2_lt_X2v3
#print axioms LeanLab.JohnstonStarichkova.Audit1601.sieveRange79_of_sieveRange
#print axioms LeanLab.JohnstonStarichkova.Audit1601.sieveRange79_nonvacuous
