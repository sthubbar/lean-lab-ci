/-
Mann's sharper counting target and an obstruction to one proposed proof.
Source: Nathanson, arXiv:2407.12253v4, page 4, Theorem 1.
The cited target is a Prop definition. It is not asserted here.
AI wrote this Lean code, OpenAI Codex, task26, 2026-10-22.
-/
import LeanLab.Schnirelmann.Counting

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

/-- Mann's sharper theorem, with the finite minimum over missing indices.
The full interval case is handled by requiring a nonempty set of missing indices. -/
def MannCounting : Prop :=
  ∀ (A B : Set ℕ), 0 ∈ A → 0 ∈ B → ∀ n : ℕ,
    ∀ hg : ((Icc 1 n).filter (fun m => m ∉ A + B)).Nonempty,
      ((Icc 1 n).filter (fun m => m ∉ A + B)).inf' hg
        (fun m => ((cnt A m : ℝ) + cnt B m) / m) ≤ (cnt (A + B) n : ℝ) / n

/-- Bounds at missing indices do not imply the all prefix hypothesis of `mann_count`.
This refutes a proposed bridge, not Mann's theorem. -/
theorem gap_hyp_not_all_prefix :
    let A : Set ℕ := {0, 1}
    let B : Set ℕ := {0, 1, 4}
    (∀ m : ℕ, 1 ≤ m → m ≤ 5 → m ∉ A + B →
      (2 / 3 : ℝ) * m ≤ (cnt A m : ℝ) + cnt B m) ∧
    ¬ ((2 / 3 : ℝ) * 5 ≤ (cnt A 5 : ℝ) + cnt B 5) := by
  dsimp only
  have hC : ({0, 1} : Set ℕ) + {0, 1, 4} = {0, 1, 2, 4, 5} := by
    ext x
    simp [Set.mem_add, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_and_right, and_or_left, exists_or]
    omega
  constructor
  · intro m hm hm5 hgap
    rw [hC] at hgap
    interval_cases m <;> norm_num [cnt, Finset.filter_insert, Finset.filter_singleton, show Icc 1 3 = {1, 2, 3} by decide,
      show Icc 1 5 = {1, 2, 3, 4, 5} by decide] at *
  · norm_num [cnt, Finset.filter_insert, Finset.filter_singleton, show Icc 1 3 = {1, 2, 3} by decide,
      show Icc 1 5 = {1, 2, 3, 4, 5} by decide]

/-- A slope at most one needs checking only at the missing indices of a set.
This reduces the target's final counting step, not its additive input. -/
theorem count_of_gap_bounds (S : Set ℕ) (δ : ℝ) (hδ : δ ≤ 1) :
    ∀ n : ℕ, (∀ m, 1 ≤ m → m ≤ n → m ∉ S → δ * m ≤ (cnt S m : ℝ)) →
      δ * n ≤ (cnt S n : ℝ) := by
  intro n
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    intro hyp
    by_cases hn : n + 1 ∈ S
    · have hi := ih (fun m hm hmn => hyp m hm (by omega))
      have hc : cnt S (n + 1) = cnt S n + 1 := by
        rw [cnt_split S (Nat.le_succ n)]
        simp [Finset.filter_singleton, hn]
      rw [hc]
      push_cast
      nlinarith
    · exact hyp (n + 1) (by omega) le_rfl hn

end LeanLab.Schnirelmann.Mann
