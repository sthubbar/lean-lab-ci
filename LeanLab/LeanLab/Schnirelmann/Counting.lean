/-
Finite counting forms of Mann's theorem.
Source: Nathanson, arXiv:2407.12253v4, page 4, Theorem 1 and Corollary 1.
AI wrote this Lean code, OpenAI Codex, task26, 2026-10-22.
-/
import LeanLab.Schnirelmann.Mann

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

/-- The finite all prefix counting bound, Nathanson page 4, Corollary 1. -/
theorem mann_count (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (n : ℕ) (γ : ℝ)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → γ * m ≤ (cnt A m : ℝ) + cnt B m) :
    min 1 γ * n ≤ (cnt (A + B) n : ℝ) := by
  let F : ℕ → Set ℕ := fun i => if i = 0 then A else B
  have hd : DysonHypR F 2 n (min 1 γ) := by
    intro m hm hmn
    have h := hyp m hm hmn
    have hle : min 1 γ * (m : ℝ) ≤ γ * m :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg m)
    simpa [phi, sum_range_succ, F] using hle.trans h
  have hd := dysonR 1 n F (min 1 γ) (min_le_left _ _) hd
  have hs : SumSet F 2 ⊆ A + B := by
    intro p hp
    obtain ⟨f, hf, he⟩ := hp
    have hf0 : f 0 ∈ A := by
      rcases hf 0 (by omega) with hz | ha
      · rwa [hz]
      · simpa [F] using ha
    have hf1 : f 1 ∈ B := by
      rcases hf 1 (by omega) with hz | hb
      · rwa [hz]
      · simpa [F] using hb
    refine ⟨f 0, hf0, f 1, hf1, ?_⟩
    simpa [sum_range_succ] using he
  exact hd.trans (by exact_mod_cast cnt_mono_set hs n)

end LeanLab.Schnirelmann.Mann
