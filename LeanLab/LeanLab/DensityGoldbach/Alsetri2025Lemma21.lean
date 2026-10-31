/-
P0085 Alsetri 2025, arXiv 2505.09648 v2, Lemma 2.1 as printed.
The paper: "For even n ≥ 6, let a0 ≥ a1 ≥ ⋯ ≥ a_{n−1} be a decreasing sequence of numbers in
[0,1]. Suppose that for all triples (i,j,k) with 0 ≤ i,j,k ≤ n−1 and with i+j+k ≥ n we have
ai aj + aj ak + ak ai ≤ 1/2 (a1 + a2 + a3). Then the average value A is bounded by 1/2."
The right side a1 + a2 + a3 is presumably a slip for ai + aj + ak, as in Shao's Lemma 2.1
with 5/8. As printed the lemma is false at n = 8; the counterexample is below. The intended
form is not affected, and the main theorems do not use the printed form.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0203Z-18204, unit U-0163.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib

open Finset

namespace LeanLab.DensityGoldbach

/-- Alsetri's Lemma 2.1 exactly as printed, right side `1/2 (a 1 + a 2 + a 3)`. -/
def AlsetriLemma21Printed : Prop :=
  ∀ n : ℕ, Even n → 6 ≤ n → ∀ a : ℕ → ℝ,
    (∀ i, i + 1 < n → a (i + 1) ≤ a i) → (∀ i, i < n → 0 ≤ a i ∧ a i ≤ 1) →
    (∀ i j k, i < n → j < n → k < n → n ≤ i + j + k →
      a i * a j + a j * a k + a k * a i ≤ 1 / 2 * (a 1 + a 2 + a 3)) →
    (∑ i ∈ range n, a i) / n ≤ 1 / 2

/-- The counterexample sequence, rational. Average `10217/20000 > 1/2`. -/
def ce : ℕ → ℚ := fun i =>
  [1, 1, 379 / 500, 5583 / 10000, 3849 / 10000, 569 / 2500, 79 / 1000, 79 / 1000].getD i 0

lemma ce_triples : ∀ i < 8, ∀ j < 8, ∀ k < 8, 8 ≤ i + j + k →
    ce i * ce j + ce j * ce k + ce k * ce i ≤ 1 / 2 * (ce 1 + ce 2 + ce 3) := by
  decide +kernel

lemma ce_mono : ∀ i < 7, ce (i + 1) ≤ ce i := by decide +kernel

lemma ce_range : ∀ i < 8, 0 ≤ ce i ∧ ce i ≤ 1 := by decide +kernel

lemma ce_sum : ∑ i ∈ range 8, ce i = 10217 / 2500 := by decide +kernel

/-- The printed Lemma 2.1 is false: `n = 8` and the sequence `ce`. -/
theorem alsetri_lemma21_printed_false : ¬ AlsetriLemma21Printed := by
  intro h
  have key := h 8 (by decide) (by norm_num) (fun i => (ce i : ℝ))
    (fun i hi => by exact_mod_cast ce_mono i (by omega))
    (fun i hi => by
      obtain ⟨h0, h1⟩ := ce_range i hi
      exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩)
    (fun i j k hi hj hk hs => by
      have h1 := ce_triples i hi j hj k hk hs
      have h2 := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at h2
      exact h2)
  have hs : (∑ i ∈ range 8, (ce i : ℝ)) = 10217 / 2500 := by
    rw [← Rat.cast_sum, ce_sum]; norm_num
  rw [hs] at key
  norm_num at key

end LeanLab.DensityGoldbach
