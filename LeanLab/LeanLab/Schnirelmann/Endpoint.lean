/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the adapted Mathlib argument: Yaël Dillies, Bhavik Mehta, Doga Can Sertbas

Missing endpoint bookkeeping for Mann's sharper theorem.
Source: Nathanson, arXiv:2407.12253v4, page 4, Theorem 1.
The pigeonhole proof adapts Mathlib's
add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity.
AI wrote this Lean adaptation, OpenAI Codex, task26, 2026-10-22.
-/
import LeanLab.Schnirelmann.Sharp

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

/-- At a positive integer missing from the sumset, the combined count is smaller. -/
theorem cnt_add_lt_of_not_mem (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (n : ℕ) (hn : 0 < n) (hgap : n ∉ A + B) : cnt A n + cnt B n < n := by
  have hnA : n ∉ A := fun ha => hgap ⟨n, ha, 0, hB, by simp⟩
  have hnB : n ∉ B := fun hb => hgap ⟨0, hA, n, hb, by simp⟩
  by_contra hlt
  have hle : n ≤ cnt A n + cnt B n := by omega
  let f : ℕ ⊕ ℕ → ℕ
    | .inl x => x
    | .inr y => n - y
  let sA := {a ∈ Icc 1 n | a ∈ A}
  let sB := {b ∈ Icc 1 n | b ∈ B}
  have hc : #(image f (disjSum sA sB)) < #(disjSum sA sB) := calc
    #(image f (disjSum sA sB)) ≤ #(Ioo 0 n) := by
      gcongr
      grind [mem_disjSum]
    _ < n := by simp [Nat.card_Ioo]; omega
    _ ≤ #(disjSum sA sB) := by
      simpa only [card_disjSum, sA, sB, cnt] using hle
  obtain ⟨a | b, ha, a | b, hb, _, hxy⟩ := exists_ne_map_eq_of_card_image_lt hc <;>
    simp only [sA, sB, inl_mem_disjSum, mem_filter, mem_Icc, inr_mem_disjSum] at ha hb <;>
    first | grind [inr_mem_disjSum] |
      exact hgap ⟨a, by simp [*], b, by simp [*], by grind⟩

/-- The minimum appearing in the sharp target is strictly less than one. -/
theorem gap_min_lt_one (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B) (n : ℕ)
    (hg : ((Icc 1 n).filter (fun m => m ∉ A + B)).Nonempty) :
    ((Icc 1 n).filter (fun m => m ∉ A + B)).inf' hg
      (fun m => ((cnt A m : ℝ) + cnt B m) / m) < 1 := by
  obtain ⟨m, hm⟩ := hg
  have hmem := mem_filter.mp hm
  have hmpos : 0 < m := (mem_Icc.mp hmem.1).1
  have hc := cnt_add_lt_of_not_mem A B hA hB m hmpos hmem.2
  apply lt_of_le_of_lt (Finset.inf'_le _ hm)
  rw [div_lt_one (show (0 : ℝ) < m by exact_mod_cast hmpos)]
  exact_mod_cast hc

/-- A slope form of the still unproved sharper Mann theorem. -/
def MannGapBound : Prop :=
  ∀ (A B : Set ℕ), 0 ∈ A → 0 ∈ B → ∀ (n : ℕ) (δ : ℝ), δ ≤ 1 →
    (∀ m, 1 ≤ m → m ≤ n → m ∉ A + B → δ * m ≤ (cnt A m : ℝ) + cnt B m) →
      δ * n ≤ (cnt (A + B) n : ℝ)

/-- Equivalence of the exact finite minimum target and its missing gap slope form.
This proves neither side without an additional proof of the other. -/
theorem mannCounting_iff_gapBound : MannCounting ↔ MannGapBound := by
  constructor
  · intro h A B hA hB n δ hδ hyp
    by_cases hg : ((Icc 1 n).filter (fun m => m ∉ A + B)).Nonempty
    · have hmin := h A B hA hB n hg
      have hn : 0 < n := by
        obtain ⟨m, hm⟩ := hg
        have hm := mem_Icc.mp (mem_filter.mp hm).1
        omega
      have hle : δ ≤ ((Icc 1 n).filter (fun m => m ∉ A + B)).inf' hg
          (fun m => ((cnt A m : ℝ) + cnt B m) / m) := by
        apply Finset.le_inf'
        intro m hm
        obtain ⟨hmem, hgap⟩ := mem_filter.mp hm
        obtain ⟨hm1, hmn⟩ := mem_Icc.mp hmem
        rw [le_div_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm1)]
        exact hyp m hm1 hmn hgap
      exact (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mp (hle.trans hmin)
    · have hfull : cnt (A + B) n = n := by
        unfold cnt
        rw [filter_true_of_mem]
        · simp
        · intro m hm
          by_contra hgap
          exact hg ⟨m, mem_filter.mpr ⟨hm, hgap⟩⟩
      rw [hfull]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · intro h A B hA hB n hg
    have hn : 0 < n := by
      obtain ⟨m, hm⟩ := hg
      have hm := mem_Icc.mp (mem_filter.mp hm).1
      omega
    rw [le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)]
    apply h A B hA hB n _ (gap_min_lt_one A B hA hB n hg).le
    intro m hm1 hmn hgap
    have hmem : m ∈ ((Icc 1 n).filter (fun m => m ∉ A + B)) :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1, hmn⟩, hgap⟩
    have hle := Finset.inf'_le
      (fun m => ((cnt A m : ℝ) + cnt B m) / m) hmem
    exact (le_div_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm1)).mp hle

end LeanLab.Schnirelmann.Mann
