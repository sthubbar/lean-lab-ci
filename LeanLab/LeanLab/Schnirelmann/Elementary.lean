/-
Elementary instances of the missing gap slope formulation of Mann's theorem.
Source target: Nathanson, arXiv:2407.12253v4, page 4, Theorem 1.
These special cases do not assert the general theorem.
AI wrote this Lean code, OpenAI Codex, task26, 2026-10-22.
-/
import LeanLab.Schnirelmann.Endpoint

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

/-- The missing gap slope bound when A has no positive elements through n. -/
theorem gap_bound_of_count_zero (A B : Set ℕ) (hA : 0 ∈ A) (n : ℕ)
    (hzero : cnt A n = 0) (δ : ℝ) (hδ : δ ≤ 1)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → m ∉ A + B →
      δ * m ≤ (cnt A m : ℝ) + cnt B m) :
    δ * n ≤ (cnt (A + B) n : ℝ) := by
  apply count_of_gap_bounds (A + B) δ hδ n
  intro m hm hmn hgap
  have hz : cnt A m = 0 := by
    have hc := cnt_mono A hmn
    omega
  have hs : B ⊆ A + B := fun b hb => ⟨0, hA, b, hb, by simp⟩
  have hc : (cnt B m : ℝ) ≤ cnt (A + B) m := by
    exact_mod_cast cnt_mono_set hs m
  have hp := hyp m hm hmn hgap
  rw [hz] at hp
  simpa using hp.trans (by simpa using hc)

/-- Disjoint positive inputs contribute their counts without overlap to the sumset. -/
theorem cnt_add_le_of_disjoint_positive (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hdis : ∀ x, x ∈ A → x ∈ B → x = 0) (n : ℕ) :
    cnt A n + cnt B n ≤ cnt (A + B) n := by
  let sA := (Icc 1 n).filter (fun x => x ∈ A)
  let sB := (Icc 1 n).filter (fun x => x ∈ B)
  have hd : Disjoint sA sB := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨hxI, hxA⟩ := mem_filter.mp hx
    obtain ⟨_, hxB⟩ := mem_filter.mp hy
    have hz := hdis x hxA hxB
    have := (mem_Icc.mp hxI).1
    omega
  have hs : sA ∪ sB ⊆ (Icc 1 n).filter (fun x => x ∈ A + B) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨hxI, hxA⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxI, ⟨x, hxA, 0, hB, by simp⟩⟩
    · obtain ⟨hxI, hxB⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxI, ⟨0, hA, x, hxB, by simp⟩⟩
  calc
    cnt A n + cnt B n = #(sA ∪ sB) := (card_union_of_disjoint hd).symm
    _ ≤ cnt (A + B) n := card_le_card hs

/-- The missing gap slope bound for inputs that meet only at zero. -/
theorem gap_bound_of_disjoint_positive (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hdis : ∀ x, x ∈ A → x ∈ B → x = 0) (n : ℕ) (δ : ℝ) (hδ : δ ≤ 1)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → m ∉ A + B →
      δ * m ≤ (cnt A m : ℝ) + cnt B m) :
    δ * n ≤ (cnt (A + B) n : ℝ) := by
  apply count_of_gap_bounds (A + B) δ hδ n
  intro m hm hmn hgap
  have hc : (cnt A m : ℝ) + cnt B m ≤ cnt (A + B) m := by
    exact_mod_cast cnt_add_le_of_disjoint_positive A B hA hB hdis m
  exact (hyp m hm hmn hgap).trans hc

/-- At the first missing endpoint, the combined input count is bounded by C's count. -/
theorem cnt_add_le_at_first_gap (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (n : ℕ) (hn : 0 < n) (hgap : n ∉ A + B)
    (hfirst : ∀ m, 1 ≤ m → m < n → m ∈ A + B) :
    cnt A n + cnt B n ≤ cnt (A + B) n := by
  have hfull : cnt (A + B) (n - 1) = n - 1 := by
    unfold cnt
    rw [filter_true_of_mem]
    · simp
    · intro m hm
      obtain ⟨hm1, hmn⟩ := mem_Icc.mp hm
      exact hfirst m hm1 (by omega)
  have hc := cnt_mono (A + B) (Nat.sub_le n 1)
  have hi := cnt_add_lt_of_not_mem A B hA hB n hn hgap
  omega

/-- The missing gap slope bound when the interval has at most one missing index. -/
theorem gap_bound_of_at_most_one_missing (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (n : ℕ)
    (huniq : ∀ i j, i ∈ Icc 1 n → j ∈ Icc 1 n →
      i ∉ A + B → j ∉ A + B → i = j)
    (δ : ℝ) (hδ : δ ≤ 1)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → m ∉ A + B →
      δ * m ≤ (cnt A m : ℝ) + cnt B m) :
    δ * n ≤ (cnt (A + B) n : ℝ) := by
  apply count_of_gap_bounds (A + B) δ hδ n
  intro m hm hmn hgap
  have hfirst : ∀ k, 1 ≤ k → k < m → k ∈ A + B := by
    intro k hk hkm
    by_contra hgapk
    have he := huniq k m (mem_Icc.mpr ⟨hk, by omega⟩)
      (mem_Icc.mpr ⟨hm, hmn⟩) hgapk hgap
    omega
  have hc : (cnt A m : ℝ) + cnt B m ≤ cnt (A + B) m := by
    exact_mod_cast cnt_add_le_at_first_gap A B hA hB m hm hgap hfirst
  exact (hyp m hm hmn hgap).trans hc

/-- Checking only the first missing index does not establish the general slope bound.
This is a counterexample to a proposed shortcut, not to Mann's theorem. -/
theorem first_gap_hyp_not_sufficient :
    let A : Set ℕ := {0, 1, 5, 6}
    (∀ m : ℕ, 1 ≤ m → m < 3 → m ∈ A + A) ∧
    3 ∉ A + A ∧ (2 / 3 : ℝ) * 3 ≤ (cnt A 3 : ℝ) + cnt A 3 ∧
    ¬ ((2 / 3 : ℝ) * 9 ≤ (cnt (A + A) 9 : ℝ)) := by
  dsimp only
  have hC : ({0, 1, 5, 6} : Set ℕ) + {0, 1, 5, 6} =
      {0, 1, 2, 5, 6, 7, 10, 11, 12} := by
    ext x
    simp [Set.mem_add, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_and_right, and_or_left, exists_or]
    omega
  rw [hC]
  constructor
  · intro m hm hm3
    interval_cases m <;> norm_num at *
  · norm_num [cnt, Finset.filter_insert, Finset.filter_singleton,
      show Icc 1 3 = {1, 2, 3} by decide,
      show Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} by decide]

/-- Mann's exact finite minimum conclusion when at most one index is missing. -/
theorem mann_counting_of_at_most_one_missing (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (n : ℕ)
    (huniq : ∀ i j, i ∈ Icc 1 n → j ∈ Icc 1 n →
      i ∉ A + B → j ∉ A + B → i = j)
    (hg : ((Icc 1 n).filter (fun m => m ∉ A + B)).Nonempty) :
    ((Icc 1 n).filter (fun m => m ∉ A + B)).inf' hg
      (fun m => ((cnt A m : ℝ) + cnt B m) / m) ≤ (cnt (A + B) n : ℝ) / n := by
  have hn : 0 < n := by
    obtain ⟨m, hm⟩ := hg
    have hi := mem_Icc.mp (mem_filter.mp hm).1
    omega
  rw [le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)]
  apply gap_bound_of_at_most_one_missing A B hA hB n huniq _
    (gap_min_lt_one A B hA hB n hg).le
  intro m hm hmn hgap
  have hmem : m ∈ ((Icc 1 n).filter (fun m => m ∉ A + B)) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨hm, hmn⟩, hgap⟩
  have hi := Finset.inf'_le (fun m => ((cnt A m : ℝ) + cnt B m) / m) hmem
  exact (le_div_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mp hi

/-- Positive overlap accounts for the loss in the elementary input count comparison. -/
theorem cnt_add_le_with_intersection (A B : Set ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (n : ℕ) :
    cnt A n + cnt B n ≤ cnt (A + B) n + cnt (A ∩ B) n := by
  let sA := (Icc 1 n).filter (fun x => x ∈ A)
  let sB := (Icc 1 n).filter (fun x => x ∈ B)
  have hs : sA ∪ sB ⊆ (Icc 1 n).filter (fun x => x ∈ A + B) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨hxI, hxA⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxI, ⟨x, hxA, 0, hB, by simp⟩⟩
    · obtain ⟨hxI, hxB⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxI, ⟨0, hA, x, hxB, by simp⟩⟩
  calc
    cnt A n + cnt B n = #(sA ∪ sB) + cnt (A ∩ B) n := by
      have hcard : #(sA ∩ sB) = cnt (A ∩ B) n := by
        unfold cnt
        congr 1
        ext x
        simp [sA, sB, and_assoc, and_left_comm, and_comm]
      rw [← hcard]
      exact (card_union_add_card_inter sA sB).symm
    _ ≤ cnt (A + B) n + cnt (A ∩ B) n := Nat.add_le_add_right (card_le_card hs) _

/-- Removing the overlap count gives a sufficient missing gap slope hypothesis. -/
theorem gap_bound_of_overlap_corrected_counts (A B : Set ℕ) (hA : 0 ∈ A)
    (hB : 0 ∈ B) (n : ℕ) (δ : ℝ) (hδ : δ ≤ 1)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → m ∉ A + B →
      δ * m + cnt (A ∩ B) m ≤ (cnt A m : ℝ) + cnt B m) :
    δ * n ≤ (cnt (A + B) n : ℝ) := by
  apply count_of_gap_bounds (A + B) δ hδ n
  intro m hm hmn hgap
  have hc : (cnt A m : ℝ) + cnt B m ≤
      cnt (A + B) m + cnt (A ∩ B) m := by
    exact_mod_cast cnt_add_le_with_intersection A B hA hB m
  have hp := hyp m hm hmn hgap
  linarith

end LeanLab.Schnirelmann.Mann
