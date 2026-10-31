/-
Finite index sets and rank density bounds for Mann's theorem.
Source: Nathanson, arXiv:2407.12253v4, pages 4 and 5, Theorems 2 and 3.
AI wrote this Lean code, OpenAI Codex, task26, 2026-10-22.
-/
import LeanLab.Schnirelmann.Mann
import LeanLab.Schnirelmann.Inequality

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann

/-- Mann's density theorem for a finite index set, with zero in every summand. -/
theorem mann_finset {ι : Type*} (s : Finset ι) (A : ι → Set ℕ)
    (hA : ∀ i ∈ s, 0 ∈ A i) :
    min 1 (∑ i ∈ s, schnirelmannDensity (A i)) ≤
      schnirelmannDensity (∑ i ∈ s, A i) := by
  have H : ∀ s : Finset ι, (∀ i ∈ s, 0 ∈ A i) →
      0 ∈ (∑ i ∈ s, A i) ∧
      min 1 (∑ i ∈ s, schnirelmannDensity (A i)) ≤
        schnirelmannDensity (∑ i ∈ s, A i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      constructor
      · simp
      · simp only [sum_empty, min_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
        exact schnirelmannDensity_nonneg
    | @insert i t hit ih =>
      intro hzero
      have hi := hzero i (mem_insert_self _ _)
      have ht := ih (fun j hj => hzero j (mem_insert_of_mem hj))
      rw [sum_insert hit, sum_insert hit]
      refine ⟨⟨0, hi, 0, ht.1, by simp⟩, ?_⟩
      have hm := mann (A i) (∑ j ∈ t, A j) hi ht.1
      have hl := min_le_min_left (1 : ℝ)
        (show schnirelmannDensity (A i) + min 1 (∑ j ∈ t, schnirelmannDensity (A j)) ≤
          schnirelmannDensity (A i) + schnirelmannDensity (∑ j ∈ t, A j) by
            linarith [ht.2])
      have he : min 1 (schnirelmannDensity (A i) +
          min 1 (∑ j ∈ t, schnirelmannDensity (A j))) =
          min 1 (schnirelmannDensity (A i) + ∑ j ∈ t, schnirelmannDensity (A j)) := by
        have hp := schnirelmannDensity_nonneg (A := A i)
        simp only [min_def]
        split_ifs <;> linarith
      rw [he] at hl
      exact hl.trans hm
  exact (H s hA).2

/-- Each index occurs in choose(card s - 1, r - 1) of the rank r subsets. -/
theorem sum_powersetCard_sum {ι : Type*} (s : Finset ι) (r : ℕ) (hr : 1 ≤ r)
    (f : ι → ℝ) :
    ∑ t ∈ s.powersetCard r, ∑ i ∈ t, f i =
      ((s.card - 1).choose (r - 1) : ℝ) * ∑ i ∈ s, f i := by
  have he : ∀ t ∈ s.powersetCard r,
      (∑ i ∈ t, f i) = ∑ i ∈ s, if i ∈ t then f i else 0 := by
    intro t ht
    rw [← sum_filter]
    have hf : s.filter (fun i => i ∈ t) = t := by
      ext i
      simp only [mem_filter]
      exact ⟨fun hi => hi.2, fun hi => ⟨(mem_powersetCard.mp ht).1 hi, hi⟩⟩
    rw [hf]
  calc
    ∑ t ∈ s.powersetCard r, ∑ i ∈ t, f i
        = ∑ t ∈ s.powersetCard r, ∑ i ∈ s, if i ∈ t then f i else 0 :=
      sum_congr rfl he
    _ = ∑ i ∈ s, ∑ t ∈ s.powersetCard r, if i ∈ t then f i else 0 := sum_comm
    _ = ∑ i ∈ s, ((s.card - 1).choose (r - 1) : ℝ) * f i := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      congr 1
      have hc := card_filter_powersetCard_subset ({i} : Finset ι) s r
        (singleton_subset_iff.mpr hi) (by simpa using hr)
      exact_mod_cast (by simpa only [singleton_subset_iff, card_singleton] using hc)
    _ = ((s.card - 1).choose (r - 1) : ℝ) * ∑ i ∈ s, f i := (mul_sum _ _ _).symm

/-- Nathanson's rank density theorem, page 5, Theorem 3. -/
theorem mann_rank {ι : Type*} (s : Finset ι) (A : ι → Set ℕ)
    (r : ℕ) (hr : 1 ≤ r) (_hrh : r ≤ s.card) (hA : ∀ i ∈ s, 0 ∈ A i) :
    ((s.card - 1).choose (r - 1) : ℝ) *
        min 1 (∑ i ∈ s, schnirelmannDensity (A i)) ≤
      ∑ t ∈ s.powersetCard r, schnirelmannDensity (∑ i ∈ t, A i) := by
  let f : ι → ℝ := fun i => schnirelmannDensity (A i)
  let total : ℝ := ∑ i ∈ s, f i
  have ht : ∀ t ∈ s.powersetCard r, (∑ i ∈ t, f i) ≤ total := by
    intro t hts
    exact sum_le_sum_of_subset_of_nonneg (mem_powersetCard.mp hts).1
      (fun i _ _ => schnirelmannDensity_nonneg)
  have hm : ∀ t ∈ s.powersetCard r,
      min 1 (∑ i ∈ t, f i) ≤ schnirelmannDensity (∑ i ∈ t, A i) := by
    intro t hts
    exact mann_finset t A (fun i hi => hA i ((mem_powersetCard.mp hts).1 hi))
  change ((s.card - 1).choose (r - 1) : ℝ) * min 1 total ≤ _
  by_cases htotal : total ≤ 1
  · rw [min_eq_right htotal]
    calc
      ((s.card - 1).choose (r - 1) : ℝ) * total
          = ∑ t ∈ s.powersetCard r, ∑ i ∈ t, f i :=
        (sum_powersetCard_sum s r hr f).symm
      _ ≤ ∑ t ∈ s.powersetCard r, schnirelmannDensity (∑ i ∈ t, A i) := by
        apply sum_le_sum
        intro t hts
        simpa only [min_eq_right ((ht t hts).trans htotal)] using hm t hts
  · have hone : 1 ≤ total := le_of_lt (lt_of_not_ge htotal)
    rw [min_eq_left hone, mul_one]
    have hb : ∀ t ∈ s.powersetCard r,
        (∑ i ∈ t, f i) ≤ total * schnirelmannDensity (∑ i ∈ t, A i) := by
      intro t hts
      have hmt := hm t hts
      have hst := ht t hts
      have hn : 0 ≤ schnirelmannDensity (∑ i ∈ t, A i) := schnirelmannDensity_nonneg
      by_cases hsmall : (∑ i ∈ t, f i) ≤ 1
      · rw [min_eq_right hsmall] at hmt
        nlinarith
      · rw [min_eq_left (le_of_lt (lt_of_not_ge hsmall))] at hmt
        nlinarith
    have hs := sum_le_sum hb
    rw [sum_powersetCard_sum s r hr f, ← mul_sum] at hs
    change ((s.card - 1).choose (r - 1) : ℝ) * total ≤
      total * (∑ t ∈ s.powersetCard r, schnirelmannDensity (∑ i ∈ t, A i)) at hs
    nlinarith

/-- Repeated Mann gives a linear lower bound for every iterated sumset. -/
theorem density_nsmul_ge_min (A : Set ℕ) (hA : 0 ∈ A) (h : ℕ) :
    min 1 ((h : ℝ) * schnirelmannDensity A) ≤ schnirelmannDensity (h • A) := by
  have hm := mann_finset (range h) (fun _ : ℕ => A) (fun _ _ => hA)
  simpa only [sum_const, card_range, nsmul_eq_mul] using hm

/-- A concrete basis order criterion from the linear Mann bound. -/
theorem nsmul_eq_univ_of_one_le (A : Set ℕ) (hA : 0 ∈ A) (h : ℕ)
    (hσ : 1 ≤ (h : ℝ) * schnirelmannDensity A) : h • A = Set.univ := by
  have hm := density_nsmul_ge_min A hA h
  rw [min_eq_left hσ] at hm
  have hd : schnirelmannDensity (h • A) = 1 :=
    le_antisymm schnirelmannDensity_le_one hm
  exact (schnirelmannDensity_eq_one_iff_of_zero_mem
    (LeanLab.Schnirelmann.zero_mem_nsmul A hA h)).mp hd

/-- Positive density gives the explicit basis order ceiling of its reciprocal. -/
theorem ceil_inv_density_nsmul_eq_univ (A : Set ℕ) (hA : 0 ∈ A)
    (hpos : 0 < schnirelmannDensity A) :
    ⌈1 / schnirelmannDensity A⌉₊ • A = Set.univ := by
  apply nsmul_eq_univ_of_one_le A hA
  have hc : 1 / schnirelmannDensity A ≤ (⌈1 / schnirelmannDensity A⌉₊ : ℝ) :=
    Nat.le_ceil _
  have he : (1 / schnirelmannDensity A) * schnirelmannDensity A = 1 := by
    field_simp
  nlinarith

end LeanLab.Schnirelmann.Mann
