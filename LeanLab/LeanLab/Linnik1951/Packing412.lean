/-
P0093 page 165 proof of Lemma 5. Finite equal length interval packing.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 165 proof of Lemma 5, the measure divided by length step.
A set in the unit interval with radius delta neighborhoods in a finite
measure set has a finite interval cover of length delta and cardinality
at most the larger measure divided by delta. -/
theorem interval_packing412 (s t : Set ℝ) (hs : s ⊆ Set.Icc 0 1)
    (ht : volume t ≠ ⊤) (δ : ℝ) (hδ : 0 < δ)
    (hthick : ∀ x ∈ s, Set.Icc (x - δ) (x + δ) ⊆ t) :
    ∃ I : Finset (ℝ × ℝ), (I.card : ℝ) * δ ≤ volume.real t ∧
      (∀ p ∈ I, p.2 - p.1 ≤ δ) ∧ s ⊆ ⋃ p ∈ I, Set.Icc p.1 p.2 := by
  classical
  let J := (Finset.range (⌈1 / δ⌉₊ + 1)).filter fun j : ℕ =>
    (Set.Icc ((j : ℝ) * δ) (((j : ℝ) + 1) * δ) ∩ s).Nonempty
  let cell : ℕ → Set ℝ := fun j => Set.Ioc ((j : ℝ) * δ) (((j : ℝ) + 1) * δ)
  have hsub : ⋃ j ∈ J, cell j ⊆ t := by
    intro y hy
    obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨x, hx, hxs⟩ := (Finset.mem_filter.mp hj).2
    apply hthick x hxs
    change (j : ℝ) * δ < y ∧ y ≤ ((j : ℝ) + 1) * δ at hy
    constructor <;> nlinarith [hx.1, hx.2]
  have hd : Set.PairwiseDisjoint (J : Set ℕ) cell := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change (i : ℝ) * δ < x ∧ x ≤ ((i : ℝ) + 1) * δ at hxi
    change (j : ℝ) * δ < x ∧ x ≤ ((j : ℝ) + 1) * δ at hxj
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      nlinarith
    · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij
      nlinarith
  have hm : (J.card : ℝ) * δ ≤ volume.real t := by
    calc
      _ = ∑ j ∈ J, volume.real (cell j) := by
        simp [cell, Real.volume_real_Ioc, hδ.le, add_mul]
      _ = volume.real (⋃ j ∈ J, cell j) :=
        (measureReal_biUnion_finset hd (fun j hj => measurableSet_Ioc)
          (fun j hj => by simp [cell, Real.volume_Ioc])).symm
      _ ≤ _ := measureReal_mono hsub ht
  let I := J.image fun (j : ℕ) => ((j : ℝ) * δ, ((j : ℝ) + 1) * δ)
  refine ⟨I, ?_, ?_, ?_⟩
  · have hc : I.card ≤ J.card := Finset.card_image_le
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hδ.le).trans hm
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    dsimp
    linarith
  · intro x hx
    let j := ⌊x / δ⌋₊
    have hx0 : 0 ≤ x / δ := div_nonneg (hs hx).1 hδ.le
    have hjlo : (j : ℝ) * δ ≤ x := (le_div_iff₀ hδ).mp (Nat.floor_le hx0)
    have hjhi : x ≤ ((j : ℝ) + 1) * δ :=
      ((div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (x / δ))).le
    have hjbound : j ≤ ⌈1 / δ⌉₊ := by
      apply Nat.floor_le_of_le
      exact (div_le_div_of_nonneg_right (hs hx).2 hδ.le).trans (Nat.le_ceil _)
    have hj : j ∈ J := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), x, ⟨hjlo, hjhi⟩, hx⟩
    exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image.mpr ⟨j, hj, rfl⟩, hjlo, hjhi⟩

end LeanLab.Linnik1951
