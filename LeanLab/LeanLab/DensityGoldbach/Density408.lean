/-
The counting formulation of Alsetri and Shao Theorem 1.1 implies the sealed
relative lower density formulation. Source 2405.18576v2 page 2.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.AlsetriShaoThm11
import LeanLab.DensityGoldbach.Statements

open Finset Filter
open scoped Classical

namespace LeanLab.DensityGoldbach.Density408

/-- Alsetri and Shao page 2, relative lower density definition.
For a prime subset, the inclusive range count equals the Icc count. -/
theorem prime_subset_count (A : Set ℕ) (hA : A ⊆ P) (N : ℕ) :
    ((range (N + 1)).filter (· ∈ A)).card =
      ((Icc 1 N).filter (fun p => p ∈ A ∧ p.Prime)).card := by
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨hpN, hpA⟩
    have hp := hA hpA
    exact ⟨⟨hp.one_lt.le, by omega⟩, hpA, hp⟩
  · rintro ⟨⟨_, hpN⟩, hpA, _⟩
    exact ⟨by omega, hpA⟩

/-- Alsetri and Shao page 2, lower density definition.
An eventual lower bound on prime counts gives the same bound on the liminf. -/
theorem density_of_eventual_count (A : Set ℕ) (hA : A ⊆ P) (d : ℝ)
    (h : ∀ᶠ N : ℕ in atTop, d *
      (((range (N + 1)).filter Nat.Prime).card : ℝ) ≤
      (((range (N + 1)).filter (· ∈ A)).card : ℝ)) : d ≤ lowerDensity A := by
  have hpcount (N : ℕ) : ((range (N + 1)).filter Nat.Prime).card =
      ((Icc 1 N).filter Nat.Prime).card := by
    simpa only [P, Set.mem_setOf_eq, and_self] using prime_subset_count P (Set.Subset.refl _) N
  have hupper : ∀ N, relRatio A N ≤ 1 := by
    intro N
    unfold relRatio
    apply div_le_one_of_le₀
    · exact_mod_cast card_le_card (show
        ((Icc 1 N).filter (fun p => p ∈ A ∧ p.Prime)) ⊆ (Icc 1 N).filter Nat.Prime from
          fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.2⟩)
    · positivity
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hupper)
  filter_upwards [h, eventually_ge_atTop 2] with N hN hN2
  have hpositive : (0 : ℝ) < ((Icc 1 N).filter Nat.Prime).card := by
    exact_mod_cast card_pos.mpr ⟨2, mem_filter.mpr ⟨mem_Icc.mpr ⟨by norm_num, hN2⟩, Nat.prime_two⟩⟩
  rw [prime_subset_count A hA N, hpcount N] at hN
  exact (le_div_iff₀ hpositive).mpr hN

/-- Exact original Theorem 1.1 stub, from the existing count construction.
No cited input is introduced. The possible count of zero is removed explicitly. -/
theorem alsetriShao_1_1 : AlsetriShao11 := by
  intro ε hε
  obtain ⟨A, hA, ⟨d, hd, Nd, hcount⟩, c, hc, Nc, hexc⟩ :=
    AlsetriShaoThm11.theorem1_1 ε hε
  have hAP : A ⊆ P := fun _ hp => hA _ hp
  have hdensity : d ≤ lowerDensity A := density_of_eventual_count A hAP d
    (eventually_atTop.mpr ⟨Nd, hcount⟩)
  refine ⟨A, hAP, hd.trans_le hdensity, c / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop Nc, eventually_ge_atTop ⌈2 / c⌉₊]
    with N hNc hNlarge
  have hNbound : (2 : ℝ) / c ≤ N := (Nat.le_ceil (2 / c)).trans (by exact_mod_cast hNlarge)
  have hgap : 1 ≤ c * (N : ℝ) / 2 := by
    have := (div_le_iff₀ hc).mp hNbound
    nlinarith
  have hraw := hexc N hNc
  have hcard : (((range (N + 1)).filter
      (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q)).card : ℝ) ≤
      ((Icc 1 N).filter
      (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, p + q = n)).card + 1 := by
    have hsub : ((range (N + 1)).filter
        (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, n = p + q)) ⊆
        insert 0 ((Icc 1 N).filter
        (fun n => Even n ∧ ¬ ∃ p ∈ A, ∃ q ∈ A, p + q = n)) := by
      intro n hn
      simp only [mem_filter, mem_range] at hn
      by_cases hn0 : n = 0
      · simp [hn0]
      · apply mem_insert_of_mem
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hn.2.1, ?_⟩
        rintro ⟨p, hp, q, hq, he⟩
        exact hn.2.2 ⟨p, hp, q, hq, he.symm⟩
    have := (card_le_card hsub).trans (card_insert_le _ _)
    exact_mod_cast this
  nlinarith

end LeanLab.DensityGoldbach.Density408

#print axioms LeanLab.DensityGoldbach.Density408.prime_subset_count
#print axioms LeanLab.DensityGoldbach.Density408.density_of_eventual_count
#print axioms LeanLab.DensityGoldbach.Density408.alsetriShao_1_1
