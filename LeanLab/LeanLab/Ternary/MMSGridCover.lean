/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3 proof, page 9.
A uniform grid covers the large spectrum and charges each occupied cell to its moment integral.
This is the finite counting part of the standard covering argument.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
open Finset
open scoped Classical
noncomputable section
namespace LeanLab.Ternary.MMS

theorem exists_unit_grid_cell {L : ℕ} (hL : 0 < L) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ j : ℕ, j < L ∧ (j : ℝ) / L ≤ γ ∧ γ ≤ ((j : ℝ) + 1) / L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  by_cases hγ : γ < 1
  · let j := ⌊γ * L⌋₊
    have hγL : 0 ≤ γ * L := mul_nonneg hγ0 hLr.le
    have hj : j < L := (Nat.floor_lt hγL).mpr (by nlinarith)
    refine ⟨j, hj, (div_le_iff₀ hLr).mpr ?_, (le_div_iff₀ hLr).mpr ?_⟩
    · exact Nat.floor_le hγL
    · exact (Nat.lt_floor_add_one (γ * L)).le
  · have hγeq : γ = 1 := by linarith
    subst γ
    have hL1 : 1 ≤ L := hL
    have he : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub hL1]
      norm_num
    refine ⟨L - 1, by omega, (div_le_iff₀ hLr).mpr ?_, (le_div_iff₀ hLr).mpr ?_⟩ <;>
      rw [he] <;> linarith

theorem exists_grid_spectrum_cover (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) (T : Set ℝ) (hT : T ⊆ Set.Icc 0 1)
    {L : ℕ} (hL : 0 < L) {A q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hnear : ∀ γ ∈ T, ∀ β : ℝ, |γ - β| ≤ 1 / (L : ℝ) → A ≤ F β) :
    ∃ R : Finset ℝ, (∀ r ∈ R, r ∈ T) ∧
      (R.card : ℝ) * A ^ q ≤ (L : ℝ) * (∫ x in (0 : ℝ)..1, F x ^ q) ∧
      ∀ γ ∈ T, ∃ r ∈ R, |γ - r| ≤ 1 / (L : ℝ) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  let P (j : ℕ) : Prop := ∃ γ ∈ T, (j : ℝ) / L ≤ γ ∧ γ ≤ ((j : ℝ) + 1) / L
  let S := (range L).filter P
  let r : ℕ → ℝ := fun j => if h : P j then Classical.choose h else 0
  have hr (j : ℕ) (hj : j ∈ S) :
      r j ∈ T ∧ (j : ℝ) / L ≤ r j ∧ r j ≤ ((j : ℝ) + 1) / L := by
    have hp := (mem_filter.mp hj).2
    dsimp [r]
    rw [dite_eq_left hp]
    exact Classical.choose_spec hp
  have hwidth (j : ℕ) : ((j : ℝ) + 1) / L = (j : ℝ) / L + 1 / L := by ring
  have hclose (j : ℕ) (x y : ℝ)
      (hx : (j : ℝ) / L ≤ x ∧ x ≤ ((j : ℝ) + 1) / L)
      (hy : (j : ℝ) / L ≤ y ∧ y ≤ ((j : ℝ) + 1) / L) :
      |x - y| ≤ 1 / (L : ℝ) := by
    rw [abs_le]
    rw [hwidth] at hx hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hc : Continuous (fun x => F x ^ q) := hF.rpow_const (fun _ => Or.inr hq)
  have hcell (j : ℕ) (hj : j ∈ S) :
      A ^ q / L ≤ ∫ x in ((j : ℝ) / L)..(((j : ℝ) + 1) / L), F x ^ q := by
    calc
      A ^ q / L = ∫ x in ((j : ℝ) / L)..(((j : ℝ) + 1) / L), A ^ q := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
      _ ≤ _ := intervalIntegral.integral_mono_on
        (by rw [hwidth]; linarith [one_div_pos.mpr hLr]) intervalIntegrable_const (hc.intervalIntegrable _ _)
        (fun x hx => Real.rpow_le_rpow hA
          (hnear (r j) (hr j hj).1 x (hclose j _ _ (hr j hj).2 hx)) hq)
  have htotal : (∑ j ∈ range L,
      ∫ x in ((j : ℝ) / L)..(((j : ℝ) + 1) / L), F x ^ q) =
      ∫ x in (0 : ℝ)..1, F x ^ q := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (a := fun j : ℕ => (j : ℝ) / L) (n := L) (fun j hj => hc.intervalIntegrable _ _)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hLr.ne'] using h
  have hsum : (S.card : ℝ) * (A ^ q / L) ≤ ∫ x in (0 : ℝ)..1, F x ^ q := by
    calc (S.card : ℝ) * (A ^ q / L) = ∑ j ∈ S, A ^ q / L := by simp
      _ ≤ ∑ j ∈ S, ∫ x in ((j : ℝ) / L)..(((j : ℝ) + 1) / L), F x ^ q := sum_le_sum hcell
      _ ≤ ∑ j ∈ range L, ∫ x in ((j : ℝ) / L)..(((j : ℝ) + 1) / L), F x ^ q := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro j hj hjS
        exact intervalIntegral.integral_nonneg_of_forall (by rw [hwidth]; linarith [one_div_pos.mpr hLr])
          (fun x => Real.rpow_nonneg (hF0 x) _)
      _ = _ := htotal
  have hsum' : (S.card : ℝ) * A ^ q ≤ (∫ x in (0 : ℝ)..1, F x ^ q) * L := by
    apply (div_le_iff₀ hLr).mp
    convert hsum using 1 <;> ring
  refine ⟨S.image r, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    exact (hr j hj).1
  · have hcard : ((S.image r).card : ℝ) ≤ S.card := by exact_mod_cast card_image_le
    exact (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hA q)).trans (by linarith)
  · intro γ hγ
    obtain ⟨j, hjL, hj0, hj1⟩ := exists_unit_grid_cell hL (hT hγ).1 (hT hγ).2
    have hj : j ∈ S := mem_filter.mpr ⟨mem_range.mpr hjL, ⟨γ, hγ, hj0, hj1⟩⟩
    exact ⟨r j, mem_image.mpr ⟨j, hj, rfl⟩, hclose j _ _ ⟨hj0, hj1⟩ (hr j hj).2⟩
end LeanLab.Ternary.MMS
