/-
Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4, pages 194 and 195.
Platt and Trudgian, arXiv https://arxiv.org/abs/1404.5669, sections 3 and 4.
Periodic transfer of the unshifted exceptional measure to every slice.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp577b
import LeanLab.Hathi2021.Decomp577eLeavesPT

open Finset Real MeasureTheory Filter Topology Set
open LeanLab.Hathi2021.Decomp319a LeanLab.Hathi2021.Decomp570b

namespace LeanLab.Hathi2021.Decomp577e

/-- Helper for Hu page 195. The finite powers of two sum has period one. -/
theorem G_periodic (n₁ : ℕ) : Function.Periodic (G n₁) 1 := by
  intro x
  unfold G
  apply Finset.sum_congr rfl
  intro ν hν
  rw [mul_add, mul_one, e_add]
  have he : e ((2 : ℝ) ^ ν) = 1 := by
    unfold e
    have harg : 2 * Real.pi * Complex.I * (((2 : ℝ) ^ ν : ℝ) : ℂ) =
        (((2 : ℤ) ^ ν : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I ((2 : ℤ) ^ ν)
  rw [he, mul_one]

/-- Hu page 195, the periodic change of variable in a translated slice.
The exceptional slice has the same measure for every real translate. -/
theorem exceptionalSlice_volume_eq (n₁ : ℕ) (t : ℝ) :
    volume.real (exceptionalSlice n₁ t) = volume.real (exceptionalSlice n₁ 0) := by
  classical
  let A : Set ℝ := {x | (PairLinnik.lam : ℝ) * L n₁ ≤ ‖G n₁ x‖}
  let F : ℝ → ℝ := A.indicator (fun _ => 1)
  have hc : Continuous (G n₁) := by unfold G e; fun_prop
  have hper : Function.Periodic F 1 := by
    intro x
    have hG := G_periodic n₁ x
    simp only [F, A, Set.indicator_apply, Set.mem_setOf_eq, hG]
  have heq (s : ℝ) : (∫ x in Icc (0 : ℝ) 1, F (x + s)) =
      volume.real (exceptionalSlice n₁ s) := by
    let B : Set ℝ := {x | (PairLinnik.lam : ℝ) * L n₁ ≤ ‖G n₁ (x + s)‖}
    have hB : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
    have hid : (fun x => F (x + s)) = B.indicator (fun _ => (1 : ℝ)) := by rfl
    rw [hid, setIntegral_indicator hB]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [← heq t, ← heq 0]
  calc
    (∫ x in Icc (0 : ℝ) 1, F (x + t)) = ∫ x in (0 : ℝ)..1, F (x + t) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = ∫ x in t..t + 1, F x := by
      rw [intervalIntegral.integral_comp_add_right]
      simp only [zero_add, add_zero, add_comm]
    _ = ∫ x in (0 : ℝ)..1, F x := by
      simpa only [zero_add] using hper.intervalIntegral_add_eq t 0
    _ = ∫ x in Icc (0 : ℝ) 1, F (x + 0) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simp only [add_zero]

/-- Hu page 194, Lemma 2.3, the exceptional measure display. Split in
Decomp577eLeavesPT, CONDITIONAL ON its moment certificate and shift leaves.
Only the unshifted unit interval remains. The strict exponent reserve is
retained literally. Platt and Trudgian sections 3 and 4 describe the
interval computation but the lab has no certificate for this strict reserve. -/
theorem platt_trudgian_unshifted_bound :
    ∃ E : ℝ, 3 / 4 + 1 / 10 ^ 10 < E ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ n₁ : ℕ, N₀ ≤ n₁ →
        volume.real (exceptionalSlice n₁ 0) ≤ K * (n₁ : ℝ) ^ (-E) :=
  LeanLab.Hathi2021.Decomp577eLeavesPT.platt_trudgian_unshifted_bound_of_leaves

/-- Hu pages 194 and 195. CONDITIONAL ON the unshifted strict exceptional
measure estimate. This supplies the exact sealed translated slice statement. -/
theorem platt_trudgian_slice_bound :
    ∃ E : ℝ, 3 / 4 + 1 / 10 ^ 10 < E ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ n₁ : ℕ, N₀ ≤ n₁ → ∀ t : ℝ,
        volume.real (exceptionalSlice n₁ t) ≤ K * (n₁ : ℝ) ^ (-E) := by
  obtain ⟨E, hE, K, hK, N, hN⟩ := platt_trudgian_unshifted_bound
  refine ⟨E, hE, K, hK, N, ?_⟩
  intro n₁ hn t
  rw [exceptionalSlice_volume_eq]
  exact hN n₁ hn

/-- Helper for Hu page 194, a nonempty instance of the actual exceptional
set. Once L is at least 40, the point zero belongs to the unshifted slice. -/
theorem zero_mem_exceptionalSlice_of_L (n₁ : ℕ) (hL : 40 ≤ L n₁) :
    (0 : ℝ) ∈ exceptionalSlice n₁ 0 := by
  have hL0 : 0 ≤ L n₁ := by linarith
  have hf4 : 4 ≤ ⌊L n₁⌋₊ := by
    apply (Nat.le_floor_iff hL0).2
    norm_num
    linarith
  have hG : ‖G n₁ 0‖ = ((Finset.Icc 4 ⌊L n₁⌋₊).card : ℝ) := by simp [G, e]
  have hcard : ((Finset.Icc 4 ⌊L n₁⌋₊).card : ℝ) = (⌊L n₁⌋₊ : ℝ) - 3 := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : 4 ≤ ⌊L n₁⌋₊ + 1)]
    push_cast
    ring
  have hfloor := Nat.lt_floor_add_one (L n₁)
  simp only [exceptionalSlice, Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq, zero_add]
  refine ⟨by norm_num, ?_⟩
  rw [hG, hcard]
  norm_num [PairLinnik.lam]
  nlinarith

/-- Helper for Hu page 194. The eventual unshifted exceptional sets are
nonempty. Thus the measure input is not justified by eventual emptiness. -/
theorem exceptionalSlice_eventually_nonempty :
    ∃ N₀ : ℕ, ∀ n₁ : ℕ, N₀ ≤ n₁ → (exceptionalSlice n₁ 0).Nonempty := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_L_atTop.eventually_ge_atTop 40)
  exact ⟨N, fun n hn => ⟨0, zero_mem_exceptionalSlice_of_L n (hN n hn)⟩⟩

end LeanLab.Hathi2021.Decomp577e
