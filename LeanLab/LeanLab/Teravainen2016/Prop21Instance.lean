/-
P0076 Proposition 2.1, pages 7 to 8. A simultaneous nonvacuity instance.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Prop21

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

noncomputable def pointCutoff12 (n : ℤ) : ℝ := if n % 12 = 0 then 1 else 0

theorem pointCutoff12_mean : chiNorm 12 pointCutoff12 = 1 / 12 := by
  unfold chiNorm
  simp only [sum_range_succ]
  norm_num [pointCutoff12]

/-- A point cutoff meets display 2.1 with small eta on Z_12. -/
theorem pointCutoff12_props : ChiProps 12 {1} (1 / 100) pointCutoff12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    unfold pointCutoff12
    split_ifs <;> norm_num
  · intro n
    unfold pointCutoff12
    have he : n % 12 = 0 ↔ (-n) % 12 = 0 := by omega
    simp only [he]
  · intro n
    simp [pointCutoff12]
  · intro n hn hB
    have hd := hB 1 (by simp)
    interval_cases n <;> norm_num [distInt, round] at hd <;> norm_num [pointCutoff12]
  · intro n hn hB
    by_cases hn0 : n = 0
    · subst n
      exfalso
      apply hB
      intro ξ hξ
      simp only [mem_singleton] at hξ
      subst ξ
      norm_num [distInt]
    · have : (n : ℤ) % 12 ≠ 0 := by omega
      simp only [pointCutoff12, if_neg this]
      norm_num
  · rw [pointCutoff12_mean]
    norm_num

/-- The local lower bound and mass hypothesis hold simultaneously. -/
theorem prop21_instance_physical :
    (∀ t : ℤ, (12 : ℝ) / 3 < t → (t : ℝ) < 2 * 12 / 3 →
      1 * chiNorm 12 pointCutoff12 ≤ convChi 12 (fun _ => 12) pointCutoff12 t) ∧
    1 * (12 : ℝ) ≤ ∑ n ∈ (range 12).filter
      (fun n : ℕ => (12 : ℝ) / 3 < n ∧ (n : ℝ) < 12 / 2), (12 : ℝ) := by
  constructor
  · intro t ht1 ht2
    have htlo : 4 < t := by exact_mod_cast (show (4 : ℝ) < t by norm_num at ht1; exact ht1)
    have hthi : t < 8 := by exact_mod_cast (show (t : ℝ) < 8 by norm_num at ht2; exact ht2)
    rw [pointCutoff12_mean]
    interval_cases t <;> unfold convChi <;> simp only [sum_range_succ] <;> norm_num [pointCutoff12]
  · norm_num [sum_range_succ, filter_insert, filter_singleton]
    exact ⟨5, by norm_num⟩

/-- Crude moment estimates already give a concrete restriction constant. -/
theorem prop21_instance_moments :
    ∀ r ∈ ({3, 4} : Finset ℕ), ∑ ξ ∈ range 12, ‖fhat 12 (fun _ => 12) ξ‖ ^ r ≤ (248832 : ℝ) := by
  intro r hr
  have hnorm : ∀ ξ, ‖fhat 12 (fun _ => 12) ξ‖ ≤ 12 := by
    intro ξ
    have h := fhat_norm_le_mean 12 (fun _ => 12) (by intro _; norm_num) ξ
    norm_num at h
    exact h
  calc
    _ ≤ ∑ ξ ∈ range 12, (12 : ℝ) ^ r := by
      apply sum_le_sum
      intro ξ _
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm ξ) r
    _ ≤ _ := by
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl <;> norm_num

#print axioms pointCutoff12_mean
#print axioms pointCutoff12_props
#print axioms prop21_instance_physical
#print axioms prop21_instance_moments

end LeanLab.Teravainen2016
