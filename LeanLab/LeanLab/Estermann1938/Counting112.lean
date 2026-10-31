import LeanLab.Estermann1938.Positive112
import LeanLab.Estermann1938.Window112

/-!
Estermann 1938, P0091, pages 313 and 314, the counting inequality before display 50.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Counting112
open scoped BigOperators
open Decomp112 Coeff112 Prime112 Series112 Window112
attribute [local instance] Classical.propDecidable

/-- The exceptional even integers in the window defining Q1 before display 50. -/
noncomputable def Q1 (n : ℕ) (η : ℝ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun m => Even m ∧ ¬ IsGoldbachSum m ∧
    2 * (n : ℝ) * Real.log n ^ (-(η / 3)) ≤ m)

/-- Pages 313 and 314: the window exception count times the squared minimum error is bounded by the L2 error. -/
theorem window_count_error_bound {n : ℕ} (hn : 2 ≤ n) (η : ℝ)
    (hscale : 3 ≤ (n : ℝ) * Real.log n ^ (-(η / 3))) :
    ((Q1 n η).card : ℝ) * ((n : ℝ) * Real.log n ^ (-2 - η / 3)) ^ 2 ≤
      ∫ x in (0 : ℝ)..1, ‖f n x ^ 2 - g3 n x‖ ^ 2 := by
  have hW : 0 ≤ (n : ℝ) * Real.log n ^ (-2 - η / 3) := by
    exact mul_nonneg (Nat.cast_nonneg n)
      (Real.rpow_nonneg (Real.log_natCast_nonneg n) _)
  have hterm : ∀ m ∈ Q1 n η,
      ((n : ℝ) * Real.log n ^ (-2 - η / 3)) ^ 2 ≤
        ((a n m : ℝ) - b n m * S m) ^ 2 := by
    intro m hm
    obtain ⟨hmi, heven, hnot, hwindow⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm0, hmn⟩ := Finset.mem_Icc.mp hmi
    have hS := Positive112.display49 m heven (by omega)
    have ha := a_zero_of_not_goldbach n m hnot
    have hb := b_window hn hmn η hscale hwindow
    have hprod : b n m ≤ b n m * S m :=
      le_mul_of_one_le_right (b_nonneg n m) hS
    rw [ha, Nat.cast_zero, zero_sub, neg_sq]
    exact pow_le_pow_left₀ hW (hb.trans hprod) 2
  have hsub : Q1 n η ⊆ Finset.Icc 1 (2 * n) := by
    intro m hm
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    exact Finset.mem_Icc.mpr ⟨hh.1, by omega⟩
  calc
    ((Q1 n η).card : ℝ) * ((n : ℝ) * Real.log n ^ (-2 - η / 3)) ^ 2 =
        ∑ m ∈ Q1 n η, ((n : ℝ) * Real.log n ^ (-2 - η / 3)) ^ 2 := by simp
    _ ≤ ∑ m ∈ Q1 n η, ((a n m : ℝ) - b n m * S m) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ Finset.Icc 1 (2 * n), ((a n m : ℝ) - b n m * S m) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm hnot => sq_nonneg _)
    _ = _ := (display47 n).symm

/-- A nonempty small parameter instance of the paper's Q1 definition. -/
theorem Q1_instance : 2 ∈ Q1 3 60 := by
  apply Finset.mem_filter.mpr
  refine ⟨by norm_num, by decide, ?_, ?_⟩
  · rintro ⟨p, q, hp, hq, he⟩
    have := hp.two_le
    have := hq.two_le
    omega
  · have hl : (109 : ℝ) / 100 ≤ Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 109 / 100) hl 20
    have h3 : (3 : ℝ) ≤ Real.log 3 ^ 20 := by norm_num at hp; linarith
    norm_num only [show (60 : ℝ) / 3 = 20 by norm_num]
    rw [Real.rpow_neg (by positivity : 0 ≤ Real.log 3), Real.rpow_ofNat]
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith : 0 < Real.log 3 ^ 20)]
    nlinarith

#print axioms Q1_instance

#print axioms window_count_error_bound

end LeanLab.Estermann1938.Counting112
