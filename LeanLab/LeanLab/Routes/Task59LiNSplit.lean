/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
An elementary first step toward the U1436 next action.
The function liN is the discrete sum, not the continuous logarithmic integral.
-/
import LeanLab.PNTPort.BVMax.Primes

namespace LeanLab.Routes.Task59

open Finset Real LeanLab.PNTPort.BVMax

/-- Split the discrete logarithmic integral at an arbitrary natural cutoff. -/
theorem liN_le_split (N M : ℕ) (hM : 2 ≤ M) :
    liN N ≤ (M : ℝ) / log 2 + (N : ℝ) / log M := by
  classical
  let S := Icc 1 N
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlogM : 0 < log M := log_pos (by exact_mod_cast (by omega : 1 < M))
  have hterm : ∀ n ∈ S, 1 / log n ≤ 1 / log 2 := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    by_cases hn2 : n = 1
    · simpa [hn2] using (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hlog2.le)
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      exact one_div_le_one_div_of_le hlog2 (log_le_log (by norm_num) h2)
  have hheadCard : (S.filter (fun n => n ≤ M)).card ≤ M := by
    calc (S.filter (fun n => n ≤ M)).card ≤ (Icc 1 M).card := by
          apply card_le_card
          intro n hn
          obtain ⟨hn, hnM⟩ := mem_filter.mp hn
          exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hnM⟩
      _ = M := by simp
  have htailCard : (S.filter (fun n => ¬ n ≤ M)).card ≤ N := by
    calc (S.filter (fun n => ¬ n ≤ M)).card ≤ S.card := card_filter_le _ _
      _ = N := by simp [S]
  have hhead : (∑ n ∈ S.filter (fun n => n ≤ M), 1 / log (n : ℝ)) ≤
      (M : ℝ) * (1 / log 2) := by
    calc (∑ n ∈ S.filter (fun n => n ≤ M), 1 / log (n : ℝ)) ≤
        ∑ _n ∈ S.filter (fun n => n ≤ M), 1 / log 2 :=
          sum_le_sum (fun n hn => hterm n (mem_filter.mp hn).1)
      _ = ((S.filter (fun n => n ≤ M)).card : ℝ) * (1 / log 2) := by
          simp
      _ ≤ (M : ℝ) * (1 / log 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hheadCard) (by positivity)
  have htail : (∑ n ∈ S.filter (fun n => ¬ n ≤ M), 1 / log (n : ℝ)) ≤
      (N : ℝ) * (1 / log M) := by
    calc (∑ n ∈ S.filter (fun n => ¬ n ≤ M), 1 / log (n : ℝ)) ≤
        ∑ _n ∈ S.filter (fun n => ¬ n ≤ M), 1 / log M := by
          apply sum_le_sum
          intro n hn
          have hnM : M ≤ n := by have := (mem_filter.mp hn).2; omega
          exact one_div_le_one_div_of_le hlogM
            (log_le_log (by exact_mod_cast (by omega : 0 < M)) (by exact_mod_cast hnM))
      _ = ((S.filter (fun n => ¬ n ≤ M)).card : ℝ) * (1 / log M) := by
          simp
      _ ≤ (N : ℝ) * (1 / log M) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast htailCard) (by positivity)
  unfold liN
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n => n ≤ M)]
  simpa only [mul_one_div] using add_le_add hhead htail

/-- Concrete cutoff instance for the split bound. -/
example : liN 100 ≤ (10 : ℝ) / log 2 + (100 : ℝ) / log 10 :=
  liN_le_split 100 10 (by norm_num)

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.liN_le_split
