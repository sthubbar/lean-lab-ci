/-
AI-written Lean code, Codex task05, 2026-10-22.
Finite-prefix comparison between the lab pair series and Brun's title series.
Source: Brun 1919 title, p. 100, as reproduced by Teissier, Crible de Brun,
printed pp. 11-08 and 11-09. Original Brun page images remain inaccessible.
-/
import LeanLab.Brun1919.Final

noncomputable section
namespace LeanLab.Brun1919

/-- The only twin-prime start strictly below five is three. -/
lemma twin_start_lt_five_iff (p : ℕ) : IsTwin p ∧ p < 5 ↔ p = 3 := by
  constructor
  · rintro ⟨⟨hp, hq⟩, hlt⟩
    have hp2 := hp.two_le
    interval_cases p <;> norm_num at *
  · rintro rfl
    norm_num [IsTwin]

/-- The full pair term differs from the title convention only at the pair 3, 5. -/
lemma brun_title_term_difference (p : ℕ) :
    (if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) =
      (if 5 ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) +
        (if p = 3 then (8 / 15 : ℝ) else 0) := by
  by_cases hp : IsTwin p
  · by_cases h5 : 5 ≤ p
    · have hp3 : p ≠ 3 := by omega
      simp [hp, h5, hp3]
    · have hp3 := (twin_start_lt_five_iff p).mp ⟨hp, by omega⟩
      subst p
      norm_num [IsTwin]
  · have hp3 : p ≠ 3 := by
      rintro rfl
      norm_num [IsTwin] at hp
    simp [hp, hp3]

/-- Brun's convergent series under the title convention, starting with the pair 5, 7. -/
theorem brun_title : Summable (fun p : ℕ =>
    if 5 ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) := by
  refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) ?_ brun
  intro p
  by_cases hp : 5 ≤ p ∧ IsTwin p
  · simp only [if_pos hp, if_pos hp.2]
    exact le_rfl
  · rw [if_neg hp]
    split_ifs <;> positivity

/-- The full pair sum exceeds the title-convention sum by exactly 8/15. -/
theorem brun_title_sum_difference :
    (∑' p : ℕ, if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) =
      (∑' p : ℕ, if 5 ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) +
        8 / 15 := by
  have hs : Summable (fun p : ℕ => if p = 3 then (8 / 15 : ℝ) else 0) :=
    (hasSum_ite_eq (3 : ℕ) (8 / 15 : ℝ)).summable
  calc
    _ = ∑' p : ℕ, ((if 5 ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) +
        (if p = 3 then (8 / 15 : ℝ) else 0)) := tsum_congr brun_title_term_difference
    _ = (∑' p : ℕ, if 5 ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) +
        ∑' p : ℕ, (if p = 3 then (8 / 15 : ℝ) else 0) := brun_title.tsum_add hs
    _ = _ := by simp

#print axioms brun_title_sum_difference

#print axioms brun_title

#print axioms brun_title_term_difference

#print axioms twin_start_lt_five_iff

end LeanLab.Brun1919
