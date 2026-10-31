/-
AI wrote this Lean code for CODEX task70.
Section 2, equation 2.3, page 427, and Table I, page 430.
This is the checked prefix of the earlier-choice exclusion. The full minimum remains open.
-/
import LeanLab.SteinStein1965.EarlierOptions
import LeanLab.SteinStein1965.Earlier.Trial01
import LeanLab.SteinStein1965.Earlier.Trial02
import LeanLab.SteinStein1965.Earlier.Trial03
import LeanLab.SteinStein1965.Earlier.Trial04
import LeanLab.SteinStein1965.Earlier.Trial05
import LeanLab.SteinStein1965.Earlier.Trial06
import LeanLab.SteinStein1965.Earlier.Trial07
import LeanLab.SteinStein1965.Earlier.Trial08
import LeanLab.SteinStein1965.Earlier.Trial09
import LeanLab.SteinStein1965.Earlier.Trial10
import LeanLab.SteinStein1965.Earlier.Trial11

namespace LeanLab.SteinStein1965

theorem no_single_choice_before316 :
    ∀ r ∈ earlierOptions89, r.1 < 316 →
      ((changedRun89 r.1 r.2 400000).1.filter (· ≤ 200000)).length ≠ 1246 := by
  rw [earlierOptions89_eq]
  intro r hr ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [earlierTrial01]
    decide
  · rw [earlierTrial02]
    decide
  · rw [earlierTrial03]
    decide
  · rw [earlierTrial04]
    decide
  · rw [earlierTrial05]
    decide
  · rw [earlierTrial06]
    decide
  · rw [earlierTrial07]
    decide
  · rw [earlierTrial08]
    decide
  · rw [earlierTrial09]
    decide
  · rw [earlierTrial10]
    decide
  · rw [earlierTrial11]
    decide
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.no_single_choice_before316
