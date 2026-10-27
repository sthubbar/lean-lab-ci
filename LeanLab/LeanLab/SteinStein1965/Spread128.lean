/-
AI wrote this Lean code for CODEX task128.
QUESTION: the strict 1.5 percent remark on page 429 against Table I on page 430.
Only arithmetic on the printed entries is checked. No algorithm counts are asserted.
-/
import LeanLab.SteinStein1965.Statements

namespace LeanLab.SteinStein1965

/-- Page 430, x equal to 2600000, columns starting at 3 and 97. -/
theorem printed_spread_row13 :
    (tableI[1]!).1 = 3 ∧ (tableI[11]!).1 = 97 ∧
    (tableI[1]!).2.getD 12 0 = 5108 ∧ (tableI[11]!).2.getD 12 0 = 5024 ∧
    3 * (tableI[11]!).2.getD 12 0 <
      200 * ((tableI[1]!).2.getD 12 0 - (tableI[11]!).2.getD 12 0) := by
  decide +kernel

/-- Page 430, x equal to 2800000, the same two columns. -/
theorem printed_spread_row14 :
    (tableI[1]!).2.getD 13 0 = 5318 ∧ (tableI[11]!).2.getD 13 0 = 5236 ∧
    3 * (tableI[11]!).2.getD 13 0 <
      200 * ((tableI[1]!).2.getD 13 0 - (tableI[11]!).2.getD 13 0) := by
  decide +kernel

/-- QUESTION. Page 429's strict 1.5 percent statement fails for the printed Table I. -/
theorem printed_late_spread_question :
    ¬ ∀ r ∈ tableI, ∀ s ∈ tableI, r.1 ≠ 7 → s.1 ≠ 7 →
      ∀ k < 25, 11 ≤ k →
        200 * (r.2.getD k 0 - s.2.getD k 0) < 3 * s.2.getD k 0 := by
  intro h
  have hb := h (tableI[1]!) (by decide) (tableI[11]!) (by decide)
    (by decide) (by decide) 12 (by decide) (by decide)
  exact (Nat.not_lt_of_gt printed_spread_row13.2.2.2.2) hb

/-- Page 430, a separate arithmetic upper bound for the printed late rows. -/
theorem printed_late_spread_17 :
    ∀ r ∈ tableI, ∀ s ∈ tableI, r.1 ≠ 7 → s.1 ≠ 7 →
      ∀ k < 25, 11 ≤ k →
        1000 * (r.2.getD k 0 - s.2.getD k 0) < 17 * s.2.getD k 0 := by
  decide +kernel

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.printed_spread_row13
#print axioms LeanLab.SteinStein1965.printed_spread_row14
#print axioms LeanLab.SteinStein1965.printed_late_spread_question

#print axioms LeanLab.SteinStein1965.printed_late_spread_17
