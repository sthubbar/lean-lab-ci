import LeanLab.ExceptionalSet.ETDQ4Split

/-!
Task685. The exact count form of Kuipers and Niederreiter 1974, chapter 2,
Theorem 2.5, page 112 display 2.33. The proof on pages 113 and 114 uses the
Fejer kernel and the discrepancy function. ETDQ4Split supplies that proof.
The constants are 6 over m plus 1 and 4 over pi.
P0082 page 359 Lemma 4 then follows CONDITIONAL ON Theorem2 alone.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.DQLemma4

/-- Kuipers and Niederreiter page 112 display 2.33 in the sealed count form. -/
theorem erdosTuranDQ4_proved : ErdosTuranDQ4 := by
  exact ETDQ4.erdosTuranDQ4_split

/-- P0082 page 359 Lemma 4. CONDITIONAL ON Theorem2. -/
theorem lemma4_of_theorem2 : U1539.Theorem2 → U1539.Lemma4 := by
  exact lemma4_of_erdosTuran_theorem2 erdosTuranDQ4_proved

end LeanLab.ExceptionalSet.DQLemma4
