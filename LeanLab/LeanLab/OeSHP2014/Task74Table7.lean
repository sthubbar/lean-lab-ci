import Mathlib.Tactic.NormNum

/-! Internal arithmetic of Table 7 on page 2047.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- Printed partial sums, represented as exact rationals at their printed precision. -/
def table7Sums : List (ℕ × ℚ) := [
  (1, 956762609731646985 / 10),
  (2, -1634504070427191937 / 10),
  (3, 2166355093958032465 / 10),
  (4, -1788769679611982637 / 10),
  (5, 1415827714924861865 / 10),
  (6, -697709480643092000 / 10),
  (10, 62966865710230219 / 10),
  (15, 83045015601298407 / 10),
  (20, 83030411009713764 / 10),
  (25, 83030411896680305 / 10),
  (30, 83030411896675260 / 10),
  (44, 83030411896675260 / 10)]

/-- The alternating truncations enclose the printed full approximation. -/
theorem table7_alternating : ∀ r ∈ table7Sums,
    (Even r.1 → r.2 ≤ 8303041189667526) ∧
    (Odd r.1 → 8303041189667526 ≤ r.2) := by
  norm_num [table7Sums, even_iff_two_dvd]

/-- Derived count and relative error arithmetic at four times ten to the eighteenth. -/
theorem table7_count_arithmetic :
    (8303041189667526 : ℚ) - 8303041149824931 = 39842595 ∧
    (39842595 : ℚ) / 8303041149824931 < 1 / 200000000 ∧
    (8303041149824931 : ℕ) + 1991696958850175068 = 2 * 10^18 - 1 ∧
    (8303041149824931 : ℕ) < 2 * 10^18 - 1 := by
  norm_num

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table7_alternating

#print axioms LeanLab.OeSHP2014.Task74.table7_count_arithmetic
