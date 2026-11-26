import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 9

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 9: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs9 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (6410880, [(2, 7), (3, 3), (5, 1), (7, 1), (53, 1)], [(53, [(2, 7), (3, 3), (5, 1), (7, 1)])]),
  (6441120, [(2, 5), (3, 4), (5, 1), (7, 1), (71, 1)], [(71, [(2, 5), (3, 4), (5, 1), (7, 1)])]),
  (6471360, [(2, 6), (3, 3), (5, 1), (7, 1), (107, 1)], [(107, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (6612480, [(2, 9), (3, 2), (5, 1), (7, 1), (41, 1)], [(41, [(2, 9), (3, 2), (5, 1), (7, 1)])]),
  (6622560, [(2, 5), (3, 4), (5, 1), (7, 1), (73, 1)], [(73, [(2, 5), (3, 4), (5, 1), (7, 1)])])]

theorem certOK9 : certOK certs9 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
