import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 7

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 7: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs7 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (5682600, [(2, 3), (3, 2), (5, 2), (7, 1), (11, 1), (41, 1)], [(41, [(2, 3), (3, 2), (5, 2), (7, 1), (11, 1)])]),
  (5685120, [(2, 7), (3, 3), (5, 1), (7, 1), (47, 1)], [(47, [(2, 7), (3, 3), (5, 1), (7, 1)])]),
  (5785920, [(2, 6), (3, 2), (5, 1), (7, 2), (41, 1)], [(41, [(2, 6), (3, 2), (5, 1), (7, 2)])]),
  (5866560, [(2, 6), (3, 3), (5, 1), (7, 1), (97, 1)], [(97, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (5972400, [(2, 4), (3, 3), (5, 2), (7, 1), (79, 1)], [(79, [(2, 4), (3, 3), (5, 2), (7, 1)])])]

theorem certOK7 : certOK certs7 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
