import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 4

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 4: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs4 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (5019840, [(2, 6), (3, 3), (5, 1), (7, 1), (83, 1)], [(83, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (5034960, [(2, 4), (3, 5), (5, 1), (7, 1), (37, 1)], [(37, [(2, 4), (3, 5), (5, 1), (7, 1)])]),
  (5065200, [(2, 4), (3, 3), (5, 2), (7, 1), (67, 1)], [(67, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (5166000, [(2, 4), (3, 2), (5, 3), (7, 1), (41, 1)], [(41, [(2, 4), (3, 2), (5, 3), (7, 1)])]),
  (5201280, [(2, 7), (3, 3), (5, 1), (7, 1), (43, 1)], [(43, [(2, 7), (3, 3), (5, 1), (7, 1)])])]

theorem certOK4 : certOK certs4 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
