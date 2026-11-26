import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 0

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 0: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs0 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (4006800, [(2, 4), (3, 3), (5, 2), (7, 1), (53, 1)], [(53, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (4052160, [(2, 6), (3, 3), (5, 1), (7, 1), (67, 1)], [(67, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (4183200, [(2, 5), (3, 2), (5, 2), (7, 1), (83, 1)], [(83, [(2, 5), (3, 2), (5, 2), (7, 1)])]),
  (4221360, [(2, 4), (3, 2), (5, 1), (11, 1), (13, 1), (41, 1)], [(41, [(2, 4), (3, 2), (5, 1), (11, 1), (13, 1)])]),
  (4263840, [(2, 5), (3, 4), (5, 1), (7, 1), (47, 1)], [(47, [(2, 5), (3, 4), (5, 1), (7, 1)])])]

theorem certOK0 : certOK certs0 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
