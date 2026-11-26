import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 3

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 3: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs3 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (4752720, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (41, 1)], [(41, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1)])]),
  (4777920, [(2, 6), (3, 3), (5, 1), (7, 1), (79, 1)], [(79, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (4808160, [(2, 5), (3, 4), (5, 1), (7, 1), (53, 1)], [(53, [(2, 5), (3, 4), (5, 1), (7, 1)])]),
  (4959360, [(2, 7), (3, 3), (5, 1), (7, 1), (41, 1)], [(41, [(2, 7), (3, 3), (5, 1), (7, 1)])]),
  (4984560, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (43, 1)], [(43, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1)])])]

theorem certOK3 : certOK certs3 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
