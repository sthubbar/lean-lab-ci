import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 5

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 5: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs5 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (5282640, [(2, 4), (3, 2), (5, 1), (11, 1), (23, 1), (29, 1)], [(29, [(2, 4), (3, 2), (5, 1), (11, 1), (23, 1)])]),
  (5332320, [(2, 5), (3, 2), (5, 1), (7, 1), (23, 2)], [(23, [(2, 5), (3, 2), (5, 1), (7, 1), (23, 1)]), (23, [(2, 5), (3, 2), (5, 1), (7, 1)])]),
  (5352480, [(2, 5), (3, 4), (5, 1), (7, 1), (59, 1)], [(59, [(2, 5), (3, 4), (5, 1), (7, 1)])]),
  (5367600, [(2, 4), (3, 3), (5, 2), (7, 1), (71, 1)], [(71, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (5382720, [(2, 6), (3, 3), (5, 1), (7, 1), (89, 1)], [(89, [(2, 6), (3, 3), (5, 1), (7, 1)])])]

theorem certOK5 : certOK certs5 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
