import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 1

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 1: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs1 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (4289040, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (37, 1)], [(37, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1)])]),
  (4294080, [(2, 6), (3, 3), (5, 1), (7, 1), (71, 1)], [(71, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (4339440, [(2, 4), (3, 3), (5, 1), (7, 2), (41, 1)], [(41, [(2, 4), (3, 3), (5, 1), (7, 2)])]),
  (4415040, [(2, 6), (3, 3), (5, 1), (7, 1), (73, 1)], [(73, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (4427280, [(2, 4), (3, 2), (5, 1), (11, 1), (13, 1), (43, 1)], [(43, [(2, 4), (3, 2), (5, 1), (11, 1), (13, 1)])])]

theorem certOK1 : certOK certs1 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
