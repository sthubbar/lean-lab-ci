import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 6

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 6: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs6 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (5448240, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (47, 1)], [(47, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1)])]),
  (5456880, [(2, 4), (3, 2), (5, 1), (11, 1), (13, 1), (53, 1)], [(53, [(2, 4), (3, 2), (5, 1), (11, 1), (13, 1)])]),
  (5518800, [(2, 4), (3, 3), (5, 2), (7, 1), (73, 1)], [(73, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (5533920, [(2, 5), (3, 4), (5, 1), (7, 1), (61, 1)], [(61, [(2, 5), (3, 4), (5, 1), (7, 1)])]),
  (5579280, [(2, 4), (3, 5), (5, 1), (7, 1), (41, 1)], [(41, [(2, 4), (3, 5), (5, 1), (7, 1)])])]

theorem certOK6 : certOK certs6 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
