import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 13

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 13: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs13 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (7852320, [(2, 5), (3, 2), (5, 1), (7, 1), (19, 1), (41, 1)], [(41, [(2, 5), (3, 2), (5, 1), (7, 1), (19, 1)])]),
  (7922880, [(2, 6), (3, 3), (5, 1), (7, 1), (131, 1)], [(131, [(2, 6), (3, 3), (5, 1), (7, 1)])])]

theorem certOK13 : certOK certs13 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
