import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 10

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 10: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs10 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (6728400, [(2, 4), (3, 3), (5, 2), (7, 1), (89, 1)], [(89, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (6834240, [(2, 6), (3, 3), (5, 1), (7, 1), (113, 1)], [(113, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (7025760, [(2, 5), (3, 2), (5, 1), (7, 1), (17, 1), (41, 1)], [(41, [(2, 5), (3, 2), (5, 1), (7, 1), (17, 1)])]),
  (7071120, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (61, 1)], [(61, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1)])]),
  (7136640, [(2, 7), (3, 3), (5, 1), (7, 1), (59, 1)], [(59, [(2, 7), (3, 3), (5, 1), (7, 1)])])]

theorem certOK10 : certOK certs10 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
