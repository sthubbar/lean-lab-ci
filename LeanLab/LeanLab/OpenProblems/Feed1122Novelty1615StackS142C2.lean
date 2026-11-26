import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 2

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 2: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs2 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (4460400, [(2, 4), (3, 3), (5, 2), (7, 1), (59, 1)], [(59, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (4475520, [(2, 7), (3, 3), (5, 1), (7, 1), (37, 1)], [(37, [(2, 7), (3, 3), (5, 1), (7, 1)])]),
  (4541040, [(2, 4), (3, 2), (5, 1), (7, 1), (17, 1), (53, 1)], [(53, [(2, 4), (3, 2), (5, 1), (7, 1), (17, 1)])]),
  (4611600, [(2, 4), (3, 3), (5, 2), (7, 1), (61, 1)], [(61, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (4662000, [(2, 4), (3, 2), (5, 3), (7, 1), (37, 1)], [(37, [(2, 4), (3, 2), (5, 3), (7, 1)])])]

theorem certOK2 : certOK certs2 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
