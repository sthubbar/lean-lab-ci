import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 11

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 11: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs11 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (7166880, [(2, 5), (3, 4), (5, 1), (7, 1), (79, 1)], [(79, [(2, 5), (3, 4), (5, 1), (7, 1)])]),
  (7232400, [(2, 4), (3, 2), (5, 2), (7, 2), (41, 1)], [(41, [(2, 4), (3, 2), (5, 2), (7, 2)])]),
  (7333200, [(2, 4), (3, 3), (5, 2), (7, 1), (97, 1)], [(97, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (7368480, [(2, 5), (3, 2), (5, 1), (7, 1), (17, 1), (43, 1)], [(43, [(2, 5), (3, 2), (5, 1), (7, 1), (17, 1)])]),
  (7378560, [(2, 7), (3, 3), (5, 1), (7, 1), (61, 1)], [(61, [(2, 7), (3, 3), (5, 1), (7, 1)])])]

theorem certOK11 : certOK certs11 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
