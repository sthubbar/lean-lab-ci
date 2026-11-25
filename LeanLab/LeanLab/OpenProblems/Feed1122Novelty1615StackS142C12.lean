import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 12

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 12: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs12 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (7529760, [(2, 5), (3, 4), (5, 1), (7, 1), (83, 1)], [(83, [(2, 5), (3, 4), (5, 1), (7, 1)])]),
  (7585200, [(2, 4), (3, 2), (5, 2), (7, 2), (43, 1)], [(43, [(2, 4), (3, 2), (5, 2), (7, 2)])]),
  (7635600, [(2, 4), (3, 3), (5, 2), (7, 1), (101, 1)], [(101, [(2, 4), (3, 3), (5, 2), (7, 1)])]),
  (7766640, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (67, 1)], [(67, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1)])]),
  (7786800, [(2, 4), (3, 3), (5, 2), (7, 1), (103, 1)], [(103, [(2, 4), (3, 3), (5, 2), (7, 1)])])]

theorem certOK12 : certOK certs12 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
