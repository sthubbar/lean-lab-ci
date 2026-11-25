import LeanLab.OpenProblems.Feed1122Novelty1615StackS142

/-!
# Erdős 273, Novelty1615, S142 orbit certificates, piece 8

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. One piece of the orbit chain
certificate table of `Feed1122Novelty1615StackS142`, checked by `decide +kernel`; one module per
piece keeps each build under the memory limit.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

/-- Certificate piece 8: candidate `L`, its factorization, its orbit chain, computed by session
S142 in Python. -/
def certs8 : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) := [
  (6078240, [(2, 5), (3, 4), (5, 1), (7, 1), (67, 1)], [(67, [(2, 5), (3, 4), (5, 1), (7, 1)])]),
  (6108480, [(2, 6), (3, 3), (5, 1), (7, 1), (101, 1)], [(101, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (6143760, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (53, 1)], [(53, [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1)])]),
  (6229440, [(2, 6), (3, 3), (5, 1), (7, 1), (103, 1)], [(103, [(2, 6), (3, 3), (5, 1), (7, 1)])]),
  (6274800, [(2, 4), (3, 3), (5, 2), (7, 1), (83, 1)], [(83, [(2, 4), (3, 3), (5, 2), (7, 1)])])]

theorem certOK8 : certOK certs8 = true := by decide +kernel

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
