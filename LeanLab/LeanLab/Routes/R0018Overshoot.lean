/-
Route R-0018, T3, part 3: the overshoot of the q ∣ N major arcs, stated with the lab's
twin prime constant bound. For N = 2^(k+1) the discrete major arc constant is
Σ_{q ∣ N} μ(q)²/φ(q) = 2 (R0018MajorArc.major_const_two_pow), while the Hardy-Littlewood
singular series of N is 2 twinC ≤ 1.32034 (ChenExplicit.TwinCUpper.twinC_le_066017). So the
major arcs exceed the conjectured main term by more than 0.6796 times π(N)²/N, which the
remaining arcs must cancel. The arcs' heuristic size is not proved here; only the two
constants are.

AI wrote this Lean code. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.Routes.R0018MajorArc
import LeanLab.ChenExplicit.TwinCUpper

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace LeanLab.Routes.R0018

theorem overshoot_two_pow (k : ℕ) :
    ((∑ q ∈ (2 ^ (k + 1)).divisors, ((μ q : ℤ) : ℚ) ^ 2 / (Nat.totient q : ℚ) : ℚ) : ℝ)
      - 2 * LeanLab.ChenExplicit.twinC ≥ 0.67966 := by
  rw [major_const_two_pow]
  have h := LeanLab.ChenExplicit.TwinCUpper.twinC_le_066017
  push_cast
  linarith

end LeanLab.Routes.R0018

#print axioms LeanLab.Routes.R0018.overshoot_two_pow
