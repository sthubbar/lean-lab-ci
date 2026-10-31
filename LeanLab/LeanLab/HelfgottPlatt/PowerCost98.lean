/-
P0006, page 2, Section 2, multiplication count for binary modular powering.
The count follows LeanLab.Verifications.Pratt.pm. Modular reductions and integer
bit operations are not counted. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.Proth

namespace LeanLab.HelfgottPlatt.Task98

/-- Page 2, multiplication count for step 6. The base branch has no multiplication.
A nonzero exponent uses one squaring and one more multiplication if it is odd. -/
def powerMulCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, e =>
    if e = 0 then 0 else
      powerMulCount fuel (e / 2) + if e % 2 = 1 then 2 else 1

/-- Page 2, binary powering uses at most two multiplications per fuel step. -/
theorem powerMulCount_le (fuel e : ℕ) : powerMulCount fuel e ≤ 2 * fuel := by
  induction fuel generalizing e with
  | zero => simp [powerMulCount]
  | succ fuel ih =>
    by_cases he : e = 0
    · simp [powerMulCount, he]
    · simp only [powerMulCount, ite_eq_right he]
      have h := ih (e / 2)
      split <;> omega

/-- Page 2, step 6 and the sentence after it. Fuel N.log2 + 1 is sufficient
for the half exponent and uses at most 2 times that fuel in ring multiplications. -/
theorem certified_half_power (a N : ℕ) :
    ((LeanLab.Verifications.Pratt.pm (N.log2 + 1) a ((N - 1) / 2) N : ℕ) : ZMod N) =
      (a : ZMod N) ^ ((N - 1) / 2) ∧
    powerMulCount (N.log2 + 1) ((N - 1) / 2) ≤ 2 * (N.log2 + 1) := by
  have he : (N - 1) / 2 < 2 ^ (N.log2 + 1) :=
    lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) Nat.lt_log2_self
  exact ⟨LeanLab.Verifications.Pratt.pm_cast _ _ _ _ he, powerMulCount_le _ _⟩

/-- Page 2, a small instance of the operation count and the power congruence.
For N = 13 and a = 2 the exponent is six and five multiplications suffice. -/
theorem powerCost_instance :
    (13 : ℕ).log2 + 1 = 4 ∧
    LeanLab.Verifications.Pratt.pm 4 2 6 13 = 12 ∧ powerMulCount 4 6 = 5 := by
  decide +kernel

end LeanLab.HelfgottPlatt.Task98
