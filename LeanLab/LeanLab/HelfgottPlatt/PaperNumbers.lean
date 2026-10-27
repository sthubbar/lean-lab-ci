/-
Helfgott and Platt 2013, P0006, unit U-0950, run 20261018T1404Z-22216.
Every printed number of the paper that can be checked by arithmetic, and Theorem 4.1 as a
CONDITIONAL theorem: it follows from binary Goldbach to 4e18, a lower ternary range, and a
prime ladder with gaps at most 4e18 - 4 that ends within 2e18 of T. The ladder itself is the
paper's computation and stays cited.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.HelfgottPlatt.Ladder
import LeanLab.HelfgottPlatt.Proth

namespace LeanLab.HelfgottPlatt.PaperNumbers

open LeanLab.HelfgottPlatt LeanLab.HelfgottPlatt.Proth

/-- T is exactly the 492,700 ranges of Section 5 times the interval width 2^54 · 10^9 of Section 4. -/
theorem T_eq_ranges : T = 492700 * (2 ^ 54 * 10 ^ 9) := by norm_num [T]

/-- T is itself k · 2^52 with k = 1.9708 · 10^15 < 2^52, the Proth range with n = 52. -/
theorem T_eq_k : T = 1970800000000000 * 2 ^ 52 ∧ 1970800000000000 < 2 ^ 52 := by
  norm_num [T]

/-- Section 4: reaching 10^31 needs n at least 52, since a Proth number with n ≤ 51 is below 10^31. -/
theorem proth_lt_of_le_51 {k n : ℕ} (hk : k < 2 ^ n) (hn : n ≤ 51) : k * 2 ^ n + 1 < 10 ^ 31 := by
  have h1 : k * 2 ^ n < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_right hk (by positivity)
  have h2 : 2 ^ n * 2 ^ n ≤ 2 ^ 51 * 2 ^ 51 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hn) (Nat.pow_le_pow_right (by norm_num) hn)
  have h3 : (2 : ℕ) ^ 51 * 2 ^ 51 < 10 ^ 31 - 1 := by norm_num
  omega

/-- Section 6: with n = 52 the method reaches about 2 · 10^31: the largest Proth number is above it. -/
theorem reach_n52 : 2 * 10 ^ 31 < (2 ^ 52 - 1) * 2 ^ 52 + 1 := by norm_num

/-- Section 4: an interval of width 2^54 · 10^9 holds 4 · 10^9 numbers k · 2^52 + 1. -/
theorem candidates : 2 ^ 54 * 10 ^ 9 / 2 ^ 52 = 4 * 10 ^ 9 := by norm_num

/-- Section 6: T is more than 8 · 10^10 times Saouter's 10^20. -/
theorem factor_vs_1998 : 8 * 10 ^ 10 * 10 ^ 20 < T := by norm_num [T]

/-- Section 6: the gain 10^7 · 10 · 800 = 8 · 10^10, and 10^7 is 4e18 over Sinisalo's 4e11. -/
theorem gain_split : 10 ^ 7 * 10 * 800 = 8 * 10 ^ 10 ∧ 4 * 10 ^ 18 = 10 ^ 7 * (4 * 10 ^ 11) := by
  norm_num

/-- Section 5: 492,700 ranges at about 270 + 40 seconds each is about 42,400 core hours,
which the paper rounds to about 40,000. -/
theorem core_hours : 40000 * 3600 ≤ 492700 * (270 + 40) ∧ 492700 * (270 + 40) < 42500 * 3600 := by
  norm_num

/-- The ladder reduction from a lower ternary range, not from 3. -/
theorem ternary_of_lower_and_ladder {B A X p₀ : ℕ} (hB : EvenGoldbachUpTo B)
    (hA : TernaryGoldbachUpTo A) (hp : p₀.Prime) (h3 : 3 ≤ p₀) (hpA : p₀ + 3 ≤ A)
    (t : List ℕ) (ht : ∀ p ∈ t, p.Prime) (hc : (p₀ :: t).IsChain (LadderStep B))
    (hX : X ≤ t.getLastD p₀ + B) : TernaryGoldbachUpTo X := by
  intro n hn h7 hnX
  by_cases hnA : n ≤ A
  · exact hA n hn h7 hnA
  · exact ternary_of_ladder_aux hB t p₀ hp h3 ht hc n hn (by omega) (by omega)

/-- Theorem 4.1, CONDITIONAL ON binary Goldbach to 4e18, ternary Goldbach to A, and the cited
ladder: primes from p₀ ≤ A - 3 with gaps at most 4e18 - 4 whose last rung is within 2e18 of T. -/
theorem theorem4_1_of {A p₀ : ℕ} (hB : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hA : TernaryGoldbachUpTo A) (hp : p₀.Prime) (h3 : 3 ≤ p₀) (hpA : p₀ + 3 ≤ A)
    (t : List ℕ) (ht : ∀ p ∈ t, p.Prime) (hc : (p₀ :: t).IsChain (LadderStep (4 * 10 ^ 18)))
    (hlast : T ≤ t.getLastD p₀ + 2 * 10 ^ 18) : TernaryGoldbachUpTo T :=
  ternary_of_lower_and_ladder hB hA hp h3 hpA t ht hc (by omega)

end LeanLab.HelfgottPlatt.PaperNumbers
