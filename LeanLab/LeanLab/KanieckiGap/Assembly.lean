/-
P0022 Kaniecki 1995, Theorem, odd half: under RH every odd n > 1 is a sum of at most five
primes. The lab cites it as `SchnirelmannBounds.kaniecki_odd` with `sorry`. Here it is PROVED
CONDITIONAL ON named inputs only, none of them Kaniecki's Lemmas 4 to 7:
* the three cited inputs of `ChirreHagen2025.goldbach_10`: the bilinear J_ψ bound under RH,
  even Goldbach to 4 · 10^18, Schoenfeld's θ bound under RH;
* Liu-Wang 2002, every odd n ≥ e^3100 a sum of three primes, `Ternary.liuWang`'s type;
* `GapBound1476`, prime gaps below 4 · 10^18 at most 1476.
Route: goldbach_10 gives Kaniecki's interval statement for log N₀ ≤ 374000, FromG10, and
N₀ = ⌊e^3100⌋ has log N₀ ≤ 3100. Unit U-1064, PC run 20261019T1204Z-858.
AI-written Lean code, Claude. Checked only by the Lean kernel. Goldbach is OPEN; ternary
Goldbach, Helfgott 2013, already implies the odd statement without RH.
-/
import Mathlib
import LeanLab.KanieckiGap.FromG10
import LeanLab.ChirreHagen2025.Bilinear64
import LeanLab.Ternary.Statements

namespace LeanLab.KanieckiGap
open Real LeanLab.SchnirelmannConstant
open LeanLab.GoldbachGaps.Sumset (GapBound1476)

/-- `log ⌊e^3100⌋ ≤ 374000`. -/
theorem log_floor_exp3100_le : Real.log (⌊Real.exp 3100⌋₊ : ℝ) ≤ 374000 := by
  have hpos : (0 : ℝ) < (⌊Real.exp 3100⌋₊ : ℝ) := by
    have : (1 : ℝ) ≤ Real.exp 3100 := Real.one_le_exp (by norm_num)
    exact_mod_cast Nat.floor_pos.mpr this
  calc Real.log (⌊Real.exp 3100⌋₊ : ℝ) ≤ Real.log (Real.exp 3100) :=
        Real.log_le_log hpos (Nat.floor_le (Real.exp_pos _).le)
    _ = 3100 := Real.log_exp _
    _ ≤ 374000 := by norm_num

/-- Liu-Wang's range in the shape `kaniecki_odd_of_g10` takes, at `N₀ = ⌊e^3100⌋`. -/
theorem above_floor_of_liuWang (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) :
    ∀ n : ℕ, Odd n → ⌊Real.exp 3100⌋₊ < n → IsTernarySum n := by
  intro n ho hn
  exact hLW n ho (Nat.lt_of_floor_lt hn).le

/-- **Kaniecki 1995, odd half, from goldbach_10's inputs and Liu-Wang.** CONDITIONAL ON the
three goldbach_10 inputs, Liu-Wang 2002 and the 1476 gap bound; RH is the hypothesis of the
statement itself, exactly as `SchnirelmannBounds.kaniecki_odd` states it. -/
theorem kaniecki_odd_of_inputs
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      LeanLab.ChirreHagen2025.Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hS : RiemannHypothesis → LeanLab.ChirreHagen2025.SchoenfeldTheta)
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) (hG : GapBound1476) :
    RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := fun hRH =>
  kaniecki_odd_of_g10 (LeanLab.ChirreHagen2025.goldbach_10 h2 hE hS hRH)
    log_floor_exp3100_le (above_floor_of_liuWang hLW) hG

/-- Type check: the conclusion is exactly the cited `SchnirelmannBounds.kaniecki_odd` shape. -/
example (h : RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n) :
    RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := h

/-- Vacuity: the conclusion is not empty at n = 7 = 2 + 2 + 3. -/
example : AtMostPrimes 5 7 :=
  ((AtMostPrimes.prime Nat.prime_two).add ((AtMostPrimes.prime Nat.prime_two).add
    (AtMostPrimes.prime Nat.prime_three))).mono (by norm_num)

end LeanLab.KanieckiGap

#print axioms LeanLab.KanieckiGap.log_floor_exp3100_le
#print axioms LeanLab.KanieckiGap.above_floor_of_liuWang
#print axioms LeanLab.KanieckiGap.kaniecki_odd_of_inputs
