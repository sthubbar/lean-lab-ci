/-
Connection sweep 2026-10-19, I-5062, unit U-5470, CLOUD 20261019T1116Z-cloud23.

Kaniecki's interval statement, every [x, x + 1.4045 · 10^12] with x ≤ n₀ holds a sum of two odd
primes, rests on his Lemmas 4 to 7 and the hard Lemma 5. Under RH the lab's
`ChirreHagen2025.goldbach_10`, from Chirre-Hagen 2025, puts a sum of two odd primes in every
(x, x + 10 log² x), and 10 log² x ≤ 1.4045 · 10^12 while log x ≤ 374000. Kaniecki's
n₀ = exp(exp(11.503)) has log n₀ ≈ 99012. So:
* `intervalProp_of_g10`: `IntervalProp (1.4045 · 10^12) N₀` for every `N₀` with
  `log N₀ ≤ 374000`, from the conclusion of `goldbach_10`;
* `kaniecki_odd_of_g10`: Kaniecki's odd statement CONDITIONAL ON that conclusion, odd n > N₀
  a sum of three primes, and the 1476 gap table.
Kaniecki's own analytic lemmas drop out. KNOWN in substance: Helfgott 2013 gives the odd
statement outright.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel. Goldbach is OPEN.
-/
import Mathlib
import LeanLab.KanieckiGap.Lemma6Gap
import LeanLab.ChirreHagen2025.Statements

namespace LeanLab.KanieckiGap
open Real LeanLab.SchnirelmannConstant
open LeanLab.GoldbachGaps.Sumset (GapBound1476)

/-- The conclusion of `ChirreHagen2025.goldbach_10`, as a Prop. -/
def G10 : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∃ n : ℕ, LeanLab.ChirreHagen2025.IsGoldbachNumber n ∧ x < n ∧
    (n : ℝ) < x + 10 * Real.log x ^ 2

/-- **Kaniecki's interval statement from `goldbach_10`**, for `log N₀ ≤ 374000`. -/
theorem intervalProp_of_g10 (h : G10) {N₀ : ℕ} (hN : Real.log N₀ ≤ 374000) :
    IntervalProp (14045 * 10 ^ 8) N₀ := by
  intro x hx
  rcases Nat.lt_or_ge x 2 with hs | hb
  · exact ⟨3, 3, Nat.prime_three, by decide, Nat.prime_three, by decide, by omega, by omega⟩
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hb
  obtain ⟨n, ⟨p, q, hp, hq, op, oq, rfl⟩, hlo, hhi⟩ := h x hxR
  have hlx : Real.log x ≤ 374000 := by
    rcases Nat.eq_zero_or_pos N₀ with h0 | h0
    · omega
    have : (x : ℝ) ≤ N₀ := by exact_mod_cast hx
    exact (Real.log_le_log (by linarith) this).trans hN
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : 10 * Real.log x ^ 2 ≤ 10 * 374000 ^ 2 := by
    have := pow_le_pow_left₀ hl0 hlx 2; linarith
  refine ⟨p, q, hp, op, hq, oq, ?_, ?_⟩
  · have : (x : ℝ) < ((p + q : ℕ) : ℝ) := hlo
    exact_mod_cast this.le
  · have hhi' : ((p + q : ℕ) : ℝ) < x + 10 * Real.log x ^ 2 := hhi
    have : ((p + q : ℕ) : ℝ) < x + 14045 * 10 ^ 8 := by
      have e : (14045 * 10 ^ 8 : ℝ) = 1404500000000 := by norm_num
      rw [e]; norm_num at hsq; linarith
    exact_mod_cast this.le

/-- **Kaniecki, odd half, through `goldbach_10`**: CONDITIONAL ON `G10`, odd `n > N₀` a sum of
three primes, and the 1476 gap table, for any `N₀` with `log N₀ ≤ 374000`. -/
theorem kaniecki_odd_of_g10 (h : G10) {N₀ : ℕ} (hN : Real.log N₀ ≤ 374000)
    (hCW : ∀ n : ℕ, Odd n → N₀ < n → IsTernarySum n) (hG : GapBound1476) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n :=
  kaniecki_odd_of' (intervalProp_of_g10 h hN) hCW hG

end LeanLab.KanieckiGap
