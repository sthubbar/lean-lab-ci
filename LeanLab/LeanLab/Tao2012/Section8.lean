/-
Tao 2012, Section 8, Sums of five primes, as printed in arXiv 1201.6656v4.
Read in full on 2026-10-18 by run 20261018T0503Z-16389 through Claude in Chrome,
arxiv.org/html/1201.6656, Section 8, per Lean Lab RULES_BLOCKERS B1.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.

This file replaces the lab's earlier paraphrases with the paper's own wording:
* Theorem 8.1, Ramare-Saouter, taken as a cited hypothesis `Theorem8_1`,
* the three bullet points after it, proved here from Theorem 8.1 and Theorem 1.6,
  exactly by Tao's argument, so `SmallRange` follows from those two inputs alone,
* Theorem 8.2 in its printed form, an interval `[x - N0, x - 2]` and a finite range
  `8.7e36 ≤ x ≤ exp 3100`, taken as a cited hypothesis `Theorem8_2_printed`,
* the Liu-Wang input [24], odd numbers above `exp 3100`, a cited hypothesis `LiuWang`.
-/
import Mathlib
import LeanLab.Tao2012.Statements

namespace LeanLab.Tao2012
open LeanLab.SchnirelmannConstant

/-- Theorem 8.1, Ramare-Saouter [40, Theorem 3], as printed: if `x ≥ 1.1 · 10^10` is real
there is a prime `p ≤ x` with `x - p ≤ x / (2.8 · 10^7)`. This is its restriction to
natural `x`, written without division. The paper's real statement implies it. -/
def Theorem8_1 : Prop :=
  ∀ y : ℕ, 11 * 10 ^ 9 ≤ y → ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ 28 * 10 ^ 6 * (y - p) ≤ y

/-- The prime given by Theorem 8.1 is odd. -/
theorem odd_of_81 {y p : ℕ} (hy : 11 * 10 ^ 9 ≤ y) (hp : p.Prime) (hpy : p ≤ y)
    (h : 28 * 10 ^ 6 * (y - p) ≤ y) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | h2
  · subst h2; omega
  · exact h2

/-- `B3 = 2.8 · 10^7 · N0`, the first bullet's range. -/
def B3 : ℕ := 28 * 10 ^ 6 * N0

/-- First bullet after Theorem 8.1: every odd number between 3 and `(2.8 · 10^7) N0` is a
sum of at most three primes. Proved from Theorem 8.1 and Theorem 1.6. -/
theorem bullet1 (h81 : Theorem8_1) (h16 : EvenGoldbachUpTo N0) {n : ℕ} (hn : n % 2 = 1)
    (h3 : 3 ≤ n) (hB : n ≤ B3) : AtMostPrimes 3 n := by
  simp only [B3, N0] at hB
  rcases Nat.lt_or_ge n (11 * 10 ^ 9) with hs | hl
  · have hev : Even (n - 3) := ⟨(n - 3) / 2, by omega⟩
    have h := (AtMostPrimes.prime Nat.prime_three).add
      (atMost2_of_even h16 hev (by simp only [N0]; omega))
    rw [show 3 + (n - 3) = n by omega] at h
    exact h
  · obtain ⟨p, hp, hpy, hpd⟩ := h81 n hl
    have hpo := odd_of_81 hl hp hpy hpd
    have hev : Even (n - p) := ⟨(n - p) / 2, by omega⟩
    have h := (AtMostPrimes.prime hp).add
      (atMost2_of_even h16 hev (by simp only [N0]; omega))
    rw [show 1 + 2 = 3 by rfl, show p + (n - p) = n by omega] at h
    exact h

/-- `B4 = 2.8 · 10^7 · (B3 - 3)`, slightly below the second bullet's `(2.8 · 10^7)^2 N0`;
the shift by 3 avoids the case `x - p = 1`, which the printed bullet passes over. -/
def B4 : ℕ := 28 * 10 ^ 6 * (B3 - 3)

/-- Second bullet: every even number from 2 to `B4` is a sum of at most four primes. -/
theorem bullet2 (h81 : Theorem8_1) (h16 : EvenGoldbachUpTo N0) {m : ℕ} (hm : m % 2 = 0)
    (hB : m ≤ B4) : AtMostPrimes 4 m := by
  simp only [B4, B3, N0] at hB
  rcases Nat.lt_or_ge m (11 * 10 ^ 9 + 3) with hs | hl
  · exact (atMost2_of_even h16 ⟨m / 2, by omega⟩ (by simp only [N0]; omega)).mono
      (by norm_num)
  · obtain ⟨p, hp, hpy, hpd⟩ := h81 (m - 3) (by omega)
    have hpo := odd_of_81 (by omega) hp hpy hpd
    have h := (AtMostPrimes.prime hp).add
      (bullet1 h81 h16 (n := m - p) (by omega) (by omega) (by simp only [B3, N0]; omega))
    rw [show 1 + 3 = 4 by rfl, show p + (m - p) = m by omega] at h
    exact h

/-- `B5 = 2.8 · 10^7 · (B4 - 3) + 3`. -/
def B5 : ℕ := 28 * 10 ^ 6 * (B4 - 3) + 3

/-- Third bullet: every odd number from 3 to `B5` is a sum of at most five primes. -/
theorem bullet3 (h81 : Theorem8_1) (h16 : EvenGoldbachUpTo N0) {x : ℕ} (hx : x % 2 = 1)
    (h3 : 3 ≤ x) (hB : x ≤ B5) : AtMostPrimes 5 x := by
  rcases Nat.lt_or_ge x (11 * 10 ^ 9 + 3) with hs | hl
  · exact (bullet1 h81 h16 hx h3 (by simp only [B3, N0]; omega)).mono (by norm_num)
  · simp only [B5, B4, B3, N0] at hB
    obtain ⟨p, hp, hpy, hpd⟩ := h81 (x - 3) (by omega)
    have hpo := odd_of_81 (by omega) hp hpy hpd
    have h := (AtMostPrimes.prime hp).add
      (bullet2 h81 h16 (m := x - p) (by omega) (by simp only [B4, B3, N0]; omega))
    rw [show 1 + 4 = 5 by rfl, show p + (x - p) = x by omega] at h
    exact h

/-- "In particular, Theorem 1.4 holds up to `(2.8 · 10^7)^3 N0 ≥ 8.7 · 10^36`": the lab's
shifted range `B5` already covers `8.7 · 10^36`. -/
theorem X0_le_B5 : X0 ≤ B5 := by
  simp only [X0, B5, B4, B3, N0]; norm_num

theorem X0_le_cube : (87 : ℝ) * 10 ^ 35 ≤ (2.8e7 : ℝ) ^ 3 * (4 * 10 ^ 14) := by norm_num

/-- `SmallRange` from Theorem 8.1 and Theorem 1.6 alone, Tao's own argument, zero sorry. -/
theorem small_range_of_81 (h81 : Theorem8_1) (h16 : EvenGoldbachUpTo N0) : SmallRange := by
  intro x hx h1 hX
  have hxo := Nat.odd_iff.mp hx
  exact bullet3 h81 h16 hxo (by omega) (le_trans hX X0_le_B5)

/-- Theorem 8.2, as printed: let `8.7 · 10^36 ≤ x ≤ exp 3100` be an integer. Then there is
an integer in the interval `[x - N0, x - 2]` which is the sum of three odd primes. -/
def Theorem8_2_printed : Prop :=
  ∀ x : ℕ, X0 ≤ x → (x : ℝ) ≤ Real.exp 3100 →
    ∃ y p q r : ℕ, x - N0 ≤ y ∧ y ≤ x - 2 ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧
      p % 2 = 1 ∧ q % 2 = 1 ∧ r % 2 = 1 ∧ y = p + q + r

/-- The Liu-Wang input [24] as Tao quotes it: every odd number larger than `exp 3100` is
the sum of three primes. -/
def LiuWang : Prop :=
  ∀ x : ℕ, Odd x → Real.exp 3100 < (x : ℝ) → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
    x = p + q + r

/-- Theorem 1.4 from the four inputs Section 8 names: Theorem 8.1, Theorem 1.6, Theorem 8.2
as printed and Liu-Wang. Zero sorry of its own; CONDITIONAL ON those four. -/
theorem theorem1_4_of_section8 (h81 : Theorem8_1) (h16 : EvenGoldbachUpTo N0)
    (h82 : Theorem8_2_printed) (hLW : LiuWang) :
    ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x := by
  intro x hx h1
  rcases Nat.lt_or_ge X0 x with h | h
  · by_cases he : (x : ℝ) ≤ Real.exp 3100
    · obtain ⟨y, p, q, r, hy1, hy2, hp, hq, hr, -, -, -, rfl⟩ := h82 x h.le he
      have hX0 : N0 < X0 := by simp only [N0, X0]; norm_num
      exact five_of_three_plus_small h16 hx hp hq hr (m := x - (p + q + r))
        (by omega) (by omega) (by omega)
    · obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hLW x hx (lt_of_not_ge he)
      have h3 := ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add
        (AtMostPrimes.prime hr)
      exact h3.mono (by norm_num)
  · exact small_range_of_81 h81 h16 x hx h1 h

/-- The abstract's Schnirelmann bound, six primes, from the same four inputs. -/
theorem every_at_most_six_of_section8 (h81 : Theorem8_1) (h16 : EvenGoldbachUpTo N0)
    (h82 : Theorem8_2_printed) (hLW : LiuWang) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 6 n :=
  every_at_most_six_of (theorem1_4_of_section8 h81 h16 h82 hLW)

end LeanLab.Tao2012
