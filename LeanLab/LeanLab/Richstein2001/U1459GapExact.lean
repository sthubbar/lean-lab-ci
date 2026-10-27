/-
P0017 Richstein 2001, Section 4, page 1747, as transcribed by unit U-0937: "a prime gap of 64
first occurs at 31397". Gap.lean PROVED this in the sense of at least 64, the gap 31397 to 31469
of length 72, and left a wording QUESTION: a gap of exactly 64 first occurs later.
This file, unit U-1459, run 20261022T0003Z-15508, PROVES that QUESTION's claim, zero sorry:
89689 and 89753 are consecutive primes, so a gap of exactly 64 occurs at 89689, and no pair of
consecutive primes p, p + 64 has p below 89689. So the printed sentence holds only as "a gap of
64 or more"; read literally as "exactly 64" it would be false. Prime gap facts only, no Goldbach
range check. The kernel check is U1459GapCheck.lean and files B to I, one range per file.
AI-written Lean code, Claude, 2026-10-22. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Richstein2001.Gap
import LeanLab.Richstein2001.U1459GapCheckB
import LeanLab.Richstein2001.U1459GapCheckC
import LeanLab.Richstein2001.U1459GapCheckD
import LeanLab.Richstein2001.U1459GapCheckE
import LeanLab.Richstein2001.U1459GapCheckF
import LeanLab.Richstein2001.U1459GapCheckG
import LeanLab.Richstein2001.U1459GapCheckH
import LeanLab.Richstein2001.U1459GapCheckI

namespace LeanLab.Richstein2001

open LeanLab

theorem primeC_of_prime {p : ℕ} (hp : p.Prime) : Core.primeC p = true := by
  rw [primeC_eq]
  unfold primeB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp.two_le, primeB_complete_aux p hp⟩

theorem chkE_sound {a b : ℕ} (h : Core.chkE a b = true) {m : ℕ} (h1 : a ≤ m) (h2 : m < b)
    (hm : Core.primeC m = true) (hm64 : Core.primeC (m + 64) = true) :
    Core.nextWithin m = true := by
  have h := List.all_eq_true.mp h (m - a) (List.mem_range.mpr (by omega))
  rw [show a + (m - a) = m by omega] at h
  simpa [Core.okExact, hm, hm64] using h

/-- No pair of consecutive primes p, p + 64 with p below 89689: whenever p and p + 64 are both
prime, some prime lies strictly between them. -/
theorem no_gap_eq64_below : ∀ p, p.Prime → p < 89689 → (p + 64).Prime →
    ∃ q, q.Prime ∧ p < q ∧ q < p + 64 := by
  intro p hp hlt hp64
  have h2 := hp.two_le
  have a := primeC_of_prime hp
  have b := primeC_of_prime hp64
  have h : Core.nextWithin p = true := by
    by_cases c1 : p < 15000
    · exact chkE_sound Core.chkE_1 h2 c1 a b
    by_cases c2 : p < 30000
    · exact chkE_sound Core.chkE_2 (by omega) c2 a b
    by_cases c3 : p < 45000
    · exact chkE_sound Core.chkE_3 (by omega) c3 a b
    by_cases c4 : p < 52500
    · exact chkE_sound Core.chkE_4 (by omega) c4 a b
    by_cases c5 : p < 60000
    · exact chkE_sound Core.chkE_5 (by omega) c5 a b
    by_cases c6 : p < 67500
    · exact chkE_sound Core.chkE_6 (by omega) c6 a b
    by_cases c7 : p < 75000
    · exact chkE_sound Core.chkE_7 (by omega) c7 a b
    by_cases c8 : p < 82500
    · exact chkE_sound Core.chkE_8 (by omega) c8 a b
    · exact chkE_sound Core.chkE_9 (by omega) hlt a b
  obtain ⟨i, hi, hq⟩ := List.any_eq_true.mp h
  rw [primeC_eq] at hq
  exact ⟨p + 1 + i, primeB_sound hq, by omega, by have := List.mem_range.mp hi; omega⟩

theorem p89689 : Nat.Prime 89689 := primeB_sound (by decide +kernel)

theorem p89753 : Nat.Prime 89753 := primeB_sound (by decide +kernel)

def noneBetween89689 : Bool :=
  (List.range 63).all (fun i => LeanLab.Verifications.OeSHP.hasDiv (89690 + i) (89690 + i) 2)

theorem noneBetween89689_true : noneBetween89689 = true := by decide +kernel

theorem composite_between89689 : ∀ m, 89689 < m → m < 89753 → ¬ m.Prime := by
  intro m h1 h2
  have h := List.all_eq_true.mp noneBetween89689_true (m - 89690) (List.mem_range.mpr (by omega))
  rw [show 89690 + (m - 89690) = m by omega] at h
  exact LeanLab.Verifications.OeSHP.hasDiv_sound m m 2 le_rfl h

/-- The first gap of exactly 64 between consecutive primes is 89689 to 89753. -/
theorem first_gap_eq64 : Nat.Prime 89689 ∧ Nat.Prime 89753 ∧
    (∀ m, 89689 < m → m < 89753 → ¬ m.Prime) ∧ 89753 - 89689 = 64 ∧
    (∀ p, p.Prime → p < 89689 → (p + 64).Prime → ∃ q, q.Prime ∧ p < q ∧ q < p + 64) :=
  ⟨p89689, p89753, composite_between89689, rfl, no_gap_eq64_below⟩

/-- The two readings of the Section 4 sentence side by side: the first gap of at least 64 starts
at 31397, the first gap of exactly 64 at 89689, so they differ. -/
theorem gap64_readings_differ :
    (Nat.Prime 31397 ∧ Nat.Prime 31469 ∧ (∀ m, 31397 < m → m < 31469 → ¬ m.Prime) ∧
      31469 - 31397 ≠ 64) ∧
    (∀ p, p.Prime → p < 89689 → (p + 64).Prime → ∃ q, q.Prime ∧ p < q ∧ q < p + 64) ∧
    Nat.Prime 89689 ∧ (∀ m, 89689 < m → m < 89753 → ¬ m.Prime) ∧ Nat.Prime 89753 :=
  ⟨⟨p31397, p31469, composite_between, by norm_num⟩, no_gap_eq64_below, p89689,
    composite_between89689, p89753⟩

end LeanLab.Richstein2001
