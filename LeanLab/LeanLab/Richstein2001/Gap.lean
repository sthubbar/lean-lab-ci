/-
P0017 Richstein 2001, Section 4, page 1747: "a prime gap of 64 first occurs at 31397". Read in
Claude in Chrome 2026-10-18, run 20261018T1103Z-12430, unit U-0937.
PROVED, zero sorry: 31397 and 31469 are consecutive primes, a gap of 72; and every prime p below
31397 has a prime q with p < q < p + 64. So 31397 starts the first gap of at least 64, which is
what the sieve needs. A gap of exactly 64 first occurs later, at 89689 by the lab's Python, so
the sentence is right in the sense of at least 64; recorded as a wording QUESTION, no finding.
The check runs in core Lean, GapCheck.lean; soundness and completeness of trial division here.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Verifications.OeSHPTables
import LeanLab.Richstein2001.GapCheck

namespace LeanLab.Richstein2001

open LeanLab

theorem noDivFrom_eq (n : ℕ) : ∀ fuel d, Core.noDivFrom n fuel d = LeanLab.noDivFrom n fuel d := by
  intro fuel
  induction fuel with
  | zero => intro d; rfl
  | succ k ih => intro d; simp only [Core.noDivFrom, LeanLab.noDivFrom, ih]

theorem primeC_eq (n : ℕ) : Core.primeC n = primeB n := by
  simp only [Core.primeC, primeB, noDivFrom_eq]

/-- Trial division accepts every prime. -/
theorem primeB_complete_aux (n : ℕ) (hp : n.Prime) : LeanLab.noDivFrom n n 2 = true := by
  have key : ∀ k d, 2 ≤ d → n + 2 ≤ d + k → d ≤ n + 1 → LeanLab.noDivFrom n k d = true := by
    intro k
    induction k with
    | zero => intro d _ h1 h2; omega
    | succ k ih =>
      intro d hd h1 h2
      simp only [LeanLab.noDivFrom]
      split_ifs with hlt hmod
      · rfl
      · exfalso
        have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
        rcases (Nat.dvd_prime hp).mp hdvd with h | h
        · omega
        · subst h
          push_neg at hlt
          nlinarith
      · push_neg at hlt
        apply ih (d + 1) (by omega) (by omega)
        nlinarith
  exact key n 2 le_rfl (by omega) (by have := hp.two_le; omega)

theorem chk_sound {a b : ℕ} (h : Core.chk a b = true) {m : ℕ} (h1 : a ≤ m) (h2 : m < b)
    (hm : Core.primeC m = true) : Core.nextWithin m = true := by
  have h := List.all_eq_true.mp h (m - a) (List.mem_range.mpr (by omega))
  rw [show a + (m - a) = m by omega, hm] at h
  simpa using h

/-- No gap of 64 or more starts at a prime below 31397. -/
theorem no_gap64_below : ∀ p, p.Prime → p < 31397 → ∃ q, q.Prime ∧ p < q ∧ q < p + 64 := by
  intro p hp hlt
  have h2 := hp.two_le
  have hpc : Core.primeC p = true := by
    rw [primeC_eq]
    unfold primeB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h2, primeB_complete_aux p hp⟩
  have h : Core.nextWithin p = true := by
    by_cases c1 : p < 8000
    · exact chk_sound Core.chk_1 h2 c1 hpc
    by_cases c2 : p < 16000
    · exact chk_sound Core.chk_2 (by omega) c2 hpc
    by_cases c3 : p < 24000
    · exact chk_sound Core.chk_3 (by omega) c3 hpc
    · exact chk_sound Core.chk_4 (by omega) hlt hpc
  obtain ⟨i, hi, hq⟩ := List.any_eq_true.mp h
  rw [primeC_eq] at hq
  exact ⟨p + 1 + i, primeB_sound hq, by omega, by have := List.mem_range.mp hi; omega⟩

theorem p31397 : Nat.Prime 31397 := primeB_sound (by decide +kernel)

theorem p31469 : Nat.Prime 31469 := primeB_sound (by decide +kernel)

/-- Nothing strictly between 31397 and 31469 is prime: each has a divisor. -/
def noneBetween : Bool :=
  (List.range 71).all (fun i => LeanLab.Verifications.OeSHP.hasDiv (31398 + i) (31398 + i) 2)

theorem noneBetween_true : noneBetween = true := by decide +kernel

theorem composite_between : ∀ m, 31397 < m → m < 31469 → ¬ m.Prime := by
  intro m h1 h2
  have h := List.all_eq_true.mp noneBetween_true (m - 31398) (List.mem_range.mpr (by omega))
  rw [show 31398 + (m - 31398) = m by omega] at h
  exact LeanLab.Verifications.OeSHP.hasDiv_sound m m 2 le_rfl h

/-- The first gap of at least 64: 31397 to 31469, length 72. -/
theorem first_gap_ge64 : Nat.Prime 31397 ∧ Nat.Prime 31469 ∧
    (∀ m, 31397 < m → m < 31469 → ¬ m.Prime) ∧ 31469 - 31397 = 72 ∧
    (∀ p, p.Prime → p < 31397 → ∃ q, q.Prime ∧ p < q ∧ q < p + 64) :=
  ⟨p31397, p31469, composite_between, rfl, no_gap64_below⟩

end LeanLab.Richstein2001
