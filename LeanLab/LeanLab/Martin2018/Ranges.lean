/-
Kernel-checked finite ranges for Martin's conjectures, P0084.
Martin checked them numerically to 1e7 and 1e8; these ranges are far smaller and serve as
independent kernel checks of the statements as encoded.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Every conjecture here remains OPEN in general.
-/
import Mathlib
import LeanLab.Martin2018.Statements

namespace LeanLab.Martin2018

/-- Check every `n ≤ N` with `cond n` for a representation `p ≡ a`, `q ≡ b` mod `m`. -/
def allAP (m a b : ℕ) (cond : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => (if cond (n + 1) then apFrom m a b (n + 1) (n + 1) 2 else true) && allAP m a b cond n

theorem allAP_sound (m a b : ℕ) (cond : ℕ → Bool) (h0 : cond 0 = false) :
    ∀ N, allAP m a b cond N = true → ∀ n, n ≤ N → cond n = true → GoldbachAP m a b n := by
  intro N
  induction N with
  | zero => intro _ n hn hc; have : n = 0 := by omega
            subst this; rw [h0] at hc; exact absurd hc (by simp)
  | succ k ih =>
    intro h n hn hc
    rw [allAP, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · exact ih h.2 n (by omega) hc
    · have hn' : n = k + 1 := by omega
      subst hn'
      have := h.1
      rw [if_pos hc] at this
      exact apFrom_sound _ _ _ _ _ _ this

/-- Conj 1.2 ii for `n ≤ 2000`. -/
theorem conj1_2_ii_upTo : ∀ n, n ≤ 2000 → 0 < n → n % 4 = 0 → n ≠ 4 → GoldbachAP 4 1 3 n := by
  intro n hn h0 h4 hne
  exact allAP_sound 4 1 3 (fun n => 0 < n && n % 4 == 0 && n != 4) (by decide) 2000
    (by decide +kernel) n hn (by simp [h0, h4, hne])

/-- Conj 1.2 iii for `n ≤ 2000`. -/
theorem conj1_2_iii_upTo : ∀ n, n ≤ 2000 → n % 4 = 2 → n ≠ 2 → GoldbachAP 4 3 3 n := by
  intro n hn h2 hne
  exact allAP_sound 4 3 3 (fun n => n % 4 == 2 && n != 2) (by decide) 2000
    (by decide +kernel) n hn (by simp [h2, hne])

/-- Conj 1.2 i for `n ≤ 2000`, from ii and iii in range. -/
theorem conj1_2_i_upTo : ∀ n, n ≤ 2000 → Even n → 4 < n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 = 3 ∧ p + q = n := by
  intro n hn hev h4
  have := Nat.even_iff.mp hev
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 2) with h | h
  · obtain ⟨p, q, hp, hq, _, hq3, hpq⟩ := conj1_2_ii_upTo n hn (by omega) h (by omega)
    exact ⟨q, p, hq, hp, by omega, by omega⟩
  · obtain ⟨p, q, hp, hq, hp3, _, hpq⟩ := conj1_2_iii_upTo n hn h (by omega)
    exact ⟨p, q, hp, hq, by omega, hpq⟩

/-- Conj 1.3 ii, both parts, for `n ≤ 2000`. -/
theorem conj1_3_ii_upTo :
    (∀ n, n ≤ 2000 → 0 < n → Even n → n % 5 = 0 → GoldbachAP 5 2 3 n) ∧
    (∀ n, n ≤ 2000 → 0 < n → Even n → n % 5 = 0 → n ≠ 10 → n ≠ 20 → GoldbachAP 5 1 4 n) := by
  constructor
  · intro n hn h0 hev h5
    have := Nat.even_iff.mp hev
    exact allAP_sound 5 2 3 (fun n => 0 < n && n % 10 == 0) (by decide) 2000
      (by decide +kernel) n hn (by simp [h0]; omega)
  · intro n hn h0 hev h5 h10 h20
    have := Nat.even_iff.mp hev
    exact allAP_sound 5 1 4 (fun n => 0 < n && n % 10 == 0 && n != 10 && n != 20) (by decide)
      2000 (by decide +kernel) n hn (by simp [h0, h10, h20]; omega)

/-- Conj 1.3 iii to vi, moduli 7, 11, 8, 16, for `n ≤ 2000`. -/
theorem conj1_3_mod_upTo (m : ℕ) (hm : m ∈ ({7, 11, 8, 16} : Finset ℕ)) :
    ∀ n, n ≤ 2000 → 0 < n → Even n → n % m = 0 → GoldbachAP m 3 (m - 3) n := by
  intro n hn h0 hev hmn
  have := Nat.even_iff.mp hev
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact allAP_sound 7 3 4 (fun n => 0 < n && n % 14 == 0) (by decide) 2000
      (by decide +kernel) n hn (by simp [h0]; omega)
  · exact allAP_sound 11 3 8 (fun n => 0 < n && n % 22 == 0) (by decide) 2000
      (by decide +kernel) n hn (by simp [h0]; omega)
  · exact allAP_sound 8 3 5 (fun n => 0 < n && n % 8 == 0) (by decide) 2000
      (by decide +kernel) n hn (by simp [h0]; omega)
  · exact allAP_sound 16 3 13 (fun n => 0 < n && n % 16 == 0) (by decide) 2000
      (by decide +kernel) n hn (by simp [h0]; omega)

end LeanLab.Martin2018
