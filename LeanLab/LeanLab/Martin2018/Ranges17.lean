/-
Kernel-checked range for Martin's Conjecture 1.7, P0084: every odd n > 5 is p + q + r with
primes p ≡ q ≡ 2 mod 3. Martin checked it numerically; here n ≤ 501.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
The conjecture is OPEN in general.
-/
import Mathlib
import LeanLab.Martin2018.Statements

namespace LeanLab.Martin2018

/-- Inner search over `q` for fixed `p`. -/
def qFrom (n p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, q => if n < p + q then false
      else if primeB q && q % 3 == 2 && primeB (n - p - q) then true
      else qFrom n p fuel (q + 1)

/-- Outer search over `p`. -/
def pFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, p => if n < p then false
      else if primeB p && p % 3 == 2 && qFrom n p n 2 then true
      else pFrom n fuel (p + 1)

theorem qFrom_sound (n p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) : ∀ fuel q,
    qFrom n p fuel q = true → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p % 3 = 2 ∧
      q % 3 = 2 ∧ p + q + r = n := by
  intro fuel
  induction fuel with
  | zero => intro q h; simp [qFrom] at h
  | succ k ih =>
    intro q h
    simp only [qFrom] at h
    by_cases h1 : n < p + q
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : (primeB q && q % 3 == 2 && primeB (n - p - q)) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at h2
        exact ⟨p, q, n - p - q, hp, primeB_sound h2.1.1, primeB_sound h2.2, hp3, h2.1.2,
          by omega⟩
      · rw [if_neg h2] at h; exact ih (q + 1) h

theorem pFrom_sound (n : ℕ) : ∀ fuel p, pFrom n fuel p = true →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p % 3 = 2 ∧ q % 3 = 2 ∧ p + q + r = n := by
  intro fuel
  induction fuel with
  | zero => intro p h; simp [pFrom] at h
  | succ k ih =>
    intro p h
    simp only [pFrom] at h
    by_cases h1 : n < p
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : (primeB p && p % 3 == 2 && qFrom n p n 2) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at h2
        exact qFrom_sound n p (primeB_sound h2.1.1) h2.1.2 n 2 h2.2
      · rw [if_neg h2] at h; exact ih (p + 1) h

/-- Check every odd `n` with `5 < n ≤ N`. -/
def all17 : ℕ → Bool
  | 0 => true
  | n + 1 => (if (n + 1) % 2 = 1 && 5 < n + 1 then pFrom (n + 1) (n + 1) 2 else true) && all17 n

theorem all17_sound : ∀ N, all17 N = true → ∀ n, n ≤ N → Odd n → 5 < n →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p % 3 = 2 ∧ q % 3 = 2 ∧ p + q + r = n := by
  intro N
  induction N with
  | zero => intro _ n hn _ h5; omega
  | succ k ih =>
    intro h n hn ho h5
    rw [all17, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · exact ih h.2 n (by omega) ho h5
    · have hn' : n = k + 1 := by omega
      subst hn'
      have hc : ((k + 1) % 2 = 1 && 5 < k + 1) = true := by
        have := Nat.odd_iff.mp ho; simp [this, h5]
      have := h.1
      rw [if_pos hc] at this
      exact pFrom_sound _ _ _ this

/-- Conj 1.7 for every odd `n` with `5 < n ≤ 501`. -/
theorem conj1_7_upTo : ∀ n, n ≤ 501 → Odd n → 5 < n →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p % 3 = 2 ∧ q % 3 = 2 ∧ p + q + r = n :=
  all17_sound 501 (by decide +kernel)

end LeanLab.Martin2018
