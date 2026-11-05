/-
Elementary arithmetic for the twisted Ramanujan bound in Pintz Part I page 11 display 4.3.
This supplies the totient ratio step for the fixed data coefficient bound.
The induced Gauss sum identities remain OPEN in Decomp247a.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BhowmikGrimmelt2026

/-- Multiplying a modulus by m increases its totient by at most a factor m.
Source: elementary helper for Pintz Part I page 11 display 4.3. -/
theorem totient_mul_le247 (m n : ℕ) : Nat.totient (m * n) ≤ m * Nat.totient n := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst m; simp
    by_cases hm1 : m = 1
    · subst m; simp
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hklt : m / p < m := Nat.div_lt_self hmpos hp.one_lt
    have hmk : p * (m / p) = m := Nat.mul_div_cancel' hpm
    have hrec := ih (m / p) hklt
    have hprime : Nat.totient (p * (m / p * n)) ≤ p * Nat.totient (m / p * n) := by
      by_cases hd : p ∣ m / p * n
      · rw [Nat.totient_mul_of_prime_of_dvd hp hd]
      · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]
        exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
    calc
      Nat.totient (m * n) = Nat.totient (p * (m / p * n)) := by rw [← mul_assoc, hmk]
      _ ≤ p * Nat.totient (m / p * n) := hprime
      _ ≤ p * (m / p * Nat.totient n) := Nat.mul_le_mul_left p hrec
      _ = m * Nat.totient n := by rw [← mul_assoc, hmk]

/-- Dividing a positive modulus by a positive divisor gives a totient ratio at most that divisor.
Source: elementary helper for Pintz Part I page 11 display 4.3. -/
theorem totient_divisor_ratio247 (q d : ℕ) (hq : 0 < q) (hd : d ∣ q) (hdpos : 0 < d) :
    (Nat.totient q : ℝ) / (Nat.totient (q / d) : ℝ) ≤ d := by
  have hquot : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hd) hdpos
  have hphi : (0 : ℝ) < Nat.totient (q / d) := by exact_mod_cast Nat.totient_pos.mpr hquot
  apply (div_le_iff₀ hphi).mpr
  have h := totient_mul_le247 d (q / d)
  rw [Nat.mul_div_cancel' hd] at h
  exact_mod_cast h

/-- The totient quotient in the twisted Ramanujan formula is at most positive N.
Source: Pintz Part I page 11 display 4.3 with q one equal q divided by gcd of q and N. -/
theorem totient_gcd_ratio247 (q N : ℕ) (hq : 0 < q) (hN : 0 < N) :
    (Nat.totient q : ℝ) / (Nat.totient (q / Nat.gcd q N) : ℝ) ≤ N := by
  have h := totient_divisor_ratio247 q (Nat.gcd q N) hq
    (Nat.gcd_dvd_left q N) (Nat.gcd_pos_of_pos_left N hq)
  exact h.trans (by exact_mod_cast Nat.gcd_le_right q hN)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.totient_mul_le247
#print axioms LeanLab.BhowmikGrimmelt2026.totient_divisor_ratio247
#print axioms LeanLab.BhowmikGrimmelt2026.totient_gcd_ratio247
