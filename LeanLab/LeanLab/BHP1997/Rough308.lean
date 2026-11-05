/-
BHP1997, pages 25 to 27. An independent finite rough-number API.
The proofs reuse the CODEX task217 API in DecompC165b without its numerical imports.
Mathlib search uses Nat.le_minFac and Nat.minFac_le_of_dvd.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Task308
open Classical

/-- Pages 25 to 27, psi at natural cutoff. This is the indicator of having no prime divisor below the cutoff. -/
noncomputable def roughIndicator (n z : ℕ) : ℝ :=
 if n = 1 ∨ z ≤ n.minFac then 1 else 0

/-- Pages 25 to 27, exact support of psi. Reuses Nat.le_minFac. -/
theorem rough_indicator_support (n z : ℕ) :
    roughIndicator n z = 1 ↔ ∀ p : ℕ, p.Prime → p < z → ¬p ∣ n := by
  by_cases h : n = 1 ∨ z ≤ n.minFac
  · simp only [roughIndicator, ite_eq_left h, true_iff]
    intro p hp hpz hpn
    rcases h with hn | hz
    · subst n
      exact hp.not_dvd_one hpn
    · have hm := Nat.minFac_le_of_dvd hp.two_le hpn
      omega
  · simp only [roughIndicator, ite_eq_right h, zero_ne_one, false_iff]
    intro hh
    apply h
    exact Nat.le_minFac.mpr (fun p hp hpn => le_of_not_gt (fun hlt => hh p hp hlt hpn))

/-- Page 27, the smallest-prime partition in 4.14. -/
theorem rough_quotient_at_prime {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    roughIndicator (n / p) p = if p = n.minFac then 1 else 0 := by
  by_cases heq : p = n.minFac
  · rw [ite_eq_left heq]
    apply (rough_indicator_support _ _).mpr
    intro q hq hqp hqn
    have hqn' : q ∣ n := hqn.trans (Nat.div_dvd_of_dvd hpn)
    have hm := Nat.minFac_le_of_dvd hq.two_le hqn'
    omega
  · rw [ite_eq_right heq]
    have hn1 : n ≠ 1 := by rintro rfl; exact hp.not_dvd_one hpn
    have hq : n.minFac.Prime := Nat.minFac_prime hn1
    have hq_lt : n.minFac < p := lt_of_le_of_ne (Nat.minFac_le_of_dvd hp.two_le hpn) (Ne.symm heq)
    have hnot : ¬n.minFac ∣ p := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with h | h
      · exact hq.ne_one h
      · exact heq h.symm
    have hqn : n.minFac ∣ n / p := by
      have hm : n.minFac ∣ p * (n / p) := by
        rw [Nat.mul_div_cancel' hpn]
        exact Nat.minFac_dvd n
      exact (hq.dvd_mul.mp hm).resolve_left hnot
    have hfail : ¬ (n / p = 1 ∨ p ≤ (n / p).minFac) := by
      intro hh
      rcases hh with hh | hh
      · rw [hh] at hqn
        exact hq.not_dvd_one hqn
      · have hm := Nat.minFac_le_of_dvd hq.two_le hqn
        omega
    simp [roughIndicator, hfail]

/-- Page 27, identity 4.14 at natural cutoffs. -/
theorem rough_buchstab_finite (n w z : ℕ) (hwz : w ≤ z) :
    roughIndicator n z = roughIndicator n w -
      ∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p ∧ p ∣ n), roughIndicator (n / p) p := by
  have hsum : (∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p ∧ p ∣ n), roughIndicator (n / p) p) =
      ∑ p ∈ (z.primesBelow).filter (fun p => w ≤ p ∧ p ∣ n),
        if p = n.minFac then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpf := Finset.mem_filter.mp hp
    exact rough_quotient_at_prime (Nat.mem_primesBelow.mp hpf.1).2 hpf.2.2
  rw [hsum, Finset.sum_ite_eq']
  by_cases hn : n = 1
  · subst n
    norm_num [roughIndicator, Nat.mem_primesBelow]
  · have hp := Nat.minFac_prime hn
    simp only [Finset.mem_filter, Nat.mem_primesBelow]
    simp only [hp, Nat.minFac_dvd, and_true]
    simp only [roughIndicator, hn, false_or]
    split_ifs <;> norm_num at * <;> omega

end LeanLab.BHP1997.Task308
