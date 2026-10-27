/-
P0069, page 27, equation 4.14. Elementary least prime factor bookkeeping.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
attribute [local instance] Classical.propDecidable

/-- Roughness is a lower bound on the least prime factor, away from n = 1. -/
theorem rough_iff_le_minFac {n : ℕ} (hn : n ≠ 1) (z : ℝ) :
    Rough n z ↔ z ≤ (n.minFac : ℝ) := by
  constructor
  · intro h
    by_contra hz
    exact h n.minFac (Nat.minFac_prime hn) (lt_of_not_ge hz) (Nat.minFac_dvd n)
  · intro hz p hp hpz hpn
    have hmin : n.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpn
    have : (n.minFac : ℝ) ≤ p := by exact_mod_cast hmin
    linarith

/-- A prime factor leaves a p-rough quotient exactly when it is the least prime factor. -/
theorem rough_quotient_iff_minFac {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) :
    Rough (n / p) (p : ℝ) ↔ p = n.minFac := by
  have hnp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hmin : n.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpn
  constructor
  · intro h
    by_contra hne
    have hlt : n.minFac < p := by omega
    have hnot : ¬ n.minFac ∣ p := by
      intro hdiv
      rcases (Nat.dvd_prime hp).mp hdiv with heq | heq
      · exact hnp.ne_one heq
      · omega
    have hprod : n.minFac ∣ p * (n / p) := by
      simpa only [Nat.mul_div_cancel' hpn] using Nat.minFac_dvd n
    have hdiv := (hnp.dvd_mul.mp hprod).resolve_left hnot
    exact h n.minFac hnp (by exact_mod_cast hlt) hdiv
  · intro heq q hq hqp hqdiv
    have hqn : q ∣ n := hqdiv.trans (Nat.div_dvd_of_dvd hpn)
    have hmq : n.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqn
    have : (p : ℝ) ≤ q := by exact_mod_cast (heq ▸ hmq)
    linarith

/-- Composite integers below z squared have a prime factor below z. -/
theorem prime_of_rough_of_lt_sq {n : ℕ} {z : ℝ} (hn : 2 ≤ n) (hz : 0 ≤ z)
    (hsize : (n : ℝ) < z ^ 2) (hr : Rough n z) : n.Prime := by
  by_contra hnp
  have hsq : (n.minFac : ℝ) ^ 2 ≤ n := by
    exact_mod_cast Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  have hmin : z ≤ (n.minFac : ℝ) := (rough_iff_le_minFac (by omega) z).mp hr
  nlinarith

/-- Buchstab's identity, equation 4.14 on page 27, as a finite prime divisor sum. -/
theorem buchstab_identity {n : ℕ} (hn : 0 < n) {w z : ℝ} (hwz : w ≤ z) :
    psi n z = psi n w -
      ∑ p ∈ n.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        psi (n / p) (p : ℝ) := by
  by_cases hn1 : n = 1
  · subst n
    have hr : ∀ t : ℝ, Rough 1 t := by
      intro t p hp hpt hdiv
      exact hp.not_dvd_one hdiv
    simp [psi, hr]
  have hn2 : 2 ≤ n := by omega
  have hmin := Nat.minFac_prime hn1
  have hmem : n.minFac ∈ n.primeFactors :=
    hmin.mem_primeFactors (Nat.minFac_dvd n) hn.ne'
  have hterm : ∀ p ∈ n.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      psi (n / p) (p : ℝ) = if p = n.minFac then 1 else 0 := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    simp only [psi, rough_quotient_iff_minFac hn2 (Nat.prime_of_mem_primeFactors hp')
      (Nat.dvd_of_mem_primeFactors hp')]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp only [Finset.mem_filter, hmem, true_and, psi, rough_iff_le_minFac hn1]
  by_cases hz : z ≤ (n.minFac : ℝ)
  · have hnot : ¬ (n.minFac : ℝ) < z := not_lt_of_ge hz
    have hw : w ≤ (n.minFac : ℝ) := hwz.trans hz
    simp [hw, hz, hnot]
  · have hlt : (n.minFac : ℝ) < z := lt_of_not_ge hz
    by_cases hw : w ≤ (n.minFac : ℝ) <;> simp [hw, hz, hlt]

/-- The first two Buchstab steps in equation 4.24, with a variable inner cutoff. -/
theorem buchstab_twice {n : ℕ} (hn : 0 < n) {w z : ℝ} (hwz : w ≤ z) (r : ℕ → ℝ)
    (hr : ∀ p ∈ n.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      r p ≤ (p : ℝ)) :
    psi n z = psi n w -
      (∑ p ∈ n.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        psi (n / p) (r p)) +
      ∑ p ∈ n.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        ∑ q ∈ (n / p).primeFactors.filter (fun q : ℕ => r p ≤ (q : ℝ) ∧ (q : ℝ) < p),
          psi ((n / p) / q) (q : ℝ) := by
  rw [buchstab_identity hn hwz]
  have hinner : ∀ p ∈ n.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      psi (n / p) (p : ℝ) = psi (n / p) (r p) -
        ∑ q ∈ (n / p).primeFactors.filter (fun q : ℕ => r p ≤ (q : ℝ) ∧ (q : ℝ) < p),
          psi ((n / p) / q) (q : ℝ) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    have hpn := Nat.dvd_of_mem_primeFactors hp'
    have hprime := Nat.prime_of_mem_primeFactors hp'
    have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hprime.pos
    exact buchstab_identity hquot (hr p hp)
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib]
  ring

#print axioms rough_iff_le_minFac
#print axioms rough_quotient_iff_minFac
#print axioms prime_of_rough_of_lt_sq
#print axioms buchstab_identity
#print axioms buchstab_twice
end LeanLab.BakerHarmanPintz1997
