import LeanLab.ChenDoubleSieve.Decomp315a

/-!
The exact three step Buchstab expansion used before Wu 2004 equation 9.6.
Source: https://arxiv.org/pdf/0705.1652, page 36 first display.
The sums descend through distinct primes, so no repeated prime error enters.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task315
open Wu41 (S PS)

/-- Lower the sifting level of a forced prime through smaller distinct primes.
Source: page 36 first Buchstab expansion, derived exact component. -/
theorem buchstab_forced_prime (A : Finset ℕ) (N p : ℕ) (hp : p.Prime)
    {w : ℝ} (hwp : w ≤ p) :
    S A p N w = S A p N p + ∑ q ∈ PS N w p, S A (p * q) N q := by
  apply buchstab_divisor A p N hwp
  intro q hq
  obtain ⟨hqp, _, hqp_lt, _⟩ := Wu41.mem_PS.mp hq
  apply (hqp.coprime_iff_not_dvd).mpr
  intro hd
  have heq := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hd
  rw [heq] at hqp_lt
  exact lt_irrefl _ hqp_lt

/-- Lower the sifting level of two forced primes through smaller distinct primes.
Source: page 36 first Buchstab expansion, derived exact component. -/
theorem buchstab_forced_pair (A : Finset ℕ) (N p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    {w : ℝ} (hwq : w ≤ q) :
    S A (p * q) N w = S A (p * q) N q +
      ∑ r ∈ PS N w q, S A (p * q * r) N r := by
  apply buchstab_divisor A (p * q) N hwq
  intro r hr
  obtain ⟨hrp, _, hrq, _⟩ := Wu41.mem_PS.mp hr
  have hrqN : r < q := by exact_mod_cast hrq
  apply (hrp.coprime_iff_not_dvd).mpr
  intro hd
  rcases hrp.dvd_mul.mp hd with hd | hd
  · have heq := (Nat.prime_dvd_prime_iff_eq hrp hp).mp hd
    omega
  · have heq := (Nat.prime_dvd_prime_iff_eq hrp hq).mp hd
    omega

/-- The three exact Buchstab steps in descending prime coordinates.
Source: page 36 first display before equation 9.6. Reindexing gives Upsilon 4
and the first triple term. This theorem holds for every finite sequence. -/
theorem three_step_buchstab (A : Finset ℕ) (N : ℕ) {w z : ℝ} (hwz : w ≤ z) :
    2 * (S A 1 N z : ℝ) = 2 * (S A 1 N w : ℝ) -
      (∑ p ∈ PS N w z, S A p N p : ℕ) -
      (∑ p ∈ PS N w z, S A p N w : ℕ) +
      (∑ p ∈ PS N w z, ∑ q ∈ PS N w p, S A (p * q) N w : ℕ) -
      (∑ p ∈ PS N w z, ∑ q ∈ PS N w p,
        ∑ r ∈ PS N w q, S A (p * q * r) N r : ℕ) := by
  have hb := buchstab_base A N hwz
  have hprime : ∀ p ∈ PS N w z,
      S A p N w = S A p N p + ∑ q ∈ PS N w p, S A (p * q) N q := by
    intro p hp
    exact buchstab_forced_prime A N p (Wu41.mem_PS.mp hp).1 (Wu41.mem_PS.mp hp).2.1
  have hpairs : ∀ p ∈ PS N w z, ∀ q ∈ PS N w p,
      S A (p * q) N w = S A (p * q) N q +
        ∑ r ∈ PS N w q, S A (p * q * r) N r := by
    intro p hp q hq
    obtain ⟨hpp, _, _, _⟩ := Wu41.mem_PS.mp hp
    obtain ⟨hqp, hwq, hqp_lt, _⟩ := Wu41.mem_PS.mp hq
    exact buchstab_forced_pair A N p q hpp hqp (by exact_mod_cast hqp_lt) hwq
  have hpSum := sum_congr rfl hprime
  rw [sum_add_distrib] at hpSum
  have hpairSum := sum_congr rfl (fun p hp => sum_congr rfl (hpairs p hp))
  simp only [sum_add_distrib] at hpairSum
  have hbR := congrArg (fun n : ℕ => (n : ℝ)) hb
  have hpR := congrArg (fun n : ℕ => (n : ℝ)) hpSum
  have hpairR := congrArg (fun n : ℕ => (n : ℝ)) hpairSum
  push_cast at hbR hpR hpairR ⊢
  linarith only [hbR, hpR, hpairR]

end LeanLab.ChenDoubleSieve.Task347
