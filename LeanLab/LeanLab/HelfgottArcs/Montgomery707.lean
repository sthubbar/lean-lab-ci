/-
Coprime support energy input for P0013 page 45 equation 4.39.
The support condition is explicit. No sharp additive sieve is assumed here.
Source: Montgomery 1968 and the author book Lemma 19.12, coprime support case.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119
import LeanLab.PNTPort.Vinogradov.MajorArc

namespace LeanLab.HelfgottArcs.Montgomery707
open Finset ArithmeticFunction

/-- Sum over reduced rational shifts using the coprime Ramanujan identity.
Source: P0013 page 45 equation 4.39, derived coprime support input. -/
theorem coprime_phase_average707 (s : Finset ℕ) (c : ℕ → ℂ) (r : ℕ) (hr : 1 ≤ r)
    (hc : ∀ n ∈ s, n.Coprime r) (β : ℝ) :
    ∑ a ∈ (range r).filter (fun a => a.Coprime r),
      ∑ n ∈ s, c n * e ((β + (a : ℝ) / r) * n) =
      (moebius r : ℂ) * ∑ n ∈ s, c n * e (β * n) := by
  have he (t : ℝ) : LeanLab.PNTPort.LargeSieve.e t = e t := by
    unfold LeanLab.PNTPort.LargeSieve.e e
    congr 1
    push_cast
    ring
  have hadd (a n : ℕ) : e ((β + (a : ℝ) / r) * n) =
      e (β * n) * e ((n : ℝ) * a / r) := by
    unfold e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro n hn
  simp_rw [hadd, ← mul_assoc]
  rw [← mul_sum]
  have hram := LeanLab.PNTPort.Vinogradov.ramanujan_coprime hr
    (Int.isCoprime_iff_nat_coprime.mpr (by simpa using hc n hn) : IsCoprime (n : ℤ) (r : ℤ))
  simp only [he, Int.cast_natCast] at hram
  rw [hram]
  ring


example := coprime_phase_average707 {1, 5} (fun _ => (1 : ℂ)) 6 (by norm_num)
  (by intro n hn; simp only [mem_insert, mem_singleton] at hn; rcases hn with rfl | rfl <;> norm_num) 0


/-- Cauchy gives the Mobius squared over totient energy factor for coprime support.
Source: P0013 page 45 equation 4.39, derived coprime support input. -/
theorem coprime_phase_energy707 (s : Finset ℕ) (c : ℕ → ℂ) (r : ℕ) (hr : 1 ≤ r)
    (hc : ∀ n ∈ s, n.Coprime r) (β : ℝ) :
    (((moebius r : ℤ) : ℝ) ^ 2 / (r.totient : ℝ)) *
      ‖∑ n ∈ s, c n * e (β * n)‖ ^ 2 ≤
    ∑ a ∈ (range r).filter (fun a => a.Coprime r),
      ‖∑ n ∈ s, c n * e ((β + (a : ℝ) / r) * n)‖ ^ 2 := by
  let t := (range r).filter (fun a => a.Coprime r)
  let F : ℕ → ℂ := fun a => ∑ n ∈ s, c n * e ((β + (a : ℝ) / r) * n)
  have hcard : t.card = r.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp [t, Nat.coprime_comm]
  have ht := norm_sum_le t F
  have hcs := sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) (fun a => ‖F a‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, hcard] at hcs
  have hb := (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hcs
  have havg : ∑ a ∈ t, F a = (moebius r : ℂ) * ∑ n ∈ s, c n * e (β * n) :=
    coprime_phase_average707 s c r hr hc β
  rw [havg, norm_mul, mul_pow] at hb
  have hmu : ‖(moebius r : ℂ)‖ ^ 2 = ((moebius r : ℤ) : ℝ) ^ 2 := by
    change ‖(((moebius r : ℤ) : ℝ) : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hmu] at hb
  have hphi : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hphi).mpr
  nlinarith only [hb]

example := coprime_phase_energy707 {1, 5} (fun _ => (1 : ℂ)) 6 (by norm_num)
  (by intro n hn; simp only [mem_insert, mem_singleton] at hn; rcases hn with rfl | rfl <;> norm_num) 0


/-- The finite Montgomery energy input for prime support strictly above the modulus cutoff.
Source: P0013 page 45 equation 4.39, derived coprime support input. -/
theorem montgomery_prime_supported_energy707 (P I : Finset ℕ) (c : ℕ → ℂ)
    (β : ℕ → ℝ) (R q : ℕ) (hprime : ∀ n ∈ P, n.Prime ∧ R < n) :
    (∑ r ∈ (Icc 1 R).filter (fun r => r.Coprime q),
      ((moebius r : ℤ) : ℝ) ^ 2 / (r.totient : ℝ)) *
      (∑ i ∈ I, ‖∑ n ∈ P, c n * e (β i * n)‖ ^ 2) ≤
    ∑ r ∈ (Icc 1 R).filter (fun r => r.Coprime q),
      ∑ a ∈ (range r).filter (fun a => a.Coprime r),
        ∑ i ∈ I, ‖∑ n ∈ P, c n * e ((β i + (a : ℝ) / r) * n)‖ ^ 2 := by
  rw [sum_mul]
  apply sum_le_sum
  intro r hr
  have hr1 := (mem_Icc.mp (mem_filter.mp hr).1).1
  have hrR := (mem_Icc.mp (mem_filter.mp hr).1).2
  have hc : ∀ n ∈ P, n.Coprime r := by
    intro n hn
    have hp := hprime n hn
    apply hp.1.coprime_iff_not_dvd.mpr
    intro hd
    have := Nat.le_of_dvd (by omega : 0 < r) hd
    omega
  rw [mul_sum, sum_comm]
  exact sum_le_sum (fun i hi => coprime_phase_energy707 P c r hr1 hc (β i))

example := montgomery_prime_supported_energy707 {5} {0} (fun _ => (1 : ℂ))
  (fun _ => (0 : ℝ)) 2 1 (by
    intro n hn
    simp only [mem_singleton] at hn
    subst n
    norm_num)

end LeanLab.HelfgottArcs.Montgomery707
