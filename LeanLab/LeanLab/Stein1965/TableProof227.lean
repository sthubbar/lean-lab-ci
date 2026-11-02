/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
The divisor table gives exactly the original prime predicate.
-/
import LeanLab.Stein1965.TablePrime227
import LeanLab.Stein1965.CoreBridge227

namespace LeanLab.Stein1965.TableProof227
open Core227 TablePrime227
open LeanLab.SteinStein1965
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem divisors_lower (p : Nat) (hp : p ∈ divisors) : 2 ≤ p := by
  have h : divisors.all (fun q => decide (2 ≤ q)) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp h) p hp)

theorem core_prime_iff (n : Nat) : Core227.prime n = true ↔ 3 ≤ n ∧ n.Prime := by
  rw [CoreBridge227.prime_eq, primeA_iff]
  constructor
  · rintro ⟨h3, h | ⟨_, hp⟩⟩
    · omega
    · exact ⟨h3, hp⟩
  · rintro ⟨h3, hp⟩
    exact ⟨h3, Or.inr ⟨by omega, hp⟩⟩

theorem small_prime_mem (p : Nat) (hp : p.Prime) (h : p < 3204) : p ∈ divisors := by
  have ht : (List.range 3204).all
      (fun q => !(q == 2 || Core227.prime q) || divisors.contains q) = true := by
    decide +kernel
  have hq := (List.all_eq_true.mp ht) p (List.mem_range.mpr h)
  have hb : (p == 2 || Core227.prime p) = true := by
    by_cases he : p = 2
    · simp [he]
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      have hc := (core_prime_iff p).mpr ⟨h3, hp⟩
      simp [hc]
  have hc : divisors.contains p = true := by simpa [hb] using hq
  simpa only [List.contains_iff_mem] using hc

theorem tablePrime_iff (n : Nat) : tablePrime n = true ↔ Core227.prime n = true := by
  by_cases hN : n ≤ 10000000
  · rw [tablePrime, if_pos hN, Bool.and_eq_true, decide_eq_true_eq, core_prime_iff]
    constructor
    · rintro ⟨h3, hall⟩
      refine ⟨h3, ?_⟩
      by_contra hnot
      have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hs := Nat.minFac_sq_le_self (by omega : 0 < n) hnot
      have hb : n.minFac < 3204 := by nlinarith
      have hm := small_prime_mem n.minFac hp hb
      have ht := (List.all_eq_true.mp hall) n.minFac hm
      have hz : n % n.minFac = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
      have hn : ¬ n < n.minFac * n.minFac := by nlinarith
      simp [hz, hn] at ht
    · rintro ⟨h3, hp⟩
      refine ⟨h3, List.all_eq_true.mpr ?_⟩
      intro p hmem
      have h2 := divisors_lower p hmem
      by_cases hs : n < p * p
      · simp [hs]
      · have hz : n % p ≠ 0 := by
          intro hz
          rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hz) with he | he
          · omega
          · subst p
            nlinarith
        simp [hz]
  · simp only [tablePrime, if_neg hN, FastCore227.fastPrime_eq]

theorem tablePrime_eq (n : Nat) : tablePrime n = Core227.prime n := by
  have h := tablePrime_iff n
  cases ht : tablePrime n <;> cases hc : Core227.prime n <;> simp_all

end LeanLab.Stein1965.TableProof227
#print axioms LeanLab.Stein1965.TableProof227.divisors_lower
#print axioms LeanLab.Stein1965.TableProof227.small_prime_mem
#print axioms LeanLab.Stein1965.TableProof227.core_prime_iff
#print axioms LeanLab.Stein1965.TableProof227.tablePrime_iff
#print axioms LeanLab.Stein1965.TableProof227.tablePrime_eq
