/-
A faster kernel checker for even Goldbach, unit U-0324, run 20261017T1402Z-26900.
Primality of m < 10^8 by trial division over the proved list P10k of primes below 10000,
stopping at the first prime d with m < d². Each even n is checked by trying q = 2, 3, 5, ...
from P10k until n - q passes. The lab's older checker reached 1000.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Common.GoldbachSmall
import LeanLab.Verifications.Top50.Base

namespace LeanLab.Verifications.Top50.Fast

open LeanLab.Verifications.Top50

/-- Trial division of `m` by a list, stopping at the first `d` with `m < d * d`. -/
def td (m : ℕ) : List ℕ → Bool
  | [] => false
  | d :: t => if m < d * d then true else m % d != 0 && td m t

theorem P10k_chain : P10k.IsChain (· < ·) := by decide +kernel

theorem P10k_sorted : P10k.Pairwise (· < ·) := List.isChain_iff_pairwise.mp P10k_chain

theorem P10k_prime : ∀ q ∈ P10k, q.Prime := by
  have h : P10k.all (fun q => primeB q) = true := by decide +kernel
  intro q hq
  exact primeB_sound (List.all_eq_true.mp h q hq)

/-- If `td m L` holds for a sorted list, no `d ∈ L` with `d * d ≤ m` divides `m`. -/
theorem td_sound (m : ℕ) : ∀ L : List ℕ, L.Pairwise (· < ·) → td m L = true →
    ∀ d ∈ L, d * d ≤ m → ¬ d ∣ m := by
  intro L
  induction L with
  | nil => intro _ h; simp [td] at h
  | cons a t ih =>
    intro hs h d hd hdm hdiv
    rw [List.pairwise_cons] at hs
    simp only [td] at h
    by_cases ha : m < a * a
    · rcases List.mem_cons.mp hd with rfl | hd'
      · omega
      · have := hs.1 d hd'
        have : a * a < d * d := Nat.mul_lt_mul'' this this
        omega
    · rw [if_neg ha] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact h.1 (Nat.mod_eq_zero_of_dvd hdiv)
      · exact ih hs.2 h.2 d hd' hdm hdiv

/-- `td` over P10k decides primality below 10^8, the `true` direction. -/
theorem prime_of_td {m : ℕ} (h2 : 2 ≤ m) (hm : m < 10 ^ 8) (h : td m P10k = true) :
    m.Prime := by
  by_contra hp
  have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
  have hsq : m.minFac * m.minFac ≤ m := by
    have := Nat.minFac_sq_le_self (show 0 < m by omega) hp
    simpa [sq] using this
  have hlt : m.minFac < 10000 := by
    by_contra hge
    push_neg at hge
    have : 10000 * 10000 ≤ m.minFac * m.minFac := Nat.mul_le_mul hge hge
    omega
  exact td_sound m P10k P10k_sorted h m.minFac (P10k_complete _ hlt hmf) hsq (Nat.minFac_dvd m)

/-- Try `q ∈ L` in order until `n - q` passes `td`. -/
def findQ (n : ℕ) : List ℕ → Bool
  | [] => false
  | q :: t => (q + 2 ≤ n && td (n - q) P10k) || findQ n t

theorem findQ_sound (n : ℕ) (hn : n < 10 ^ 8) : ∀ L : List ℕ, (∀ q ∈ L, q.Prime) →
    findQ n L = true → IsGoldbachSum n := by
  intro L
  induction L with
  | nil => intro _ h; simp [findQ] at h
  | cons a t ih =>
    intro hL h
    simp only [findQ, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨a, n - a, hL a (by simp), prime_of_td (by omega) (by omega) h2, by omega⟩
    · exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) h

/-- Check the even numbers `n, n + 2, ...`, `fuel` of them. -/
def allGB : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, n => findQ n P10k && allGB fuel (n + 2)

theorem allGB_sound : ∀ fuel n, n + 2 * fuel ≤ 10 ^ 8 → allGB fuel n = true →
    ∀ k, k < fuel → IsGoldbachSum (n + 2 * k) := by
  intro fuel
  induction fuel with
  | zero => intro n _ _ k hk; omega
  | succ f ih =>
    intro n hb h k hk
    simp only [allGB, Bool.and_eq_true] at h
    rcases k with _ | k
    · simpa using findQ_sound n (by omega) P10k P10k_prime h.1
    · have := ih (n + 2) (by omega) h.2 k (by omega)
      rwa [show n + 2 + 2 * k = n + 2 * (k + 1) by ring] at this

/-- From a checked block of even numbers to the `EvenGoldbachUpTo` form. -/
theorem upTo_of_blocks {a N : ℕ} (ha : EvenGoldbachUpTo a) (hae : Even a) (fuel : ℕ)
    (hb : a + 2 + 2 * fuel ≤ 10 ^ 8) (hN : N = a + 2 * fuel)
    (h : allGB fuel (a + 2) = true) : EvenGoldbachUpTo N := by
  intro n hn h4 hnN
  by_cases hna : n ≤ a
  · exact ha n hn h4 hna
  · obtain ⟨j, rfl⟩ := hn
    obtain ⟨i, rfl⟩ := hae
    have hk : (j + j) = i + i + 2 + 2 * (j - i - 1) := by omega
    rw [hk]
    exact allGB_sound fuel (i + i + 2) hb h (j - i - 1) (by omega)

/-- Blocks of 5000 even numbers each. Test block first. -/
theorem block_1 : allGB 200 1002 = true := by decide +kernel

theorem upTo_1400 : EvenGoldbachUpTo 1400 :=
  upTo_of_blocks LeanLab.evenGoldbachUpTo_1000 ⟨500, rfl⟩ 200 (by norm_num) (by norm_num) block_1

end LeanLab.Verifications.Top50.Fast
