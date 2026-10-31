/-
Helfgott and Platt 2013, P0006, unit U-0950, run 20261018T1404Z-22216.
Theorem 2.3 of the paper, Proth's theorem, the direction the computation uses: if
N = k 2^n + 1 with 0 < k < 2^n and a^((N-1)/2) = -1 mod N, then N is prime.
The Jacobi symbol condition in the paper's display only guides the choice of a; it is not
needed for primality, so it is left out here, which makes the statement stronger.
Then a kernel-checked Proth certificate for the top rung below the paper's bound T.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Pratt

namespace LeanLab.HelfgottPlatt.Proth

open LeanLab.Verifications.Pratt

/-- Proth's theorem, sufficiency, paper Theorem 2.3. -/
theorem proth {k m a N : ℕ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1)) (hN : N = k * 2 ^ (m + 1) + 1)
    (ha : (a : ZMod N) ^ (k * 2 ^ m) = -1) : N.Prime := by
  have hN3 : 3 ≤ N := by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [hN, pow_succ]; nlinarith
  by_contra hNp
  set p := N.minFac with hp_def
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ N := Nat.minFac_dvd N
  have hsq : p ^ 2 ≤ N := by
    have := Nat.minFac_sq_le_self (by omega : 0 < N) hNp
    simpa [sq] using this
  have : Fact p.Prime := ⟨hpp⟩
  -- N is odd, so p is odd
  have hp2 : p ≠ 2 := by
    intro h2
    have h2N : 2 ∣ k * 2 ^ (m + 1) + 1 := hN ▸ (h2 ▸ hpd)
    have h2X : 2 ∣ k * 2 ^ (m + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (Nat.succ_ne_zero m)) k
    have h21 := (Nat.dvd_add_right h2X).mp h2N
    norm_num at h21
  -- move the congruence to ZMod p
  set c : ZMod p := (a : ZMod p) ^ k with hc
  have hcm : c ^ (2 ^ m) = -1 := by
    have h := congrArg (ZMod.castHom hpd (ZMod p)) ha
    simp only [map_pow, map_natCast, map_neg, map_one] at h
    rw [hc, ← pow_mul]; exact h
  have hne : (-1 : ZMod p) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by
      have : (1 : ZMod p) + 1 = 0 := by
        calc (1 : ZMod p) + 1 = -1 + 1 := by rw [h]
          _ = 0 := by ring
      simpa [one_add_one_eq_two] using this
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have hnot : ¬ c ^ (2 ^ m) = 1 := by rw [hcm]; exact hne
  have hfin : c ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, hcm]; norm_num
  have hord : orderOf c = 2 ^ (m + 1) := orderOf_eq_prime_pow hnot hfin
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hcm
    exact hne (by
      have : (0 : ZMod p) = -1 := hcm
      have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
      exfalso; apply h1; linear_combination this)
  have hdvd : 2 ^ (m + 1) ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hc0
  have hp1 : 2 ^ (m + 1) + 1 ≤ p := by
    have := Nat.le_of_dvd (by have := hpp.two_le; omega) hdvd
    omega
  have : (2 ^ (m + 1) + 1) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hp1 2) hsq
  rw [hN] at this
  nlinarith

/-- The Boolean Proth test with the lab's fast modular power. -/
def prothB (k m a : ℕ) : Bool :=
  let N := k * 2 ^ (m + 1) + 1
  decide (0 < k) && decide (k < 2 ^ (m + 1)) &&
    (pm (N.log2 + 1) a (k * 2 ^ m) N == N - 1)

theorem prime_of_prothB {k m a : ℕ} (h : prothB k m a = true) : (k * 2 ^ (m + 1) + 1).Prime := by
  simp only [prothB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hk0, hk⟩, hpm⟩ := h
  set N := k * 2 ^ (m + 1) + 1 with hN
  apply proth hk0 hk rfl
  have he : k * 2 ^ m < 2 ^ (N.log2 + 1) := by
    have h1 : k * 2 ^ m < N := by rw [hN, pow_succ]; nlinarith [Nat.one_le_two_pow (n := m)]
    exact lt_trans h1 Nat.lt_log2_self
  rw [← pm_cast _ a _ N he, hpm]
  have hN1 : 1 ≤ N := by omega
  rw [Nat.cast_sub hN1]
  simp

/-- The paper's bound, Theorem 4.1. -/
def T : ℕ := 8875694145621773516800000000000

/-- A Proth prime with n = 52 just below T, found by the lab's Python, Proth witness a = 5. -/
def topK : ℕ := 1970799999999951

theorem top_prime : (topK * 2 ^ 52 + 1).Prime :=
  prime_of_prothB (k := topK) (m := 51) (a := 5) (by decide +kernel)

theorem top_value : topK * 2 ^ 52 + 1 = 8875694145621552840418258845697 := by
  norm_num [topK]

/-- The top rung sits within 2 · 10^18 of T, as the paper says its ladder ends. -/
theorem top_near_T : topK * 2 ^ 52 + 1 ≤ T ∧ T - (topK * 2 ^ 52 + 1) < 2 * 10 ^ 18 := by
  norm_num [topK, T]

end LeanLab.HelfgottPlatt.Proth
