/-
The window sieve of BitSieve.lean past 10^8, unit U-0350, run 20261017T1903Z-8357.
Same bignum check, sieving list P32, the primes below 31700, so every window ending at most
31700 * 31700 = 1004890000 is sound. Soundness proved once here; each window is one
equality of natural numbers checked by `decide +kernel`.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.P32

namespace LeanLab.Verifications.Top50.Bits

open LeanLab.Verifications.Top50

/-- The sieving primes for windows ending at `L`, from P32. -/
def D2 (L : ℕ) : List ℕ := P32.filter (fun p => p * p < L)

/-- The bound up to which `D2` is complete. -/
def B2 : ℕ := 31700 * 31700

theorem mem_D2 {L p : ℕ} (hL : L ≤ B2) (hp : p.Prime) (hpL : p * p < L) : p ∈ D2 L := by
  unfold D2
  rw [List.mem_filter]
  refine ⟨P32_complete p ?_ hp, by simpa using hpL⟩
  by_contra h
  have h := not_lt.mp h
  have : 31700 * 31700 ≤ p * p := Nat.mul_le_mul h h
  unfold B2 at hL
  omega

/-- Window prime bitmap with the sieving list `D2`. -/
def wpm2 (lo W : ℕ) : ℕ := (wsieve lo W (D2 (lo + W)) % 2 ^ W) ^^^ (2 ^ W - 1)

theorem prime_of_wpm2 {lo W i : ℕ} (h2 : 2 ≤ lo) (hW : lo + W ≤ B2)
    (h : (wpm2 lo W).testBit i = true) : (lo + i).Prime := by
  simp only [wpm2, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one] at h
  by_cases hiW : i < W
  · simp only [hiW, decide_true, Bool.true_and] at h
    by_contra hp
    set m := lo + i with hm
    have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
    have hsq : m.minFac * m.minFac ≤ m := by
      have := Nat.minFac_sq_le_self (show 0 < m by omega) hp
      simpa [sq] using this
    have hb := wsieve_of_dvd lo W m m.minFac hmf.one_lt.le hsq (by omega) (by omega)
      (Nat.minFac_dvd m) (D2 (lo + W)) (mem_D2 hW hmf (by omega))
    rw [show m - lo = i by omega] at hb
    rw [hb] at h
    simp at h
  · simp [hiW] at h

/-- Soundness of one window check. -/
theorem goldbach_of_wcheck2 {lo W A B : ℕ} {Q : List ℕ} (h2 : 2 ≤ lo) (hW : lo + W ≤ B2)
    (hlo : lo ≤ A) (hQ : ∀ q ∈ Q, q.Prime)
    (h : wem lo A B &&& gm (wpm2 lo W) Q = wem lo A B) :
    ∀ n, A ≤ n → n ≤ B → 2 ∣ n - A → IsGoldbachSum n := by
  intro n hA hB he
  have h1 := testBit_wem hlo hA hB he
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨q, hq, hqn, hp⟩ := of_gm _ Q _ h1.2
  have := prime_of_wpm2 h2 hW hp
  exact ⟨q, lo + (n - lo - q), hQ q hq, this, by omega⟩

/-- Extend `EvenGoldbachUpTo a` by one window `[A, B]` with `A = a + 2`, the start as a numeral. -/
theorem upTo_extend2 {lo W a A B : ℕ} {Q : List ℕ} (ha : EvenGoldbachUpTo a) (hae : 2 ∣ a)
    (hA : a + 2 = A) (h2 : 2 ≤ lo) (hW : lo + W ≤ B2) (hlo : lo ≤ A) (hQ : ∀ q ∈ Q, q.Prime)
    (h : wem lo A B &&& gm (wpm2 lo W) Q = wem lo A B) : EvenGoldbachUpTo B := by
  subst hA
  intro n hn h4 hnB
  by_cases hna : n ≤ a
  · exact ha n hn h4 hna
  · have hn2 : a + 2 ≤ n := by
      obtain ⟨k, hk⟩ := hn
      obtain ⟨i, hi⟩ := hae
      omega
    apply goldbach_of_wcheck2 h2 hW hlo hQ h n hn2 hnB
    exact Nat.dvd_sub (even_iff_two_dvd.mp hn) (Nat.dvd_add hae (dvd_refl 2))

theorem upTo_mono {a b : ℕ} (h : EvenGoldbachUpTo b) (hab : a ≤ b) : EvenGoldbachUpTo a :=
  fun n hn h4 hna => h n hn h4 (le_trans hna hab)

end LeanLab.Verifications.Top50.Bits
