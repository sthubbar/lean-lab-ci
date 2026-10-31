import LeanLab.ExceptionalSet.ChenPrimes
import LeanLab.ExceptionalSet.ChenClass2

/-!
# T2 FRONTIER: two Chen primes in the classes 0 and 2 mod 6 is a prime pair problem

Unit U-1067, PC run 20261019T1403Z-32628. AI wrote this Lean code. KNOWN mathematics in method.

P0039 Grimmelt-Teräväinen 2025 prove that almost all `m ≡ 4 mod 6` are sums of two Chen primes.
The frontier question is the other even classes. For `m ≡ 2 mod 6` this file shows the
question is out of reach of current methods for a structural reason: if all but finitely many
`m ≡ 2 mod 6` were sums of two Chen primes, there would be infinitely many primes `r` with
`3 r - 2` also prime, a Dickson prime pair statement of twin prime type, which is open.

Proof shape. Take `m = 30 j + 8`, so `m ≡ 2 mod 6` and `m - 3 = 5 (6 j + 1)` is composite.
In `m = p + q` neither prime is `2`, nor `3`, since the partner would be `m - 3`; so both exceed
`3`, both are `1 mod 3` by `three_dvd_add_two`, hence `1 mod 6`, and by `chen_one_mod_six`
the larger one is `p = 3 r - 2` with `r` prime and `r ≥ m / 6`.

`dickson_of_class0` gives the same conclusion for `m ≡ 0 mod 6`: there one summand is always
`1 mod 6`, and if the Dickson pairs stopped at `B`, at `m = 6 (3B)! (M₀ + 2)` that summand would
divide `m` and so the other prime. So `m ≡ 4 mod 6` is the only even class where a theorem of
P0039's kind avoids an open prime pair conjecture.

Not progress on binary Goldbach, which is open.
-/

namespace LeanLab.ExceptionalSet.ChenClass2Barrier

open LeanLab.ExceptionalSet

/-- the Dickson pair `(r, 3 r - 2)`, both prime -/
def DicksonPair (r : ℕ) : Prop := r.Prime ∧ (3 * r - 2).Prime

/-- a Chen prime above `3` in a sum `≡ 2 mod 6` of two primes above `3` is `3 r - 2`, `r` prime -/
theorem chen_pair_of_class2 {p q : ℕ} (hp : IsChenPrime p) (hq : q.Prime) (hp3 : 3 < p)
    (hq3 : 3 < q) (h : (p + q) % 6 = 2) : ∃ r, DicksonPair r ∧ p + 2 = 3 * r := by
  have hd := (ChenClass2.three_dvd_add_two hp.1 hq hp3 hq3 h).1
  have hodd : p % 2 = 1 := by
    by_contra h0
    have := hp.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega))
    omega
  have h1 : p % 6 = 1 := by omega
  obtain ⟨r, hr, hpr⟩ := chen_one_mod_six hp h1
  refine ⟨r, ⟨hr, ?_⟩, hpr⟩
  have : 3 * r - 2 = p := by omega
  rw [this]; exact hp.1

/-- `m = 30 j + 8` has `m - 3 = 5 (6 j + 1)` composite for `j ≥ 1` -/
theorem not_prime_sub_three {j : ℕ} (hj : 1 ≤ j) : ¬ (30 * j + 8 - 3).Prime := by
  have : 30 * j + 8 - 3 = 5 * (6 * j + 1) := by omega
  rw [this]
  exact Nat.not_prime_mul (by norm_num) (by omega)

/-- **the barrier.** If every `m ≡ 2 mod 6` beyond some `M₀` is a sum of two Chen primes, there
are Dickson pairs `(r, 3 r - 2)` with `r` arbitrarily large. -/
theorem dickson_of_class2 (M₀ : ℕ)
    (hall : ∀ m, M₀ ≤ m → m % 6 = 2 → ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m) :
    ∀ B, ∃ r, B < r ∧ DicksonPair r := by
  intro B
  set j := M₀ + B + 1 with hj
  have hj1 : 1 ≤ j := by omega
  obtain ⟨p, q, hp, hq, hpq⟩ := hall (30 * j + 8) (by omega) (by omega)
  have hnp := not_prime_sub_three hj1
  -- neither summand is 2 or 3
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hq2 : q % 2 = 0 := by omega
    have := hq.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hq2); omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hp2' : p % 2 = 0 := by omega
    have := hp.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hp2'); omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    apply hnp; have : 30 * j + 8 - 3 = q := by omega
    rw [this]; exact hq.1
  have hq3 : q ≠ 3 := by
    rintro rfl
    apply hnp; have : 30 * j + 8 - 3 = p := by omega
    rw [this]; exact hp.1
  have hp3' : 3 < p := by have := hp.1.two_le; omega
  have hq3' : 3 < q := by have := hq.1.two_le; omega
  have hmod : (p + q) % 6 = 2 := by omega
  -- the larger summand gives the pair
  rcases le_total q p with hle | hle
  · obtain ⟨r, hr, hpr⟩ := chen_pair_of_class2 hp hq.1 hp3' hq3' hmod
    exact ⟨r, by omega, hr⟩
  · obtain ⟨r, hr, hqr⟩ := chen_pair_of_class2 hq hp.1 hq3' hp3' (by omega)
    exact ⟨r, by omega, hr⟩

/-- in a sum `p + q ≡ 0 mod 6` of two primes above `3`, one summand is `1 mod 6` -/
theorem one_mod_six_of_class0 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p)
    (hq3 : 3 < q) (h : (p + q) % 6 = 0) : p % 6 = 1 ∨ q % 6 = 1 := by
  have h2 : ∀ x : ℕ, x.Prime → 3 < x → x % 2 = 1 ∧ x % 3 ≠ 0 := by
    intro x hx hx3
    constructor
    · by_contra h0
      have := hx.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
    · intro h0
      have := hx.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0); omega
  obtain ⟨hp2, hp3'⟩ := h2 p hp hp3
  obtain ⟨hq2, hq3'⟩ := h2 q hq hq3
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 := by omega
  rcases hp6 with h6 | h6 <;> rcases hq6 with h7 | h7 <;> simp_all [Nat.add_mod]

/-- **the class 0 mod 6 barrier.** If every `m ≡ 0 mod 6` beyond some `M₀` is a sum of two Chen
primes, there are Dickson pairs `(r, 3 r - 2)` with `r` arbitrarily large. Proof: otherwise the
summand `≡ 1 mod 6` is at most `3 B`, and at `m = 6 (3B)! (M₀ + 2)` it divides `m`, hence
divides the other prime summand, impossible. -/
theorem dickson_of_class0 (M₀ : ℕ)
    (hall : ∀ m, M₀ ≤ m → m % 6 = 0 → ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m) :
    ∀ B, ∃ r, B < r ∧ DicksonPair r := by
  intro B
  by_contra hno
  push Not at hno
  set m := 6 * (Nat.factorial (3 * B)) * (M₀ + 2) with hm
  have hf : 0 < Nat.factorial (3 * B) := Nat.factorial_pos _
  have hmM : M₀ ≤ m := by
    have : M₀ + 2 ≤ m := by
      rw [hm]; exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hm6 : m % 6 = 0 := by rw [hm, mul_assoc]; exact Nat.mul_mod_right 6 _
  have hm8 : 12 ≤ m := by
    have h1 : 2 ≤ Nat.factorial (3 * B) * (M₀ + 2) :=
      le_trans (by omega : 2 ≤ 1 * 2) (Nat.mul_le_mul hf (by omega))
    rw [hm, mul_assoc]; omega
  obtain ⟨p, q, hp, hq, hpq⟩ := hall m hmM hm6
  -- neither summand is 2 or 3
  have small : ∀ x y : ℕ, IsChenPrime x → IsChenPrime y → x + y = m → 3 < x := by
    intro x y hx hy hxy
    have hx2 := hx.1.two_le
    rcases (show x = 2 ∨ x = 3 ∨ 3 < x by omega) with h | h | h
    · subst h
      have : y % 2 = 0 := by omega
      have := hy.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero this); omega
    · subst h
      have : y % 3 = 0 := by omega
      have := hy.1.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero this); omega
    · exact h
  have hp3 := small p q hp hq hpq
  have hq3 := small q p hq hp (by rw [add_comm]; exact hpq)
  -- the summand that is 1 mod 6
  have key : ∀ x y : ℕ, IsChenPrime x → IsChenPrime y → x + y = m → 3 < x → 3 < y →
      x % 6 = 1 → False := by
    intro x y hx hy hxy hx3 hy3 h1
    obtain ⟨r, hr, hxr⟩ := chen_one_mod_six hx h1
    have hrB : r ≤ B := by
      by_contra hrB
      apply hno r (by omega)
      refine ⟨hr, ?_⟩
      have : 3 * r - 2 = x := by omega
      rw [this]; exact hx.1
    have hxle : x ≤ 3 * B := by omega
    have hxd : x ∣ Nat.factorial (3 * B) := Nat.dvd_factorial (by omega) hxle
    have hxm : x ∣ m := by
      rw [hm, mul_assoc]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hxd _) 6
    have hxy' : x ∣ y := by
      have : y = m - x := by omega
      rw [this]; exact Nat.dvd_sub hxm (dvd_refl x)
    rcases hy.1.eq_one_or_self_of_dvd x hxy' with h | h
    · omega
    · -- x = y, so m = 2 x ≡ 2 mod 6, not 0
      omega
  rcases one_mod_six_of_class0 hp.1 hq.1 hp3 hq3 (by omega) with h | h
  · exact key p q hp hq hpq hp3 hq3 h
  · exact key q p hq hp (by rw [add_comm]; exact hpq) hq3 hp3 h

/-- vacuity: the hypothesis shape has instances, `20 = 7 + 13` with both Chen primes,
`7 + 2 = 9 = 3²`, `13 + 2 = 15 = 3 · 5`, and `(3, 7)`, `(5, 13)` are Dickson pairs. -/
theorem vacuity_20 : IsChenPrime 7 ∧ IsChenPrime 13 ∧ 7 + 13 = 20 ∧ 20 % 6 = 2 := by
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, rfl, rfl⟩
  · rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors]
    rw [show (7 + 2 : ℕ) = 3 * 3 by norm_num,
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_three]
  · rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors]
    rw [show (13 + 2 : ℕ) = 3 * 5 by norm_num,
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_three,
      ArithmeticFunction.cardFactors_apply_prime (by norm_num : Nat.Prime 5)]

theorem vacuity_pairs : DicksonPair 3 ∧ DicksonPair 5 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end LeanLab.ExceptionalSet.ChenClass2Barrier
