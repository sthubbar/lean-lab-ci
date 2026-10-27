/-
Goldbach with primes in progressions.
P0084 Kimball Martin 2018, Refined Goldbach conjectures with primes in progressions,
  arXiv 1806.00946. Every numbered item in the paper is a conjecture; nothing there is
  proved. The paper checks them numerically, m ≤ 200 to at least 10^7, Conj 1.2 to 10^8.
Here: the conjectures as `Prop`s; the implications the paper remarks on, PROVED; the
listed exceptions of Conj 1.2 iv and 1.3 ii PROVED to be exceptions; a finite range PROVED
by a kernel-checked search.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Binary Goldbach is OPEN, and so is every conjecture below.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Martin2018

/-- `n = p + q` with primes `p ≡ a`, `q ≡ b` mod `m`. -/
def GoldbachAP (m a b n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % m = a % m ∧ q % m = b % m ∧ p + q = n

/-- Conj 1.1: for `a, b` units mod `m`, every large even `n ≡ a + b` mod `m` is such a sum;
equivalently `E_{a,b,m}` is finite. -/
def Conj1_1 : Prop :=
  ∀ m a b : ℕ, 0 < m → Nat.Coprime a m → Nat.Coprime b m →
    ∃ N, ∀ n, Even n → n % m = (a + b) % m → N ≤ n → GoldbachAP m a b n

/-- Conj 1.2 i: every even `n > 4` is `p + q` with `p ≡ 3` mod 4. -/
def Conj1_2_i : Prop := ∀ n, Even n → 4 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 = 3 ∧ p + q = n

/-- Conj 1.2 ii: every `n ≡ 0` mod 4 except 4, with `p ≡ 1`, `q ≡ 3`. Includes `n = 0` only
as excluded, `n` positive. -/
def Conj1_2_ii : Prop := ∀ n, 0 < n → n % 4 = 0 → n ≠ 4 → GoldbachAP 4 1 3 n

/-- Conj 1.2 iii: every `n ≡ 2` mod 4 except 2, with `p ≡ q ≡ 3`. -/
def Conj1_2_iii : Prop := ∀ n, n % 4 = 2 → n ≠ 2 → GoldbachAP 4 3 3 n

/-- Conj 1.2 iv AS PRINTED: every `n ≡ 2` mod 4 except 2, 6, 14, 18, 62, with `p ≡ q ≡ 1`.
FALSE as printed, see `conj1_2_iv_printed_false`: 38 is an exception and 18 = 5 + 13 is not. -/
def Conj1_2_iv_printed : Prop :=
  ∀ n, n % 4 = 2 → n ∉ ({2, 6, 14, 18, 62} : Finset ℕ) → GoldbachAP 4 1 1 n

/-- Conj 1.2 iv corrected to the paper's own table `E_{1,1,4} = {2, 6, 14, 38, 62}`. -/
def Conj1_2_iv : Prop :=
  ∀ n, n % 4 = 2 → n ∉ ({2, 6, 14, 38, 62} : Finset ℕ) → GoldbachAP 4 1 1 n

/-- Conj 1.3 i: every even `n ≡ 0` mod 3 except 6, with `p ≡ -q ≡ 1` mod 3. -/
def Conj1_3_i : Prop := ∀ n, 0 < n → Even n → n % 3 = 0 → n ≠ 6 → GoldbachAP 3 1 2 n

/-- Conj 1.3 ii: every even `n ≡ 0` mod 5 with `p ≡ -q ≡ 2`; and except 10, 20 with
`p ≡ -q ≡ 1`. -/
def Conj1_3_ii : Prop :=
  (∀ n, 0 < n → Even n → n % 5 = 0 → GoldbachAP 5 2 3 n) ∧
  (∀ n, 0 < n → Even n → n % 5 = 0 → n ≠ 10 → n ≠ 20 → GoldbachAP 5 1 4 n)

/-- Conj 1.3 iii to vi: `p ≡ -q ≡ 3` mod 7, 11, 8, 16, for even `n ≡ 0` mod the modulus. -/
def Conj1_3_mod (m : ℕ) : Prop := ∀ n, 0 < n → Even n → n % m = 0 → GoldbachAP m 3 (m - 3) n

/-- Conj 1.3 vii: `n ≡ 0` mod 60, `p ≡ -q ≡ a`, `a` coprime to 60 and not `±1, ±11`. -/
def Conj1_3_vii : Prop :=
  ∀ a, Nat.Coprime a 60 → a % 60 ∉ ({1, 59, 11, 49} : Finset ℕ) →
    ∀ n, 0 < n → n % 60 = 0 → GoldbachAP 60 a (60 - a % 60) n

/-- Conj 1.7: every odd `n > 5` is `p + q + r` with `p ≡ q ≡ 2` mod 3. -/
def Conj1_7 : Prop :=
  ∀ n, Odd n → 5 < n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p % 3 = 2 ∧ q % 3 = 2 ∧
    p + q + r = n

/-! ### The implications the paper remarks on, PROVED zero sorry -/

theorem odd_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two h2)

/-- "ii follows from Goldbach". -/
theorem conj1_2_ii_of_goldbach (hG : BinaryGoldbach) : Conj1_2_ii := by
  intro n hn h4 hne
  obtain ⟨p, q, hp, hq, hpq⟩ := hG n (Nat.even_iff.mpr (by omega)) (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : q % 2 = 0 := by omega
    have : q = 2 := (hq.eq_one_or_self_of_dvd 2 (by omega)).resolve_left (by norm_num) |>.symm
    omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : p % 2 = 0 := by omega
    have : p = 2 := (hp.eq_one_or_self_of_dvd 2 (by omega)).resolve_left (by norm_num) |>.symm
    omega
  have := odd_of_prime_ne_two hp hp2
  have := odd_of_prime_ne_two hq hq2
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · exact ⟨p, q, hp, hq, by omega, by omega, hpq⟩
  · exact ⟨q, p, hq, hp, by omega, by omega, by omega⟩

/-- "ii with iii gives i". -/
theorem conj1_2_i_of (h2 : Conj1_2_ii) (h3 : Conj1_2_iii) : Conj1_2_i := by
  intro n hev h4
  have := Nat.even_iff.mp hev
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 2) with h | h
  · obtain ⟨p, q, hp, hq, _, hq3, hpq⟩ := h2 n (by omega) h (by omega)
    exact ⟨q, p, hq, hp, by omega, by omega⟩
  · obtain ⟨p, q, hp, hq, hp3, _, hpq⟩ := h3 n h (by omega)
    exact ⟨p, q, hp, hq, by omega, hpq⟩

/-- "1.3 i follows directly from binary Goldbach". -/
theorem conj1_3_i_of_goldbach (hG : BinaryGoldbach) : Conj1_3_i := by
  intro n hn hev h3 h6
  have := Nat.even_iff.mp hev
  obtain ⟨p, q, hp, hq, hpq⟩ := hG n hev (by omega)
  have p3 : p % 3 = 0 → p = 3 := fun h =>
    ((hp.eq_one_or_self_of_dvd 3 (by omega)).resolve_left (by norm_num)).symm
  have q3 : q % 3 = 0 → q = 3 := fun h =>
    ((hq.eq_one_or_self_of_dvd 3 (by omega)).resolve_left (by norm_num)).symm
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
  · have := p3 h; subst this
    have : q % 3 = 0 := by omega
    have := q3 this; omega
  · exact ⟨p, q, hp, hq, by omega, by omega, hpq⟩
  · exact ⟨q, p, hq, hp, by omega, by omega, by omega⟩

/-! ### The listed exceptions really are exceptions, PROVED zero sorry -/

theorem goldbachAP_bounded {m a b n : ℕ} :
    GoldbachAP m a b n ↔ ∃ p ∈ Finset.range (n + 1), p.Prime ∧ (n - p).Prime ∧
      p % m = a % m ∧ (n - p) % m = b % m := by
  constructor
  · rintro ⟨p, q, hp, hq, ha, hb, rfl⟩
    exact ⟨p, Finset.mem_range.mpr (by omega), hp, by simpa using hq, ha, by simpa using hb⟩
  · rintro ⟨p, hp', hp, hq, ha, hb⟩
    exact ⟨p, n - p, hp, hq, ha, hb, by have := Finset.mem_range.mp hp'; omega⟩

/-- The corrected exceptions 2, 6, 14, 38, 62 are not sums of two primes `≡ 1` mod 4. -/
theorem conj1_2_iv_exceptions :
    ∀ n ∈ ({2, 6, 14, 38, 62} : Finset ℕ), ¬ GoldbachAP 4 1 1 n := by
  intro n hn
  rw [goldbachAP_bounded]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide

/-- 18 = 5 + 13 with both primes `≡ 1` mod 4, so 18 is not an exception. -/
theorem eighteen_is_sum : GoldbachAP 4 1 1 18 :=
  ⟨5, 13, by norm_num, by norm_num, rfl, rfl, rfl⟩

/-- Conj 1.2 iv as printed is FALSE: `n = 38` is `≡ 2` mod 4, not in the printed list, and is
not a sum of two primes `≡ 1` mod 4. A misprint of 38 as 18; the paper's table has 38. -/
theorem conj1_2_iv_printed_false : ¬ Conj1_2_iv_printed := by
  intro h
  exact conj1_2_iv_exceptions 38 (by decide) (h 38 (by norm_num) (by decide))

/-- Conj 1.3 ii's exceptions 10, 20 are not sums `p + q`, `p ≡ 1`, `q ≡ 4` mod 5. -/
theorem conj1_3_ii_exceptions : ¬ GoldbachAP 5 1 4 10 ∧ ¬ GoldbachAP 5 1 4 20 := by
  rw [goldbachAP_bounded, goldbachAP_bounded]
  constructor <;> decide

/-! ### A kernel-checked finite range for Conj 1.2 iv -/

/-- Search `p = d, d+1, ...` for prime `p ≡ a`, `n - p` prime `≡ b` mod `m`. -/
def apFrom (m a b n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, p => if n < p then false
      else if primeB p && primeB (n - p) && (p % m == a % m) && ((n - p) % m == b % m) then true
      else apFrom m a b n fuel (p + 1)

theorem apFrom_sound (m a b n : ℕ) : ∀ fuel p, apFrom m a b n fuel p = true →
    GoldbachAP m a b n := by
  intro fuel
  induction fuel with
  | zero => intro p h; simp [apFrom] at h
  | succ k ih =>
    intro p h
    simp only [apFrom] at h
    by_cases h1 : n < p
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : (primeB p && primeB (n - p) && (p % m == a % m) &&
          ((n - p) % m == b % m)) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at h2
        exact ⟨p, n - p, primeB_sound h2.1.1.1, primeB_sound h2.1.1.2, h2.1.2, h2.2, by omega⟩
      · rw [if_neg h2] at h; exact ih (p + 1) h

/-- Check Conj 1.2 iv for every `n ≤ N`. -/
def allIv : ℕ → Bool
  | 0 => true
  | n + 1 => (if (n + 1) % 4 = 2 && !((n + 1) ∈ [2, 6, 14, 38, 62]) then
      apFrom 4 1 1 (n + 1) (n + 1) 2 else true) && allIv n

theorem allIv_sound : ∀ N, allIv N = true → ∀ n, n ≤ N → n % 4 = 2 →
    n ∉ ({2, 6, 14, 38, 62} : Finset ℕ) → GoldbachAP 4 1 1 n := by
  intro N
  induction N with
  | zero => intro _ n hn h; omega
  | succ k ih =>
    intro h n hn h2 hex
    rw [allIv, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · exact ih h.2 n (by omega) h2 hex
    · have hn' : n = k + 1 := by omega
      subst hn'
      have hc : ((k + 1) % 4 = 2 && !((k + 1) ∈ [2, 6, 14, 38, 62])) = true := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hex
        simp [h2, hex.1, hex.2.1, hex.2.2.1, hex.2.2.2.1, hex.2.2.2.2]
      have := h.1
      rw [if_pos hc] at this
      exact apFrom_sound _ _ _ _ _ _ this

/-- Corrected Conj 1.2 iv holds for every `n ≤ 3000`. Martin checked to 10^8. -/
theorem conj1_2_iv_upTo : ∀ n, n ≤ 3000 → n % 4 = 2 →
    n ∉ ({2, 6, 14, 38, 62} : Finset ℕ) → GoldbachAP 4 1 1 n :=
  allIv_sound 3000 (by decide +kernel)

end LeanLab.Martin2018
