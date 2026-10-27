/-
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488, read in full on 2026-10-18 by run 20261018T0503Z-16389, unit U-0917,
through Claude in Chrome, arxiv.org/html/2608.09488, per Lean Lab RULES_BLOCKERS B1.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.

Theorem 1.2: every integer `N ≥ 2` is `a + b` with positive `a, b` and `Ω(ab) ≤ 33`.
The proof has three ranges, Section 4: `2 ≤ N ≤ N₀`, by Lemma 5.1 and maximal prime gap
data; `N₀ < N < N₁ = 10^132`, by a finite computer verification that `S(𝒜, z) > 0`; and
`N ≥ N₁`, by the explicit Friedlander-Iwaniec sieve, Theorem 2.1, and Lemmas 4.1 to 4.3.
In both upper ranges Lemma 5.2 turns `S(𝒜, z) > 0`, with `z = N^{1/16.5}`, into the theorem.

Here: Lemma 5.1 and Lemma 5.2 PROVED in full; Case 1 CONDITIONAL ON the cited gap table;
Theorem 1.2 CONDITIONAL ON the gap table and on `S(𝒜, z) > 0` for `N > N₀`, which is
what the computer check and the sieve give; and the printed Case 3 arithmetic.
Goldbach itself is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.SmallRange

namespace LeanLab.AlmostPrimes.Campbell2026
open LeanLab.AlmostPrimes

/-- `G = 101412319996363310923`, p. 5.1. -/
def G : ℕ := 101412319996363310923

/-- `N₀ = 117465180365547648498934439`, Section 4. -/
def N0 : ℕ := 117465180365547648498934439

/-- The cited prime gap table [2] as Campbell uses it: every prime `q < G` is followed by a
prime `q'` with `q' - q ≤ 1854`. -/
def GapTable : Prop := ∀ q : ℕ, q.Prime → q < G → ∃ q' : ℕ, q'.Prime ∧ q < q' ∧ q' - q ≤ 1854

theorem bigOmega_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  simp only [bigOmega_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_mul ha hb

theorem bigOmega_prime {p : ℕ} (hp : p.Prime) : bigOmega p = 1 := by
  rw [bigOmega_eq_cardFactors, ArithmeticFunction.cardFactors_apply_prime hp]

/-- **Lemma 5.1, PROVED from the gap table.** Let `m` be 1 or a prime and `M` a positive
integer with `1854 m ≤ 2^(M-2)`. Then every `2 ≤ N ≤ G m` is `a + b` with `Ω(ab) ≤ M`. -/
theorem lemma5_1 (hG : GapTable) {m M : ℕ} (hm : m = 1 ∨ m.Prime) (hM : 0 < M)
    (hmM : 1854 * m ≤ 2 ^ (M - 2)) : ∀ N : ℕ, 2 ≤ N → N ≤ G * m → TwoAlmostPrimes M N := by
  have hm1 : 1 ≤ m := by
    rcases hm with h | h
    · omega
    · exact h.one_lt.le
  have hM3 : 3 ≤ M := by
    by_contra h
    have : M - 2 ≤ 0 := by omega
    have : 2 ^ (M - 2) ≤ 1 := by
      calc 2 ^ (M - 2) ≤ 2 ^ 0 := Nat.pow_le_pow_right (by norm_num) this
        _ = 1 := by norm_num
    omega
  have hpow : 2 ^ (M - 2) < 2 ^ (M - 2 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  intro N h2 hN
  rcases Nat.lt_or_ge (2 * m) N with hbig | hsmall
  · -- the largest prime `q` with `m q < N`
    let P : ℕ → Prop := fun q => q.Prime ∧ m * q < N
    have hP2 : P 2 := ⟨Nat.prime_two, by omega⟩
    let q := Nat.findGreatest P N
    have hq : P q := Nat.findGreatest_spec (P := P) (m := 2) (by omega) hP2
    have hqN : q ≤ N := Nat.findGreatest_le N
    have hqG : q < G := by
      by_contra h
      have : G * m ≤ q * m := Nat.mul_le_mul_right m (by omega)
      have : q * m = m * q := Nat.mul_comm q m
      omega
    obtain ⟨q', hq', hqq', hgap⟩ := hG q hq.1 hqG
    have hmq' : N ≤ m * q' := by
      by_contra h
      push_neg at h
      have hq'N : q' ≤ N := by nlinarith
      exact Nat.findGreatest_is_greatest (P := P) hqq' hq'N ⟨hq', h⟩
    have hd : N - m * q ≤ 1854 * m := by
      have : m * q' - m * q = m * (q' - q) := (Nat.mul_sub m q' q).symm
      have : m * (q' - q) ≤ m * 1854 := Nat.mul_le_mul_left m hgap
      omega
    have hpos : 0 < N - m * q := by have := hq.2; omega
    have hmq0 : 0 < m * q := Nat.mul_pos (by omega) hq.1.pos
    refine ⟨m * q, N - m * q, hmq0, hpos, by omega, ?_⟩
    rw [bigOmega_mul hmq0.ne' hpos.ne']
    have h1 : bigOmega (m * q) ≤ 2 := by
      rcases hm with h | h
      · subst h; rw [one_mul, bigOmega_prime hq.1]; norm_num
      · rw [bigOmega_mul h.ne_zero hq.1.ne_zero, bigOmega_prime h, bigOmega_prime hq.1]
    have h2' : bigOmega (N - m * q) ≤ M - 2 := bigOmega_le_of_lt hpos (by omega)
    omega
  · refine ⟨1, N - 1, by norm_num, by omega, by omega, ?_⟩
    rw [one_mul]
    have : bigOmega (N - 1) ≤ M - 2 := bigOmega_le_of_lt (by omega) (by omega)
    omega

/-- Case 1 numbers: `m = 1158293` is prime, `1854 m = 2147475222 < 2^31`, `G m = N₀`. -/
theorem m_prime : Nat.Prime 1158293 := by norm_num

theorem case1_numbers : 1854 * 1158293 = 2147475222 ∧ 2147475222 < 2 ^ 31 ∧
    G * 1158293 = N0 := by
  unfold G N0; norm_num

/-- **Case 1, CONDITIONAL ON the gap table:** every `2 ≤ N ≤ N₀` is `a + b` with
`Ω(ab) ≤ 33`. -/
theorem case1 (hG : GapTable) : ∀ N : ℕ, 2 ≤ N → N ≤ N0 → TwoAlmostPrimes 33 N := by
  intro N h2 hN
  have h := lemma5_1 hG (m := 1158293) (M := 33) (Or.inr m_prime) (by norm_num)
    (by norm_num) N h2
  apply h
  rw [case1_numbers.2.2]; exact hN

/-! ### Lemma 5.2 -/

/-- `aₙ`, Section 3: `n(N - n)` for even `N`, `n(N - n)/2` for odd `N`. -/
def aSeq (N n : ℕ) : ℕ := if Even N then n * (N - n) else n * (N - n) / 2

/-- `S(𝒜, z) > 0` unpacked: some `1 ≤ n ≤ N - 1` has `aₙ` free of prime factors below `z`.
The paper's `(aₙ, P(z)) = 1` with `3 ∤ aₙ` and `𝒫` all primes but 3 is exactly this. -/
def SiftedExists (N : ℕ) (z : ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ n ≤ N - 1 ∧ ∀ p : ℕ, p.Prime → p ∣ aSeq N n → z ≤ p

theorem pow_length_le_prod (z : ℝ) (hz : 0 ≤ z) :
    ∀ l : List ℕ, (∀ x ∈ l, z ≤ (x : ℝ)) → z ^ l.length ≤ (l.prod : ℝ)
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.length_cons, List.prod_cons, pow_succ', Nat.cast_mul]
    have ha := h a (by simp)
    have hl := pow_length_le_prod z hz l (fun x hx => h x (by simp [hx]))
    exact mul_le_mul ha hl (pow_nonneg hz _) (le_trans hz ha)

/-- If every prime factor of `k > 0` is at least `z ≥ 0`, then `z^Ω(k) ≤ k`. -/
theorem pow_bigOmega_le {k : ℕ} (hk : 0 < k) {z : ℝ} (hz : 0 ≤ z)
    (h : ∀ p : ℕ, p.Prime → p ∣ k → z ≤ p) : z ^ bigOmega k ≤ k := by
  unfold bigOmega
  have := pow_length_le_prod z hz k.primeFactorsList (fun x hx =>
    h x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx))
  rwa [Nat.prod_primeFactorsList hk.ne'] at this

/-- **Lemma 5.2, PROVED.** Let `N ≥ 2`, `r > 1`, `z = N^{1/r}`. If `S(𝒜, z) > 0` then
`N = a + b` with positive `a, b` and `Ω(ab) < 2r` for even `N`, `Ω(ab) < 2r + 1` for
odd `N`. -/
theorem lemma5_2 {N : ℕ} {r : ℝ} (hN : 2 ≤ N) (hr : 1 < r)
    (hS : SiftedExists N ((N : ℝ) ^ (1 / r))) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → (bigOmega (a * b) : ℝ) < 2 * r) ∧
      (¬ Even N → (bigOmega (a * b) : ℝ) < 2 * r + 1) := by
  obtain ⟨n, hn1, hn2, hs⟩ := hS
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hr0 : 0 < r := by linarith
  have hb : 0 < N - n := by omega
  have hprod : n * (N - n) < N ^ 2 := by
    have h1 : n * (N - n) ≤ n * N := Nat.mul_le_mul_left n (by omega)
    have h2 : n * N < N * N := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    rw [pow_two]; omega
  have hapos : 0 < aSeq N n := by
    unfold aSeq
    split_ifs with he
    · exact Nat.mul_pos (by omega) hb
    · have h3 : 3 ≤ N := by
        rcases Nat.lt_or_ge N 3 with h | h
        · exfalso; exact he ⟨1, by omega⟩
        · exact h
      have : 2 ≤ n * (N - n) := by
        rcases Nat.lt_or_ge n 2 with h | h
        · have : n = 1 := by omega
          subst this; omega
        · nlinarith
      omega
  have halt : aSeq N n < N ^ 2 := by
    unfold aSeq; split_ifs
    · exact hprod
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) hprod
  have hz0 : 0 ≤ (N : ℝ) ^ (1 / r) := Real.rpow_nonneg (by positivity) _
  have hzt := pow_bigOmega_le hapos hz0 hs
  -- `N^{t/r} ≤ aₙ < N^2`, so `t < 2 r`
  have ht : (bigOmega (aSeq N n) : ℝ) < 2 * r := by
    have e : ((N : ℝ) ^ (1 / r)) ^ bigOmega (aSeq N n) =
        (N : ℝ) ^ ((bigOmega (aSeq N n) : ℝ) / r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
    rw [e] at hzt
    have hlt : (N : ℝ) ^ ((bigOmega (aSeq N n) : ℝ) / r) < (N : ℝ) ^ (2 : ℝ) := by
      calc (N : ℝ) ^ ((bigOmega (aSeq N n) : ℝ) / r) ≤ (aSeq N n : ℝ) := hzt
        _ < ((N ^ 2 : ℕ) : ℝ) := by exact_mod_cast halt
        _ = (N : ℝ) ^ (2 : ℝ) := by push_cast; rw [Real.rpow_two]
    have := (Real.rpow_lt_rpow_left_iff hNr).mp hlt
    rw [div_lt_iff₀ hr0] at this; linarith
  refine ⟨n, N - n, by omega, hb, by omega, ?_, ?_⟩
  · intro he
    have : aSeq N n = n * (N - n) := by unfold aSeq; rw [if_pos he]
    rw [← this]; exact ht
  · intro he
    have hev : 2 ∣ n * (N - n) := by
      rcases Nat.even_or_odd n with h | h
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
      · apply Dvd.dvd.mul_left
        apply even_iff_two_dvd.mp
        have hNo : Odd N := Nat.not_even_iff_odd.mp he
        obtain ⟨k, hk⟩ := h; obtain ⟨j, hj⟩ := hNo
        exact ⟨j - k, by omega⟩
    have hdef : aSeq N n = n * (N - n) / 2 := by unfold aSeq; rw [if_neg he]
    have e2 : n * (N - n) = 2 * aSeq N n := by rw [hdef]; exact (Nat.mul_div_cancel' hev).symm
    rw [e2, bigOmega_mul (by norm_num) hapos.ne', bigOmega_prime Nat.prime_two]
    push_cast
    linarith

/-- **Theorem 1.2, CONDITIONAL ON** the gap table and on `S(𝒜, N^{1/16.5}) > 0` for every
`N > N₀`, which the paper's finite verification, Case 2, and sieve estimates, Case 3, give.
Zero sorry of its own. -/
theorem theorem1_2_of (hG : GapTable)
    (hS : ∀ N : ℕ, N0 < N → SiftedExists N ((N : ℝ) ^ (1 / (16.5 : ℝ)))) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N := by
  intro N h2
  rcases Nat.lt_or_ge N0 N with h | h
  · obtain ⟨a, b, ha, hb, hab, he, ho⟩ := lemma5_2 h2 (by norm_num) (hS N h)
    refine ⟨a, b, ha, hb, hab, ?_⟩
    by_cases hN : Even N
    · have := he hN
      have : (bigOmega (a * b) : ℝ) < 34 := by linarith
      have : bigOmega (a * b) < 34 := by exact_mod_cast this
      omega
    · have := ho hN
      have : (bigOmega (a * b) : ℝ) < 34 := by linarith
      have : bigOmega (a * b) < 34 := by exact_mod_cast this
      omega
  · exact case1 hG N h2 h

/-- The P0020 abstract statement from the same two inputs, matching `campbell` in
Statements.lean. -/
theorem campbell_of (hG : GapTable)
    (hS : ∀ N : ℕ, N0 < N → SiftedExists N ((N : ℝ) ^ (1 / (16.5 : ℝ)))) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N := theorem1_2_of hG hS

/-! ### The printed Case 3 arithmetic -/

/-- `1.241 (16.5)^2 (0.0563) / 3 > 6.34`. MATCHES. -/
theorem case3_main : (6.34 : ℝ) < 1.241 * 16.5 ^ 2 * 0.0563 / 3 := by norm_num

/-- `2 (0.563) / 16.5^8 < 2.05 · 10^-10`. MATCHES. -/
theorem case3_error : 2 * (0.563 : ℝ) / 16.5 ^ 8 < 2.05e-10 := by norm_num

/-- `s ≥ 2k + 3` in Case 3, `s = 14.66`, `k = 2 + log 1.097`, and in Case 2,
`s = 14.8`, `k = 2 + log 1.146`. MATCHES. -/
theorem s_conditions : 2 * (2 + Real.log 1.097) + 3 ≤ 14.66 ∧
    2 * (2 + Real.log 1.146) + 3 ≤ 14.8 := by
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.097)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.146)
  constructor <;> linarith

set_option exponentiation.threshold 1000 in
/-- `log 10 < 2.30261`, from `10^205 < 2^681`. -/
theorem log_ten_lt : Real.log 10 < 2.30261 := by
  have hn : (10 : ℕ) ^ 205 < 2 ^ 681 := by norm_num
  have h : (10 : ℝ) ^ 205 < 2 ^ 681 := by exact_mod_cast hn
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  have := Real.log_two_lt_d9
  push_cast at h'
  nlinarith

/-- `5.248 < 10^0.72`, since `5.248^25 < 10^18 = (10^0.72)^25`. -/
theorem rpow_072_gt : (5.248 : ℝ) < (10 : ℝ) ^ (0.72 : ℝ) := by
  have e : ((10 : ℝ) ^ (0.72 : ℝ)) ^ (25 : ℕ) = 10 ^ (18 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h : (5.248 : ℝ) ^ 25 < ((10 : ℝ) ^ (0.72 : ℝ)) ^ 25 := by rw [e]; norm_num
  exact lt_of_pow_lt_pow_left₀ 25 (Real.rpow_nonneg (by norm_num) _) h

/-- Case 3: at `N = N₁ = 10^132` the ratio
`(6.34 / 2.05e-10)(1 - 1/N) N^{1.84/16.5} / log^{10} N` exceeds `2.41`, as printed. Since
`132 · 1.84 / 16.5 = 14.72`, the claim is
`2.41 (132 log 10)^10 < (6.34 / 2.05e-10)(1 - 10^-132) 10^{14.72}`. MATCHES, margin
about 0.05 percent. -/
theorem case3_ratio :
    2.41 * (132 * Real.log 10) ^ 10 <
      (6.34 / 2.05e-10) * (1 - 1 / 10 ^ 132) * (10 : ℝ) ^ (14.72 : ℝ) := by
  have hl := log_ten_lt
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hr := rpow_072_gt
  have e : (10 : ℝ) ^ (14.72 : ℝ) = 10 ^ (14 : ℕ) * (10 : ℝ) ^ (0.72 : ℝ) := by
    rw [show (14.72 : ℝ) = (14 : ℕ) + 0.72 by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_natCast]
  have hA : 2.41 * (132 * Real.log 10) ^ 10 ≤ 2.41 * (132 * 2.30261 : ℝ) ^ 10 := by gcongr
  have hB : (6.34 / 2.05e-10) * (1 - 1 / 10 ^ 132) * (10 ^ (14 : ℕ) * 5.248 : ℝ) <
      (6.34 / 2.05e-10) * (1 - 1 / 10 ^ 132) * (10 : ℝ) ^ (14.72 : ℝ) := by
    rw [e]; gcongr
  have hC : 2.41 * (132 * 2.30261 : ℝ) ^ 10 <
      (6.34 / 2.05e-10) * (1 - 1 / 10 ^ 132) * (10 ^ (14 : ℕ) * 5.248 : ℝ) := by norm_num
  linarith

end LeanLab.AlmostPrimes.Campbell2026
