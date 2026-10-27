/-
U-1433, PC run 20261021T1403Z-5629, T1 PROVE on P0039, L. Grimmelt and J. Teräväinen,
The Exceptional Set in Goldbach's Problem with two Chen Primes, arXiv 2508.16400v2.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Theorem 1.1 stays cited, `grimmeltTeravainen` in ChenPrimes.lean.

The values `S = 1` on `B₁` and `S = 0` on `B₂` that `eq312printed_fails_B1` and `_B2` of
GrimmeltTeravainen2025Chain.lean take as inputs, where `S` is the number of primes `p ∣ n` with
`N^{1/10} ≤ p ≤ N^{1/3-δ₁}`, the sum in (3.11).

Range of `n`, settling U-1424 QUESTION 1: the arXiv HTML of v2 introduces (3.11) with
"we have for N/2 < n ≤ N that", and Proposition 3.4 (i) states (3.7) "for N/2 < n ≤ N".
In (3.7) the set B₁ ∪ B₂ is evaluated at `n + 2`, which lies in `(N/2 + 2, N + 2]`; either way
the integer `m` tested for membership satisfies `N ≤ 2 m`, the hypothesis used below.

Definitions (3.1) and (3.2), quoted from the HTML:
B₁ = { p₁p₂p₃ : N^{1/10} ≤ p₁ < N^{1/3-δ₁} ≤ p₂ ≤ (N/p₁)^{1/2}, p₃ ≥ N^{1/10} },
B₂ = { p₁p₂p₃ : N^{1/3-δ₁} ≤ p₁ ≤ p₂ ≤ (N/p₁)^{1/2}, p₃ ≥ N^{1/10} }.
Here `lo` stands for `N^{1/10}` and `a` for `N^{1/3-δ₁}`; `p₂ ≤ (N/p₁)^{1/2}` is written
`p₁ p₂² ≤ N`.

Named hypothesis, not in the paper: `EndpointNotPrime a`, that `a = N^{1/3-δ₁}` is not a prime.
The sum in (3.11) is over the closed range `p ≤ N^{1/3-δ₁}` while (3.1) and (3.2) allow
`p₂ = N^{1/3-δ₁}` resp. `p₁ = N^{1/3-δ₁}`; if that real number is a prime, `S` is 2 on such
`n ∈ B₁` and 1 on such `n ∈ B₂`. The `S` values are CONDITIONAL on this hypothesis.
-/
import LeanLab.ChenPrimeExceptional.U1424GTElementary

open Finset

namespace LeanLab.ChenPrimeExceptional.U1433

open LeanLab.ExceptionalSet.GT2025 LeanLab.ChenPrimeExceptional.U1424

/-! ### The size of `p₃` on `B₂` -/

/-- For `n = p₁ p₂ p₃` with `p₁ ≤ p₂`, `p₁ p₂² ≤ N` and `N ≤ 2 n`: `N ≤ 8 p₃³`, that is
`p₃ ≥ N^{1/3}/2`. -/
theorem B2_cube_bound {p₁ p₂ p₃ N : ℝ} (h1 : 0 < p₁) (h2 : 0 < p₂) (h3 : 0 < p₃)
    (h12 : p₁ ≤ p₂) (hp2 : p₁ * p₂ ^ 2 ≤ N) (hn : N ≤ 2 * (p₁ * p₂ * p₃)) :
    N ≤ 8 * p₃ ^ 3 := by
  have hN0 : 0 < N := by nlinarith [mul_pos (mul_pos h1 h2) h3]
  -- p₁³ ≤ p₁ p₂² ≤ N
  have hp1c : p₁ ^ 3 ≤ N := by
    have : p₁ ^ 2 ≤ p₂ ^ 2 := pow_le_pow_left₀ h1.le h12 2
    nlinarith [mul_le_mul_of_nonneg_left this h1.le]
  -- N² ≤ 4 (p₁p₂)² p₃² = 4 p₁ (p₁p₂²) p₃² ≤ 4 p₁ N p₃², so N ≤ 4 p₁ p₃²
  have hsq : N ^ 2 ≤ 4 * (p₁ * p₂ * p₃) ^ 2 := by nlinarith
  have hb : (p₁ * p₂ * p₃) ^ 2 ≤ p₁ * N * p₃ ^ 2 := by
    have e : (p₁ * p₂ * p₃) ^ 2 = p₁ * (p₁ * p₂ ^ 2) * p₃ ^ 2 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hp2 h1.le
    exact mul_le_mul_of_nonneg_right this (sq_nonneg p₃)
  have hNle : N ≤ 4 * p₁ * p₃ ^ 2 := by
    have : N * N ≤ (4 * p₁ * p₃ ^ 2) * N := by nlinarith
    exact le_of_mul_le_mul_right this hN0
  -- N³ ≤ 64 p₁³ p₃⁶ ≤ 64 N p₃⁶, so N² ≤ 64 p₃⁶ = (8 p₃³)²
  have hc : N ^ 3 ≤ (4 * p₁ * p₃ ^ 2) ^ 3 := pow_le_pow_left₀ hN0.le hNle 3
  have hc2 : (4 * p₁ * p₃ ^ 2) ^ 3 ≤ 64 * N * p₃ ^ 6 := by
    have e : (4 * p₁ * p₃ ^ 2) ^ 3 = 64 * p₁ ^ 3 * p₃ ^ 6 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hp1c (by positivity : (0 : ℝ) ≤ 64 * p₃ ^ 6)
    nlinarith
  have hN2 : N ^ 2 ≤ (8 * p₃ ^ 3) ^ 2 := by
    have : N * N ^ 2 ≤ N * (8 * p₃ ^ 3) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hN0
  exact (pow_le_pow_iff_left₀ hN0.le (by positivity) (by norm_num)).1 hN2

/-- **`B2_p3_large`, first half:** `p₃ ≥ N^{1/3}/2` on `B₂`, for `N ≥ 2 n`-range `n`. -/
theorem B2_p3_ge {p₁ p₂ p₃ N : ℝ} (h1 : 0 < p₁) (h2 : 0 < p₂) (h3 : 0 < p₃)
    (h12 : p₁ ≤ p₂) (hp2 : p₁ * p₂ ^ 2 ≤ N) (hn : N ≤ 2 * (p₁ * p₂ * p₃)) :
    N ^ ((1 : ℝ) / 3) / 2 ≤ p₃ := by
  have hb := B2_cube_bound h1 h2 h3 h12 hp2 hn
  have hN0 : 0 ≤ N := by nlinarith [mul_pos (mul_pos h1 h2) h3]
  have hx : 0 ≤ N ^ ((1 : ℝ) / 3) / 2 := by positivity
  have hcube : (N ^ ((1 : ℝ) / 3) / 2) ^ 3 = N / 8 := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have : (N ^ ((1 : ℝ) / 3) / 2) ^ 3 ≤ p₃ ^ 3 := by rw [hcube]; linarith
  exact (pow_le_pow_iff_left₀ hx h3.le (by norm_num)).1 this

/-- **`B2_p3_large`:** with `a` such that `8 a³ < N`, `p₃ > a` on `B₂`. For `a = N^{1/3-δ₁}`
the condition is `N^{3δ₁} > 8`, `cube_lt`. -/
theorem B2_p3_large {p₁ p₂ p₃ a N : ℝ} (h1 : 0 < p₁) (h2 : 0 < p₂) (h3 : 0 < p₃)
    (h12 : p₁ ≤ p₂) (hp2 : p₁ * p₂ ^ 2 ≤ N) (hn : N ≤ 2 * (p₁ * p₂ * p₃))
    (ha : 8 * a ^ 3 < N) : a < p₃ := by
  have hb := B2_cube_bound h1 h2 h3 h12 hp2 hn
  by_contra hc
  push Not at hc
  have : p₃ ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ h3.le hc 3
  linarith

/-- `N^{3δ} > c` gives `c (N^{1/3-δ})³ < N`; with `c = 8` the size condition of `B2_p3_large`. -/
theorem cube_lt {N δ c : ℝ} (hN : 0 < N) (h : c < N ^ (3 * δ)) :
    c * (N ^ ((1 : ℝ) / 3 - δ)) ^ 3 < N := by
  have hc : (N ^ ((1 : ℝ) / 3 - δ)) ^ 3 = N ^ (1 - 3 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num; ring_nf
  rw [hc]
  have hsplit : N = N ^ (1 - 3 * δ) * N ^ (3 * δ) := by
    rw [← Real.rpow_add hN]; simp
  have hpos : 0 < N ^ (1 - 3 * δ) := Real.rpow_pos_of_pos hN _
  calc c * N ^ (1 - 3 * δ) < N ^ (3 * δ) * N ^ (1 - 3 * δ) :=
        mul_lt_mul_of_pos_right h hpos
    _ = N := by rw [mul_comm]; exact hsplit.symm

/-- Vacuity of `B2_p3_large`: `p₁ = p₂ = 2`, `p₃ = 3`, `N = 8`, `a = 0.9`:
`2 · 4 ≤ 8`, `8 ≤ 2 · 12`, `8 · 0.729 < 8`, and `0.9 < 3`. -/
theorem B2_p3_large_vacuity :
    (2 : ℝ) ≤ 2 ∧ (2 : ℝ) * 2 ^ 2 ≤ 8 ∧ (8 : ℝ) ≤ 2 * (2 * 2 * 3) ∧ 8 * (0.9 : ℝ) ^ 3 < 8 ∧
      (0.9 : ℝ) < 3 := by norm_num

/-- `B2_p3_large` needs the range `N ≤ 2 n`: `p₁ = p₂ = 2`, `p₃ = 1`, `N = 8`, `a = 0.9` meet
the other hypotheses, `2 · 4 = 8 > 2 · 4`, fails it, and still `a < p₃`; with `p₃ = 0.5` instead,
`N ≤ 2 n` fails and the conclusion `0.9 < 0.5` fails. -/
theorem B2_p3_large_needs_range :
    ¬ ((8 : ℝ) ≤ 2 * (2 * 2 * 0.5)) ∧ ¬ ((0.9 : ℝ) < 0.5) := by norm_num

/-! ### The count `S` and the sets `B₁`, `B₂` -/

/-- `S(n)`, the number of primes `p ∣ n` with `lo ≤ p ≤ a`, the sum in (3.11). -/
noncomputable def Scount (lo a : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ a)).card

/-- Membership in `B₁`, (3.1). -/
def InB1 (lo a N : ℝ) (n : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ n = p₁ * p₂ * p₃ ∧
    lo ≤ p₁ ∧ (p₁ : ℝ) < a ∧ a ≤ p₂ ∧ (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ N ∧ lo ≤ p₃

/-- Membership in `B₂`, (3.2). -/
def InB2 (lo a N : ℝ) (n : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ n = p₁ * p₂ * p₃ ∧
    a ≤ p₁ ∧ p₁ ≤ p₂ ∧ (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ N ∧ lo ≤ p₃

/-- Named hypothesis, not in the paper: the endpoint `a = N^{1/3-δ₁}` is not a prime. -/
def EndpointNotPrime (a : ℝ) : Prop := ∀ q : ℕ, q.Prime → (q : ℝ) ≠ a

private lemma mem_three {q p₁ p₂ p₃ : ℕ} (hq : q.Prime) (h1 : p₁.Prime) (h2 : p₂.Prime)
    (h3 : p₃.Prime) (hd : q ∣ p₁ * p₂ * p₃) : q = p₁ ∨ q = p₂ ∨ q = p₃ := by
  rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq h1).1 h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq h2).1 h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq h3).1 h))

private lemma cast_pos_prime {p : ℕ} (hp : p.Prime) : (0 : ℝ) < p := by
  exact_mod_cast hp.pos

/-- **`S = 1` on `B₁`**, CONDITIONAL on `EndpointNotPrime a`: for `n = p₁p₂p₃ ∈ B₁` with
`N ≤ 2 n` and `4 a³ ≤ N`, exactly `p₁` lies in `[lo, a]`. -/
theorem S_eq_one_B1 {lo a N : ℝ} {n : ℕ} (hB : InB1 lo a N n) (hn : N ≤ 2 * (n : ℝ))
    (ha : 4 * a ^ 3 ≤ N) (hE : EndpointNotPrime a) : Scount lo a n = 1 := by
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, rfl, hlo1, hp1a, hap2, hp2N, hlo3⟩ := hB
  have hap2' : a < p₂ := lt_of_le_of_ne hap2 (hE p₂ h2).symm
  have hn' : N ≤ 2 * ((p₁ : ℝ) * p₂ * p₃) := by push_cast at hn; exact hn
  have hap3 : a < p₃ := B1_p3_large (cast_pos_prime h1) (cast_pos_prime h2) (cast_pos_prime h3)
    hp1a hp2N hn' ha
  have hne : p₁ * p₂ * p₃ ≠ 0 := by
    have := h1.pos; have := h2.pos; have := h3.pos; positivity
  unfold Scount
  rw [Finset.card_eq_one]
  refine ⟨p₁, ?_⟩
  ext q
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hq, hd, -⟩, -, hqa⟩
    rcases mem_three hq h1 h2 h3 hd with rfl | rfl | rfl
    · rfl
    · exact absurd hqa (not_le.2 hap2')
    · exact absurd hqa (not_le.2 hap3)
  · rintro rfl
    exact ⟨⟨h1, ⟨p₂ * p₃, by ring⟩, hne⟩, hlo1, hp1a.le⟩

/-- **`S = 0` on `B₂`**, CONDITIONAL on `EndpointNotPrime a`: for `n = p₁p₂p₃ ∈ B₂` with
`N ≤ 2 n` and `8 a³ < N`, no prime factor lies in `[lo, a]`. -/
theorem S_eq_zero_B2 {lo a N : ℝ} {n : ℕ} (hB : InB2 lo a N n) (hn : N ≤ 2 * (n : ℝ))
    (ha : 8 * a ^ 3 < N) (hE : EndpointNotPrime a) : Scount lo a n = 0 := by
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, rfl, hap1, h12, hp2N, hlo3⟩ := hB
  have hap1' : a < p₁ := lt_of_le_of_ne hap1 (hE p₁ h1).symm
  have h12' : (p₁ : ℝ) ≤ p₂ := by exact_mod_cast h12
  have hn' : N ≤ 2 * ((p₁ : ℝ) * p₂ * p₃) := by push_cast at hn; exact hn
  have hap3 : a < p₃ := B2_p3_large (cast_pos_prime h1) (cast_pos_prime h2) (cast_pos_prime h3)
    h12' hp2N hn' ha
  unfold Scount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  simp only [Nat.mem_primeFactors] at hq
  rintro ⟨-, hqa⟩
  rcases mem_three hq.1 h1 h2 h3 hq.2.1 with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

/-- **`B₁` and `B₂` are disjoint** in the range `N ≤ 2 n`, `8 a³ < N`, no endpoint hypothesis
needed: an element of `B₁` has the prime factor `p₁ < a`, every prime factor of an element of
`B₂` is at least `a`. So `1_{B₁} = 1, 1_{B₂} = 0` on `B₁` and the reverse on `B₂`. -/
theorem B1_B2_disjoint {lo a N : ℝ} {n : ℕ} (h1 : InB1 lo a N n) (h2 : InB2 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 8 * a ^ 3 < N) : False := by
  obtain ⟨p₁, p₂, p₃, hp1, -, -, hn1, -, hp1a, -, -, -⟩ := h1
  obtain ⟨q₁, q₂, q₃, hq1, hq2, hq3, rfl, haq1, h12, hq2N, -⟩ := h2
  have h12' : (q₁ : ℝ) ≤ q₂ := by exact_mod_cast h12
  have hn' : N ≤ 2 * ((q₁ : ℝ) * q₂ * q₃) := by push_cast at hn; exact hn
  have haq3 : a < q₃ := B2_p3_large (cast_pos_prime hq1) (cast_pos_prime hq2)
    (cast_pos_prime hq3) h12' hq2N hn' ha
  have hd : p₁ ∣ q₁ * q₂ * q₃ := by rw [hn1]; exact ⟨p₂ * p₃, by ring⟩
  rcases mem_three hp1 hq1 hq2 hq3 hd with rfl | rfl | rfl
  · linarith
  · linarith
  · linarith

/-! ### Feeding `eq312printed_fails_B1` and `_B2` -/

/-- **(3.12) as printed fails on `B₁`**, CONDITIONAL on `EndpointNotPrime a`: at `n ∈ B₁` with
`r = r_Z(n)`, `Z ≥ 3`, `Z ≤ lo`, `S` from `S_eq_one_B1`, `1_{B₁} = 1`, `1_{B₂} = 0` by
`B1_B2_disjoint`, and `E'(n) = 0`, the value `e = 0` the Chain file fixes for squarefree `n`:
(3.11) has right side 0 and printed (3.12) has positive right side. -/
theorem eq312printed_fails_at_B1 {lo a N : ℝ} {n Z : ℕ} (hB : InB1 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 4 * a ^ 3 ≤ N) (hE : EndpointNotPrime a) (hZ : 3 ≤ Z)
    (hZlo : (Z : ℝ) ≤ lo) :
    rhs311 (rz Z n) (Scount lo a n) 1 0 0 = 0 ∧
      (0 : ℝ) < rhs312printed (rz Z n) (Scount lo a n) 1 0 0 := by
  rw [S_eq_one_B1 hB hn ha hE]
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, hn1, hlo1, hp1a, hap2, -, hlo3⟩ := hB
  have hrough : ∀ p, p.Prime → p < Z → ¬ p ∣ n := by
    intro p hp hpZ hd
    rw [hn1] at hd
    have hpZ' : (p : ℝ) < Z := by exact_mod_cast hpZ
    rcases mem_three hp h1 h2 h3 hd with rfl | rfl | rfl
    · linarith
    · linarith
    · linarith
  have hr := two_le_rz hZ hrough
  have := eq312printed_fails_B1 (r := rz Z n) (by linarith)
  simpa using this

/-- **(3.12) as printed fails on `B₂`**, CONDITIONAL on `EndpointNotPrime a`, as above with
`S = 0`, `1_{B₁} = 0`, `1_{B₂} = 1`. -/
theorem eq312printed_fails_at_B2 {lo a N : ℝ} {n Z : ℕ} (hB : InB2 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 8 * a ^ 3 < N) (hE : EndpointNotPrime a) (hZ : 3 ≤ Z)
    (hZlo : (Z : ℝ) ≤ lo) (hloa : lo ≤ a) :
    rhs311 (rz Z n) (Scount lo a n) 0 1 0 = 0 ∧
      (0 : ℝ) < rhs312printed (rz Z n) (Scount lo a n) 0 1 0 := by
  rw [S_eq_zero_B2 hB hn ha hE]
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, hn1, hap1, h12, -, hlo3⟩ := hB
  have h12' : (p₁ : ℝ) ≤ p₂ := by exact_mod_cast h12
  have hrough : ∀ p, p.Prime → p < Z → ¬ p ∣ n := by
    intro p hp hpZ hd
    rw [hn1] at hd
    have hpZ' : (p : ℝ) < Z := by exact_mod_cast hpZ
    rcases mem_three hp h1 h2 h3 hd with rfl | rfl | rfl
    · linarith
    · linarith
    · linarith
  have hr := two_le_rz hZ hrough
  have := eq312printed_fails_B2 (r := rz Z n) (by linarith)
  simpa using this

/-! ### Vacuity -/

/-- Vacuity of `InB1`, `S_eq_one_B1` and `EndpointNotPrime`: `n = 2 · 3 · 5 = 30`, `lo = 2`,
`a = 2.5`, `N = 60`: `2 ≤ 2 < 2.5 ≤ 3`, `2 · 9 ≤ 60`, `5 ≥ 2`, `60 ≤ 2 · 30`,
`4 · 2.5³ = 62.5`, too big, so `a = 2.4`: `4 · 13.824 = 55.296 ≤ 60`. `2.4` is not a prime. -/
theorem S_eq_one_B1_vacuity : InB1 2 2.4 60 30 ∧ EndpointNotPrime 2.4 ∧
    (60 : ℝ) ≤ 2 * ((30 : ℕ) : ℝ) ∧ 4 * (2.4 : ℝ) ^ 3 ≤ 60 ∧ Scount 2 2.4 30 = 1 := by
  have hB : InB1 2 2.4 60 30 :=
    ⟨2, 3, 5, Nat.prime_two, Nat.prime_three, Nat.prime_five, rfl, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num⟩
  have hE : EndpointNotPrime 2.4 := by
    intro q _ h
    have h1 : (2 : ℝ) < q := by rw [h]; norm_num
    have h2 : (q : ℝ) < 3 := by rw [h]; norm_num
    have : 2 < q := by exact_mod_cast h1
    have : q < 3 := by exact_mod_cast h2
    omega
  exact ⟨hB, hE, by norm_num, by norm_num, S_eq_one_B1 hB (by norm_num) (by norm_num) hE⟩

/-- Vacuity of `InB2` and `S_eq_zero_B2`: `n = 3 · 3 · 5 = 45`, `lo = 2`, `a = 1.5`, `N = 81`:
`1.5 ≤ 3 ≤ 3`, `3 · 9 = 27 ≤ 81`, `5 ≥ 2`, `81 ≤ 90`, `8 · 3.375 = 27 < 81`. -/
theorem S_eq_zero_B2_vacuity : InB2 2 1.5 81 45 ∧ Scount 2 1.5 45 = 0 := by
  have hB : InB2 2 1.5 81 45 :=
    ⟨3, 3, 5, Nat.prime_three, Nat.prime_three, Nat.prime_five, rfl, by norm_num, le_refl _,
      by norm_num, by norm_num⟩
  have hE : EndpointNotPrime 1.5 := by
    intro q _ h
    have h1 : (1 : ℝ) < q := by rw [h]; norm_num
    have h2 : (q : ℝ) < 2 := by rw [h]; norm_num
    have : 1 < q := by exact_mod_cast h1
    have : q < 2 := by exact_mod_cast h2
    omega
  exact ⟨hB, S_eq_zero_B2 hB (by norm_num) (by norm_num) hE⟩

/-- `EndpointNotPrime` cannot be dropped from `S_eq_one_B1`: with the prime `a = 3`,
`n = 2 · 3 · 11 = 66 ∈ B₁` for `lo = 2`, `N = 108`, all other hypotheses hold,
`108 ≤ 132`, `4 · 27 ≤ 108`, and `S = 2` since both 2 and 3 lie in `[2, 3]`. -/
theorem endpoint_needed : InB1 2 3 108 66 ∧ (108 : ℝ) ≤ 2 * ((66 : ℕ) : ℝ) ∧
    4 * (3 : ℝ) ^ 3 ≤ 108 ∧ Scount 2 3 66 = 2 := by
  refine ⟨⟨2, 3, 11, Nat.prime_two, Nat.prime_three, by norm_num, rfl, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, ?_⟩
  unfold Scount
  rw [show (66 : ℕ) = 2 * 3 * 11 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.prime_two.primeFactors,
    Nat.prime_three.primeFactors, (show Nat.Prime 11 by norm_num).primeFactors,
    Finset.filter_union, Finset.filter_union, Finset.filter_singleton, Finset.filter_singleton,
    Finset.filter_singleton]
  norm_num

end LeanLab.ChenPrimeExceptional.U1433

#print axioms LeanLab.ChenPrimeExceptional.U1433.B2_cube_bound
#print axioms LeanLab.ChenPrimeExceptional.U1433.B2_p3_ge
#print axioms LeanLab.ChenPrimeExceptional.U1433.B2_p3_large
#print axioms LeanLab.ChenPrimeExceptional.U1433.cube_lt
#print axioms LeanLab.ChenPrimeExceptional.U1433.B2_p3_large_vacuity
#print axioms LeanLab.ChenPrimeExceptional.U1433.B2_p3_large_needs_range
#print axioms LeanLab.ChenPrimeExceptional.U1433.S_eq_one_B1
#print axioms LeanLab.ChenPrimeExceptional.U1433.S_eq_zero_B2
#print axioms LeanLab.ChenPrimeExceptional.U1433.B1_B2_disjoint
#print axioms LeanLab.ChenPrimeExceptional.U1433.eq312printed_fails_at_B1
#print axioms LeanLab.ChenPrimeExceptional.U1433.eq312printed_fails_at_B2
#print axioms LeanLab.ChenPrimeExceptional.U1433.S_eq_one_B1_vacuity
#print axioms LeanLab.ChenPrimeExceptional.U1433.S_eq_zero_B2_vacuity
#print axioms LeanLab.ChenPrimeExceptional.U1433.endpoint_needed
