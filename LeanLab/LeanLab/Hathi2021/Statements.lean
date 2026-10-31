/-
P0080 S. Hathi, "Representation of even integers as a sum of squares of primes and
powers of two", arXiv 2109.13174.
Statements of Theorems 1.1 and 1.2, Lemma 3.1, the section 4 main inequality and Table 2,
the singular series factor κ(h) of display 2.4, with cheap links and kernel checks.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.
Cited results are `sorry`; everything else below is proved with zero sorry.
-/
import Mathlib

open Finset

namespace LeanLab.Hathi2021

/-! ### Representations -/

/-- `n` is four squares of primes plus exactly `k` powers of 2, each exponent at least 1.
The theorem statements do not fix the exponents; the proof uses `4 ≤ ν ≤ L`, plus at most
two even powers, so exponent at least 1 is implied. -/
def FourSqExact (k n : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ p₄ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₄.Prime ∧
    ∃ ν : Fin k → ℕ, (∀ i, 1 ≤ ν i) ∧ n = p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2 + ∑ i, 2 ^ ν i

/-- Four squares of primes plus at most `k` powers of 2. -/
def FourSqAtMost (k n : ℕ) : Prop := ∃ j, j ≤ k ∧ FourSqExact j n

/-- `n` is a prime plus two squares of primes plus exactly `k` powers of 2. -/
def OneTwoExact (k n : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
    ∃ ν : Fin k → ℕ, (∀ i, 1 ≤ ν i) ∧ n = p₁ + p₂ ^ 2 + p₃ ^ 2 + ∑ i, 2 ^ ν i

/-- A prime plus two squares of primes plus at most `k` powers of 2. -/
def OneTwoAtMost (k n : ℕ) : Prop := ∃ j, j ≤ k ∧ OneTwoExact j n

/-- Every sufficiently large even integer has `P`. -/
def AllLargeEven (P : ℕ → Prop) : Prop := ∃ N₀ : ℕ, ∀ n, Even n → N₀ ≤ n → P n

/-- Every sufficiently large odd integer has `P`. -/
def AllLargeOdd (P : ℕ → Prop) : Prop := ∃ N₀ : ℕ, ∀ n, Odd n → N₀ ≤ n → P n

/-! ### The paper, cited -/

/-- Theorem 1.1: every sufficiently large even integer is a sum of four squares of primes
and at most 31 powers of two. -/
def Theorem11 : Prop := AllLargeEven (FourSqAtMost 31)

theorem theorem_1_1 : Theorem11 := by sorry

/-- Theorem 1.2: every sufficiently large odd integer is a prime, two squares of primes and
at most 12 powers of two. -/
def Theorem12 : Prop := AllLargeOdd (OneTwoAtMost 12)

theorem theorem_1_2 : Theorem12 := by sorry

/-- Zhao 2014 as quoted in the abstract: the same as Theorem 1.1 with 46. -/
def Zhao46 : Prop := AllLargeEven (FourSqAtMost 46)

/-! ### Links -/

theorem fourSq_mono {k k' n : ℕ} (h : k ≤ k') (hn : FourSqAtMost k n) : FourSqAtMost k' n := by
  obtain ⟨j, hj, hn⟩ := hn; exact ⟨j, hj.trans h, hn⟩

theorem oneTwo_mono {k k' n : ℕ} (h : k ≤ k') (hn : OneTwoAtMost k n) : OneTwoAtMost k' n := by
  obtain ⟨j, hj, hn⟩ := hn; exact ⟨j, hj.trans h, hn⟩

/-- Theorem 1.1 implies Zhao's 46. -/
theorem zhao46_of_theorem11 (h : Theorem11) : Zhao46 := by
  obtain ⟨N₀, h⟩ := h; exact ⟨N₀, fun n he hn => fourSq_mono (by norm_num) (h n he hn)⟩

/-! ### Parity and the residue 4 mod 8 -/

theorem sq_mod_eight_of_odd {p : ℕ} (hp : Odd p) : p ^ 2 % 8 = 1 := by
  obtain ⟨m, rfl⟩ := hp
  have : (2 * m + 1) ^ 2 = 8 * (m * (m + 1) / 2) + 1 := by
    have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
    obtain ⟨t, ht⟩ := h2
    rw [ht, Nat.mul_div_cancel_left t (by norm_num)]
    nlinarith [ht]
  omega

/-- Four odd prime squares sum to 4 mod 8, the residue in Lemma 2.1. -/
theorem four_odd_sq_mod_eight {a b c d : ℕ} (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (hd : Odd d) : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 8 = 4 := by
  have := sq_mod_eight_of_odd ha; have := sq_mod_eight_of_odd hb
  have := sq_mod_eight_of_odd hc; have := sq_mod_eight_of_odd hd
  omega

/-- Four prime squares are at least 16, so "sufficiently large" is needed: no even `n < 16`
is represented. -/
theorem not_fourSq_lt_sixteen {k n : ℕ} (hn : n < 16) : ¬ FourSqExact k n := by
  rintro ⟨p₁, p₂, p₃, p₄, h₁, h₂, h₃, h₄, ν, -, rfl⟩
  have a := Nat.pow_le_pow_left h₁.two_le 2; have b := Nat.pow_le_pow_left h₂.two_le 2
  have c := Nat.pow_le_pow_left h₃.two_le 2; have d := Nat.pow_le_pow_left h₄.two_le 2
  omega

/-! ### Small ranges by binary digits, with every prime equal to 2 or 3 -/

/-- An even `m < 2^(k+1)` is a sum of exactly `j ≤ k` powers of two with exponents ≥ 1. -/
theorem even_sum_pow_two : ∀ k m : ℕ, Even m → m < 2 ^ (k + 1) →
    ∃ j, j ≤ k ∧ ∃ ν : Fin j → ℕ, (∀ i, 1 ≤ ν i) ∧ m = ∑ i, 2 ^ ν i
  | 0, m, he, hm => by
      refine ⟨0, le_rfl, Fin.elim0, fun i => i.elim0, ?_⟩
      obtain ⟨r, rfl⟩ := he; simp at hm ⊢; omega
  | k + 1, m, he, hm => by
      by_cases hlt : m < 2 ^ (k + 1)
      · obtain ⟨j, hj, ν, hν, h⟩ := even_sum_pow_two k m he hlt
        exact ⟨j, by omega, ν, hν, h⟩
      · push_neg at hlt
        have hpow : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
        have hev : Even (m - 2 ^ (k + 1)) := by
          have : Even (2 ^ (k + 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
          exact (Nat.even_sub hlt).mpr (by simp [he, this])
        obtain ⟨j, hj, ν, hν, h⟩ := even_sum_pow_two k (m - 2 ^ (k + 1)) hev (by omega)
        refine ⟨j + 1, by omega, Fin.cons (k + 1) ν, ?_, ?_⟩
        · intro i; refine Fin.cases (by simp) (fun i => by simpa using hν i) i
        · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; omega

/-- Every even `n` with `16 ≤ n < 2^32 + 16` is four prime squares, all `2²`, plus at most
31 powers of two. Theorem 1.1 is content only beyond this range. -/
theorem fourSq_small {n : ℕ} (he : Even n) (h1 : 16 ≤ n) (h2 : n < 2 ^ 32 + 16) :
    FourSqAtMost 31 n := by
  have hev : Even (n - 16) := (Nat.even_sub h1).mpr (by simp [he]; decide)
  obtain ⟨j, hj, ν, hν, h⟩ := even_sum_pow_two 31 (n - 16) hev (by omega)
  exact ⟨j, hj, 2, 2, 2, 2, Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
    ν, hν, by omega⟩

/-- Every odd `n` with `11 ≤ n < 2^13 + 11` is `3 + 2² + 2²` plus at most 12 powers of two.
Theorem 1.2 is content only beyond this range. -/
theorem oneTwo_small {n : ℕ} (ho : Odd n) (h1 : 11 ≤ n) (h2 : n < 2 ^ 13 + 11) :
    OneTwoAtMost 12 n := by
  have hev : Even (n - 11) := by
    obtain ⟨r, rfl⟩ := ho; exact ⟨r - 5, by omega⟩
  obtain ⟨j, hj, ν, hν, h⟩ := even_sum_pow_two 12 (n - 11) hev (by omega)
  exact ⟨j, hj, 3, 2, 2, Nat.prime_three, Nat.prime_two, Nat.prime_two, ν, hν, by omega⟩

/-! ### Lemma 3.1, the section 4 inequality and Table 2 -/

/-- Lemma 3.1, the printed upper bounds for `c_{0,l}`, `1 ≤ l ≤ 8`. -/
def c0 : ℕ → ℚ
  | 1 => 1127 / 1000
  | 2 => 803 / 1000
  | 3 => 782 / 1000
  | 4 => 779 / 1000
  | 5 => 7773 / 10000
  | 6 => 7772 / 10000
  | 7 => 77708 / 100000
  | 8 => 77707 / 100000
  | _ => 0

/-- `λ₀ = 0.8844473`, from Table 1(A) of the paper's reference 33. -/
def lam0 : ℚ := 8844473 / 10000000

/-- The leading coefficient of the section 4 lower bound
`R ≥ 8 N L^{k'} (0.9 J(1) − λ₀^{k'−2l} (11 + ε) c_{0,l} (1 + O(η)) J(0))`,
in the limit `ε = 0`, `J(0) = J(1)`; the paper has `J(1) ≤ J(0) ≤ (1 + O(η)) J(1)`, and
`margin_l5_robust` covers the slack. Its positivity is the criterion behind Table 2. -/
def margin (l k' : ℕ) : ℚ := 9 / 10 - lam0 ^ (k' - 2 * l) * 11 * c0 l

/-- Table 2: the least `k'` with positive margin, for `l = 5, 6, 7, 8`. -/
theorem table2_l5 : 0 < margin 5 29 ∧ margin 5 28 < 0 := by
  unfold margin c0 lam0; norm_num
theorem table2_l6 : 0 < margin 6 31 ∧ margin 6 30 < 0 := by
  unfold margin c0 lam0; norm_num
theorem table2_l7 : 0 < margin 7 33 ∧ margin 7 32 < 0 := by
  unfold margin c0 lam0; norm_num
theorem table2_l8 : 0 < margin 8 35 ∧ margin 8 34 < 0 := by
  unfold margin c0 lam0; norm_num

/-- The same criterion at `l = 4` would give `k' = 27`; Lemma 2.2 needs `l ≥ 5`, which is
why `l = 5` is optimal among admissible `l`. -/
theorem margin_l4 : 0 < margin 4 27 ∧ margin 4 26 < 0 := by
  unfold margin c0 lam0; norm_num

/-- The margin at `l = 5, k' = 29` survives a small `ε` and the `J(0)/J(1)` loss: it stays
positive with `11.001` in place of `11` and `J(0) ≤ 1.001 J(1)`. -/
theorem margin_l5_robust : 0 < 9 / 10 - lam0 ^ 19 * (11001 / 1000) * c0 5 * (1001 / 1000) := by
  unfold c0 lam0; norm_num

/-- Lemma 3.1 values decrease in `l`. -/
theorem c0_antitone : ∀ l ∈ Icc 1 7, c0 (l + 1) < c0 l := by
  intro l hl; simp only [Finset.mem_Icc] at hl; obtain ⟨h1, h2⟩ := hl
  interval_cases l <;> simp only [c0] <;> norm_num

/-- The section 4 count: `k = k' + 2` with `k' = 29` gives the 31 of Theorem 1.1. -/
theorem k_of_kprime : 29 + 2 = 31 := rfl

/-! ### The step `k = k' + 2`: at most two powers of two reach the class 4 mod 8 -/

/-- Every even `n ≥ 6` has `n − s ≡ 4 (mod 8)` with `s` a sum of at most two powers of
two with exponents ≥ 1 and `s ≤ 6`. -/
theorem two_powers_to_four_mod_eight {n : ℕ} (he : Even n) (h6 : 6 ≤ n) :
    ∃ j, j ≤ 2 ∧ ∃ ν : Fin j → ℕ, (∀ i, 1 ≤ ν i) ∧ ∑ i, 2 ^ ν i ≤ 6 ∧
      (n - ∑ i, 2 ^ ν i) % 8 = 4 := by
  obtain ⟨r, rfl⟩ := he
  have : (r + r) % 8 = 0 ∨ (r + r) % 8 = 2 ∨ (r + r) % 8 = 4 ∨ (r + r) % 8 = 6 := by omega
  rcases this with h | h | h | h
  · exact ⟨1, by norm_num, ![2], by intro i; fin_cases i; simp, by simp, by simp; omega⟩
  · exact ⟨2, le_rfl, ![1, 2], by intro i; fin_cases i <;> simp, by simp [Fin.sum_univ_two],
      by simp [Fin.sum_univ_two]; omega⟩
  · exact ⟨0, by norm_num, Fin.elim0, fun i => i.elim0, by simp, by simp; omega⟩
  · exact ⟨1, by norm_num, ![1], by intro i; fin_cases i; simp, by simp, by simp; omega⟩

/-- Adding exactly `j` powers of two to a `FourSqExact k` representation. -/
theorem fourSqExact_add {k j m : ℕ} (hm : FourSqExact k m) (μ : Fin j → ℕ)
    (hμ : ∀ i, 1 ≤ μ i) : FourSqExact (k + j) (m + ∑ i, 2 ^ μ i) := by
  obtain ⟨p₁, p₂, p₃, p₄, h₁, h₂, h₃, h₄, ν, hν, rfl⟩ := hm
  refine ⟨p₁, p₂, p₃, p₄, h₁, h₂, h₃, h₄, Fin.append ν μ, ?_, ?_⟩
  · intro i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hν i
    · simpa using hμ i
  · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]; ring

/-- The class 4 mod 8 case with `k'` powers gives every large even integer with `k' + 2`:
the reduction of section 4, proved. -/
theorem allEven_of_fourMod8 {k' : ℕ}
    (h : ∃ N₀ : ℕ, ∀ n, n % 8 = 4 → N₀ ≤ n → FourSqAtMost k' n) :
    AllLargeEven (FourSqAtMost (k' + 2)) := by
  obtain ⟨N₀, h⟩ := h
  refine ⟨N₀ + 6, fun n he hn => ?_⟩
  obtain ⟨j, hj, μ, hμ, hs, hmod⟩ := two_powers_to_four_mod_eight he (by omega)
  obtain ⟨i, hi, hrep⟩ := h (n - ∑ t, 2 ^ μ t) hmod (by omega)
  have := fourSqExact_add hrep μ hμ
  rw [Nat.sub_add_cancel (by omega)] at this
  exact ⟨i + j, by omega, this⟩

/-- Theorem 1.1 from the class 4 mod 8 statement with 29 powers, the paper's `k' = 29`. -/
theorem theorem11_of_fourMod8_29
    (h : ∃ N₀ : ℕ, ∀ n, n % 8 = 4 → N₀ ≤ n → FourSqAtMost 29 n) : Theorem11 :=
  allEven_of_fourMod8 h

/-! ### The local factor κ(h), display 2.4 -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `κ(h)`: 0 if `3 ∤ h`; `15 (5 − 3 (h/5)) / 32` if `3 ∣ h`, `5 ∤ h`; `45/8` if `15 ∣ h`. -/
def kappa (h : ℤ) : ℚ :=
  if ¬ (3 : ℤ) ∣ h then 0
  else if (5 : ℤ) ∣ h then 45 / 8
  else 15 * (5 - 3 * (legendreSym 5 h : ℚ)) / 32

theorem legendre5_sq (h : ℤ) (h5 : ¬ (5 : ℤ) ∣ h) :
    legendreSym 5 h = 1 ∨ legendreSym 5 h = -1 := by
  have : (h : ZMod 5) ≠ 0 := by
    intro h0; apply h5; exact (ZMod.intCast_zmod_eq_zero_iff_dvd h 5).mp h0
  exact legendreSym.eq_one_or_neg_one 5 this

/-- The values of κ when `3 ∣ h`, `5 ∤ h`: `15/16` or `15/4`. -/
theorem kappa_values (h : ℤ) (h3 : (3 : ℤ) ∣ h) (h5 : ¬ (5 : ℤ) ∣ h) :
    kappa h = 15 / 16 ∨ kappa h = 15 / 4 := by
  unfold kappa; rw [if_neg (not_not.mpr h3), if_neg h5]
  rcases legendre5_sq h h5 with e | e <;> rw [e] <;> norm_num

/-- κ is nonnegative and at most `45/8`. -/
theorem kappa_bounds (h : ℤ) : 0 ≤ kappa h ∧ kappa h ≤ 45 / 8 := by
  by_cases h3 : (3 : ℤ) ∣ h
  · by_cases h5 : (5 : ℤ) ∣ h
    · unfold kappa; rw [if_neg (not_not.mpr h3), if_pos h5]; norm_num
    · rcases kappa_values h h3 h5 with e | e <;> rw [e] <;> norm_num
  · unfold kappa; rw [if_pos h3]; norm_num

end LeanLab.Hathi2021
