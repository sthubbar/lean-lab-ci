/-
P0039 L. Grimmelt, J. Teräväinen, The Exceptional Set in Goldbach's Problem with two Chen
Primes, arXiv 2508.16400v2 of 2026-07-29, copy papers/P0039.pdf. Unit U-6790, CLOUD
20261021T0117Z-cloud55. AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.

The elementary parts of the paper, all unconditional:
* Definition 2.1, p.8: the exponent hierarchy of the parameters, exactly for `0 < δ₁ < 1/200`.
* Remark 8.2, p.65, and the exceptional case exponent of the proof of Proposition 7.11, p.64.
* Lemma 3.2, p.12: the vector sieve inequality.
* (2.1), p.10: the local factors of the singular series.
-/
import Mathlib

open Finset

namespace LeanLab.ExceptionalSet.GT2025

/-! ### Definition 2.1, p.8

`D_{M,1} = N^{1/3-δ₁}, D_{M,2} = N^{1/6-δ₁}, D₁ = N^{δ₁³/100}, P₀ = N^{δ₁}, P₁ = N^{δ₁⁴},
R₀ = N^{δ₁³}, R₁ = N^{δ₁⁴/100}, R̃ = N^{2δ₁⁵}`, with the hierarchy
`D_{M,1} ≥ D_{M,2} ≥ P₀ ≥ R₀ ≫ D₁ ≥ P₁ ≫ R₁ ≥ R̃`. We record the exponents and show that the
strict exponent hierarchy holds exactly when `0 < δ₁ < 1/200`. -/


/-- The strict exponent hierarchy of Definition 2.1. -/
def StrictHierarchy (δ : ℝ) : Prop :=
  1 / 6 - δ < 1 / 3 - δ ∧ δ < 1 / 6 - δ ∧ δ ^ 3 < δ ∧ δ ^ 3 / 100 < δ ^ 3 ∧
    δ ^ 4 < δ ^ 3 / 100 ∧ δ ^ 4 / 100 < δ ^ 4 ∧ 2 * δ ^ 5 < δ ^ 4 / 100

/-- **Definition 2.1 hierarchy, p.8.** For `δ₁ > 0` the exponents are strictly ordered exactly
when `δ₁ < 1/200`; the binding comparisons are `D₁ ≥ P₁`, needing `δ₁ < 1/100`, and
`R₁ ≥ R̃`, needing `δ₁ < 1/200`. -/
theorem strictHierarchy_iff {δ : ℝ} (hδ : 0 < δ) : StrictHierarchy δ ↔ δ < 1 / 200 := by
  have h3 : 0 < δ ^ 3 := by positivity
  have h4 : 0 < δ ^ 4 := by positivity
  constructor
  · rintro ⟨-, -, -, -, -, -, h⟩
    have : δ ^ 4 * (200 * δ) < δ ^ 4 * 1 := by nlinarith
    have := lt_of_mul_lt_mul_left this h4.le
    linarith
  · intro h
    have hδ1 : δ < 1 := by linarith
    refine ⟨by linarith, by linarith, ?_, by linarith, ?_, by linarith, ?_⟩
    · have : δ ^ 3 < δ ^ 1 := pow_lt_pow_right_of_lt_one₀ hδ hδ1 (by norm_num)
      simpa using this
    · have : δ ^ 4 = δ ^ 3 * δ := by ring
      rw [this]; nlinarith
    · have : δ ^ 5 = δ ^ 4 * δ := by ring
      rw [this]; nlinarith

/-- Vacuity: the hierarchy is satisfiable, at `δ₁ = 1/201`. -/
theorem strictHierarchy_vacuity : StrictHierarchy (1 / 201) :=
  (strictHierarchy_iff (by norm_num)).2 (by norm_num)

/-- Sharpness: the hierarchy fails at `δ₁ = 1/200`. -/
theorem not_strictHierarchy_200 : ¬ StrictHierarchy (1 / 200) := fun h =>
  absurd ((strictHierarchy_iff (by norm_num)).1 h) (by norm_num)

/-- **Remark 8.2, p.65:** `D₁ ≪ R₀^{1/3}`, as exponents `δ₁³/100 ≤ δ₁³/3`. -/
theorem remark82_D1_R0 {δ : ℝ} (hδ : 0 < δ) : δ ^ 3 / 100 < δ ^ 3 / 3 := by
  have : 0 < δ ^ 3 := by positivity
  linarith

/-- **Proof of Proposition 7.11, p.64:** the exponent of `R̃² D₁ N R₀^{-1/3}` is
`1 + 4δ₁⁵ + δ₁³/100 - δ₁³/3`, and it is at most `1 - δ₁³/4` exactly when
`δ₁² ≤ 11/600`. -/
theorem exceptional_exponent_iff {δ : ℝ} (hδ : 0 < δ) :
    1 + 4 * δ ^ 5 + δ ^ 3 / 100 - δ ^ 3 / 3 ≤ 1 - δ ^ 3 / 4 ↔ δ ^ 2 ≤ 11 / 600 := by
  have h3 : 0 < δ ^ 3 := by positivity
  have key : (1 - δ ^ 3 / 4) - (1 + 4 * δ ^ 5 + δ ^ 3 / 100 - δ ^ 3 / 3) =
      4 * δ ^ 3 * (11 / 600 - δ ^ 2) := by ring
  constructor
  · intro h
    by_contra hc
    have : 4 * δ ^ 3 * (11 / 600 - δ ^ 2) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by linarith)
    linarith
  · intro h
    have : 0 ≤ 4 * δ ^ 3 * (11 / 600 - δ ^ 2) := by
      apply mul_nonneg (by positivity); linarith
    linarith

/-- In the range of Definition 2.1 the exceptional case exponent holds. -/
theorem exceptional_exponent {δ : ℝ} (hδ : 0 < δ) (h : δ < 1 / 200) :
    1 + 4 * δ ^ 5 + δ ^ 3 / 100 - δ ^ 3 / 3 ≤ 1 - δ ^ 3 / 4 :=
  (exceptional_exponent_iff hδ).2 (by nlinarith)

/-- **Theorem 1.2 hypotheses at `P = P₀, R = R₀`, p.5 and p.65:** `R₀⁴⁰ ≤ P₀ ≤ N^{1/5}` as
exponents `40 δ₁³ ≤ δ₁ ≤ 1/5`, true for `0 < δ₁ < 1/200`. -/
theorem thm12_range {δ : ℝ} (hδ : 0 < δ) (h : δ < 1 / 200) : 40 * δ ^ 3 ≤ δ ∧ δ ≤ 1 / 5 := by
  refine ⟨?_, by linarith⟩
  have : δ ^ 3 = δ * δ ^ 2 := by ring
  rw [this]
  have : δ ^ 2 ≤ 1 / 40 := by nlinarith
  nlinarith

/-- The Mertens ratio behind the constant `3/5` of Proposition 3.4, p.17:
`log N^{1/10} / log N^{1/6} = 3/5`. -/
theorem mertens_ratio : ((1 : ℝ) / 10) / (1 / 6) = 3 / 5 := by norm_num

/-! ### Lemma 3.2, p.12, vector sieve inequality -/

/-- **Lemma 3.2 (vector sieve inequality), p.12.** If `A, B⁺ ≥ 0`, `B⁻ ≤ B ≤ B⁺` and
`A⁻ ≤ A ≤ A⁺`, then `A⁺ B⁻ + (A⁻ - A⁺) B⁺ ≤ A B`. -/
theorem vector_sieve {A B Ap Am Bp Bm : ℝ} (hA : 0 ≤ A) (hBp : 0 ≤ Bp)
    (hBm : Bm ≤ B) (hB : B ≤ Bp) (hAm : Am ≤ A) (hAp : A ≤ Ap) :
    Ap * Bm + (Am - Ap) * Bp ≤ A * B := by
  nlinarith [mul_le_mul_of_nonneg_left hBm hA, mul_le_mul_of_nonneg_right hAm hBp,
    mul_le_mul_of_nonneg_right hAp (sub_nonneg.2 (hBm.trans hB)), mul_nonneg hA hBp]

/-- Vacuity of Lemma 3.2: an instance with every hypothesis strict and a strict conclusion. -/
theorem vector_sieve_vacuity :
    (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 2 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 ∧ (1 / 2 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 ∧
      (3 / 2 : ℝ) * 0 + (1 / 2 - 3 / 2) * 2 < 1 * 1 := by norm_num

/-- The hypothesis `A ≥ 0` of Lemma 3.2 cannot be dropped: `A = -1`, `B = 0`, `B⁻ = -1`,
`B⁺ = 1`, `A⁻ = A⁺ = -1` meets the other hypotheses and breaks the conclusion. -/
theorem vector_sieve_needs_A_nonneg :
    ¬ ((-1 : ℝ) * (-1) + ((-1) - (-1)) * 1 ≤ (-1) * 0) := by norm_num

/-- The hypothesis `B⁺ ≥ 0` cannot be dropped: `A = 1`, `A⁻ = 0`, `A⁺ = 1`,
`B = B⁻ = B⁺ = -1`. -/
theorem vector_sieve_needs_Bp_nonneg :
    ¬ ((1 : ℝ) * (-1) + (0 - 1) * (-1) ≤ 1 * (-1)) := by norm_num

/-! ### (2.1), p.10, the singular series -/

/-- The generic local factor of (2.1): `1 - (6p² - 4p + 1)/(p - 1)⁴ = p³ (p - 4)/(p - 1)⁴`.
This is the density of `n` mod `p` with `n, n + 2, m - n, m - n + 2` all units, `p - 4` of
`p` classes when `p ∤ m(m+2)(m+4)`, normalised by `(1 - 1/p)^{-4}`. -/
theorem local_factor_identity (p : ℝ) : (p - 1) ^ 4 - (6 * p ^ 2 - 4 * p + 1) = p ^ 3 * (p - 4) := by
  ring

/-- The generic local factor equals `(p - 4)/p · (p/(p - 1))⁴`. -/
theorem local_factor_eq {p : ℝ} (hp : 5 ≤ p) :
    1 - (6 * p ^ 2 - 4 * p + 1) / (p - 1) ^ 4 = (p - 4) / p * (p / (p - 1)) ^ 4 := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h0 : p ≠ 0 := by linarith
  field_simp
  ring

/-- Every generic local factor of (2.1) lies in `(0, 1)` for `p ≥ 5`. -/
theorem local_factor_pos {p : ℝ} (hp : 5 ≤ p) :
    0 < 1 - (6 * p ^ 2 - 4 * p + 1) / (p - 1) ^ 4 ∧ 1 - (6 * p ^ 2 - 4 * p + 1) / (p - 1) ^ 4 < 1 := by
  have h4 : 0 < (p - 1) ^ 4 := by have : 0 < p - 1 := by linarith
                                  positivity
  have hnum : 0 < 6 * p ^ 2 - 4 * p + 1 := by nlinarith
  constructor
  · rw [sub_pos, div_lt_one h4]
    have := local_factor_identity p
    have : 0 < p ^ 3 * (p - 4) := by
      apply mul_pos (by positivity); linarith
    linarith
  · have : 0 < (6 * p ^ 2 - 4 * p + 1) / (p - 1) ^ 4 := div_pos hnum h4
    linarith

/-- The correction factors of (2.1) are at least 1 for `p ≥ 5`. -/
theorem correction_factors_ge_one {p : ℝ} (hp : 5 ≤ p) :
    1 ≤ 1 + 1 / (p - 4) ∧ 1 ≤ 1 + 2 / (p - 4) := by
  have : 0 < p - 4 := by linarith
  have h1 := div_pos (by norm_num : (0:ℝ) < 1) this
  have h2 := div_pos (by norm_num : (0:ℝ) < 2) this
  constructor <;> linarith

/-- Number of residues `n` mod `p` with `n, n + 2, m - n, m - n + 2` all nonzero mod `p`. -/
def localCount (p m : ℕ) : ℕ :=
  #{n ∈ range p | n % p ≠ 0 ∧ (n + 2) % p ≠ 0 ∧ (m + p * p - n) % p ≠ 0 ∧
    (m + p * p - n + 2) % p ≠ 0}

/-- **The local factors at 2 and 3 of (2.1).** For `m ≡ 4 mod 6` exactly one class mod 2 and
one class mod 3 survive, so the factors are `(1/2) 2⁴ = 8` and `(1/3) (3/2)⁴ = 27/16`, with
product the `27/2` of (2.1). -/
theorem localCount_two_three : ∀ r < 6, (localCount 2 r * localCount 3 r ≠ 0 ↔ r = 4) := by
  decide

theorem localCount_four : localCount 2 4 = 1 ∧ localCount 3 4 = 1 := by decide

theorem localCount_periodic (p m : ℕ) : localCount p m = localCount p (m % p) := by
  unfold localCount
  congr 1
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_range] at hn
  have hm := Nat.mod_add_div m p
  have e1 : (m + p * p - n) % p = (m % p + p * p - n) % p := by
    have : m + p * p - n = (m % p + p * p - n) + p * (m / p) := by
      have : n ≤ p * p := by nlinarith
      omega
    rw [this, Nat.add_mul_mod_self_left]
  have e2 : (m + p * p - n + 2) % p = (m % p + p * p - n + 2) % p := by
    have : m + p * p - n + 2 = (m % p + p * p - n + 2) + p * (m / p) := by
      have : n ≤ p * p := by nlinarith
      omega
    rw [this, Nat.add_mul_mod_self_left]
  rw [e1, e2]

/-- The 2-adic and 3-adic factors vanish off `m ≡ 4 mod 6`: in the Cramér model the classes
0, 2 mod 6 get no representations, matching the indicator in (2.1). -/
theorem singular_zero_off_four (m : ℕ) (h : m % 6 ≠ 4) :
    localCount 2 m * localCount 3 m = 0 := by
  rw [localCount_periodic 2 m, localCount_periodic 3 m]
  have h6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have e2 : m % 2 = m % 6 % 2 := by omega
  have e3 : m % 3 = m % 6 % 3 := by omega
  rw [e2, e3]
  have := (localCount_two_three (m % 6) h6)
  have k2 : localCount 2 (m % 6 % 2) = localCount 2 (m % 6) := (localCount_periodic 2 _).symm
  have k3 : localCount 3 (m % 6 % 3) = localCount 3 (m % 6) := (localCount_periodic 3 _).symm
  rw [k2, k3]
  by_contra hc
  exact h (this.1 hc)

/-- `(1/2)·2⁴ · (1/3)·(3/2)⁴ = 27/2`, the constant of (2.1). -/
theorem two_three_constant : ((1 : ℚ) / 2 * 2 ^ 4) * ((1 : ℚ) / 3 * (3 / 2) ^ 4) = 27 / 2 := by
  norm_num

end LeanLab.ExceptionalSet.GT2025
