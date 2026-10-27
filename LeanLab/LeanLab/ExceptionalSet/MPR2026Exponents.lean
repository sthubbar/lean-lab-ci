/-
Maynard, Pandey, Radziwiłł, "Exponential sums over primes", arXiv 2608.14777v1, 14 Aug 2026,
read in full in Chrome by PC run 20261019T2003Z-20508, unit U-1110, idea I-0082. Not one of the
100 catalogued papers: it is the minor arc input, 19/24, of Pintz-Althöfer's 7/12, I-0080.

Theorem 1.1, cited, not proved: for `α = a/q + ε`, `(a, q) = 1`, `q ≤ N^{1/2}`,
`|ε| ≤ 1/(q N^{1/2})`, `B = max(q, qN|ε|)`: `|Σ_{n<N} Λ(n) e(nα)| ≤ N^{o(1)} (N/B^{1/2} + N^{19/24})`.

PROVED here, every exponent step of the paper, in log_x units: lengths `M_i = x^{m_i}`,
`qT = x^Q`, large value levels `σ_i`, `x^σ = Π M_i^{σ_i}`:
* `lemma37_case1` to `lemma37_case8`: the eight cases of Lemma 3.7, each weighted geometric
  mean and, in Cases 5 to 8, its combination with (3.2), bounded by `1 − σ` or by
  `7/8 Q + 29/48 − σ` over the whole region `x^{5/12} ≥ M1 ≥ M2 ≥ M3² ≥ x^{1/3}`,
  `x^{5/12} < qT ≤ x^{1/2}`.
* `lemma32_k5`: Lemma 3.2 for k = 5, the case the proof reduces to.
* crossings: Lemma 3.5, Lemma 3.9, Lemma 4.1, Section 2's 67/84, the introduction's 29/60.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.MPR2026

/-- The Lemma 3.7 region, in log_x units. -/
structure Region (m1 m2 m3 Q : ℝ) : Prop where
  h1 : m1 ≤ 5 / 12
  h2 : m2 ≤ m1
  h3 : 2 * m3 ≤ m2
  h4 : 1 / 3 ≤ 2 * m3
  hsum : m1 + m2 + m3 = 1
  hQ1 : 5 / 12 < Q
  hQ2 : Q ≤ 1 / 2

/-- `σ = Σ σ_i m_i ≤ 1` from `σ_i ≤ 1`. -/
theorem sigma_le_one {m1 m2 m3 Q s1 s2 s3 : ℝ} (R : Region m1 m2 m3 Q)
    (hs1 : s1 ≤ 1) (hs2 : s2 ≤ 1) (hs3 : s3 ≤ 1) : s1 * m1 + s2 * m2 + s3 * m3 ≤ 1 := by
  have := R.h1; have := R.h2; have := R.h3; have := R.h4; have := R.hsum
  have hm3 : 0 ≤ m3 := by linarith
  have hm2 : 0 ≤ m2 := by linarith
  have hm1 : 0 ≤ m1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hs1 hm1, mul_le_mul_of_nonneg_right hs2 hm2,
    mul_le_mul_of_nonneg_right hs3 hm3]

/-- (3.2): the 2/5, 2/5, 1/5 mean of the mean value bounds is `Q + (2 − 4σ)/5`. -/
theorem eq32 (m1 m2 m3 Q s1 s2 s3 : ℝ) (hsum : m1 + m2 + m3 = 1) :
    Q + 2 / 5 * ((1 - 2 * s1) * m1) + 2 / 5 * ((1 - 2 * s2) * m2) + 1 / 5 * ((2 - 4 * s3) * m3)
      = Q + (2 - 4 * (s1 * m1 + s2 * m2 + s3 * m3)) / 5 := by
  have : m3 = 1 - m1 - m2 := by linarith
  subst this; ring

section cases
variable {m1 m2 m3 Q s1 s2 s3 : ℝ}

/-- Lemma 3.7, Case 1. -/
theorem lemma37_case1 (R : Region m1 m2 m3 Q) (hs1 : s1 ≤ 1) (hs2 : s2 ≤ 1) (hs3 : s3 ≤ 1) :
    2 / 5 * ((2 - 2 * s1) * m1) + 2 / 5 * ((2 - 2 * s2) * m2) + 1 / 5 * ((4 - 4 * s3) * m3)
      ≤ 1 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have hs := sigma_le_one R hs1 hs2 hs3
  have := R.hsum
  nlinarith

/-- Lemma 3.7, Case 2. -/
theorem lemma37_case2 (R : Region m1 m2 m3 Q) (hs1 : s1 ≤ 1) (hs2 : s2 ≤ 1) (hs3 : s3 ≤ 1) :
    4 / 9 * ((2 - 2 * s1) * m1) + 4 / 9 * ((2 - 2 * s2) * m2)
      + 1 / 9 * (Q / 2 + 5 / 12 + (4 - 8 * s3) * m3) ≤ 1 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have hs := sigma_le_one R hs1 hs2 hs3
  have := R.hsum; have := R.hQ2; have := R.h4
  nlinarith

/-- Lemma 3.7, Case 3. -/
theorem lemma37_case3 (R : Region m1 m2 m3 Q) :
    1 / 2 * ((2 - 2 * s1) * m1) + 1 / 4 * (Q / 2 + 5 / 12 + (2 - 4 * s2) * m2)
      + 1 / 4 * ((4 - 4 * s3) * m3) ≤ 1 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have := R.hsum; have := R.hQ2; have := R.h3; have := R.h4
  nlinarith

/-- Lemma 3.7, Case 4. -/
theorem lemma37_case4 (R : Region m1 m2 m3 Q) :
    1 / 4 * (Q / 2 + 5 / 12 + (2 - 4 * s1) * m1) + 1 / 2 * ((2 - 2 * s2) * m2)
      + 1 / 4 * ((4 - 4 * s3) * m3) ≤ 1 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have := R.hsum; have := R.hQ2; have := R.h2; have := R.h3; have := R.h4
  nlinarith

/-- Lemma 3.7, Case 5, the 1/3 mean combined with (3.2) at weights 5/8 and 3/8. -/
theorem lemma37_case5 (R : Region m1 m2 m3 Q) :
    5 / 8 * (Q + (2 - 4 * (s1 * m1 + s2 * m2 + s3 * m3)) / 5)
      + 3 / 8 * (1 / 3 * (Q / 2 + 5 / 12 + (2 - 4 * s1) * m1)
        + 1 / 3 * (Q / 2 + 5 / 12 + (2 - 4 * s2) * m2) + 1 / 3 * ((4 - 4 * s3) * m3))
      ≤ 7 / 8 * Q + 29 / 48 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have := R.hsum; have := R.hQ1; have := R.h1; have := R.h2; have := R.h3
  nlinarith

/-- Lemma 3.7, Case 6, combined with (3.2) at weights 5/12 and 7/12. -/
theorem lemma37_case6 (R : Region m1 m2 m3 Q) :
    5 / 12 * (Q + (2 - 4 * (s1 * m1 + s2 * m2 + s3 * m3)) / 5)
      + 7 / 12 * (4 / 7 * ((2 - 2 * s1) * m1) + 2 / 7 * (Q / 2 + 5 / 12 + (2 - 4 * s2) * m2)
        + 1 / 7 * (Q / 2 + 5 / 12 + (4 - 8 * s3) * m3))
      ≤ 7 / 8 * Q + 29 / 48 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have := R.hsum; have := R.hQ1; have := R.h1
  nlinarith

/-- Lemma 3.7, Case 7, Case 6 with `M1` and `M2` interchanged. -/
theorem lemma37_case7 (R : Region m1 m2 m3 Q) :
    5 / 12 * (Q + (2 - 4 * (s1 * m1 + s2 * m2 + s3 * m3)) / 5)
      + 7 / 12 * (2 / 7 * (Q / 2 + 5 / 12 + (2 - 4 * s1) * m1) + 4 / 7 * ((2 - 2 * s2) * m2)
        + 1 / 7 * (Q / 2 + 5 / 12 + (4 - 8 * s3) * m3))
      ≤ 7 / 8 * Q + 29 / 48 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have := R.hsum; have := R.hQ1; have := R.h1; have := R.h2
  nlinarith

/-- Lemma 3.7, Case 8, combined with (3.2) at weights 3/4 and 1/4; equality. -/
theorem lemma37_case8 (R : Region m1 m2 m3 Q) :
    3 / 4 * (Q + (2 - 4 * (s1 * m1 + s2 * m2 + s3 * m3)) / 5)
      + 1 / 4 * (Q / 2 + 5 / 12 + (2 / 5 * ((2 - 4 * s1) * m1) + 2 / 5 * ((2 - 4 * s2) * m2)
        + 1 / 5 * ((4 - 8 * s3) * m3)))
      = 7 / 8 * Q + 29 / 48 - (s1 * m1 + s2 * m2 + s3 * m3) := by
  have h := R.hsum
  have : m3 = 1 - m1 - m2 := by linarith
  subst this; ring

end cases

/-! ### Crossings and constants -/

theorem four_fifths : (4 : ℝ) / 5 = 19 / 24 + 1 / 120 := by norm_num

/-- Introduction: `B^{1/2} N^{11/20} = N^{19/24}` at `B = N^{29/60}`, and `1/2 − 29/60 = 1/60`. -/
theorem kumchev_cross : (29 : ℝ) / 60 / 2 + 11 / 20 = 19 / 24 ∧ (1 : ℝ) / 2 - 29 / 60 = 1 / 60 := by
  constructor <;> norm_num

/-- Lemma 4.1: `b/2 + 11/20 ≤ 1 − b/2` iff `b ≤ 9/20`. -/
theorem kumchev_small (b : ℝ) : b / 2 + 11 / 20 ≤ 1 - b / 2 ↔ b ≤ 9 / 20 := by
  constructor <;> intro h <;> linarith

/-- Lemma 3.9: `7/8 Q + 29/48 ≤ Q/2 + 19/24` iff `Q ≤ 1/2`. -/
theorem lemma39_cross (Q : ℝ) : 7 / 8 * Q + 29 / 48 ≤ Q / 2 + 19 / 24 ↔ Q ≤ 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- Lemma 3.5: with `M1, M2 ≥ x^{5/12}`, `x/M^{1/2} ≤ x^{19/24}`. -/
theorem lemma35_exp {m : ℝ} (h : 5 / 12 ≤ m) : 1 - m / 2 ≤ 19 / 24 := by linarith

/-- Section 2: `5/7 + 1/2 · 1/6 = 67/84`, and the two density exponents cross at `σ = 5/7`. -/
theorem section2 : (5 : ℝ) / 7 + 1 / 6 * (1 / 2) = 67 / 84 ∧
    7 * (1 - (5 : ℝ) / 7) / 3 = 3 * (1 - 5 / 7) / (2 - 5 / 7) := by
  constructor <;> norm_num

/-- Lemma 3.2 for `k = 5`, sorted, in the form its proof uses: if none of the sums
`a1, a1+a2, a1+a2+a3, a1+a3, a1+a5, a3+a4, a3+a4+a5` lies in `[5/12 − η, 7/12 + η]`,
then the partition `{1,2}, {3,4}, {5}` has `5/12 ≥ a1+a2 ≥ a3+a4 ≥ 2a5 ≥ 1/3`. -/
theorem lemma32_k5 {a1 a2 a3 a4 a5 η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 100)
    (h12 : a2 ≤ a1) (h23 : a3 ≤ a2) (h34 : a4 ≤ a3) (h45 : a5 ≤ a4) (h5 : 0 ≤ a5)
    (hsum : a1 + a2 + a3 + a4 + a5 = 1) (hpair : 2 / 9 - η ≤ a4 + a5)
    (w1 : a1 < 5 / 12 - η ∨ 7 / 12 + η < a1)
    (w2 : a1 + a2 < 5 / 12 - η ∨ 7 / 12 + η < a1 + a2)
    (w3 : a1 + a2 + a3 < 5 / 12 - η ∨ 7 / 12 + η < a1 + a2 + a3)
    (w4 : a1 + a3 < 5 / 12 - η ∨ 7 / 12 + η < a1 + a3)
    (w5 : a1 + a5 < 5 / 12 - η ∨ 7 / 12 + η < a1 + a5)
    (w6 : a3 + a4 < 5 / 12 - η ∨ 7 / 12 + η < a3 + a4)
    (w7 : a3 + a4 + a5 < 5 / 12 - η ∨ 7 / 12 + η < a3 + a4 + a5) :
    a1 + a2 ≤ 5 / 12 ∧ a3 + a4 ≤ a1 + a2 ∧ 2 * a5 ≤ a3 + a4 ∧ 1 / 3 ≤ 2 * a5 := by
  -- j = 0 is impossible: a1 below the window
  have f1 : a1 < 5 / 12 - η := by
    rcases w1 with h | h
    · exact h
    · exfalso; linarith
  -- j = 1 is impossible: a1 + a2 below the window, through a1 + a3 and a1 + a5
  have f2 : a1 + a2 < 5 / 12 - η := by
    rcases w2 with h | h
    · exact h
    · exfalso
      rcases w4 with h4 | h4 <;> rcases w5 with h5 | h5 <;> linarith
  -- so a1 + a2 + a3 is above the window, and so is a3 + a4 + a5
  have f7 : 7 / 12 + η < a3 + a4 + a5 := by
    rcases w7 with h | h
    · exfalso; linarith
    · exact h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Vacuity: the Lemma 3.7 region is inhabited, `M1 = M2 = x^{5/12}`, `M3 = x^{1/6}`, `qT = x^{1/2}`. -/
theorem region_inhabited : Region (5 / 12) (5 / 12) (1 / 6) (1 / 2) := by
  constructor <;> norm_num

/-- Vacuity for `lemma32_k5`: `a = (41, 41, 41, 41, 36)/200`, `η = 0`, meets every hypothesis. -/
example : (41 : ℝ) / 200 + 41 / 200 ≤ 5 / 12 ∧ 1 / 3 ≤ 2 * ((36 : ℝ) / 200) :=
  (lemma32_k5 (a1 := 41 / 200) (a2 := 41 / 200) (a3 := 41 / 200) (a4 := 41 / 200)
    (a5 := 36 / 200) (η := 0) le_rfl (by norm_num) le_rfl le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num)) (Or.inr (by norm_num)) (Or.inl (by norm_num))
    (Or.inl (by norm_num)) (Or.inl (by norm_num)) (Or.inr (by norm_num))) |> fun h => ⟨h.1, h.2.2.2⟩

end LeanLab.ExceptionalSet.MPR2026
