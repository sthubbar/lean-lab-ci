/-
J. Liu, K.-M. Tsang 2005, Small prime solutions of ternary linear equations, Acta Arith. 118,
79-100. Unit U-1533, run 20261026T0004Z-24325, type DECOMPOSE, file a of three.

Lemma 4.2, p. 86: for pairwise coprime nonzero integers a₁, a₂, a₃ and
`1/(2A) < |λ| < 1/2`, with `A = max(2, |a₁|, |a₂|, |a₃|)`, one has
`max_j ‖aⱼ λ‖ ≥ 1/(2A)`, where `‖x‖` is the distance from `x` to the nearest integer.
The proof splits into the case where the three ratios `nⱼ/aⱼ` agree and the case where two differ,
`nⱼ` the nearest integer to `aⱼ λ`. This lemma is the minor-arc input of Section 4.

Here `‖x‖` is `dnint x = |x - round x|`.

AI-written Lean code, Claude, 2026-10-26. Ternary Goldbach is Helfgott 2013; binary Goldbach is
OPEN, nothing here is progress on it.
-/
import LeanLab.LiuTsang2005.Statements

namespace LeanLab.LiuTsang2005.Decomp1533a
open Real

/-- `‖x‖`, the distance from `x` to the nearest integer. -/
noncomputable def dnint (x : ℝ) : ℝ := |x - round x|

/-- LEAF. Unit U-1533. The distance to the nearest integer is at most one half, the bound
`‖x‖ ≤ 1/2` used in both cases of Lemma 4.2, p. 86. -/
theorem dnint_le_half (x : ℝ) : dnint x ≤ 1 / 2 := by
  have dnint_eq : dnint x = |x - (round x : ℤ)| := rfl
  rw [dnint_eq]
  exact abs_sub_round x

/-- LEAF. Unit U-1533. Rational gap step of case 2 of Lemma 4.2, p. 86: if `n₁ a₂ ≠ n₂ a₁`
then with `δⱼ = aⱼ λ - nⱼ` one has `|δ₁ a₂ - δ₂ a₁| ≥ 1`, since that quantity equals the nonzero
integer `n₂ a₁ - n₁ a₂`. -/
theorem gap_ge_one (a₁ a₂ n₁ n₂ : ℤ) (lam : ℝ) (hne : n₁ * a₂ ≠ n₂ * a₁) :
    1 ≤ |((a₁ : ℝ) * lam - n₁) * a₂ - ((a₂ : ℝ) * lam - n₂) * a₁| := by
  have : ((a₁ : ℝ) * lam - n₁) * a₂ - ((a₂ : ℝ) * lam - n₂) * a₁ = (n₂ * a₁ - n₁ * a₂ : ℤ) := by
    push_cast
    ring
  rw [this]
  norm_cast
  apply Int.one_le_abs
  intro h
  apply hne
  linarith

/-- LEAF. Unit U-1533. Case 2 of Lemma 4.2, p. 86: from `|δ₁ a₂ - δ₂ a₁| ≥ 1` one gets
`max(|δ₁|, |δ₂|) (|a₁| + |a₂|) ≥ 1` by the triangle inequality. -/
theorem max_mul_sum_ge (a₁ a₂ d₁ d₂ : ℝ) (h : 1 ≤ |d₁ * a₂ - d₂ * a₁|) :
    1 ≤ max |d₁| |d₂| * (|a₁| + |a₂|) := by
  have : |d₁ * a₂ - d₂ * a₁| ≤ |d₁ * a₂| + |d₂ * a₁| := abs_sub _ _
  have h1 : |d₁ * a₂| = |d₁| * |a₂| := abs_mul _ _
  have h2 : |d₂ * a₁| = |d₂| * |a₁| := abs_mul _ _
  rw [h1, h2] at this
  have h3 : |d₁| * |a₂| ≤ max |d₁| |d₂| * |a₂| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have h4 : |d₂| * |a₁| ≤ max |d₁| |d₂| * |a₁| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  have h5 : |d₁| * |a₂| + |d₂| * |a₁| ≤ max |d₁| |d₂| * (|a₁| + |a₂|) := by
    calc |d₁| * |a₂| + |d₂| * |a₁| ≤ max |d₁| |d₂| * |a₂| + max |d₁| |d₂| * |a₁| := add_le_add h3 h4
      _ = max |d₁| |d₂| * (|a₁| + |a₂|) := by ring
  exact le_trans h (le_trans this h5)

/-- LEAF. Unit U-1533. Last line of case 2 of Lemma 4.2, p. 86: if `m (x + y) ≥ 1` with
`0 < x + y ≤ 2A` then `m ≥ 1/(2A)`. -/
theorem ge_inv_twoA {m s A : ℝ} (hs : 0 < s) (hsA : s ≤ 2 * A) (h : 1 ≤ m * s) :
    1 / (2 * A) ≤ m := by
  have : 1 / s ≤ m := (div_le_iff₀ hs).mpr h
  have hA : 1 / (2 * A) ≤ 1 / s := by
    apply one_div_le_one_div_of_le hs hsA
  exact le_trans hA this

/-- LEAF. Unit U-1533. Case 1 of Lemma 4.2, p. 86: if `n₁ a₂ = n₂ a₁` and `n₁ a₃ = n₃ a₁` with
`a₁` coprime to `a₂` and to `a₃`, `a₁ ≠ 0`, then there is an integer `k` with `nⱼ = k aⱼ` for all
three `j`. -/
theorem common_ratio (a₁ a₂ a₃ n₁ n₂ n₃ : ℤ) (ha₁ : a₁ ≠ 0) (h12 : Int.gcd a₁ a₂ = 1)
    (h12' : n₁ * a₂ = n₂ * a₁) (h13' : n₁ * a₃ = n₃ * a₁) :
    ∃ k : ℤ, n₁ = k * a₁ ∧ n₂ = k * a₂ ∧ n₃ = k * a₃ := by
  have hdvd1 : a₁ ∣ a₂ * n₁ := by rw [mul_comm, h12']; exact dvd_mul_left _ _
  have hdvd2 : a₁ ∣ n₁ := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd1 h12
  obtain ⟨k, hk⟩ := hdvd2
  have hk_eq : n₁ = k * a₁ := by rw [hk, mul_comm]
  use k
  refine ⟨hk_eq, ?_, ?_⟩
  · have h_eq : n₂ * a₁ = k * a₁ * a₂ := by
      rw [← hk_eq]
      exact h12'.symm
    have h_eq2 : n₂ * a₁ = (k * a₂) * a₁ := by
      calc n₂ * a₁ = k * a₁ * a₂ := h_eq
        _ = k * (a₁ * a₂) := by ring
        _ = (k * a₂) * a₁ := by ring
    exact mul_right_cancel₀ ha₁ h_eq2
  · have h_eq : n₃ * a₁ = k * a₁ * a₃ := by
      rw [← hk_eq]
      exact h13'.symm
    have h_eq2 : n₃ * a₁ = (k * a₃) * a₁ := by
      calc n₃ * a₁ = k * a₁ * a₃ := h_eq
        _ = k * (a₁ * a₃) := by ring
        _ = (k * a₃) * a₁ := by ring
    exact mul_right_cancel₀ ha₁ h_eq2

/-- LEAF. Unit U-1533. Case 1 of Lemma 4.2, p. 86, the common ratio vanishes: if `a ≠ 0`,
`|λ| < 1/2` and `|a λ - k a| ≤ 1/2` for an integer `k`, then `k = 0`. -/
theorem ratio_eq_zero (a k : ℤ) (ha : a ≠ 0) (lam : ℝ) (hlam : |lam| < 1 / 2)
    (h : |(a : ℝ) * lam - (k * a : ℤ)| ≤ 1 / 2) : k = 0 := by
  have : ((k * a : ℤ) : ℝ) = (k : ℝ) * (a : ℝ) := by push_cast; rfl
  rw [this] at h
  have h1 : (a : ℝ) * lam - (k : ℝ) * (a : ℝ) = (a : ℝ) * (lam - (k : ℝ)) := by ring
  rw [h1] at h
  have h2 : |(a : ℝ) * (lam - (k : ℝ))| = |(a : ℝ)| * |lam - (k : ℝ)| := abs_mul _ _
  rw [h2] at h
  by_contra hk
  have h3 : 1 ≤ |(k : ℝ)| := by
    have hk' : k ≠ 0 := hk
    exact_mod_cast Int.one_le_abs hk'
  have h4 : 1 - 1 / 2 < |lam - (k : ℝ)| := by
    calc 1 - 1 / 2 < |(k : ℝ)| - |lam| := by linarith
      _ ≤ |(k : ℝ) - lam| := by exact abs_sub_abs_le_abs_sub _ _
      _ = |lam - (k : ℝ)| := abs_sub_comm _ _
  have h5 : 1 / 2 < |lam - (k : ℝ)| := by linarith
  have h6 : 1 ≤ |(a : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha
  have h7 : 1 * (1 / 2) < |(a : ℝ)| * |lam - (k : ℝ)| := by
    nlinarith
  linarith

/-- LEAF. Unit U-1533. End of case 1 of Lemma 4.2, p. 86: if `a ≠ 0` is an integer and
`|λ| > 1/(2A)` with `A > 0` then `|a λ| > 1/(2A)`, as `|a| ≥ 1`. -/
theorem abs_mul_gt (a : ℤ) (ha : a ≠ 0) {lam A : ℝ} (hA : 0 < A) (hlam : 1 / (2 * A) < |lam|) :
    1 / (2 * A) < |(a : ℝ) * lam| := by
  have : 1 ≤ |(a : ℝ)| := by
    norm_cast
    exact Int.one_le_abs ha
  have h1 : |(a : ℝ) * lam| = |(a : ℝ)| * |lam| := abs_mul _ _
  rw [h1]
  calc 1 / (2 * A) < |lam| := hlam
    _ = 1 * |lam| := (one_mul _).symm
    _ ≤ |(a : ℝ)| * |lam| := mul_le_mul_of_nonneg_right this (abs_nonneg _)

/-- The bridge between `dnint` and the nearest integer. Proved here. -/
theorem dnint_eq (x : ℝ) : dnint x = |x - (round x : ℤ)| := rfl

/-- Case 2 for one pair, CONDITIONAL ON the leaves `gap_ge_one`, `max_mul_sum_ge`,
`ge_inv_twoA`; zero sorry of its own. -/
theorem case2_pair (a₁ a₂ : ℤ) (A lam : ℝ) (hA : 0 < A) (h1 : |(a₁ : ℝ)| ≤ A)
    (h2 : |(a₂ : ℝ)| ≤ A) (ha : a₁ ≠ 0)
    (hne : round ((a₁ : ℝ) * lam) * a₂ ≠ round ((a₂ : ℝ) * lam) * a₁) :
    1 / (2 * A) ≤ max (dnint ((a₁ : ℝ) * lam)) (dnint ((a₂ : ℝ) * lam)) := by
  have hg := gap_ge_one a₁ a₂ (round ((a₁ : ℝ) * lam)) (round ((a₂ : ℝ) * lam)) lam hne
  have hm := max_mul_sum_ge (a₁ : ℝ) a₂ _ _ hg
  have hpos : 0 < |(a₁ : ℝ)| + |(a₂ : ℝ)| := by
    have : 0 < |(a₁ : ℝ)| := abs_pos.2 (by exact_mod_cast ha)
    linarith [abs_nonneg (a₂ : ℝ)]
  exact ge_inv_twoA hpos (by linarith) hm

/-- **Lemma 4.2, p. 86.** For pairwise coprime nonzero `a₁, a₂, a₃` and
`1/(2A) < |λ| < 1/2`: `max_j ‖aⱼ λ‖ ≥ 1/(2A)`. CONDITIONAL ON the seven leaves above;
zero sorry of its own. -/
theorem lemma42 (a₁ a₂ a₃ : ℤ) (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0) (h3 : a₃ ≠ 0)
    (h12 : Int.gcd a₁ a₂ = 1) (lam : ℝ)
    (hlo : 1 / (2 * Abig a₁ a₂ a₃) < |lam|) (hhi : |lam| < 1 / 2) :
    1 / (2 * Abig a₁ a₂ a₃) ≤
      max (dnint ((a₁ : ℝ) * lam)) (max (dnint ((a₂ : ℝ) * lam)) (dnint ((a₃ : ℝ) * lam))) := by
  set A := Abig a₁ a₂ a₃
  have hA : 0 < A := by linarith [two_le_Abig a₁ a₂ a₃]
  have b1 := abs_le_Abig₁ a₁ a₂ a₃
  have b2 := abs_le_Abig₂ a₁ a₂ a₃
  have b3 := abs_le_Abig₃ a₁ a₂ a₃
  set n₁ := round ((a₁ : ℝ) * lam)
  set n₂ := round ((a₂ : ℝ) * lam)
  set n₃ := round ((a₃ : ℝ) * lam)
  by_cases e12 : n₁ * a₂ = n₂ * a₁
  · by_cases e13 : n₁ * a₃ = n₃ * a₁
    · obtain ⟨k, hk1, -, -⟩ := common_ratio a₁ a₂ a₃ n₁ n₂ n₃ h1 h12 e12 e13
      have hd : |(a₁ : ℝ) * lam - (k * a₁ : ℤ)| ≤ 1 / 2 := by
        have := dnint_le_half ((a₁ : ℝ) * lam)
        rw [dnint_eq] at this
        rwa [← hk1]
      have hk0 : k = 0 := ratio_eq_zero a₁ k h1 lam hhi hd
      have hn : n₁ = 0 := by rw [hk1, hk0, zero_mul]
      have hlt := abs_mul_gt a₁ h1 hA hlo
      have : dnint ((a₁ : ℝ) * lam) = |(a₁ : ℝ) * lam| := by
        rw [dnint_eq]
        change |(a₁ : ℝ) * lam - ((n₁ : ℤ) : ℝ)| = _
        rw [hn]; simp
      rw [this] at *
      exact le_trans hlt.le (le_max_left _ _)
    · have hne : n₁ * a₃ ≠ n₃ * a₁ := e13
      have := case2_pair a₁ a₃ A lam hA b1 b3 h1 hne
      rcases le_max_iff.1 this with h | h
      · exact le_trans h (le_max_left _ _)
      · exact le_trans h (le_trans (le_max_right _ _) (le_max_right _ _))
  · have := case2_pair a₁ a₂ A lam hA b1 b2 h1 e12
    rcases le_max_iff.1 this with h | h
    · exact le_trans h (le_max_left _ _)
    · exact le_trans h (le_trans (le_max_left _ _) (le_max_right _ _))

end LeanLab.LiuTsang2005.Decomp1533a
