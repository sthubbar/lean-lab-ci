/-
Vinogradov's theorem with almost equal summands.
P0028 Matomaki, Maynard, Shao 2016, arXiv 1610.02017 v2, Proc. LMS 2017, doi 10.1112/plms.12040.
Theorem 1.1: Let θ > 11/20. Every sufficiently large odd integer n can be written as a sum
of three primes n = p1 + p2 + p3 with |pi − n/3| ≤ n^θ for i ∈ {1, 2, 3}.
Earlier exponents, as the paper's introduction quotes them, originals not read here:
Pan and Pan, θ > 2/3; Baker and Harman, θ > 4/7.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Ternary.Statements

namespace LeanLab.Ternary

/-- `n` is a sum of three primes, each within `h` of `n/3`. -/
def IsAlmostEqualTernary (n : ℕ) (h : ℝ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = n ∧
    |(p₁ : ℝ) - n / 3| ≤ h ∧ |(p₂ : ℝ) - n / 3| ≤ h ∧ |(p₃ : ℝ) - n / 3| ≤ h

/-- Every sufficiently large odd `n` is a sum of three primes within `n^θ` of `n/3`. -/
def AlmostEqualVinogradov (θ : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → IsAlmostEqualTernary n ((n : ℝ) ^ θ)

/-! ### The papers, cited, with `sorry` -/

/-- P0028 Matomaki-Maynard-Shao 2016, Theorem 1.1. -/
theorem mms_theorem11 (θ : ℝ) (hθ : 11 / 20 < θ) : AlmostEqualVinogradov θ := by sorry

/-- Baker-Harman, as quoted in P0028's introduction: `θ > 4/7` suffices. -/
theorem bakerHarman_quoted (θ : ℝ) (hθ : 4 / 7 < θ) : AlmostEqualVinogradov θ := by
  exact mms_theorem11 θ (lt_trans (by norm_num : (11 / 20 : ℝ) < 4 / 7) hθ)

/-- Pan-Pan, as quoted in P0028's introduction: `θ > 2/3` suffices. -/
theorem panPan_quoted (θ : ℝ) (hθ : 2 / 3 < θ) : AlmostEqualVinogradov θ := by
  exact mms_theorem11 θ (lt_trans (by norm_num : (11 / 20 : ℝ) < 2 / 3) hθ)

/-! ### Links, zero sorry -/

theorem isAlmostEqualTernary_mono {n : ℕ} {h h' : ℝ} (hh : h ≤ h')
    (H : IsAlmostEqualTernary n h) : IsAlmostEqualTernary n h' := by
  obtain ⟨a, b, c, ha, hb, hc, hs, h1, h2, h3⟩ := H
  exact ⟨a, b, c, ha, hb, hc, hs, h1.trans hh, h2.trans hh, h3.trans hh⟩

theorem IsAlmostEqualTernary.isTernarySum {n : ℕ} {h : ℝ} (H : IsAlmostEqualTernary n h) :
    IsTernarySum n := by
  obtain ⟨a, b, c, ha, hb, hc, hs, -⟩ := H
  unfold IsTernarySum
  exact ⟨a, b, c, ha, hb, hc, hs⟩

/-- A smaller exponent is a stronger theorem: for `n ≥ 1`, `n^θ ≤ n^θ'` when `θ ≤ θ'`. -/
theorem almostEqualVinogradov_mono {θ θ' : ℝ} (hθ : θ ≤ θ') (H : AlmostEqualVinogradov θ) :
    AlmostEqualVinogradov θ' := by
  obtain ⟨N₀, hN⟩ := H
  refine ⟨max N₀ 1, fun n ho hn => ?_⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  exact isAlmostEqualTernary_mono (Real.rpow_le_rpow_of_exponent_le h1 hθ)
    (hN n ho ((le_max_left _ _).trans hn))

/-- Matomaki-Maynard-Shao gives Baker-Harman's range. -/
theorem bakerHarman_of_mms (H : ∀ θ : ℝ, 11 / 20 < θ → AlmostEqualVinogradov θ)
    (θ : ℝ) (hθ : 4 / 7 < θ) : AlmostEqualVinogradov θ :=
  H θ (by linarith [show (11 : ℝ) / 20 < 4 / 7 by norm_num])

/-- Baker-Harman's range gives Pan-Pan's. -/
theorem panPan_of_bakerHarman (H : ∀ θ : ℝ, 4 / 7 < θ → AlmostEqualVinogradov θ)
    (θ : ℝ) (hθ : 2 / 3 < θ) : AlmostEqualVinogradov θ :=
  H θ (by linarith [show (4 : ℝ) / 7 < 2 / 3 by norm_num])

/-- Any almost equal theorem gives Vinogradov's qualitative theorem. -/
theorem vinogradov_of_almostEqual {θ : ℝ} (H : AlmostEqualVinogradov θ) :
    ∃ C : ℝ, TernaryAbove C := by
  obtain ⟨N₀, hN⟩ := H
  exact ⟨N₀, fun n ho hn => (hN n ho (by exact_mod_cast hn)).isTernarySum⟩

/-- Why the exponent is tied to primes in short intervals: an almost equal theorem with
exponent `θ` puts a prime in `[n/3 − n^θ, n/3 + n^θ]` for every large odd `n`. So any
improvement below the short-interval prime exponent, 0.525 by Baker-Harman-Pintz, would
itself be a new short-interval prime result. This is the paper's remark that 11/20 cannot
improve by more than 0.025 without new ideas, made precise in one direction. -/
theorem prime_near_third_of_almostEqual {θ : ℝ} (H : AlmostEqualVinogradov θ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n →
      ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 3 - (n : ℝ) ^ θ ≤ p ∧ (p : ℝ) ≤ n / 3 + (n : ℝ) ^ θ := by
  obtain ⟨N₀, hN⟩ := H
  refine ⟨N₀, fun n ho hn => ?_⟩
  obtain ⟨a, -, -, ha, -, -, -, h1, -, -⟩ := hN n ho hn
  rw [abs_le] at h1
  exact ⟨a, ha, by linarith [h1.1], by linarith [h1.2]⟩

/-- The pigeonhole half: the three summands average exactly `n/3`, so at least one is
`≤ n/3` and one is `≥ n/3`; with the window this pins the smallest prime in
`[n/3 − n^θ, n/3]`. -/
theorem exists_prime_le_third {n : ℕ} {h : ℝ} (H : IsAlmostEqualTernary n h) :
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 3 - h ≤ p ∧ (p : ℝ) ≤ n / 3 := by
  obtain ⟨a, b, c, ha, hb, hc, hs, h1, h2, h3⟩ := H
  rw [abs_le] at h1 h2 h3
  have hs' : (a : ℝ) + b + c = n := by exact_mod_cast hs
  by_cases hA : (a : ℝ) ≤ n / 3
  · exact ⟨a, ha, by linarith [h1.1], hA⟩
  by_cases hB : (b : ℝ) ≤ n / 3
  · exact ⟨b, hb, by linarith [h2.1], hB⟩
  refine ⟨c, hc, by linarith [h3.1], ?_⟩
  push Not at hA hB
  linarith

/-- And one in `[n/3, n/3 + n^θ]`. -/
theorem exists_prime_ge_third {n : ℕ} {h : ℝ} (H : IsAlmostEqualTernary n h) :
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 3 ≤ p ∧ (p : ℝ) ≤ n / 3 + h := by
  obtain ⟨a, b, c, ha, hb, hc, hs, h1, h2, h3⟩ := H
  rw [abs_le] at h1 h2 h3
  have hs' : (a : ℝ) + b + c = n := by exact_mod_cast hs
  by_cases hA : (n : ℝ) / 3 ≤ a
  · exact ⟨a, ha, hA, by linarith [h1.2]⟩
  by_cases hB : (n : ℝ) / 3 ≤ b
  · exact ⟨b, hb, hB, by linarith [h2.2]⟩
  refine ⟨c, hc, ?_, by linarith [h3.2]⟩
  push Not at hA hB
  linarith

/-- The window cannot shrink to nothing: with `h < 1/3` a summand `p` has `|3p − n| < 1`,
so `n = 3p`. Hence when `3 ∤ n` there is no almost equal representation with `h < 1/3`.
So no exponent statement can hold with a window below a fixed constant for all large odd n. -/
theorem not_almostEqual_small_window {n : ℕ} {h : ℝ} (hh : h < 1 / 3) (h3 : ¬ 3 ∣ n) :
    ¬ IsAlmostEqualTernary n h := by
  rintro ⟨a, b, c, -, -, -, -, h1, -, -⟩
  rw [abs_le] at h1
  have key : |(3 * a : ℝ) - n| < 1 := by
    rw [abs_lt]; constructor <;> linarith [h1.1, h1.2]
  have hlt : |((3 * a : ℤ) - n : ℤ)| < 1 := by
    have : |(((3 * a : ℤ) - n : ℤ) : ℝ)| < 1 := by push_cast; exact key
    exact_mod_cast this
  have hz := abs_lt.mp hlt
  exact h3 ⟨a, by omega⟩

end LeanLab.Ternary
