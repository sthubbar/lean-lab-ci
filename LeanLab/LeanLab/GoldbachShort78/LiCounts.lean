import Mathlib
import LeanLab.GoldbachShort78.Statements

/-!
GEMINI task53, unit U-1337 follow-up. AI wrote the Lean code, Gemini, with Claude review fixes.

R. Li, Primes in almost all short intervals, arXiv 2407.05651 v6, Theorem 1.1, p. 1: primes in
`[n, n + n^{1/21.5 + ε}]` for all but `O(X (log X)^{-B})` of the `n ∈ [X, 2X]`. Theorem 7.1, p. 27,
Section 7: combined with Baker-Harman-Pintz 0.525, Goldbach numbers in `[X, X + X^{21/860}]`.

Review note: Theorem 1.1 carries `+ ε`; the no-`ε` input `LiAlmostAllCount` is STRONGER than
Theorem 1.1 as printed. It matches the exponent of Li's Theorem 7.1. The faithful `ε` form is
`LiAlmostAllCountEps`, with `goldbach_short_bhp_li_eps`. Binary Goldbach is OPEN.
-/

namespace LeanLab.GoldbachShort78

/-- **Cited count input, all intervals**: for `x ≥ x₀` and `Y ≥ x^0.525` with `2Y + 3 ≤ x`, the window
`[x − 2Y, x − Y]` holds at least `c Y / log x` primes. Derived from Baker-Harman-Pintz 2001 by
tiling the window; the tiling is not printed there. -/
def BHPWindowCount (c x₀ : ℝ) : Prop :=
  WindowCount 0.525 c x₀

/-- **Count input, almost all intervals, no `ε`**: for `Y ≥ y₀` and `H ≥ Y^(1/21.5)`, at most
`Y / log² Y` of the `z ∈ [Y, 2Y]` have a prime free `[z, z + H]`. STRONGER than R. Li Theorem 1.1,
which has exponent `1/21.5 + ε`; it is the form behind the exponent of Li's Theorem 7.1. -/
def LiAlmostAllCount (y₀ : ℝ) : Prop :=
  AlmostAllCount (1 / 21.5) y₀

/-- **Cited count input, almost all intervals, faithful form** of R. Li Theorem 1.1, exponent
`1/21.5 + ε`. -/
def LiAlmostAllCountEps (ε y₀ : ℝ) : Prop :=
  AlmostAllCount (1 / 21.5 + ε) y₀

/-- **Combined input, no `ε`**: BHP and the no-`ε` Li count hold with some constants. -/
def BHPLiCounts : Prop :=
  ∃ c x₀ y₀ : ℝ, 0 < c ∧ BHPWindowCount c x₀ ∧ LiAlmostAllCount y₀

/-- CONDITIONAL ON `BHPLiCounts`: Goldbach numbers in `[x, x + 3 x^{21/860}]`, the exponent of
R. Li Theorem 7.1, for `x` meeting the elementary side conditions. -/
theorem goldbach_short_bhp_li (hin : BHPLiCounts) :
    ∃ x₀ y₀ c : ℝ, 0 < c ∧ ∀ x : ℕ, x₀ ≤ x → y₀ ≤ (x : ℝ) ^ (0.525 : ℝ) → 3 ≤ (x : ℝ) ^ (0.525 : ℝ) →
      1 < c * (0.525 : ℝ) ^ 2 * Real.log x → 2 * ⌈(x : ℝ) ^ (0.525 : ℝ)⌉₊ + 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧
        (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (21 / 860 : ℝ) := by
  obtain ⟨c, x₀, y₀, hc, hW, hA⟩ := hin
  refine ⟨x₀, y₀, c, hc, ?_⟩
  intro x h0 h1 h2 h3 h4
  have ha : (0 : ℝ) < 0.525 := by norm_num
  have hb0 : (0 : ℝ) ≤ 1 / 21.5 := by norm_num
  have hb1 : (1 : ℝ) / 21.5 ≤ 1 := by norm_num
  obtain ⟨n, hn, hx, hn2⟩ := goldbach_short_b ha hb0 hb1 hc hW hA h0 h1 h2 h3 h4
  refine ⟨n, hn, hx, ?_⟩
  have : (0.525 : ℝ) * (1 / 21.5) = 21 / 860 := by norm_num
  rwa [this] at hn2

/-- CONDITIONAL ON `BHPWindowCount c x₀` and `LiAlmostAllCountEps ε y₀`, the faithful form of
Li Theorem 1.1: Goldbach numbers in `[x, x + 3 x^{0.525 (1/21.5 + ε)}]`, i.e. `21/860 + 0.525 ε`. -/
theorem goldbach_short_bhp_li_eps {c x₀ y₀ ε : ℝ} (hc : 0 < c) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hW : BHPWindowCount c x₀) (hA : LiAlmostAllCountEps ε y₀) {x : ℕ}
    (h0 : x₀ ≤ x) (h1 : y₀ ≤ (x : ℝ) ^ (0.525 : ℝ)) (h2 : 3 ≤ (x : ℝ) ^ (0.525 : ℝ))
    (h3 : 1 < c * (0.525 : ℝ) ^ 2 * Real.log x) (h4 : 2 * ⌈(x : ℝ) ^ (0.525 : ℝ)⌉₊ + 3 ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧
      (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (21 / 860 + 0.525 * ε : ℝ) := by
  have ha : (0 : ℝ) < 0.525 := by norm_num
  have hb0 : (0 : ℝ) ≤ 1 / 21.5 + ε := by positivity
  have hb1 : (1 : ℝ) / 21.5 + ε ≤ 1 := by linarith [show (1 : ℝ) / 21.5 ≤ 1 / 2 by norm_num]
  obtain ⟨n, hn, hx, hn2⟩ := goldbach_short_b ha hb0 hb1 hc hW hA h0 h1 h2 h3 h4
  refine ⟨n, hn, hx, ?_⟩
  have : (0.525 : ℝ) * (1 / 21.5 + ε) = 21 / 860 + 0.525 * ε := by norm_num; ring
  rwa [this] at hn2

end LeanLab.GoldbachShort78
