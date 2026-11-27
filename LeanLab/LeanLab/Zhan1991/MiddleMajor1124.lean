/-
P0068 Zhan 1991, Theorem 2, page 262 last display: the case of the middle range reduction that the
blockwise step does not cover, split one step. burst-20261124, worker D, unit D-extra-2.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

When (1.2) holds with `τ = A² N⁻¹ L^{-c₁}` and `q ≥ L^{c₂}`, while the fresh approximation
`a₁/q₁` with `τ₁ = N^{1/3} L^{-c₁} / 4` has `q₁ < L^{c₂}`, the two fractions differ and
`|λ₁| ≥ 1/(q q₁) - 1/(q τ)`; this separation is PROVED as `cond12_sep`. What is left is the
analytic estimate of a major arc sum with that lower bound on the phase, LEAF
`middle_major_est_leaf`. `middle_major_of_est` gives the old LEAF `middle_major_leaf` of
MiddleSplit1124.lean, which now uses it.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991

noncomputable section

/-- Page 262 last display, the two approximations differ: if (1.2) holds for `α` with `a/q` and
with `a₁/q₁`, `q₁ < q`, then `|λ₁| ≥ 1/(q q₁) - 1/(q τ)`, since `a/q ≠ a₁/q₁` as `(a, q) = 1`.
PROVED, burst-20261124 D-extra-2. -/
theorem cond12_sep (α τ τ1 lam lam1 : ℝ) (a a1 : ℤ) (q q1 : ℕ)
    (h : Cond12 α τ a q lam) (h1 : Cond12 α τ1 a1 q1 lam1) (hlt : q1 < q) :
    1 / ((q : ℝ) * q1) - 1 / ((q : ℝ) * τ) ≤ |lam1| := by
  obtain ⟨hα, hg, hl, hq1, -⟩ := h
  obtain ⟨hα1, -, -, hq11, -⟩ := h1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1pos : (0 : ℝ) < q1 := by exact_mod_cast hq11
  have hint : (1 : ℤ) ≤ |a * q1 - a1 * q| := by
    apply Int.one_le_abs
    intro h0
    have hdvd : (q : ℤ) ∣ a * q1 := ⟨a1, by linarith⟩
    have hcop : IsCoprime (q : ℤ) a := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hg
    have := Int.le_of_dvd (by exact_mod_cast hq11) (hcop.dvd_of_dvd_mul_left hdvd)
    have : q ≤ q1 := by exact_mod_cast this
    omega
  have hintR : (1 : ℝ) ≤ |(a : ℝ) * q1 - a1 * q| := by exact_mod_cast hint
  have hdiff : |(a : ℝ) / q - a1 / q1| ≥ 1 / ((q : ℝ) * q1) := by
    rw [show (a : ℝ) / q - a1 / q1 = ((a : ℝ) * q1 - a1 * q) / (q * q1) by field_simp,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q1)]
    exact div_le_div_of_nonneg_right hintR (by positivity)
  have hlam1 : lam1 = ((a : ℝ) / q - a1 / q1) + lam := by linarith
  have := abs_sub_abs_le_abs_sub ((a : ℝ) / q - a1 / q1) (-lam)
  rw [abs_neg, sub_neg_eq_add, ← hlam1] at this
  linarith

/-- LEAF: page 262 last display, the major arc case of the middle range, not argued in the paper:
`α = a₁/q₁ + λ₁` with `q₁ < L^{c₂}`, `|λ₁| ≤ 1/(q₁ τ₁)` and `|λ₁| ≥ 1/(q q₁) - 1/(q τ)` for some
`L^{c₂} ≤ q ≤ τ`, so `|λ₁| ≫ 1/(q₁ τ)`. Cut into blocks of length about `N^{2/3}`; on each block
use the Siegel and Walfisz theorem in short intervals when `|λ₁| N^{2/3} ≤ L^{B+1}`, and Theorem 3
of the paper otherwise; the main terms sum to `(μ(q₁)/φ(q₁)) ∫ e(λ₁ u) du ≪ (q₁/φ(q₁)) τ`, which
is `≪ A L^{-c₁-1} log L`. Needs `c₁` large in terms of `B`. Class HARD. -/
theorem middle_major_est_leaf : ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∀ c2 : ℝ, 0 < c2 →
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α : ℝ) (q : ℕ) (a1 : ℤ) (q1 : ℕ) (lam1 : ℝ),
      N₀ ≤ N → (N : ℝ) ^ (2 / 3 : ℝ) ≤ A → A ≤ (N : ℝ) / Real.log N →
      Real.log N ^ c2 ≤ q → (q : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1) →
      Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1 → (q1 : ℝ) < Real.log N ^ c2 →
      1 / ((q : ℝ) * q1) - 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) ≤ |lam1| →
      ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B) := by
  sorry

/-- Page 262 last display, the major arc case of the middle range from the separation
`cond12_sep` and the LEAF `middle_major_est_leaf`. PROVED; same statement as
`middle_major_leaf` of MiddleSplit1124.lean. -/
theorem middle_major_of_est : ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∀ c2 : ℝ, 0 < c2 →
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) (a1 : ℤ) (q1 : ℕ) (lam1 : ℝ),
      N₀ ≤ N → (N : ℝ) ^ (2 / 3 : ℝ) ≤ A → A ≤ (N : ℝ) / Real.log N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam → Real.log N ^ c2 ≤ q →
      Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1 →
      (q1 : ℝ) < Real.log N ^ c2 → ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B) := by
  intro B hB
  obtain ⟨c1m, h⟩ := middle_major_est_leaf B hB
  refine ⟨c1m, fun c1 hc1 c2 hc2 => ?_⟩
  obtain ⟨K, N₀, h'⟩ := h c1 hc1 c2 hc2
  refine ⟨K, N₀, fun N A α lam a q a1 q1 lam1 hN hlo hhi hc hq hc' hq1 => ?_⟩
  have hlt : q1 < q := by
    have : (q1 : ℝ) < q := lt_of_lt_of_le hq1 hq
    exact_mod_cast this
  exact h' N A α q a1 q1 lam1 hN hlo hhi hq hc.2.2.2.2 hc' hq1
    (cond12_sep α _ _ lam lam1 a a1 q q1 hc hc' hlt)

end

end LeanLab.Zhan1991
