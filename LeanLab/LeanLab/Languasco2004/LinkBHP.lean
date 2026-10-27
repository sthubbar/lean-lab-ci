/-
P0089 Languasco 2004, the survey, linked to P0069 Baker-Harman-Pintz 1997. Unit U-5079,
CLOUD 20261019T0213Z-cloud14, T1 connection.

PROVED: `bhp_exceptions_le`, the exceptional count of BHP1997.Statements is at most the survey's
`EXH` once `x > 2`, the two sets differing only by the even non-Goldbach numbers 0 and 2;
`logSaving_mono`, a log saving for `H ≥ X^a` gives one for `H ≥ X^b`, `b ≥ a`;
`bhp_theorem1_of_jia`, the survey's Theorem 1.5, Jia 1996, `|E(X, H)| ≪ H log^{-A} X` for
`H ≥ X^{7/108+ε}`, implies BHP's Theorem 1 for every `θ ≥ 11/160`, since `7/108 < 11/160`;
`exponent_order`, the survey's exponents in order, `7/108 < 11/160 < 7/81 < 7/36 < 7/24 < 7/12`.
So BHP 1997 is superseded by the result the survey lists as Jia 1996; the converse link is not
available, since BHP's Theorem 1 is stated for `H = x^θ` only, not uniformly in `H`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib
import LeanLab.Languasco2004.Statements
import LeanLab.BHP1997.Statements

namespace LeanLab.Languasco2004
open Real

attribute [local instance] Classical.propDecidable

theorem bhp_exceptions_le {x y : ℝ} (hx : 2 < x) (hy : 0 ≤ y) :
    BHP1997.exceptions x y ≤ EXH x y := by
  unfold BHP1997.exceptions EXH
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢
  obtain ⟨⟨h1, h2⟩, hev, hng⟩ := hn
  have hxn : x ≤ n := le_trans (Nat.le_ceil x) (by exact_mod_cast h1)
  have hnx : (n : ℝ) ≤ x + y :=
    le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))
  refine ⟨by omega, hxn, hnx, hev, ?_, hng⟩
  have : (2 : ℝ) < n := by linarith
  exact_mod_cast this

theorem logSaving_mono {e : ℝ → ℝ → ℕ} {a b : ℝ} (hab : a ≤ b) (h : LogSaving e a) :
    LogSaving e b := by
  intro A hA
  obtain ⟨C, X₀, hC⟩ := h A hA
  refine ⟨C, max X₀ 1, fun X H hX hH => hC X H (le_trans (le_max_left _ _) hX) ?_⟩
  exact le_trans (rpow_le_rpow_of_exponent_le (le_trans (le_max_right _ _) hX) hab) hH

/-- Jia's Theorem 1.5, as quoted, implies BHP 1997 Theorem 1. -/
theorem bhp_theorem1_of_jia (h : Thm15) : BHP1997.Theorem1 := by
  intro θ hθ A hA
  have hε : (0 : ℝ) < 11 / 160 - 7 / 108 := by norm_num
  obtain ⟨C, X₀, hC⟩ := h _ hε (A + 1) (by linarith)
  refine ⟨max (max X₀ 3) (Real.exp (|C| + 1)), fun x hx => ?_⟩
  have hx0 : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp (|C| + 1) ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hL : |C| + 1 ≤ Real.log x := by
    rw [← Real.log_exp (|C| + 1)]; exact Real.log_le_log (Real.exp_pos _) hxe
  have hLpos : 0 < Real.log x := by linarith [abs_nonneg C]
  have hH : x ^ ((7 : ℝ) / 108 + (11 / 160 - 7 / 108)) ≤ x ^ θ := by
    rw [show (7 : ℝ) / 108 + (11 / 160 - 7 / 108) = 11 / 160 by norm_num]
    exact rpow_le_rpow_of_exponent_le (by linarith) hθ
  have hb := hC x (x ^ θ) hx0 hH
  have hy : 0 ≤ x ^ θ := rpow_nonneg hxpos.le θ
  have hle := bhp_exceptions_le (show 2 < x by linarith) hy
  have hle' : (BHP1997.exceptions x (x ^ θ) : ℝ) ≤ EXH x (x ^ θ) := by exact_mod_cast hle
  have hpow : Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) / Real.log x := by
    rw [show -(A + 1) = -A + -1 by ring, rpow_add hLpos, rpow_neg_one]; ring
  have hxθ : 0 < x ^ θ := rpow_pos_of_pos hxpos θ
  have hLA : 0 < Real.log x ^ (-A) := rpow_pos_of_pos hLpos _
  calc (BHP1997.exceptions x (x ^ θ) : ℝ) ≤ C * x ^ θ * Real.log x ^ (-(A + 1)) :=
        le_trans hle' hb
    _ = C / Real.log x * (x ^ θ * Real.log x ^ (-A)) := by rw [hpow]; ring
    _ < 1 * (x ^ θ * Real.log x ^ (-A)) := by
        apply mul_lt_mul_of_pos_right _ (mul_pos hxθ hLA)
        rw [div_lt_one hLpos]; linarith [le_abs_self C]
    _ = x ^ θ / Real.log x ^ A := by
        rw [one_mul, rpow_neg hLpos.le, div_eq_mul_inv]

/-- The survey's exponents, with BHP's, in order. -/
theorem exponent_order :
    (7 / 108 : ℝ) < 11 / 160 ∧ (11 / 160 : ℝ) < 7 / 81 ∧ (7 / 81 : ℝ) < 7 / 36 ∧
      (7 / 36 : ℝ) < 7 / 24 ∧ (7 / 24 : ℝ) < 7 / 12 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Languasco2004
