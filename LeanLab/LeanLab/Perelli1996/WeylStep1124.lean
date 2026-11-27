/-
P0083 Perelli 1996 page 482 display 6, input Vaughan 1981 chapter 2, the first display of the
proof of the Weyl differencing lemma: the squared modulus of a sum expanded by the difference h.
ROUTE BURST S8 burst-20261124 unit S8-13, piece 1 of the split plan for
Weyl1122.leaf_iterated_differencing. Proved, no sorry.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Perelli1996.WeylStep1124
open Finset

/-- The correlation at shift h plus one, the inner sum of Vaughan's first display. -/
abbrev corr (z : ℕ → ℂ) (Q h : ℕ) : ℂ :=
  ∑ n ∈ range (Q - 1 - h), z (n + h + 1) * (starRingEnd ℂ) (z n)

/-- The expansion of S times its conjugate by the difference of the two indices. -/
theorem mul_conj_expand (z : ℕ → ℂ) (Q : ℕ) :
    (∑ n ∈ range Q, z n) * (starRingEnd ℂ) (∑ n ∈ range Q, z n) =
      ∑ n ∈ range Q, z n * (starRingEnd ℂ) (z n) +
        ∑ h ∈ range Q, (corr z Q h + (starRingEnd ℂ) (corr z Q h)) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    have hstep : ∀ h ∈ range Q, corr z (Q + 1) h =
        corr z Q h + z Q * (starRingEnd ℂ) (z (Q - 1 - h)) := by
      intro h hh
      have hh' := mem_range.mp hh
      unfold corr
      have e1 : Q + 1 - 1 - h = (Q - 1 - h) + 1 := by omega
      rw [e1, sum_range_succ]
      have e2 : Q - 1 - h + h + 1 = Q := by omega
      rw [e2]
    have hlast : corr z (Q + 1) Q = 0 := by
      unfold corr; simp
    have hrefl : ∑ h ∈ range Q, (starRingEnd ℂ) (z (Q - 1 - h)) =
        (starRingEnd ℂ) (∑ n ∈ range Q, z n) := by
      rw [map_sum]
      exact sum_range_reflect (fun n => (starRingEnd ℂ) (z n)) Q
    have hsum : ∑ h ∈ range (Q + 1), corr z (Q + 1) h =
        ∑ h ∈ range Q, corr z Q h + z Q * (starRingEnd ℂ) (∑ n ∈ range Q, z n) := by
      rw [sum_range_succ, hlast, add_zero, sum_congr rfl hstep, sum_add_distrib,
        ← mul_sum, hrefl]
    have hsum' : ∑ h ∈ range (Q + 1), (corr z (Q + 1) h + (starRingEnd ℂ) (corr z (Q + 1) h)) =
        ∑ h ∈ range (Q + 1), corr z (Q + 1) h +
          (starRingEnd ℂ) (∑ h ∈ range (Q + 1), corr z (Q + 1) h) := by
      rw [sum_add_distrib, map_sum]
    rw [hsum', hsum, sum_range_succ, sum_range_succ (fun n => z n * _), map_add, map_add, map_mul,
      Complex.conj_conj]
    rw [sum_add_distrib, ← map_sum] at ih
    linear_combination ih

/-- Vaughan 1981 chapter 2, the first display of the proof of the Weyl differencing lemma, for
weights of modulus at most one on Q consecutive integers: the square of the modulus of the sum is at
most Q plus twice the sum over the differences 1 to Q of the moduli of the correlations. -/
theorem norm_sq_le (z : ℕ → ℂ) (Q : ℕ) (hz : ∀ n, ‖z n‖ ≤ 1) :
    ‖∑ n ∈ range Q, z n‖ ^ 2 ≤ Q + 2 * ∑ h ∈ range Q, ‖corr z Q h‖ := by
  have hE := congrArg Complex.re (mul_conj_expand z Q)
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.add_re, Complex.re_sum, Complex.re_sum,
    Complex.normSq_eq_norm_sq] at hE
  simp_rw [Complex.mul_conj, Complex.add_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hE
  rw [hE]
  have h1 : ∑ n ∈ range Q, ‖z n‖ ^ 2 ≤ Q := by
    calc ∑ n ∈ range Q, ‖z n‖ ^ 2 ≤ ∑ _n ∈ range Q, (1 : ℝ) :=
          sum_le_sum (fun n _ => by
            have := hz n; have := norm_nonneg (z n); nlinarith)
      _ = Q := by simp
  have h2 : ∑ h ∈ range Q, 2 * (corr z Q h).re ≤ 2 * ∑ h ∈ range Q, ‖corr z Q h‖ := by
    rw [mul_sum]
    exact sum_le_sum (fun h _ => by
      have := Complex.re_le_norm (corr z Q h); linarith)
  linarith

end LeanLab.Perelli1996.WeylStep1124
