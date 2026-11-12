/-
A split of `major_minor_mean_square150`, the second moment of `r2` minus the truncated main term
over the even `N ≤ X`.

The summand `r2 N - truncMain150 N` is the sum of two errors.  The first is the error against the
full singular series, `E2 N = r2 N - N * singular N`; its second moment is the analytic core,
where the main term of the major arcs and the remainder of the minor arcs meet and the zero-free
hypothesis on `Θ` governs the contribution of the zeros.  The second is the truncation error
`truncMain150 N - N * singular N` at the Farey level `Q = ⌊N ^ (1/2)⌋`, that is the tail of the
singular series past `Q`; its second moment is elementary, since the tail is already controlled
by `singular_truncation150` in `Decomp150a.lean`.

The assembly is the pointwise inequality `(a - b) ^ 2 ≤ 2 * (a - c) ^ 2 + 2 * (c - b) ^ 2` with
`a = r2 N`, `b = truncMain150 N`, `c = N * singular N`, summed over the even `N ≤ X`, and the
monotonicity of `X ↦ X ^ s` in the exponent, which lets half of `ε` be spent on each of the two
errors.  AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150a

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

/-- LEAF. The second moment of `E2 = r2 - N * singular` over the even `N ≤ X`, bounded by
`X ^ (3/2 + 2 * Θ + ε)`.  This is the analytic step of the proof: `r2` is the weighted count of
the representations of `N` as a sum of two positive integers, and the circle method writes it as
the major-arc main term `N * singular N` plus the contribution of the zeros on the major arcs
plus the minor-arc integral; summing the squares over the even `N ≤ X` with Parseval, the zeros
cost `X ^ (2 * Θ + ε)` and the remaining factor `X ^ (1/2)` is the Farey level, so the zero-free
hypothesis on `Θ` gives exactly the stated exponent.  It is the component of the target that
carries no truncation, and it is the whole analytic content of the estimate. -/
theorem even_second_moment_main_error150 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF. The second moment of the truncation error `truncMain150 N - N * singular N` over the
even `N ≤ X`, bounded by `X ^ (3/2 + 2 * Θ + ε)`.  The truncation of the singular series at the
Farey level `Q = ⌊N ^ (1/2)⌋` leaves the tail past `Q`, whose size is at most a constant times
`N ^ (1/2 + δ)` for every `δ > 0`; squaring and summing over at most `X` values of `N` therefore
costs at most `X ^ (2 + δ)`, which sits below the stated exponent because a zero-free bound
cannot hold below `Θ = 1/2`.  Nothing here uses the zeros, only the convergence of the singular
series. -/
theorem even_second_moment_truncation_error150 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
          (truncMain150 N - (N : ℝ) * singular N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- The mean square estimate over the even `N`, assembled from the two second-moment leaves: on
each even `N` the deviation of `r2 N` from the truncated main term splits into the deviation from
`N * singular N` and the truncation error, the squares cost a factor two each, and half of `ε` is
spent on each of the two bounds, after which the exponent is monotone in the power. -/
theorem major_minor_mean_square150_split (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (r2 N - truncMain150 N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  intro ε hε
  obtain ⟨CA, hA⟩ := even_second_moment_main_error150 Θ hΘ hZ (ε / 2) (by linarith)
  obtain ⟨CB, hB⟩ := even_second_moment_truncation_error150 Θ hΘ hZ (ε / 2) (by linarith)
  refine ⟨2 * (|CA| + |CB|), ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
  have hp : 3 / 2 + 2 * Θ + ε / 2 ≤ 3 / 2 + 2 * Θ + ε := by linarith
  have hmono : (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hp
  have hP0 : (0 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2) := Real.rpow_nonneg hX0 _
  have hpt : ∀ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
      (r2 N - truncMain150 N) ^ 2 ≤
        2 * (E2 N) ^ 2 + 2 * (truncMain150 N - (N : ℝ) * singular N) ^ 2 := by
    intro N _
    have h := sq_sub_le_two150 (r2 N) (truncMain150 N) ((N : ℝ) * singular N)
    have hsq : (((N : ℝ) * singular N) - truncMain150 N) ^ 2 =
        (truncMain150 N - (N : ℝ) * singular N) ^ 2 := by ring
    rw [hsq] at h
    unfold E2
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hA' : (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2)
      ≤ |CA| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2) :=
    le_trans (hA X hX) (mul_le_mul_of_nonneg_right (le_abs_self CA) hP0)
  have hB' : (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
        (truncMain150 N - (N : ℝ) * singular N) ^ 2)
      ≤ |CB| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2) :=
    le_trans (hB X hX) (mul_le_mul_of_nonneg_right (le_abs_self CB) hP0)
  have hC : 2 * (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
      2 * (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
        (truncMain150 N - (N : ℝ) * singular N) ^ 2)
      ≤ 2 * (|CA| + |CB|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    have h1 : 2 * (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2)
        ≤ 2 * (|CA| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2)) := by linarith
    have h2 : 2 * (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N),
          (truncMain150 N - (N : ℝ) * singular N) ^ 2)
        ≤ 2 * (|CB| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2)) := by linarith
    have h3 : 2 * (|CA| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2)) +
        2 * (|CB| * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2))
        = 2 * (|CA| + |CB|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2) := by ring
    have h4 : 2 * (|CA| + |CB|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε / 2)
        ≤ 2 * (|CA| + |CB|) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    linarith
  linarith

end LeanLab.BhowmikGrimmelt2026
