/-
Split of `SPLITLeaf521.leaf521_dirichlet_mvt`, the mean value theorem for Dirichlet polynomials cited
for `G` in P0069 Baker Harman Pintz 1997, page 52 display 5.21, burst 2026-11-22 unit P1122-0103.

The cited source is Montgomery and Vaughan 1974, Hilbert's inequality, J. London Math. Soc. 8,
pages 73 to 82. Corollary 3 there is proved from Theorem 1, the generalized Hilbert inequality with
the spacings `δ_r`, by expanding the square and integrating term by term. This file follows that
proof on `[-T, T]`:
- `mv_hilbert_inequality`, LEAF HARD: Theorem 1 of Montgomery and Vaughan, the citation wall.
- `mvt_integral_expansion`, PROVED: the expansion of the integral in the proof of Corollary 3.
- `log_nat_spacing`, PROVED: the spacing `δ_n ≥ 1/(2n)` of the frequencies `log n`.
- `leaf521_dirichlet_mvt_of_leaves`, PROVED from the one leaf: the statement of
  `leaf521_dirichlet_mvt` verbatim, with `C = 6π`.

Imports Mathlib only. AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.SPLITLeaf521MVT
open Complex
open scoped BigOperators

/-- LEAF: Montgomery and Vaughan 1974, Hilbert's inequality, J. London Math. Soc. 8, Theorem 1, the
generalized Hilbert inequality: for distinct real `λ_r` with `δ_r = min_{s ≠ r} |λ_r - λ_s|`,
`|Σ_{r ≠ s} x_r conj(x_s) / (λ_r - λ_s)| ≤ (3π/2) Σ |x_r|^2 / δ_r`. Stated with any positive `δ_r`
below every gap at `r`, which follows from the printed form since the right side only grows when
`δ_r` shrinks. This is the cited input behind P0069 page 52 display 5.21. Class HARD, a citation
wall not in Mathlib. -/
theorem mv_hilbert_inequality (S : Finset ℕ) (lam δ : ℕ → ℝ) (x : ℕ → ℂ)
    (hδ : ∀ r ∈ S, 0 < δ r)
    (hgap : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ r ≤ |lam r - lam s|) :
    ‖∑ r ∈ S, ∑ s ∈ S.erase r, x r * (starRingEnd ℂ) (x s) / ((lam r - lam s : ℝ) : ℂ)‖ ≤
      3 * Real.pi / 2 * ∑ r ∈ S, ‖x r‖ ^ 2 / δ r := by
  sorry

/-- Montgomery and Vaughan 1974, proof of Corollary 3: `n^(-it) = e^(-it log n)` for `n ≥ 1`. -/
lemma mvt_cpow_nat (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-((t : ℂ) * I)) = cexp (-(I * ((Real.log n : ℝ) : ℂ)) * t) := by
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  ring_nf

/-- Montgomery and Vaughan 1974, proof of Corollary 3: the square of the Dirichlet polynomial
as the double sum `Σ_{r,s} a_r conj(a_s) e^(-it(λ_r - λ_s))`. -/
lemma mvt_integrand (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 1 ≤ n) (t : ℝ) :
    ((‖∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ S, ∑ s ∈ S, a r * (starRingEnd ℂ) (a s) *
        cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
  rw [mvt_cpow_nat r (hS r hr), mvt_cpow_nat s (hS s hs), map_mul, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (-(I * ((Real.log s : ℝ) : ℂ)) * (t : ℂ)) =
      (I * ((Real.log s : ℝ) : ℂ)) * t := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [this]
  have : cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * t) =
      cexp (-(I * ((Real.log r : ℝ) : ℂ)) * t) * cexp ((I * ((Real.log s : ℝ) : ℂ)) * t) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

/-- Montgomery and Vaughan 1974, proof of Corollary 3: an off-diagonal term integrates to
`A (e^(-iθT) - e^(iθT)) / (-iθ)` for `θ ≠ 0`. -/
lemma mvt_term_integral_ne (A : ℂ) (θ T : ℝ) (hθ : θ ≠ 0) :
    ∫ t in (-T)..T, A * cexp (-(I * (θ : ℂ)) * t) =
      A * ((cexp (-(I * (θ : ℂ)) * T) - cexp (-(I * (θ : ℂ)) * ((-T : ℝ) : ℂ))) /
        (-(I * (θ : ℂ)))) := by
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex]
  have : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  simp [this, Complex.I_ne_zero]

/-- Montgomery and Vaughan 1974, proof of Corollary 3: a diagonal term integrates to `2TA`. -/
lemma mvt_term_integral_zero (A : ℂ) (T : ℝ) :
    ∫ t in (-T)..T, A * cexp (-(I * ((0 : ℝ) : ℂ)) * t) = 2 * T * A := by
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one,
    intervalIntegral.integral_const, Complex.real_smul]
  push_cast; ring

/-- Montgomery and Vaughan 1974, the expansion in the proof of Corollary 3, on `[-T, T]`.
Writing `λ_n = log n`, the square `|Σ a_n n^(-it)|^2` is `Σ_{m,n} a_m conj(a_n) e^(-it(λ_m - λ_n))`;
the diagonal integrates to `2T Σ |a_n|^2`, and an off-diagonal term integrates to
`a_m conj(a_n) (e^(iT(λ_m-λ_n)) - e^(-iT(λ_m-λ_n))) / (i(λ_m - λ_n))`, which is the difference of
the Hilbert forms of `x_r = a_r e^(iTλ_r)` and `y_r = a_r e^(-iTλ_r)`, divided by `i`. PROVED. -/
theorem mvt_integral_expansion (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) (hS : ∀ n ∈ S, 1 ≤ n) :
    (((∫ t in (-T)..T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ) =
      (2 * T : ℂ) * ∑ n ∈ S, ((‖a n‖ ^ 2 : ℝ) : ℂ) +
        ((∑ r ∈ S, ∑ s ∈ S.erase r,
            (a r * cexp (I * T * Real.log r)) *
              (starRingEnd ℂ) (a s * cexp (I * T * Real.log s)) /
                ((Real.log r - Real.log s : ℝ) : ℂ)) -
          (∑ r ∈ S, ∑ s ∈ S.erase r,
            (a r * cexp (-(I * T * Real.log r))) *
              (starRingEnd ℂ) (a s * cexp (-(I * T * Real.log s))) /
                ((Real.log r - Real.log s : ℝ) : ℂ))) / I := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [mvt_integrand S a hS]
  have hint : ∀ r s : ℕ, IntervalIntegrable (fun t : ℝ => a r * (starRingEnd ℂ) (a s) *
        cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * t)) MeasureTheory.volume (-T) T := by
    intro r s
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum (f := fun r (t : ℝ) => ∑ s ∈ S, a r * (starRingEnd ℂ) (a s) *
        cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * t))]
  swap
  · intro r _
    apply Continuous.intervalIntegrable
    fun_prop
  have hin : ∀ r ∈ S, (∫ t in (-T)..T, ∑ s ∈ S, a r * (starRingEnd ℂ) (a s) *
        cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * t)) =
      ∑ s ∈ S, ∫ t in (-T)..T, a r * (starRingEnd ℂ) (a s) *
        cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * t) := by
    intro r _
    exact intervalIntegral.integral_finsetSum (fun s _ => hint r s)
  rw [Finset.sum_congr rfl hin]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [← Finset.add_sum_erase S _ hr, ← Finset.sum_sub_distrib, Finset.sum_div]
  congr 1
  · rw [sub_self, mvt_term_integral_zero, Complex.ofReal_pow, ← Complex.mul_conj']
  · refine Finset.sum_congr rfl (fun s hs => ?_)
    have hsr : s ≠ r := Finset.ne_of_mem_erase hs
    have hs1 : 1 ≤ s := hS s (Finset.mem_of_mem_erase hs)
    have hr1 : 1 ≤ r := hS r hr
    have hθ : Real.log r - Real.log s ≠ 0 := by
      intro h
      apply hsr
      have h1 : Real.log (s : ℝ) = Real.log (r : ℝ) := by linarith
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hs1 : (0:ℝ) < s))
        (Set.mem_Ioi.mpr (by exact_mod_cast hr1 : (0:ℝ) < r)) h1
      exact_mod_cast this
    rw [mvt_term_integral_ne _ _ _ hθ]
    have hθc : ((Real.log r - Real.log s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hθ
    simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, Complex.conj_I]
    have e1 : cexp (I * T * Real.log r) * cexp (-I * T * Real.log s) =
        cexp (I * ((Real.log r - Real.log s : ℝ) : ℂ) * T) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : cexp (-(I * T * Real.log r)) * cexp (-(-I * T * Real.log s)) =
        cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * T) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e3 : cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * ((-T : ℝ) : ℂ)) =
        cexp (I * ((Real.log r - Real.log s : ℝ) : ℂ) * T) := by
      congr 1; push_cast; ring
    rw [e3]
    calc _ = a r * (starRingEnd ℂ) (a s) * (cexp (-(I * ((Real.log r - Real.log s : ℝ) : ℂ)) * T)
            - cexp (I * ((Real.log r - Real.log s : ℝ) : ℂ) * T)) /
            (-(I * ((Real.log r - Real.log s : ℝ) : ℂ))) := by ring
      _ = _ := by
        rw [← e1, ← e2]
        field_simp
        ring
/-- Montgomery and Vaughan 1974, proof of Corollary 3: the frequencies `log n` have spacing
`δ_n ≥ 1/(2n)`, since `log(n+1) - log n ≥ 1/(n+1)` and `log n - log(n-1) ≥ 1/n`. -/
theorem log_nat_spacing {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : n ≠ m) :
    1 / (2 * (n : ℝ)) ≤ |Real.log n - Real.log m| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · -- n < m
    have hnm : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    have key := Real.log_le_sub_one_of_pos (div_pos hn0 hm0)
    rw [Real.log_div hn0.ne' hm0.ne'] at key
    have h1 : (n : ℝ) / m ≤ n / (n + 1) :=
      div_le_div_of_nonneg_left hn0.le (by positivity) hnm
    have h2 : (n : ℝ) / (n + 1) = 1 - 1 / (n + 1) := by field_simp; ring
    have h3 : 1 / (2 * (n : ℝ)) ≤ 1 / (n + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [(by exact_mod_cast hn : (1:ℝ) ≤ n)])
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    linarith
  · -- m < n
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    have key := Real.log_le_sub_one_of_pos (div_pos hm0 hn0)
    rw [Real.log_div hm0.ne' hn0.ne'] at key
    have h2 : (m : ℝ) / n ≤ 1 - 1 / n := by
      rw [div_le_iff₀ hn0, sub_mul, one_div_mul_cancel hn0.ne']; linarith
    have h3 : 1 / (2 * (n : ℝ)) ≤ 1 / n :=
      one_div_le_one_div_of_le hn0 (by linarith)
    refine le_trans ?_ (le_abs_self _)
    linarith

/-- The statement of `SPLITLeaf521.leaf521_dirichlet_mvt` verbatim, with `C = 6π`, proved as in
Montgomery and Vaughan 1974 Corollary 3 from `mvt_integral_expansion`, `mv_hilbert_inequality`
applied to `x_r = a_r e^(±iTλ_r)` with `δ_r = 1/(2r)`, and `log_nat_spacing`. -/
theorem leaf521_dirichlet_mvt_of_leaves :
    ∃ C : ℝ, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ), 0 ≤ T → (∀ n ∈ S, 1 ≤ n) →
      ∫ t in (-T)..T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 ≤
        ∑ n ∈ S, (2 * T + C * n) * ‖a n‖ ^ 2 := by
  refine ⟨6 * Real.pi, fun S a T hT hS => ?_⟩
  have hexp := mvt_integral_expansion S a T hS
  set I0 := ∫ t in (-T)..T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 with hI0
  set Hx := ∑ r ∈ S, ∑ s ∈ S.erase r,
            (a r * cexp (I * T * Real.log r)) *
              (starRingEnd ℂ) (a s * cexp (I * T * Real.log s)) /
                ((Real.log r - Real.log s : ℝ) : ℂ) with hHx
  set Hy := ∑ r ∈ S, ∑ s ∈ S.erase r,
            (a r * cexp (-(I * T * Real.log r))) *
              (starRingEnd ℂ) (a s * cexp (-(I * T * Real.log s))) /
                ((Real.log r - Real.log s : ℝ) : ℂ) with hHy
  set A := ∑ n ∈ S, ‖a n‖ ^ 2 with hA
  have hkey : (I0 : ℂ) = ((2 * T * A : ℝ) : ℂ) + (Hx - Hy) / I := by
    rw [hexp, hA]; push_cast; ring
  have hre : I0 = 2 * T * A + ((Hx - Hy) / I).re := by
    have := congrArg Complex.re hkey
    simpa using this
  have hW : ((Hx - Hy) / I).re ≤ ‖Hx‖ + ‖Hy‖ := by
    calc ((Hx - Hy) / I).re ≤ ‖(Hx - Hy) / I‖ := Complex.re_le_norm _
      _ = ‖Hx - Hy‖ := by rw [norm_div, Complex.norm_I, div_one]
      _ ≤ ‖Hx‖ + ‖Hy‖ := norm_sub_le _ _
  have hδ : ∀ r ∈ S, (0 : ℝ) < 1 / (2 * (r : ℝ)) := by
    intro r hr
    have : (1 : ℝ) ≤ r := by exact_mod_cast hS r hr
    positivity
  have hgap : ∀ r ∈ S, ∀ s ∈ S, r ≠ s →
      1 / (2 * (r : ℝ)) ≤ |(fun n : ℕ => Real.log n) r - (fun n : ℕ => Real.log n) s| := by
    intro r hr s hs hrs
    exact log_nat_spacing (hS s hs) (hS r hr) hrs
  have hnx : ∀ r : ℕ, ‖a r * cexp (I * T * Real.log r)‖ = ‖a r‖ := by
    intro r
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re]
    simp
  have hny : ∀ r : ℕ, ‖a r * cexp (-(I * T * Real.log r))‖ = ‖a r‖ := by
    intro r
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re]
    simp
  have hsum : ∀ r ∈ S, ‖a r‖ ^ 2 / (1 / (2 * (r : ℝ))) = 2 * r * ‖a r‖ ^ 2 := by
    intro r hr
    have : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by have := hS r hr; omega)
    field_simp
  have hX := mv_hilbert_inequality S (fun n : ℕ => Real.log n) (fun r => 1 / (2 * (r : ℝ)))
    (fun r => a r * cexp (I * T * Real.log r)) hδ hgap
  have hY := mv_hilbert_inequality S (fun n : ℕ => Real.log n) (fun r => 1 / (2 * (r : ℝ)))
    (fun r => a r * cexp (-(I * T * Real.log r))) hδ hgap
  simp only [hnx, hny] at hX hY
  rw [Finset.sum_congr rfl hsum] at hX hY
  have hB : ‖Hx‖ + ‖Hy‖ ≤ 2 * (3 * Real.pi / 2 * ∑ r ∈ S, 2 * r * ‖a r‖ ^ 2) := by
    have h1 : ‖Hx‖ ≤ 3 * Real.pi / 2 * ∑ r ∈ S, 2 * r * ‖a r‖ ^ 2 := hX
    have h2 : ‖Hy‖ ≤ 3 * Real.pi / 2 * ∑ r ∈ S, 2 * r * ‖a r‖ ^ 2 := hY
    linarith
  have hfin : ∑ n ∈ S, (2 * T + 6 * Real.pi * n) * ‖a n‖ ^ 2 =
      2 * T * A + 2 * (3 * Real.pi / 2 * ∑ r ∈ S, 2 * r * ‖a r‖ ^ 2) := by
    rw [hA, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hfin, hre]
  linarith

end LeanLab.BHP1997.SPLITLeaf521MVT
