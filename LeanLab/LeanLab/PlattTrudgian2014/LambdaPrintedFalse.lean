/-
Platt, Trudgian 2014, P0024, arXiv 1404.5669v2: display (5) AS PRINTED is false for
λ = 0.8594 and c = 109/154, unit U-6776, CLOUD 20261021T0017Z-cloud54.

Plain-math twin.
Display (4): L = ⌊log N / log 2⌋ and G_L(x) = Σ_{j=0}^{L-1} e(2^j x).
Display (5), page 3, read from the arXiv v2 page image in unit U-5011:
  Δ = meas(x ∈ [0, 1] : |G_L(x)| > λL) < N^{-c/log 2}.
The lab's literal reading of that print, for all large N, is `LambdaOKPrinted c λ` in
Lambda.lean. This file proves `¬ LambdaOKPrinted (109/154) 0.8594`.

Proof. Take N = 2^L with L = 100t, t ≥ 1, so Lof N = L, and m = 97t.
For 0 ≤ x ≤ 2^{-(m+4)} and j < m the angle 2π 2^j x is at most π/8, so
Re e(2^j x) = cos(2π 2^j x) ≥ 1 - (π/8)^2/2 ≥ 0.92; the other 3t terms have real part ≥ -1.
So |G_L(x)| ≥ Re G_L(x) ≥ 0.92·97t - 3t = 86.24t > 85.94t = 0.8594 L, and the set has
measure ≥ 2^{-(97t+4)}. But N^{-c/log 2} = e^{-cL} = e^{-(10900/154)t} ≈ 2^{-102.1t},
and 2^{-(97t+4)} ≥ e^{-cL} already at t = 1. Concrete witness: N = 2^100,
`printed_fails_at_2_pow_100`: there the measure is ≥ 2^{-101} ≈ 3.9e-31 while
N^{-c/log 2} = e^{-70.78} ≈ 1.8e-31.

What this is and is not. It is a theorem about the lab's literal reading of the printed
normalization N^{-c/log 2} with Heath-Brown and Puchta's c = 109/154. It does not touch
the paper's main results: the lab's repaired reading meas < N^{-c}, `LambdaOK`, the
E(λ) > c form of Heath-Brown and Puchta, is what the cited λ bounds use, and the K = 12
and GRH K = 7 arithmetic depends only on λ and c through inequality (2). F-5009, the
other slip found in this paper, on Algorithm 1, was likewise cosmetic, AUTHOR CONFIRMED,
and the paper's C₃ values are not in question. The GRH line λ = 0.7163436, c = 1/2 is
not addressed here. No FINDING is claimed by this file alone.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PlattTrudgian2014.Lambda

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex

/-- `Lof (2^L) = L`. -/
theorem Lof_two_pow (L : ℕ) : Lof (2 ^ L) = L := by
  unfold Lof
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_div_assoc, div_self hl, mul_one,
    Nat.floor_natCast]

/-- For j < m and 0 ≤ x ≤ 2^{-(m+4)}: Re e(2^j x) ≥ 0.92. -/
theorem re_term_ge {m j : ℕ} (hj : j < m) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2 ^ (m + 4)) :
    (0.92 : ℝ) ≤ (Complex.exp (2 * Real.pi * I * ((2 : ℂ) ^ j * x))).re := by
  have harg : 2 * Real.pi * I * ((2 : ℂ) ^ j * x) = ((2 * Real.pi * (2 ^ j * x) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I_re]
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj.le
  have hpos : (0 : ℝ) < 2 ^ (m + 4) := by positivity
  have hy0 : 0 ≤ (2 : ℝ) ^ j * x := by positivity
  have hy : (2 : ℝ) ^ j * x ≤ 1 / 16 := by
    calc (2 : ℝ) ^ j * x ≤ 2 ^ m * (1 / 2 ^ (m + 4)) :=
          mul_le_mul h2j hx hx0 (by positivity)
      _ = 1 / 16 := by rw [pow_add]; field_simp; norm_num
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  set θ := 2 * Real.pi * (2 ^ j * x)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ : θ ≤ 0.4 := by
    have : θ ≤ 2 * Real.pi * (1 / 16) := by
      simp only [θ]; exact mul_le_mul_of_nonneg_left hy (by positivity)
    linarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  nlinarith

/-- Re G_{m+n}(x) ≥ 0.92 m - n on [0, 2^{-(m+4)}]. -/
theorem re_G_ge (m n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2 ^ (m + 4)) :
    (0.92 : ℝ) * m - n ≤ (G (m + n) x).re := by
  unfold G
  rw [Complex.re_sum, Finset.sum_range_add]
  have h1 : ∑ j ∈ Finset.range m, (0.92 : ℝ) ≤
      ∑ j ∈ Finset.range m, (Complex.exp (2 * Real.pi * I * ((2 : ℂ) ^ j * x))).re :=
    Finset.sum_le_sum fun j hj => re_term_ge (Finset.mem_range.mp hj) hx0 hx
  have h2 : ∑ k ∈ Finset.range n, (-1 : ℝ) ≤
      ∑ k ∈ Finset.range n, (Complex.exp (2 * Real.pi * I * ((2 : ℂ) ^ (m + k) * x))).re := by
    refine Finset.sum_le_sum fun k _ => ?_
    have := Complex.abs_re_le_norm (Complex.exp (2 * Real.pi * I * ((2 : ℂ) ^ (m + k) * x)))
    have hn : ‖Complex.exp (2 * Real.pi * I * ((2 : ℂ) ^ (m + k) * x))‖ = 1 := by
      have harg : 2 * Real.pi * I * ((2 : ℂ) ^ (m + k) * x) =
          ((2 * Real.pi * (2 ^ (m + k) * x) : ℝ) : ℂ) * I := by push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    rw [hn] at this
    linarith [abs_le.mp this]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  linarith

/-- The interval [0, 2^{-(97t+4)}] lies in the set of display (5) at N = 2^{100t}, λ = 0.8594. -/
theorem Icc_subset_bigSet {t : ℕ} (ht : 1 ≤ t) :
    Set.Icc (0 : ℝ) (1 / 2 ^ (97 * t + 4)) ⊆ bigSet (2 ^ (100 * t)) 0.8594 := by
  intro x hx
  have hδ : (1 : ℝ) / 2 ^ (97 * t + 4) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  refine ⟨⟨hx.1, hx.2.trans hδ⟩, ?_⟩
  rw [Lof_two_pow]
  have hsplit : 100 * t = 97 * t + 3 * t := by ring
  have hre := re_G_ge (97 * t) (3 * t) hx.1 hx.2
  rw [← hsplit] at hre
  have hnorm := Complex.re_le_norm (G (100 * t) x)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  push_cast at hre ⊢
  nlinarith

/-- The lower bound: meas ≥ 2^{-(97t+4)} at N = 2^{100t}, λ = 0.8594, t ≥ 1. -/
theorem volume_bigSet_ge {t : ℕ} (ht : 1 ≤ t) :
    (1 : ℝ) / 2 ^ (97 * t + 4) ≤ (volume (bigSet (2 ^ (100 * t)) 0.8594)).toReal := by
  have h := ENNReal.toReal_mono (volume_bigSet_ne_top _ _) (measure_mono (Icc_subset_bigSet ht))
  rwa [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (by positivity)] at h

/-- The printed right side is below that measure: N^{-c/log 2} ≤ 2^{-(97t+4)} at N = 2^{100t}. -/
theorem printed_rhs_le {t : ℕ} (ht : 1 ≤ t) :
    ((2 ^ (100 * t) : ℕ) : ℝ) ^ (-((109 / 154 : ℝ) / Real.log 2)) ≤ 1 / 2 ^ (97 * t + 4) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < ((2 ^ (100 * t) : ℕ) : ℝ) := by positivity
  rw [Real.rpow_def_of_pos hpos, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hexp : ↑(100 * t) * Real.log 2 * -(109 / 154 / Real.log 2) = -(109 / 154 * ↑(100 * t)) := by
    field_simp
  rw [hexp]
  have hrhs : (1 : ℝ) / 2 ^ (97 * t + 4) = Real.exp (-(↑(97 * t + 4) * Real.log 2)) := by
    rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), one_div]
  rw [hrhs, Real.exp_le_exp]
  have hl2 := Real.log_two_lt_d9
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  push_cast
  nlinarith

/-- At N = 2^{100t}, t ≥ 1, display (5) as printed fails for λ = 0.8594, c = 109/154. -/
theorem printed_fails_at {t : ℕ} (ht : 1 ≤ t) :
    ¬ ((volume (bigSet (2 ^ (100 * t)) 0.8594)).toReal <
        ((2 ^ (100 * t) : ℕ) : ℝ) ^ (-((109 / 154 : ℝ) / Real.log 2))) :=
  not_lt.mpr ((printed_rhs_le ht).trans (volume_bigSet_ge ht))

/-- Concrete witness: at N = 2^100 the printed inequality of display (5) fails. -/
theorem printed_fails_at_2_pow_100 :
    ¬ ((volume (bigSet (2 ^ 100) 0.8594)).toReal <
        ((2 ^ 100 : ℕ) : ℝ) ^ (-((109 / 154 : ℝ) / Real.log 2))) :=
  printed_fails_at (t := 1) le_rfl

/-- Display (5) as printed, `meas < N^{-c/log 2}` for all large N, is false at λ = 0.8594,
c = 109/154. -/
theorem not_lambdaOKPrinted : ¬ LambdaOKPrinted (109 / 154) 0.8594 := by
  rintro ⟨N0, hN⟩
  have ht : 1 ≤ N0 + 1 := by omega
  have hle : N0 ≤ 2 ^ (100 * (N0 + 1)) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact printed_fails_at ht (hN _ hle)

end LeanLab.PlattTrudgian2014
