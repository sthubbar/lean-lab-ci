import Mathlib

/-!
# A sharper enclosure of Euler's constant: `0.5693 < γ₀ < 0.5851`

Session 20261020T2113Z-cloud51, unit U-6740, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

Known mathematics, no cited input: `H_63 − log 64 < γ₀ < H_64 − log 64` from Mathlib's monotone
sequences, with `log 64 = 6 log 2` and Mathlib's nine digit bounds on `log 2`. Infrastructure
for P0032 Lemma 1 on `0 < x < e^{-4}`, where `1/2 < γ₀ < 2/3` is too coarse.
-/

namespace LeanLab.RieselVaughan1983

open Real

lemma log64 : Real.log 64 = 6 * Real.log 2 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num

theorem gamma_gt : (5693 / 10000 : ℝ) < eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 63
  have hl := Real.log_two_lt_d9
  have hv : (47282 / 10000 : ℚ) < harmonic 63 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  unfold Real.eulerMascheroniSeq at h
  have : ((63 : ℕ) : ℝ) + 1 = 64 := by norm_num
  rw [this, log64] at h
  have hv' : ((47282 / 10000 : ℚ) : ℝ) < ((harmonic 63 : ℚ) : ℝ) := Rat.cast_lt.mpr hv
  push_cast at hv'
  linarith

theorem gamma_lt : eulerMascheroniConstant < (5851 / 10000 : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have hl := Real.log_two_gt_d9
  have hv : harmonic 64 < (47439 / 10000 : ℚ) := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  unfold Real.eulerMascheroniSeq' at h
  simp only [show (64 : ℕ) ≠ 0 by norm_num, ite_false] at h
  have : ((64 : ℕ) : ℝ) = 64 := by norm_num
  rw [this, log64] at h
  have hv' : ((harmonic 64 : ℚ) : ℝ) < ((47439 / 10000 : ℚ) : ℝ) := Rat.cast_lt.mpr hv
  push_cast at hv'
  linarith

end LeanLab.RieselVaughan1983
