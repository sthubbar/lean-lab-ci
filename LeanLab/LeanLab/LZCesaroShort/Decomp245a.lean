import LeanLab.LZCesaroShort.Theorem1PProved

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 page 2, Theorem 1.
These auxiliary estimates handle H equal to one in the legacy assembly.
The full legacy theorem remains open.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- Chebyshev bounds the Goldbach representation weight by a constant times n log n.
This is an auxiliary estimate for the page 2 endpoint H equal to one. -/
lemma R_le_chebyshev (n : ℕ) :
    R n ≤ (Real.log 4 + 4) * n * Real.log n := by
  unfold R
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ ≤ ∑ i ∈ range (n + 1), Λ i * Real.log n := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (vonMangoldt_le_log_of_le (Nat.sub_le n i)) ArithmeticFunction.vonMangoldt_nonneg
    _ = ψ (n : ℝ) * Real.log n := by rw [← sum_mul, sum_range_vonMangoldt]
    _ ≤ ((Real.log 4 + 4) * n) * Real.log n :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n))
        (Real.log_natCast_nonneg n)

/-- Under RH, the endpoint H equal to one has error at most a constant times N log N.
This strengthens the page 2 printed endpoint estimate and does not prove the full legacy bound. -/
theorem theorem1_legacy_H1 (hRH : RiemannHypothesis) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖((cesaro N 1 : ℝ) : ℂ) - (1 : ℂ) * N + 2 / (1 : ℂ) * ZH N 1‖
        ≤ K * ((N : ℝ) * Real.log N) := by
  obtain ⟨N5, K5, h5⟩ := sec5_rh_one hRH
  refine ⟨Real.log 4 + 5 + 6 * |K5|, max N5 3, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    apply (Real.le_log_iff_exp_le hNpos).mpr
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hlog : Real.log (N : ℝ) ≤ 2 * Real.sqrt N := by
    have h := Real.log_natCast_le_rpow_div N (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N :=
    Real.mul_self_sqrt hNpos.le
  have hsL : Real.sqrt (N : ℝ) * Real.log N ^ 2 ≤ 2 * (N * Real.log N) := by
    have h := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (Real.sqrt_nonneg (N : ℝ)) hL0)
    have hslog := congrArg (fun x : ℝ => x * Real.log (N : ℝ)) hsq
    nlinarith [hslog]
  have hNL : (N : ℝ) ≤ N * Real.log N := by nlinarith
  have hz := h5 N 1 (le_trans (le_max_left _ _) hN) le_rfl (by omega)
  simp only [Nat.cast_one, div_one, one_mul, mul_one] at hz ⊢
  have hz' : ‖ZH N 1‖ ≤ |K5| * (3 * ((N : ℝ) * Real.log N)) := by
    calc
      _ ≤ K5 * (Real.sqrt N * Real.log N ^ 2 + N) := hz
      _ ≤ |K5| * (Real.sqrt N * Real.log N ^ 2 + N) :=
        mul_le_mul_of_nonneg_right (le_abs_self K5) (by positivity)
      _ ≤ |K5| * (3 * ((N : ℝ) * Real.log N)) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K5)
  rw [cesaro_one (by omega)]
  have htri : ‖((R N : ℝ) : ℂ) - (N : ℂ) + 2 * ZH N 1‖ ≤
      R N + N + 2 * ‖ZH N 1‖ := by
    refine (norm_add_le _ _).trans ?_
    have h := norm_sub_le ((R N : ℝ) : ℂ) (N : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (R_nonneg N),
      Complex.norm_natCast] at h
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have hR := R_le_chebyshev N
  refine htri.trans ?_
  nlinarith

/-- The printed page 2 theorem implies the legacy error bound when H log of 2H is at least N.
This is a restricted consequence, not the full legacy theorem. -/
theorem theorem1_legacy_large_H (hRH : RiemannHypothesis) :
    ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
      (N : ℝ) ≤ H * Real.log (2 * H) →
      ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
        ≤ K * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
          + H * Real.log N ^ 2 * Real.log (2 * H)) := by
  obtain ⟨K, hK⟩ := theorem1P_proved hRH
  refine ⟨5 * |K|, fun N H hN hH hHN hlarge => ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hNpos : (0 : ℝ) < N := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hLH0 : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ Real.log (2 * (N : ℝ) / H) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hHpos]
    linarith
  have hA : Real.log (2 * (N : ℝ) / H) ≤ 2 * Real.log N := by
    calc
      _ ≤ Real.log ((N : ℝ) ^ 2) := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hHpos]
        nlinarith
      _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
  have hA2 : Real.log (2 * (N : ℝ) / H) ^ 2 ≤ 4 * Real.log N ^ 2 := by
    nlinarith
  have hB0 : 0 ≤ Real.log (2 * (N : ℝ) ^ 2 / H) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hHpos]
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hA2 hNpos.le
  have h2 := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (Real.log (N : ℝ)))
  have hbound : (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2
      + H * Real.log N ^ 2 * Real.log (2 * H) ≤
      5 * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
        + H * Real.log N ^ 2 * Real.log (2 * H)) := by
    have h3 := mul_nonneg hNpos.le hB0
    nlinarith
  have hprinted0 : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2
      + H * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  calc
    _ ≤ K * (N * Real.log (2 * (N : ℝ) / H) ^ 2
        + H * Real.log N ^ 2 * Real.log (2 * H)) := hK N H hN hH hHN
    _ ≤ |K| * (N * Real.log (2 * (N : ℝ) / H) ^ 2
        + H * Real.log N ^ 2 * Real.log (2 * H)) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) hprinted0
    _ ≤ |K| * (5 * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
        + H * Real.log N ^ 2 * Real.log (2 * H))) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg K)
    _ = _ := by ring

/-- The legacy error expression dominates N log N throughout the page 2 numeric domain.
This is an auxiliary positivity estimate, not an assertion of the legacy theorem. -/
lemma legacy_error_ge_N_log_N {N H : ℕ} (hN : 2 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N) :
    (N : ℝ) * Real.log N ≤ N * Real.log (2 * (N : ℝ) ^ 2 / H)
      + H * Real.log N ^ 2 * Real.log (2 * H) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have harg : (N : ℝ) ≤ 2 * (N : ℝ) ^ 2 / H := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < H)]
    nlinarith
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < N) harg
  have h1 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) N)
  have hLH : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ (H : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  linarith

end LeanLab.LZCesaroShort
