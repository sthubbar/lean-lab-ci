import LeanLab.LZCesaroShort.Decomp245a

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 page 8, equation 25, and page 7, Lemma 8.
The assembly is CONDITIONAL ON the explicit legacy discrepancy estimate and RH.
The discrepancy estimate uses the inherited lab error, not the printed paper error.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- Equation 25 and Lemma 8 assemble the exact legacy target from its discrepancy estimate.
The discrepancy hypothesis is not proved by the paper and stays explicit. -/
theorem legacy_theorem1_of_discrepancy (hRH : RiemannHypothesis)
    (hD : ∃ Kd : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → H ≤ N →
      |∑ n ∈ Icc (N - H) (N + H), w N H n * (R n - (2 * ψ (n : ℝ) - n))| ≤
        Kd * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
          + H * Real.log N ^ 2 * Real.log (2 * H))) : Theorem1 := by
  obtain ⟨Kd, Nd, hD⟩ := hD
  obtain ⟨N8, K8, h8⟩ := lz_lemma8_proved
  obtain ⟨K1, N1, h1⟩ := theorem1_legacy_H1 hRH
  let K := |Kd| + 2 * |K8| + |K1|
  have hK : ∀ N H : ℕ, max (max Nd N8) (max N1 3) ≤ N → 1 ≤ H → H ≤ N →
      ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖ ≤
        K * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
          + H * Real.log N ^ 2 * Real.log (2 * H)) := by
    intro N H hN hH hHN
    have hNd : Nd ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN8 : N8 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have hNpos : (0 : ℝ) < N := by linarith
    have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
    let E := (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H)
      + H * Real.log N ^ 2 * Real.log (2 * H)
    have hEL : (N : ℝ) * Real.log N ≤ E :=
      legacy_error_ge_N_log_N (by omega) hH hHN
    have hL1 : 1 ≤ Real.log (N : ℝ) := by
      apply (Real.le_log_iff_exp_le hNpos).mpr
      have := Real.exp_one_lt_d9
      linarith
    have hEN : (N : ℝ) ≤ E := by nlinarith
    have hE0 : 0 ≤ E := by linarith
    by_cases hHone : H = 1
    · subst H
      have he := h1 N hN1
      have hNL0 : 0 ≤ (N : ℝ) * Real.log N := by positivity
      have hbound : K1 * ((N : ℝ) * Real.log N) ≤ |K1| * E :=
        (mul_le_mul_of_nonneg_right (le_abs_self K1) hNL0).trans
          (mul_le_mul_of_nonneg_left hEL (abs_nonneg K1))
      have hKK : |K1| ≤ K := by
        dsimp [K]
        linarith [abs_nonneg Kd, abs_nonneg K8]
      simpa only [Nat.cast_one, E] using
        he.trans (hbound.trans (mul_le_mul_of_nonneg_right hKK hE0))
    · have hH2 : 2 ≤ H := by omega
      let X : ℝ := ∑ n ∈ Icc (N - H) (N + H), w N H n * (R n - (2 * ψ (n : ℝ) - n))
      let P : ℝ := ∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n)
      have hX : |X| ≤ |Kd| * E :=
        (hD N H hNd hH2 hHN).trans (mul_le_mul_of_nonneg_right (le_abs_self Kd) hE0)
      have hP : ‖(P : ℂ) + ZH N H‖ ≤ |K8| * H * N := by
        refine (h8 N H hN8 hH2 hHN).trans ?_
        have h := mul_le_mul_of_nonneg_right (le_abs_self K8)
          (mul_nonneg (Nat.cast_nonneg (α := ℝ) H) (Nat.cast_nonneg (α := ℝ) N))
        nlinarith
      have hcesaro : cesaro N H = X + H * N + 2 / H * P := by
        have hs := sum_w_mul_n hH hHN
        unfold cesaro
        dsimp [X, P]
        rw [← hs, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        apply sum_congr rfl
        intro n _
        rw [w_eq hH]
        field_simp
        <;> ring
      have hid : ((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H =
          (X : ℂ) + 2 / (H : ℂ) * ((P : ℂ) + ZH N H) := by
        rw [hcesaro]
        push_cast
        ring
      have hrem : ‖2 / (H : ℂ) * ((P : ℂ) + ZH N H)‖ ≤ 2 * |K8| * N := by
        rw [norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_natCast]
        calc
          _ ≤ 2 / (H : ℝ) * (|K8| * H * N) :=
            mul_le_mul_of_nonneg_left hP (by positivity)
          _ = _ := by field_simp
      have hremE : 2 * |K8| * (N : ℝ) ≤ 2 * |K8| * E :=
        mul_le_mul_of_nonneg_left hEN (by positivity)
      rw [hid]
      have htri := norm_add_le (X : ℂ) (2 / (H : ℂ) * ((P : ℂ) + ZH N H))
      rw [Complex.norm_real, Real.norm_eq_abs] at htri
      change _ ≤ K * E
      dsimp [K]
      nlinarith [mul_nonneg (abs_nonneg K1) hE0]
  exact absorb_small
    (fun N H => ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖)
    (fun N H => N * Real.log (2 * (N : ℝ) ^ 2 / H)
      + H * Real.log N ^ 2 * Real.log (2 * H)) 1
    (fun N H hN hH hHN => lt_of_lt_of_le
      (mul_pos (by exact_mod_cast (by omega : 0 < N))
        (Real.log_pos (by exact_mod_cast (by omega : 1 < N))))
      (legacy_error_ge_N_log_N hN hH hHN)) hK

end LeanLab.LZCesaroShort
