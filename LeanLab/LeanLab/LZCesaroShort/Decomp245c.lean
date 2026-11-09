import LeanLab.LZCesaroShort.Decomp245a

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 page 2, Theorem 1.
This is an auxiliary reduction of the inherited legacy target.
It does not assert the unproved middle range estimate or identify it with the printed theorem.
-/

namespace LeanLab.LZCesaroShort

/-- The remaining middle range contains arbitrarily large N with H equal to two. -/
theorem legacy_middle_domain_nonempty (N₀ : ℕ) :
    ∃ N H : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧ 2 ≤ H ∧ H ≤ N ∧
      H * Real.log (2 * (H : ℝ)) < N := by
  refine ⟨max N₀ 10, 2, le_max_left _ _, by omega, le_rfl, by omega, ?_⟩
  have hN : (10 : ℝ) ≤ (max N₀ 10 : ℕ) := by exact_mod_cast le_max_right N₀ 10
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  change (2 : ℝ) * Real.log (2 * (2 : ℝ)) < ((max N₀ 10 : ℕ) : ℝ)
  rw [show (2 : ℝ) * 2 = 4 by norm_num]
  linarith

/-- Under RH, only the middle range of the exact legacy target remains to be proved.
The endpoint and large H cases are supplied by Decomp245a and small N are absorbed. -/
theorem theorem1_legacy_iff_middle (hRH : RiemannHypothesis) :
    Theorem1 ↔ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ,
      N₀ ≤ N → 2 ≤ H → H ≤ N → H * Real.log (2 * (H : ℝ)) < N →
      ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖ ≤
        K * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
          + H * Real.log N ^ 2 * Real.log (2 * H)) := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, 2, fun N H hN hH hHN _ => hK N H hN (by omega) hHN⟩
  · rintro ⟨Km, Nm, hm⟩
    obtain ⟨K1, N1, h1⟩ := theorem1_legacy_H1 hRH
    obtain ⟨Kl, hl⟩ := theorem1_legacy_large_H hRH
    let K := |Km| + |K1| + |Kl|
    have hK : ∀ N H : ℕ, max (max Nm N1) 2 ≤ N → 1 ≤ H → H ≤ N →
        ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖ ≤
          K * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
            + H * Real.log N ^ 2 * Real.log (2 * H)) := by
      intro N H hN hH hHN
      have hNm : Nm ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
      have hN1 : N1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
      have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
      let E := (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H)
        + H * Real.log N ^ 2 * Real.log (2 * H)
      have hEL : (N : ℝ) * Real.log N ≤ E := legacy_error_ge_N_log_N hN2 hH hHN
      have hE0 : 0 ≤ E := le_trans (by positivity) hEL
      by_cases hHone : H = 1
      · subst H
        have hNL0 : 0 ≤ (N : ℝ) * Real.log N := by positivity
        have hb : K1 * ((N : ℝ) * Real.log N) ≤ |K1| * E :=
          (mul_le_mul_of_nonneg_right (le_abs_self K1) hNL0).trans
            (mul_le_mul_of_nonneg_left hEL (abs_nonneg K1))
        have hKK : |K1| ≤ K := by dsimp [K]; linarith [abs_nonneg Km, abs_nonneg Kl]
        simpa only [Nat.cast_one, E] using
          (h1 N hN1).trans (hb.trans (mul_le_mul_of_nonneg_right hKK hE0))
      · have hH2 : 2 ≤ H := by omega
        by_cases hlarge : (N : ℝ) ≤ H * Real.log (2 * (H : ℝ))
        · have hb := hl N H hN2 hH hHN hlarge
          have hKK : Kl ≤ K := by dsimp [K]; linarith [le_abs_self Kl, abs_nonneg Km, abs_nonneg K1]
          exact hb.trans (mul_le_mul_of_nonneg_right hKK hE0)
        · have hb := hm N H hNm hH2 hHN (lt_of_not_ge hlarge)
          have hKK : Km ≤ K := by dsimp [K]; linarith [le_abs_self Km, abs_nonneg K1, abs_nonneg Kl]
          exact hb.trans (mul_le_mul_of_nonneg_right hKK hE0)
    exact absorb_small
      (fun N H => ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖)
      (fun N H => N * Real.log (2 * (N : ℝ) ^ 2 / H)
        + H * Real.log N ^ 2 * Real.log (2 * H)) 1
      (fun N H hN hH hHN => lt_of_lt_of_le
        (mul_pos (by exact_mod_cast (by omega : 0 < N))
          (Real.log_pos (by exact_mod_cast (by omega : 1 < N))))
        (legacy_error_ge_N_log_N hN hH hHN)) hK

end LeanLab.LZCesaroShort
