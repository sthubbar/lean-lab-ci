import LeanLab.LZCesaroShort.DecompJ330
import LeanLab.LZCesaroShort.Theorem2bEndpoint245

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 page 2 and page 8.
These are the exact sealed legacy cited declarations moved from Statements.
They remain CONDITIONAL ON the unresolved legacy leaves and RH.
They are not proofs of the legacy estimates from RH alone.
-/

namespace LeanLab.LZCesaroShort

open scoped Chebyshev

/-- The legacy cited Theorem 1, conditional on theorem1_leaf_4 and RH. -/
theorem lz_theorem1 : RiemannHypothesis → Theorem1 := theorem1_assembly

/-- The legacy cited Theorem 2b, conditional on theorem1_leaf_2 and RH. -/
theorem lz_theorem2b : RiemannHypothesis → Theorem2b := by
  intro hRH
  obtain ⟨Kb, Nb, hb⟩ := theorem1_leaf_2 hRH
  let C := 5 * (Real.log 4 + 4) + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlarge : ∀ N H : ℕ, max Nb 2 ≤ N → 1 ≤ H → H ≤ N →
      |wsum N H H| ≤ (|Kb| + C) * (N * Real.log (2 * (N : ℝ) ^ 2 / H)) := by
    intro N H hN hH hHN
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
    have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
    have harg : (N : ℝ) ≤ 2 * (N : ℝ) ^ 2 / H := by
      rw [le_div_iff₀ hHpos]
      nlinarith
    have hlog := Real.log_le_log (by linarith : (0 : ℝ) < N) harg
    have hE0 : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H) := by
      have h0 := le_trans hlogN hlog
      positivity
    by_cases hHone : H = 1
    · subst H
      simp only [Nat.cast_one] at *
      have h1 := theorem2b_legacy_H1 hN2
      have hcmp := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ C * N)
      dsimp [C] at *
      nlinarith [mul_nonneg (abs_nonneg Kb) hE0]
    · have hH2 : 2 ≤ H := by omega
      have hg := filter_eq_Icc (N := N) (H := H) (i := 2 * H) hHN le_rfl
      have heq : ((2 * H : ℕ) : ℝ) - H = H := by push_cast; ring
      rw [heq] at hg
      have hNH : N - H + 2 * H = N + H := by omega
      rw [hNH] at hg
      have hw : wsum N H H = ∑ j ∈ Finset.range (2 * H + 1),
          Real.exp (-((N - H + j : ℕ) : ℝ) / N) * (R (N - H + j)
            - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ)))
              * w N H (N - H + j) := by
        unfold wsum
        rw [hg, ← hNH, sum_Icc_eq_range]
      rw [hw]
      have hb' := hb N H (le_trans (le_max_left _ _) hN) hH2 hHN
      have hKK : Kb ≤ |Kb| + C := by linarith [le_abs_self Kb]
      have hb'' := hb'
      rw [mul_assoc Kb] at hb''
      exact hb''.trans (mul_le_mul_of_nonneg_right hKK hE0)
  obtain ⟨K, hK⟩ := absorb_small (fun N H => |wsum N H H|)
    (fun N H => N * Real.log (2 * (N : ℝ) ^ 2 / H)) 1
    (fun N H hN hH hHN => by
      have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
      have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
      have harg : (1 : ℝ) < 2 * (N : ℝ) ^ 2 / H := by
        rw [lt_div_iff₀ (by linarith : (0 : ℝ) < H)]
        nlinarith
      have hlog := Real.log_pos harg
      positivity) hlarge
  refine ⟨K, fun N H hN hH hHN => ?_⟩
  simpa only [mul_assoc] using hK N H hN hH hHN

end LeanLab.LZCesaroShort
