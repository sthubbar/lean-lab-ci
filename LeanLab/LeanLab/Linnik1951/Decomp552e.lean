/-
P0093 page 161 after equation 6.3. Supply for the sealed small residual leaf.
This handoff uses the existing source faithful three input decomposition.
It adds no admission and leaves the assigned file unchanged.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Data491
import LeanLab.Linnik1951.Decomp520a

namespace LeanLab.Linnik1951

/-- P0093 pages 160 and 161 equations 5.4, 5.5 and 6.3.
CONDITIONAL ON GRH, residue_square_mean520, mixed_bound520 and
principal_model520. This supplies the exact sealed small residual type
through the existing source decomposition. The three analytic inputs
remain open. No core estimate or shoulder estimate is invoked. -/
theorem local_arc_small_residual_supply552 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ 3 →
        n ≤ N →
        ‖localArc1622 N q n‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  clear hM
  obtain ⟨c, hc, N0, h⟩ := local_expansion520 hG
  refine ⟨c, hc, N0, ?_⟩
  intro N hN q hq hqQ n hn3 hnN
  have hzero : localMain520 N q n = 0 := by
    simp [localMain520, logConvolution_vanish520 n.toNat (by omega)]
  have hb := h N hN q hq hqQ n hnN
  rw [hzero, sub_zero] at hb
  exact hb

end LeanLab.Linnik1951
