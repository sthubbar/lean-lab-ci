/-
P0093 page 166 equation 9.2 and page 167 equation 10.1.
Auxiliary check of the crude bound obtained by discarding exceptional set savings.
The statement concerns the crude bound itself. No paper error is asserted.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Repair493Data

namespace LeanLab.Linnik1951

/-- The full period bound with k powers of the logarithm cannot be arbitrarily
small relative to scale111 along large even integers. The two missing logarithmic
powers require an additional saving. Source: P0093 pages 166 and 167. -/
theorem crude_bound_not_negligible493 (k : ℕ) (hk : 3 ≤ k) (C : ℝ) (hC : 0 < C) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      C * (N : ℝ) * (Real.log N / Real.log 2) ^ k ≤ ε * scale111 k N) := by
  intro h
  obtain ⟨N0, hN0⟩ := h C hC
  let N : ℕ := 2 * (N0 + 2)
  have hN : N0 < N := by dsimp [N]; omega
  have h2 : 2 < N := by dsimp [N]; omega
  have hev : Even N := ⟨N0 + 2, by dsimp [N]; omega⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 < Real.log N :=
    Real.log_lt_log (by norm_num) (by exact_mod_cast h2)
  let t : ℝ := Real.log N / Real.log 2
  have ht : 1 < t := by
    dsimp [t]
    exact (lt_div_iff₀ hl2).mpr (by simpa using hl)
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hp : t ^ k = t ^ (k - 2) * t ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hb := hN0 N hev hN
  change C * (N : ℝ) * t ^ k ≤ C * ((N : ℝ) * t ^ (k - 2)) at hb
  rw [hp] at hb
  have hpos : 0 < C * (N : ℝ) * t ^ (k - 2) := by positivity
  have hgap : 0 < t ^ 2 - 1 := by nlinarith
  have hgt := mul_pos hpos hgap
  nlinarith

end LeanLab.Linnik1951
