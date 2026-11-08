import LeanLab.ExceptionalSet.GammaTwoParameters465
import LeanLab.HeathBrown1985.DivisorEps

/-!
Elementary ranges for the split on P0082 pages361 and362.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Supply465
open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- P0082 page361 display17. The paper parameters eventually place the
finite tail between positive integer endpoints below square root X. -/
theorem gammaTwo_ranges (γ δ : ℝ) (hγ : 1 < γ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ F γ N ^ (6 * δ) ∧ 2 ≤ F γ N ^ (1 / 3 : ℝ) ∧
      ⌊F γ N ^ (6 * δ)⌋₊ ≤ ⌊F γ N ^ (1 / 3 : ℝ)⌋₊ ∧
      (⌊F γ N ^ (1 / 3 : ℝ)⌋₊ : ℝ) < F γ N ^ (1 / 2 : ℝ) ∧
      (⌊F γ N ^ (1 / 3 : ℝ)⌋₊ : ℝ) ≤ F γ N := by
  have ht : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hp := ((tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp ht).eventually_ge_atTop 2
  have hy := ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 3 : ℝ))).comp ht).eventually_ge_atTop 2
  apply eventually_atTop.mp
  filter_upwards [hp, hy, ht.eventually_gt_atTop 1] with N hP hY hX
  have hX0 : 0 < F γ N := Real.exp_pos _
  refine ⟨hP, hY, Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)), ?_, ?_⟩
  · exact (Nat.floor_le (Real.rpow_pos_of_pos hX0 _).le).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num))
  · exact (Nat.floor_le (Real.rpow_pos_of_pos hX0 _).le).trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (1 / 3 : ℝ) ≤ 1))

/-- P0082 page361 display18. A divisor bound with a fixed small exponent
is uniform below X and loses only square root P. -/
theorem gammaTwo_divisor_envelope (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (X : ℝ), 1 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X →
      (q.divisors.card : ℝ) ≤ D * (X ^ (6 * δ)) ^ (1 / 2 : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by positivity : 0 < 3 * δ)
  obtain ⟨D, hD, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow (k + 1) (by omega)
  refine ⟨D, hD, fun X hX q hq hqX => ?_⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hX0 : 0 ≤ X := by linarith
  calc
    _ ≤ D * (q : ℝ) ^ (1 / (k + 1) : ℝ) := by simpa only [one_div, Nat.cast_add, Nat.cast_one] using hτ q hq
    _ ≤ D * X ^ (1 / (k + 1) : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hq0 hqX (by positivity)) hD.le
    _ ≤ D * X ^ (3 * δ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX hk.le) hD.le
    _ = _ := by rw [← Real.rpow_mul hX0]; congr 2; ring
end LeanLab.ExceptionalSet.Supply465
