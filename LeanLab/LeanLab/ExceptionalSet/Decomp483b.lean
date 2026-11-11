import LeanLab.ExceptionalSet.Decomp483a
import LeanLab.ExceptionalSet.Decomp467a

/-!
P0082 page362 Lemma7 and page368 displays33 to35.
The conductor range is elementary.
A smaller free kernel width keeps a margin for the logarithmic error factors.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Decomp483b
open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE)

/-- P0082 page362 Lemma7, auxiliary conductor range step. The witness one
lies below the positive prime cutoff. No coefficient bound is asserted here. -/
theorem conductor_in_range_supplied (γ δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) := by
  refine ⟨1, le_rfl, ?_⟩
  have hF : 1 ≤ F γ N := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _
  simpa only [Nat.cast_one] using Real.one_le_rpow hF (by linarith : 0 ≤ 6 * δ)

/-- P0082 page368 displays33 to35, derived free width margin. A width
E to minus five twelfths absorbs the two logarithms at the required minus one third level. -/
theorem odd_error_log_absorption (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.log (F γ N) ^ 2 * calE γ κ N ^ (-(5 / 12 : ℝ)) ≤
        calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨Nl, hl⟩ := Decomp467a.log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
  refine ⟨Nl, fun N hN => ?_⟩
  have hE : 0 < calE γ κ N := Real.exp_pos _
  calc _ ≤ calE γ κ N ^ (1 / 12 : ℝ) * calE γ κ N ^ (-(5 / 12 : ℝ)) :=
      mul_le_mul_of_nonneg_right (hl N hN) (Real.rpow_pos_of_pos hE _).le
    _ = _ := by rw [← Real.rpow_add hE]; norm_num

end LeanLab.ExceptionalSet.Decomp483b
