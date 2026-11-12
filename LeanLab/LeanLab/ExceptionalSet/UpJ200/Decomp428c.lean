import LeanLab.ExceptionalSet.UpJ200.Decomp404e
import LeanLab.ExceptionalSet.UpJ200.TailParameters385

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.Decomp428c`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Nearby frequency supply for P0082 page 366 display 27.
The source separates the minor prime supremum from a localized integral.
The three analytic leaves remain OPEN for Jules and Aristotle.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp428c

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE)
open LeanLab.ExceptionalSet.UpJ200.Decomp404e

/-- Page 366 after display 27. The logarithms and inverse kernel width
are subpowers of X and are absorbed in a positive delta power. -/
theorem logarithms_absorbed (γ κ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.log (F γ N) ^ 9 / calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ F γ N ^ δ := by
  obtain ⟨Nl, hl⟩ := log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  obtain ⟨Ne, he⟩ := calE_power_le_F_power γ κ (11 / 8) δ h1 hδ
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  obtain ⟨Nf, hf⟩ := eventually_atTop.mp (hF.eventually_ge_atTop (Real.exp 1))
  refine ⟨max Nl (max Ne Nf), fun N hN => ?_⟩
  have hlN := hl N ((le_max_left _ _).trans hN)
  have heN := he N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hfN := hf N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hL : 1 ≤ Real.log (F γ N) := (Real.le_log_iff_exp_le hX).mpr hfN
  have h10 : Real.log (F γ N) ^ 10 ≤ calE γ κ N ^ (5 / 4 : ℝ) := by
    have hp := pow_le_pow_left₀ (sq_nonneg (Real.log (F γ N))) hlN 5
    rw [← pow_mul, ← Real.rpow_mul_natCast hE.le] at hp
    norm_num at hp
    exact hp
  have h9 : Real.log (F γ N) ^ 9 ≤ Real.log (F γ N) ^ 10 := by
    exact pow_le_pow_right₀ hL (by norm_num)
  calc
    _ ≤ calE γ κ N ^ (5 / 4 : ℝ) / calE γ κ N ^ (-(1 / 8 : ℝ)) := by
      gcongr
      exact h9.trans h10
    _ = calE γ κ N ^ (11 / 8 : ℝ) := by
      rw [← Real.rpow_sub hE]
      norm_num
    _ ≤ _ := heN

end LeanLab.ExceptionalSet.UpJ200.Decomp428c
