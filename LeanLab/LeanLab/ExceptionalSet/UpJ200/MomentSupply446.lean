import LeanLab.ExceptionalSet.UpJ200.PhaseInterval446
import LeanLab.ExceptionalSet.UpJ200.MinorSup446
import LeanLab.ExceptionalSet.UpJ200.Energy446
import LeanLab.ExceptionalSet.UpJ200.Localization446
import LeanLab.ExceptionalSet.UpJ200.MomentSplit428

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.MomentSupply446`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Truncated second moment with the three elementary integral inputs supplied.
Source: P0082 pages 365 and 366, displays 25 to 27.
The distant phase is supplied from two scalar leaves and the cited Karacuba route.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.MomentSupply446

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE)
open LeanLab.ExceptionalSet.UpJ200.Decomp404e
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp371b (truncatedMinor)

/-- P0082 page 366 display 27. Exact nearby moment supply, with the prime minor supremum and all integral comparisons proved. -/
theorem near_moment_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ κ : ℝ, 0 < κ → ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        nearMoment γ δ κ N ≤ B * N * F γ N ^ (2 - 2 * δ) := by
  obtain ⟨δ₀, hδ₀, hs⟩ := MinorSup446.leaf_minor_sup_supplied γ h1 h2
  obtain ⟨Ce, hCe, he⟩ := Energy446.leaf_weighted_energy_supplied
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall κ hκ => ?_⟩
  obtain ⟨Cs, hCs, Ns, hs⟩ := hs δ hδ hδsmall
  obtain ⟨Na, ha⟩ := Decomp428c.logarithms_absorbed γ κ δ h1 h2 hκ hδ
  obtain ⟨Np, hp⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  refine ⟨4 * Cs * Ce, by positivity, max Ns (max Na Np), fun N hN => ?_⟩
  have hsN := hs N ((le_max_left _ _).trans hN)
  have haN := ha N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨hX2, hP4, hΔ, hΔ1, _⟩ := hp N
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hX : 0 < F γ N := Real.exp_pos _
  have hL : 0 ≤ Real.log (F γ N) := Real.log_nonneg (by linarith)
  have henergy := he (F γ N ^ (6 * δ)) (F γ N)
    (calE γ κ N ^ (-(1 / 8 : ℝ))) (by positivity) hX2 hΔ hΔ1
  have hlocal := Localization446.leaf_localization_supplied γ δ κ N
    (Cs * F γ N ^ (2 - 6 * δ) * Real.log (F γ N) ^ 8) (by positivity) hΔ1 hsN
  have hpowers : F γ N ^ (3 * δ - 1) * F γ N ^ (2 - 6 * δ) * F γ N =
      F γ N ^ (2 - 3 * δ) := by
    calc
      _ = F γ N ^ ((3 * δ - 1) + (2 - 6 * δ) + 1) := by
        rw [Real.rpow_add hX, Real.rpow_add hX, Real.rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ ≤ 4 * N * F γ N ^ (3 * δ - 1) *
        (Cs * F γ N ^ (2 - 6 * δ) * Real.log (F γ N) ^ 8) *
          (Ce * F γ N * Real.log (F γ N) / calE γ κ N ^ (-(1 / 8 : ℝ))) := by
      exact hlocal.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
    _ = (4 * Cs * Ce) * N * F γ N ^ (2 - 3 * δ) *
        (Real.log (F γ N) ^ 9 / calE γ κ N ^ (-(1 / 8 : ℝ))) := by
      rw [show Real.log (F γ N) ^ 9 = Real.log (F γ N) ^ 8 * Real.log (F γ N) by ring]
      have hm := hpowers
      linear_combination 4 * Cs * Ce * (N : ℝ) * Real.log (F γ N) ^ 8 *
        Real.log (F γ N) / calE γ κ N ^ (-(1 / 8 : ℝ)) * hm
    _ ≤ (4 * Cs * Ce) * N * F γ N ^ (2 - 3 * δ) * F γ N ^ δ := by
      gcongr
    _ = _ := by
      rw [mul_assoc ((4 * Cs * Ce) * N), ← Real.rpow_add hX]
      congr 2
      ring

end LeanLab.ExceptionalSet.UpJ200.MomentSupply446
