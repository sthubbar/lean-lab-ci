import LeanLab.ExceptionalSet.Decomp428d
import LeanLab.ExceptionalSet.MomentSplit428

/-!
The exact truncated moment from the task428 smaller frequency leaves.
Source: P0082 pages 365 and 366, displays 25 to 27.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp428e

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor)
open LeanLab.ExceptionalSet.Decomp404e

/-- Assembly. P0082 page 366 after display 27. The exact existing truncated
moment follows from the five smaller task428 leaves and the proved
finite Gram expansion. Neither old frequency estimate is used. -/
theorem truncated_moment_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨δf, hδf, hf⟩ := Decomp428d.far_moment_assembly γ h1 h2
  obtain ⟨δn, hδn, hn⟩ := Decomp428c.near_moment_assembly γ h1 h2
  refine ⟨min δf δn, lt_min hδf hδn, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hf⟩ := hf δ hδ (hδsmall.trans_le (min_le_left _ _))
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Bf, hBf, Nf, hf⟩ := hf κ hκ hκsmall
  obtain ⟨Bn, hBn, Nn, hn⟩ := hn δ hδ (hδsmall.trans_le (min_le_right _ _)) κ hκ
  obtain ⟨Nl, hl⟩ := log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  obtain ⟨Np, hp⟩ := calE_power_le_F_power γ κ (3 / 4) (2 * δ) h1 (by positivity)
  refine ⟨Bf + Bn, add_pos hBf hBn, max 16 (max (max Nf Nn) (max Nl Np)), fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNN := (le_max_right _ _).trans hN
  have hNf : Nf ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hNN)
  have hNn : Nn ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hNN)
  have hNl : Nl ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNN)
  have hNp : Np ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNN)
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hfar : farMoment γ δ κ N ≤
      Bf * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
    calc
      _ ≤ Bf * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := hf N hNf
      _ ≤ Bf * N * F γ N ^ 2 * calE γ κ N ^ (1 / 4 : ℝ) * calE γ κ N ^ (-1 : ℝ) := by
        gcongr
        exact hl N hNl
      _ = _ := by
        rw [mul_assoc (Bf * N * F γ N ^ 2), ← Real.rpow_add hE]
        norm_num
  have hbase : F γ N ^ (2 - 2 * δ) ≤ F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
    rw [Real.rpow_sub hX, Real.rpow_two, Real.rpow_neg hE.le]
    change F γ N ^ 2 / F γ N ^ (2 * δ) ≤ F γ N ^ 2 / calE γ κ N ^ (3 / 4 : ℝ)
    exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hE _) (hp N hNp)
  have hnear : nearMoment γ δ κ N ≤
      Bn * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
    calc
      _ ≤ Bn * N * F γ N ^ (2 - 2 * δ) := hn N hNn
      _ ≤ Bn * N * (F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ))) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖truncatedMinor γ δ κ N n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Decomp371a.window_subset_Ioc γ h1 N hN16)
        (fun n _ _ => sq_nonneg _)
    _ ≤ farMoment γ δ κ N + nearMoment γ δ κ N := MomentSplit428.leaf_moment_split_supplied γ δ κ N
    _ ≤ Bf * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) +
        Bn * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := add_le_add hfar hnear
    _ = _ := by ring

end LeanLab.ExceptionalSet.Decomp428e
