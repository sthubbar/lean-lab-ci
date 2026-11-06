import LeanLab.ExceptionalSet.Decomp446c
import LeanLab.ExceptionalSet.MinorSup446
import LeanLab.ExceptionalSet.Energy446
import LeanLab.ExceptionalSet.Localization446
import LeanLab.ExceptionalSet.MomentSplit428

/-!
Truncated second moment with the three elementary integral inputs supplied.
Source: P0082 pages 365 and 366, displays 25 to 27.
The distant phase is supplied from two scalar leaves and the cited Karacuba route.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.MomentSupply446

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE)
open LeanLab.ExceptionalSet.Decomp404e
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor)

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

/-- P0082 page 366 before display 27. Exact distant moment supply,
conditional on the two scalar phase leaves and the cited Karacuba route. All integral comparisons are proved. -/
theorem far_moment_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          farMoment γ δ κ N ≤
            B * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := by
  obtain ⟨δ₀, hδ₀, hphase⟩ := Decomp446c.far_phase_assembly γ h1 h2
  obtain ⟨Ce, hCe, he⟩ := Energy446.leaf_weighted_energy_supplied
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hphase⟩ := hphase δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Cs, hCs, Ns, hs⟩ := hphase κ hκ hκsmall
  obtain ⟨Np, hp⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  refine ⟨Cs * Ce ^ 2, by positivity, max 2 (max Ns Np), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsN := hs N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨hX2, _, hΔ, hΔ1, _⟩ := hp N
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hE1 : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  have henergy := he (F γ N ^ (6 * δ)) (F γ N)
    (calE γ κ N ^ (-(1 / 8 : ℝ))) (by positivity) hX2 hΔ hΔ1
  have hlocal := Localization446.leaf_far_localization_supplied γ δ κ N
    (Cs * N * calE γ κ N ^ (-(3 / 2 : ℝ))) (by positivity) hΔ1
    (fun α hα β hβ hdist => by
      apply hsN (β - α)
      · simpa only [abs_sub_comm] using hdist
      · have ha := hα.2
        have hb := hβ.2
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])
  have hI : 0 ≤ ∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
        (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hratio : calE γ κ N ^ (-(3 / 2 : ℝ)) /
      (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 = calE γ κ N ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_sub hE]
    norm_num
  calc
    _ ≤ (Cs * N * calE γ κ N ^ (-(3 / 2 : ℝ))) *
        (Ce * F γ N * Real.log (F γ N) / calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 :=
      hlocal.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI henergy 2) (by positivity))
    _ = (Cs * Ce ^ 2) * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 *
        (calE γ κ N ^ (-(3 / 2 : ℝ)) / (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2) := by ring
    _ ≤ (Cs * Ce ^ 2) * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := by
      rw [hratio]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)) (by positivity)

/-- P0082 pages 365 and 366 displays 25 to 27. Exact truncated moment
supply, conditional on the two scalar phase leaves and the cited Karacuba route. -/
theorem truncated_moment_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨δf, hδf, hf⟩ := far_moment_supplied γ h1 h2
  obtain ⟨δn, hδn, hn⟩ := near_moment_supplied γ h1 h2
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

end LeanLab.ExceptionalSet.MomentSupply446
