import LeanLab.ExceptionalSet.UpJ200.Decomp450c

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.Decomp450e`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
P0082 page 366, scalar frequency range in the dyadic application of Theorem 2.
Source: https://doi.org/10.5802/aif.1621
Logarithms at N and at the integer half index have ratio tending to one.
This supplies the other scalar input in Decomp446c without a cancellation claim.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp450e

open Real Filter
open scoped Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE expSumF)
open LeanLab.ExceptionalSet.UpJ200.Decomp404e (phaseSum)

/-- P0082 page 366, auxiliary limit for the dyadic integer half index. -/
theorem log_half_ratio :
    Tendsto (fun N : ℕ => Real.log (N / 2 : ℕ) / Real.log (N : ℝ)) atTop (𝓝 1) := by
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := hl.const_div_atTop (Real.log 4)
  have hlow : Tendsto (fun N : ℕ => 1 - Real.log 4 / Real.log (N : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hfloor : N ≤ 4 * (N / 2) := by omega
    have hfloor' : (N : ℝ) ≤ 4 * (N / 2 : ℕ) := by exact_mod_cast hfloor
    have hh : (N : ℝ) / 4 ≤ (N / 2 : ℕ) := by linarith
    have hcomp := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) / 4) hh
    rw [Real.log_div hNpos.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hcomp
    have he : 1 - Real.log 4 / Real.log (N : ℝ) =
        (Real.log (N : ℝ) - Real.log 4) / Real.log (N : ℝ) := by
      field_simp [hlog.ne']
    rw [he]
    exact div_le_div_of_nonneg_right hcomp hlog.le
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    have hh : (0 : ℝ) < (N / 2 : ℕ) := by exact_mod_cast (by omega : 0 < N / 2)
    have hhalf : ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N 2
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    exact (div_le_one hlog).mpr (Real.log_le_log hh hhalf)

/-- P0082 page 366, auxiliary eventual relative comparison of logarithm powers. -/
theorem log_half_power_lower (γ ε : ℝ) (hγ : 0 < γ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * Real.log (N : ℝ) ^ γ ≤ Real.log (N / 2 : ℕ) ^ γ := by
  have ht : Tendsto (fun N : ℕ => (Real.log (N / 2 : ℕ) / Real.log (N : ℝ)) ^ γ)
      atTop (𝓝 1) := by
    simpa only [one_rpow] using log_half_ratio.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp ht).1 (1 - ε) (by linarith))
  refine ⟨max 4 N₀, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hhlog : 0 ≤ Real.log (N / 2 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N / 2))
  have hr := (hN₀ N ((le_max_right _ _).trans hN)).le
  rw [Real.div_rpow hhlog hlog.le] at hr
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hlog γ)).mp hr

/-- P0082 page 366, exact inherited scalar frequency range leaf. -/
theorem frequency_range_supplied (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
      F γ N ^ (3 * δ - 1) < |t| → |t| ≤ 2 * F γ N ^ (6 * δ) →
        F γ (2 * (N / 2 : ℕ)) ^ (-(1 - 2 * δ)) ≤ |t| ∧
          |t| ≤ F γ (N / 2 : ℕ) ^ (12 * δ) := by
  have hγ : 0 < γ := by linarith
  have hδ12 : δ < 1 / 12 := hδsmall.trans_le (min_le_right _ _)
  obtain ⟨Nr, hr⟩ := log_half_power_lower γ δ hγ hδ
  have ht : Tendsto (fun N : ℕ => δ * Real.log (N : ℝ) ^ γ) atTop atTop :=
    (((tendsto_rpow_atTop hγ).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).const_mul_atTop hδ
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (Real.log 2))
  refine ⟨max 4 (max Nr Nl), fun N hN t htlow hthigh => ?_⟩
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNl : Nl ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hratio := hr N hNr
  have hlog2 := hl N hNl
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hhlog : 0 ≤ Real.log (N / 2 : ℕ) := Real.log_nonneg
    (by exact_mod_cast (by omega : 1 ≤ N / 2))
  have hpow : 0 ≤ Real.log (N : ℝ) ^ γ := Real.rpow_nonneg hlog _
  have hMlog : Real.log (N / 2 : ℕ) ^ γ ≤ Real.log (2 * (N / 2 : ℕ)) ^ γ := by
    apply Real.rpow_le_rpow hhlog _ hγ.le
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < N / 2))
    exact_mod_cast (by omega : N / 2 ≤ 2 * (N / 2))
  have hcoeff : 1 - 3 * δ ≤ (1 - 2 * δ) * (1 - δ) := by nlinarith
  have hlower : (1 - 3 * δ) * Real.log (N : ℝ) ^ γ ≤
      (1 - 2 * δ) * Real.log (2 * (N / 2 : ℕ)) ^ γ := by
    have ha := mul_le_mul_of_nonneg_right hcoeff hpow
    have hb := mul_le_mul_of_nonneg_left hratio (by linarith : 0 ≤ 1 - 2 * δ)
    have hc := mul_le_mul_of_nonneg_left hMlog (by linarith : 0 ≤ 1 - 2 * δ)
    nlinarith
  have hupper : Real.log 2 + 6 * δ * Real.log (N : ℝ) ^ γ ≤
      12 * δ * Real.log (N / 2 : ℕ) ^ γ := by
    have hc : 7 * δ ≤ 12 * δ * (1 - δ) := by nlinarith
    have ha := mul_le_mul_of_nonneg_right hc hpow
    have hb := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 12 * δ)
    nlinarith
  constructor
  · refine le_trans ?_ htlow.le
    simp only [F, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  · refine hthigh.trans ?_
    simp only [F, ← Real.exp_mul]
    calc
      2 * Real.exp (Real.log (N : ℝ) ^ γ * (6 * δ)) =
          Real.exp (Real.log 2 + 6 * δ * Real.log (N : ℝ) ^ γ) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        congr 2
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [hupper])

end LeanLab.ExceptionalSet.UpJ200.Decomp450e
