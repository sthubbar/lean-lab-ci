import LeanLab.ExceptionalSet.UpJ200.Decomp371b

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.Decomp404e`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
P0082 pages 365 and 366 displays 25 to 27. Separate the moment expansion,
the distant frequency estimate and the nearby frequency estimate.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp404e

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200
open LeanLab.ExceptionalSet.UpJ200.Decomp371b (truncatedMinor)

/-- P0082 page 365 display 24. The truncated minor arc domain. -/
noncomputable def truncatedDomain (P X : ℝ) : Set ℝ :=
  (majorArcs P X)ᶜ ∩ Set.Icc (-P) P

/-- P0082 page 365 after display 25. The full dyadic index phase sum. -/
noncomputable def phaseSum (γ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (N / 2) N, eC (t * F γ n)

/-- P0082 page 366, contribution to display 26 with distant frequencies.
The integrand is the absolute majorant of the expanded complex integrand. -/
noncomputable def farMoment (γ δ κ : ℝ) (N : ℕ) : ℝ :=
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  ∫ α in truncatedDomain P X,
    ∫ β in truncatedDomain P X ∩ {β : ℝ | X ^ (3 * δ - 1) < |α - β|},
      ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖ *
        ‖Sp P X β ^ 2 * (Kfun Δ β : ℂ)‖ * ‖phaseSum γ N (β - α)‖

/-- P0082 page 366 display 27, contribution with nearby frequencies.
The boundary is included here, so this and farMoment cover the full pair domain. -/
noncomputable def nearMoment (γ δ κ : ℝ) (N : ℕ) : ℝ :=
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  ∫ α in truncatedDomain P X,
    ∫ β in truncatedDomain P X ∩ {β : ℝ | |α - β| ≤ X ^ (3 * δ - 1)},
      ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖ *
        ‖Sp P X β ^ 2 * (Kfun Δ β : ℂ)‖ * ‖phaseSum γ N (β - α)‖

/-- P0082 page 366 parameter absorption. Every fixed power of calE is
eventually bounded by every positive fixed power of X when gamma exceeds 1. -/
theorem calE_power_le_F_power (γ κ r t : ℝ) (hγ : 1 < γ) (ht : 0 < t) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → calE γ κ N ^ r ≤ F γ N ^ t := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun N : ℕ => κ * r * Real.log N ^ (3 - 3 * γ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by linarith : 0 < -(3 - 3 * γ))).comp hlog)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hr.eventually (gt_mem_nhds ht)] with N hN hrN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hp : 0 < Real.log N ^ γ := Real.rpow_pos_of_pos hL _
  have he : Real.log N ^ (3 - 3 * γ) * Real.log N ^ γ = Real.log N ^ (3 - 2 * γ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hrN.le hp.le
  rw [mul_assoc, he] at hm
  rw [calE, F, ← Real.exp_mul, ← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- P0082 page 366 after display 27. A quarter power of calE
absorbs the two logarithms in the distant frequency estimate. -/
theorem log_F_sq_le_calE_quarter (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.log (F γ N) ^ 2 ≤ calE γ κ N ^ (1 / 4 : ℝ) := by
  let a := 3 - 2 * γ
  have ha : 0 < a := by dsimp [a]; linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop ha).comp hlog
  have hs := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * γ / a) (κ / 4) (by positivity)).comp ht
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN hsN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hpow : (Real.log N ^ a) ^ (2 * γ / a) = (Real.log N ^ γ) ^ 2 := by
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul_natCast hL.le]
    congr 1
    field_simp
    norm_num
  change (Real.log N ^ a) ^ (2 * γ / a) * Real.exp (-(κ / 4) * Real.log N ^ a) < 1 at hsN
  rw [hpow, show -(κ / 4) * Real.log N ^ a = -(κ * Real.log N ^ a * (1 / 4)) by ring,
    Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)] at hsN
  simpa only [F, Real.log_exp, calE, ← Real.exp_mul, one_mul] using hsN.le

end LeanLab.ExceptionalSet.UpJ200.Decomp404e
