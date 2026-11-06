import LeanLab.ExceptionalSet.Decomp371b

/-!
P0082 page 365 display 24. Separate the finite scale tail estimate from
its eventual comparison with the exceptional set threshold.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp404c

open Real MeasureTheory Filter Topology
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.DecompJ200
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor)

/-- P0082 page 365 display 24. For positive delta, its power saving
absorbs the logarithm and both subpower factors in the tail threshold. -/
theorem tail_scale_eventually (γ δ κ C : ℝ) (hγ : 1 < γ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      C * F γ N * Real.log (F γ N) ^ 2 /
        (calE γ κ N ^ (-(1 / 8 : ℝ)) * F γ N ^ (6 * δ)) ≤
          F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => Real.log N ^ γ) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog
  have hr : Tendsto (fun N : ℕ => κ * (11 / 24 : ℝ) * Real.log N ^ (3 - 3 * γ))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by linarith : 0 < -(3 - 3 * γ))).comp hlog)
  have hs : Tendsto (fun N : ℕ => C * ((Real.log N ^ γ) ^ 2 *
      Real.exp (-(5 * δ) * Real.log N ^ γ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (5 * δ) (by positivity)).comp ht)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hr.eventually (gt_mem_nhds hδ),
    hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N hN hrN hsN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hp : 0 < Real.log N ^ γ := Real.rpow_pos_of_pos hL _
  have he : Real.log N ^ (3 - 3 * γ) * Real.log N ^ γ = Real.log N ^ (3 - 2 * γ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hsmall : κ * (11 / 24 : ℝ) * Real.log N ^ (3 - 2 * γ) ≤ δ * Real.log N ^ γ := by
    have hm := mul_le_mul_of_nonneg_right hrN.le hp.le
    rw [mul_assoc, he] at hm
    exact hm
  have hratio : C * (Real.log N ^ γ) ^ 2 *
      Real.exp (κ * (11 / 24 : ℝ) * Real.log N ^ (3 - 2 * γ) - 6 * δ * Real.log N ^ γ) ≤ 1 / 2 := by
    calc
      _ ≤ C * (Real.log N ^ γ) ^ 2 * Real.exp (-(5 * δ) * Real.log N ^ γ) := by
        gcongr
        linarith
      _ ≤ _ := by nlinarith [hsN]
  have hF : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hD : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) * F γ N ^ (6 * δ) := by positivity
  rw [div_le_iff₀ hD]
  have hpowF : F γ N ^ (6 * δ) = Real.exp (6 * δ * Real.log N ^ γ) := by
    rw [F, ← Real.exp_mul]
    congr 1
    ring
  have hpowE (r : ℝ) : calE γ κ N ^ r = Real.exp (κ * Real.log N ^ (3 - 2 * γ) * r) := by
    rw [calE, ← Real.exp_mul]
  have hlogF : Real.log (F γ N) = Real.log N ^ γ := Real.log_exp _
  rw [hlogF, hpowF, hpowE, hpowE]
  have hm := mul_le_mul_of_nonneg_right hratio
    (Real.exp_pos (κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 3 : ℝ)) +
      κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 8 : ℝ)) + 6 * δ * Real.log N ^ γ)).le
  have hcancel :
      Real.exp (κ * (11 / 24 : ℝ) * Real.log N ^ (3 - 2 * γ) - 6 * δ * Real.log N ^ γ) *
      Real.exp (κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 3 : ℝ)) +
        κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 8 : ℝ)) + 6 * δ * Real.log N ^ γ) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  rw [mul_assoc, hcancel, mul_one] at hm
  have hexpand : Real.exp (κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 3 : ℝ)) +
      κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 8 : ℝ)) + 6 * δ * Real.log N ^ γ) =
      Real.exp (κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 3 : ℝ))) *
        Real.exp (κ * Real.log N ^ (3 - 2 * γ) * (-(1 / 8 : ℝ))) *
          Real.exp (6 * δ * Real.log N ^ γ) := by rw [Real.exp_add, Real.exp_add]
  rw [hexpand] at hm
  nlinarith [mul_le_mul_of_nonneg_left hm hF.le]

/-- LEAF. P0082 page 365, the unit interval tail estimate before display 24,
using page 357 display 4 and the prime mean square on one period. The paper
has one logarithm. Two logarithms suffice here and allow the elementary
bound on the sum of the squared prime logarithms. This leaf contains no
asymptotic parameters and no exceptional set count. -/
theorem leaf_tail_integral : ∃ C : ℝ, 0 < C ∧
    ∀ P X Δ v : ℝ, 2 ≤ P → 2 ≤ X → 0 < Δ → Δ < 1 / 4 →
      ‖(∫ α in (majorArcs P X)ᶜ,
          Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) -
        (∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-P) P,
          Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v)))‖ ≤
            C * X * Real.log X ^ 2 / (Δ * P) := by
  sorry

/-- Assembly. P0082 page 365 display 24. This has the exact existing
leaf_tail statement. Only the finite scale tail estimate remains open. -/
theorem tail_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ,
      ‖minorInt γ δ κ N n - truncatedMinor γ δ κ N n‖ ≤
        F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 := by
  obtain ⟨C, hC, htail⟩ := leaf_tail_integral
  obtain ⟨Ns, hs⟩ := tail_scale_eventually γ δ κ C h1 hδ hC
  obtain ⟨Np, hp⟩ := PrimeKernel264.split_parameters_eventually γ δ κ 1 h1 h2 hδ hκ (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  have hD : Tendsto (fun N : ℕ => calE γ κ N ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 8 : ℝ))).comp hE
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop Ns, eventually_ge_atTop Np,
    hF.eventually_ge_atTop 2, hD.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
    with N hNs hNp hFN hDN
  intro n
  exact (htail _ _ _ _ (hp N hNp).1 hFN (hp N hNp).2.1 hDN).trans (hs N hNs)


end LeanLab.ExceptionalSet.Decomp404c
