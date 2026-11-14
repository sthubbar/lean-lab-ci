import LeanLab.ExceptionalSet.Decomp404e
import LeanLab.ExceptionalSet.TailParameters385

/-!
Nearby frequency supply for P0082 page 366 display 27.
The source separates the minor prime supremum from a localized integral.
The three analytic leaves remain OPEN for Jules and Aristotle.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp428c

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE)
open LeanLab.ExceptionalSet.Decomp404e

/-- LEAF. P0082 page 366 after display 27. Vaughan Theorem 3.1 gives
the squared prime sum bound on the literal minor arc complement.
No second moment or exceptional count is asserted. -/
theorem leaf_minor_sup (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ β ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
          ‖Sp (F γ N ^ (6 * δ)) (F γ N) β‖ ^ 2 ≤
            C * F γ N ^ (2 - 6 * δ) * Real.log (F γ N) ^ 8 := by
  exact UpJ200.MinorSup446.leaf_minor_sup_supplied γ h1 h2

/-- LEAF. P0082 page 365 before display 24 and page 366 display 27.
The weighted prime energy on the truncated domain is at most a constant
times X log X over Delta. This deliberately retains the inverse Delta loss
from the unit interval kernel bound. No minor arc cancellation is used. -/
theorem leaf_weighted_energy : ∃ C : ℝ, 0 < C ∧
    ∀ P X Δ : ℝ, 0 < P → 2 ≤ X → 0 < Δ → Δ < 1 →
      (∫ α in truncatedDomain P X, ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖) ≤
        C * X * Real.log X / Δ := by
  exact UpJ200.Energy446.leaf_weighted_energy_supplied

/-- LEAF. P0082 page 366 display 27. Bound the finite phase sum by N
and the second kernel by 2. The strip has length at most twice its radius.
The explicit supremum premise concerns only the prime sum on that strip. -/
theorem leaf_localization (γ δ κ : ℝ) (N : ℕ) (U : ℝ)
    (hU : 0 ≤ U) (hΔ : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hsup : ∀ β ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ‖Sp (F γ N ^ (6 * δ)) (F γ N) β‖ ^ 2 ≤ U) :
    nearMoment γ δ κ N ≤
      4 * N * F γ N ^ (3 * δ - 1) * U *
        (∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
          ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
            (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖) := by
  exact UpJ200.Localization446.leaf_localization_supplied γ δ κ N U hU hΔ hsup

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

/-- Assembly. P0082 page 366 display 27. This is the exact existing
Decomp404e.leaf_near_moment statement from the three smaller leaves.
The inverse Delta loss is absorbed only after fixing positive delta and kappa. -/
theorem near_moment_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ κ : ℝ, 0 < κ → ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        nearMoment γ δ κ N ≤ B * N * F γ N ^ (2 - 2 * δ) := by
  obtain ⟨δ₀, hδ₀, hs⟩ := leaf_minor_sup γ h1 h2
  obtain ⟨Ce, hCe, he⟩ := leaf_weighted_energy
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall κ hκ => ?_⟩
  obtain ⟨Cs, hCs, Ns, hs⟩ := hs δ hδ hδsmall
  obtain ⟨Na, ha⟩ := logarithms_absorbed γ κ δ h1 h2 hκ hδ
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
  have hlocal := leaf_localization γ δ κ N
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

end LeanLab.ExceptionalSet.Decomp428c
