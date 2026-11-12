import LeanLab.ExceptionalSet.UpJ200.PrimeTail385
import LeanLab.ExceptionalSet.UpJ200.Decomp371b

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.TailParameters385`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Elementary parameter absorption for P0082 page 365 display 24.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.TailParameters385

open Real Filter Topology MeasureTheory Set
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE majorArcs)

/-- The larger logarithmic power absorbs the smaller exponential and logarithmic factor.
Source: P0082 page 365, display 24 with the parameters on pages 354, 355, 357 and 359. -/
theorem eventually_tail_factor (γ s δ κ : ℝ) (hγ : 0 < γ) (hs : s < γ) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop,
      8 * Real.log 4 * t ^ γ * Real.exp ((11 / 24 : ℝ) * κ * t ^ s) ≤
        Real.exp (6 * δ * t ^ γ) := by
  have hr : Tendsto (fun t : ℝ => ((11 / 24 : ℝ) * κ) * t ^ (s - γ)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < γ - s)).const_mul
      ((11 / 24 : ℝ) * κ) using 1 <;> congr 2 <;> ring
  have hb := hr.eventually_le_const (show 0 < 3 * δ by positivity)
  have hp := ((isLittleO_rpow_exp_pos_mul_atTop (1 : ℝ)
    (show 0 < 3 * δ by positivity)).const_mul_left (8 * Real.log 4)).bound
      (show (0 : ℝ) < 1 by norm_num)
  have hp' := (tendsto_rpow_atTop hγ).eventually hp
  filter_upwards [hb, hp', eventually_gt_atTop (0 : ℝ)] with t ht hp ht0
  have htγ := Real.rpow_pos_of_pos ht0 γ
  have hd : (11 / 24 : ℝ) * κ * t ^ s ≤ 3 * δ * t ^ γ := by
    rw [Real.rpow_sub ht0] at ht
    exact (div_le_iff₀ htγ).mp (by simpa only [mul_div_assoc] using ht)
  have hp2 : 8 * Real.log 4 * t ^ γ ≤ Real.exp (3 * δ * t ^ γ) := by
    simpa only [Real.rpow_one, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (show 0 ≤ 8 * Real.log 4 * t ^ γ by positivity),
      abs_of_pos (Real.exp_pos _)] using hp
  calc
    _ ≤ Real.exp (3 * δ * t ^ γ) * Real.exp (3 * δ * t ^ γ) :=
      mul_le_mul hp2 (Real.exp_le_exp.mpr hd) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The paper parameters eventually put the explicit discarded tail below half the level.
Source: P0082 page 365 display 24 and pages 354, 355, 357 and 359, the parameter definitions. -/
theorem tail_parameters_eventually (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ F γ N ∧ 4 ≤ F γ N ^ (6 * δ) ∧
      0 < calE γ κ N ^ (-(1 / 8 : ℝ)) ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 ∧
      4 * (Real.log 4 * F γ N * Real.log (F γ N)) /
          (calE γ κ N ^ (-(1 / 8 : ℝ)) * Real.pi ^ 2 * F γ N ^ (6 * δ)) ≤
        F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  have hb := hlog.eventually
    (eventually_tail_factor γ (3 - 2 * γ) δ κ (by linarith) (by linarith) hδ)
  apply Filter.eventually_atTop.mp
  filter_upwards [hb, hF.eventually_ge_atTop 2, hP.eventually_ge_atTop 4,
    hE.eventually_ge_atTop 2] with N hb hX hP hE
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hE0 : 0 < calE γ κ N := Real.exp_pos _
  have hd0 : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hE0 _
  have hP0 : 0 < F γ N ^ (6 * δ) := Real.rpow_pos_of_pos hX0 _
  refine ⟨hX, hP, hd0,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num), ?_⟩
  have hfac : 8 * Real.log 4 * Real.log (F γ N) * calE γ κ N ^ (11 / 24 : ℝ) ≤
      F γ N ^ (6 * δ) := by
    simp only [F, calE, Real.log_exp, ← Real.exp_mul]
    convert hb using 1 <;> congr 1 <;> ring
  have hid : calE γ κ N ^ (11 / 24 : ℝ) *
      (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ))) = 1 := by
    rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]
    norm_num
  have hc : 8 * Real.log 4 * Real.log (F γ N) ≤
      F γ N ^ (6 * δ) *
        (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ))) := by
    calc
      _ = (8 * Real.log 4 * Real.log (F γ N) * calE γ κ N ^ (11 / 24 : ℝ)) *
          (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ))) := by
        calc
          _ = (8 * Real.log 4 * Real.log (F γ N)) *
              (calE γ κ N ^ (11 / 24 : ℝ) *
                (calE γ κ N ^ (-(1 / 3 : ℝ)) * calE γ κ N ^ (-(1 / 8 : ℝ)))) := by
            rw [hid, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac (by positivity)
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hcpi := hc.trans (le_mul_of_one_le_right (by positivity) hpi)
  have hscaled := mul_le_mul_of_nonneg_left hcpi hX0.le
  apply (div_le_iff₀ (show 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) * Real.pi ^ 2 *
    F γ N ^ (6 * δ) by positivity)).mpr
  nlinarith only [hscaled]

end LeanLab.ExceptionalSet.UpJ200.TailParameters385
