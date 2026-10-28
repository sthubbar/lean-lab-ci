import LeanLab.Grimmelt2019.Prop21
import Mathlib.Analysis.Fourier.FourierTransform

namespace LeanLab.Grimmelt2019.Decomp

open Real
open LeanLab.Grimmelt2019.Prop21
open MeasureTheory
open Complex

/-- LEAF page 7: Lemma 5.1 minorization: nu is bounded by LamP. -/
theorem leaf_nu_le (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : ∀ n, o.ν n ≤ LamP X n := by
  intro n
  exact o.nu_le n

/-- LEAF page 7: Lemma 5.1 minorization: omega is bounded by LamP. -/
theorem leaf_omega_le (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : ∀ n, o.ω n ≤ LamP X n := by
  intro n
  exact o.omega_le n

/-- LEAF page 7: Lemma 5.1 window support. -/
theorem leaf_omega_window (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : ∀ n : ℤ, o.ω n ≠ 0 → X - 3 * Y < (n : ℝ) ∧ (n : ℝ) ≤ X - Y := by
  intro n hn
  exact o.omega_window n hn

/-- LEAF page 7: nu is supported on the window. -/
theorem leaf_nu_supp (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : SuppIn (supp X) o.ν := by
  exact o.nu_supp

/-- LEAF page 7: omega is supported on the window. -/
theorem leaf_omega_supp (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : SuppIn (supp X) o.ω := by
  exact o.omega_supp

/-- LEAF page 7: omega L2 norm bound. -/
theorem leaf_omega_norm (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : sqn (supp X) o.ω ≤ K * Y * Real.log Y ^ B := by
  exact o.omega_norm

/-- LEAF page 7: T is supported on the window. -/
theorem leaf_T_supp (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : SuppIn (supp X) o.T := by
  exact o.T_supp

/-- LEAF page 7: Tp is supported on the window. -/
theorem leaf_Tp_supp (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : SuppIn (supp X) o.Tp := by
  exact o.Tp_supp

/-- LEAF page 7: Tp is nonnegative. -/
theorem leaf_Tp_nonneg (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : ∀ n, 0 ≤ o.Tp n := by
  intro n
  exact o.Tp_nonneg n

/-- LEAF page 7: Lemma 4.2 T approximation. -/
theorem leaf_lemma42 (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A)) (fun n => o.T n - o.Tp n) := by
  exact o.lemma42

/-- LEAF page 7: Corollary 4.3 nu approximation. -/
theorem leaf_cor43 (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A)) (fun n => o.ν n - o.Tp n) := by
  exact o.cor43

/-- LEAF page 10: Main term lower bound. -/
theorem leaf_mainTerm (X Y H K B A c : ℝ) (o : Sec5Objects X Y H K B A c) : (((win X H).filter (fun n => Even n ∧ conv (supp X) o.ω o.T n < c * Y)).card : ℝ) ≤ K * H / Real.log X ^ A := by
  exact o.mainTerm

/-- LEAF page 10: Assembly theorem for the full bundle. -/
theorem section5Inputs_assembly : Section5Inputs := by
  intro ε hε
  sorry

end LeanLab.Grimmelt2019.Decomp
