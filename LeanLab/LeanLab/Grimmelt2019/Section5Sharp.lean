/-
AI wrote this Lean code for CODEX task03.
P0074 pages 11 to 14. Analytic estimates remain explicit inputs.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Section5Characters
import LeanLab.Grimmelt2019.SharpBudget

namespace LeanLab.Grimmelt2019.Section5Characters
open LeanLab.Grimmelt2019.Prop21 LeanLab.Grimmelt2019.MainTerm
attribute [local instance] Classical.propDecidable

/-- Section 5 source data with the sharp character budget. -/
structure Sec5ObjectsSharp (X Y H K B A c : ℝ) where
  ν : ℤ → ℝ
  ω : ℤ → ℝ
  Tp : ℤ → ℝ
  cν : ℝ
  cω : ℝ
  Q : ℕ
  E : ℝ
  s0 : ℝ
  /-- Lemma 5.1, page 12. -/
  nu_le : ∀ n, ν n ≤ LamP X n
  omega_le : ∀ n, ω n ≤ LamP X n
  omega_window : ∀ n : ℤ, ω n ≠ 0 → X - 3 * Y < (n : ℝ) ∧ (n : ℝ) ≤ X - Y
  nu_supp : SuppIn (supp X) ν
  omega_supp : SuppIn (supp X) ω
  omega_norm : sqn (supp X) ω ≤ K * Y * Real.log Y ^ B
  /-- The model before Lemma 4.2, page 11. -/
  T_supp : SuppIn (supp X) (Tnu cν Y Q)
  Tp_supp : SuppIn (supp X) Tp
  Tp_nonneg : ∀ n, 0 ≤ Tp n
  /-- Lemma 4.2 and Corollary 4.3, pages 11 and 12. -/
  lemma42 : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A))
    (fun n => Tnu cν Y Q n - Tp n)
  cor43 : FourierClose (supp X) H (K * Y * Real.log Y ^ (-A)) (fun n => ν n - Tp n)
  /-- The lower constants in Lemma 5.1, page 12. -/
  cnu_lower : (1 / 20 : ℝ) < cν
  comega_lower : (9 / 100 : ℝ) < cω
  E_nonneg : 0 ≤ E
  /-- The literal condition 29, including the real cutoff restriction. -/
  char29 : ∀ q ∈ Finset.Icc 1 Q, PaperCondition29 X Y q ω cω E
  /-- Q-rough support in Lemma 5.1, with the definition on page 5. -/
  rough : ∀ m ∈ omegaRange X Y, ω m ≠ 0 → QRough Q m
  /-- Singular series completion on page 14, still a cited analytic input. -/
  singSeries : (((win X H).filter (fun n => Even n ∧
    (∑ q ∈ Finset.Icc 1 Q, |(ArithmeticFunction.moebius q : ℝ)| /
      (q.totient : ℝ) ^ 2 * ram q n) < s0)).card : ℝ) ≤ K * H / Real.log X ^ A
  /-- Explicit large scale geometry needed for the exact window. -/
  Y_nonneg : 0 ≤ Y
  left_large : 1 ≤ X - 3 * Y
  H_lt_Y : H < Y
  /-- The sharp arithmetic budget follows from the scalar log estimates at large scales. -/
  budget : c * Y ≤ cν * cω * Y * s0 - cν * (Q : ℝ) * Real.sqrt Q * (2 * E + |cω|)

/-- The sharp convolution error gives exactly the required main-term exception field. -/
theorem Sec5ObjectsSharp.mainTerm_count {X Y H K B A c : ℝ}
    (o : Sec5ObjectsSharp X Y H K B A c) :
    (((win X H).filter (fun n => Even n ∧
      conv (supp X) o.ω (Tnu o.cν Y o.Q) n < c * Y)).card : ℝ) ≤
      K * H / Real.log X ^ A := by
  have hcν : 0 ≤ o.cν := by linarith [o.cnu_lower]
  have hcω : 0 ≤ o.cω := by linarith [o.comega_lower]
  have hsub : (win X H).filter (fun n => Even n ∧
      conv (supp X) o.ω (Tnu o.cν Y o.Q) n < c * Y) ⊆
      (win X H).filter (fun n => Even n ∧ SQ o.Q n < o.s0) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, hn.2.1, ?_⟩
    by_contra hs
    have hs' : o.s0 ≤ SQ o.Q n := not_lt.mp hs
    have h := conv_Tnu_approx_paperCondition29 o.Y_nonneg o.left_large o.H_lt_Y
      o.E_nonneg hcν o.char29 o.rough n hn.1
    have h2 := (abs_le.mp h).1
    have h3 := mul_le_mul_of_nonneg_left hs'
      (mul_nonneg (mul_nonneg hcν hcω) o.Y_nonneg)
    linarith [o.budget, hn.2.2]
  have hcard : (((win X H).filter (fun n => Even n ∧
      conv (supp X) o.ω (Tnu o.cν Y o.Q) n < c * Y)).card : ℝ) ≤
      ((win X H).filter (fun n => Even n ∧ SQ o.Q n < o.s0)).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (by simpa only [SQ_eq_abs_moebius] using o.singSeries)

/-- Direct conversion preserves the sharp budget and bypasses the legacy Q squared object. -/
noncomputable def Sec5ObjectsSharp.toSec5 {X Y H K B A c : ℝ}
    (o : Sec5ObjectsSharp X Y H K B A c) : Sec5Objects X Y H K B A c where
  ν := o.ν
  ω := o.ω
  T := Tnu o.cν Y o.Q
  Tp := o.Tp
  nu_le := o.nu_le
  omega_le := o.omega_le
  omega_window := o.omega_window
  nu_supp := o.nu_supp
  omega_supp := o.omega_supp
  omega_norm := o.omega_norm
  T_supp := o.T_supp
  Tp_supp := o.Tp_supp
  Tp_nonneg := o.Tp_nonneg
  lemma42 := o.lemma42
  cor43 := o.cor43
  mainTerm := o.mainTerm_count

#print axioms Sec5ObjectsSharp.mainTerm_count
#print axioms Sec5ObjectsSharp.toSec5
end LeanLab.Grimmelt2019.Section5Characters
