/-
AI-written Lean code, Claude, Lean Lab run 20261022T2003Z-18, unit U-1498, track T2 FRONTIER,
paper P0009 Bordignon, Johnston, Starichkova 2022, arXiv 2207.09452 v6, idea I-0105.
Wires U1498MX3's m(X3) bound and the integral bound into U1498Margin at log X2 = e^31.567.

PROVED: `LX_ge`, e^31.567 >= 5e13; `hI`, the integral of Theorem 44 (b) at c of eq (136) is at most
0.14725; `margin_b_31567` and `margin_a_31567`, the Section 9 case (b) and case (a) margins for
every log N >= e^31.567, with m(X3) and the integral discharged, CONDITIONAL only ON the numeric
inputs still carried as hypotheses: eps1 <= 1/57 at delta1 = 1.5306, eps2 <= 1/51 at
delta2 = 1.50023, and the X2-only constants a <= 1e-18, c4*, l1*, l* <= 1e-20 at 31.567.
These are hypotheses on real numbers, not cited theorems; they become a Chen threshold only after
the Eps and X2-only chains are ported, and then still CONDITIONAL ON BJS Theorems 44, 50, 51 as
corrected and, through m(X3), on the four Bordignon Props of U1490SiegelPlus.
Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.U1498Margin
import LeanLab.ChenExplicit.U1498MX3

open Real

noncomputable section
namespace LeanLab.ChenExplicit.U1498Link

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.Section9U8 LeanLab.ChenExplicit.U1498Section9F5
  LeanLab.ChenExplicit.U1498Margin

/-- log X₂ = e^{31.567}. -/
abbrev LX : ℝ := exp (31567 / 1000)

lemma LX_ge : (5 * 10 ^ 13 : ℝ) ≤ LX := by
  have := U1498MX3.exp31567_ge; unfold LX; linarith

lemma hI : ∫ t in (2 : ℝ)..(ccP (31567 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

/-- **Case (b) at log log X₂ = 31.567**, m(X₃) and the integral discharged. -/
theorem margin_b_31567 (g T e1 e2 cb a c4s w l1s ls L : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084)
    (ha : 0 ≤ a ∧ a ≤ 1 / 10 ^ 18) (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20) (hL : LX ≤ L) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAbPU (31567 / 1000) g T e1 a c4s w L LX - cQbU g T e1 l1s ls L LX / 2 -
        cBPU ee0 g T e2 cb (U1498MX3.mX3 U1498MX3.vS) L / 2 :=
  margin_bP g T e1 e2 cb _ a c4s w l1s ls L LX hg1 hg2 hT he1 he2 hcb
    U1498MX3.mX3_vS_bounds ha hc4 hw hl1 hls LX_ge hL hI

/-- **Case (a) at log log X₂ = 31.567**, m(X₃) discharged. -/
theorem margin_a_31567 (g T e2 cb c4 l1 l L : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 20)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 20) (hL : LX ≤ L) :
    1 / 10 ≤ cAaU g T c4 L - cQaU g T l1 l L LX / 2 -
      cBPU ee0 g T e2 cb (U1498MX3.mX3 U1498MX3.vS) L / 2 :=
  margin_aP g T e2 cb _ c4 l1 l L LX hg1 hg2 hT he2 hcb U1498MX3.mX3_vS_bounds hc4 hl1 hls LX_ge hL

/-- Vacuity: every hypothesis of `margin_b_31567` holds at one concrete point, with `g = 1.781`,
`T = 0.65`, `ε₁ = ε₂ = cb = a = c₄ = w = l₁ = l = 0`, `L = log X₂`. -/
example : 2 / 10000 + 1 / 10 ^ 12 ≤
    cAbPU (31567 / 1000) 1.781 0.65 0 0 0 0 LX LX - cQbU 1.781 0.65 0 0 0 LX LX / 2 -
      cBPU ee0 1.781 0.65 0 0 (U1498MX3.mX3 U1498MX3.vS) LX / 2 :=
  margin_b_31567 1.781 0.65 0 0 0 0 0 0 0 0 LX (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨le_rfl, (by have := LX_ge; linarith)⟩ (by norm_num) (by norm_num) le_rfl

end LeanLab.ChenExplicit.U1498Link
