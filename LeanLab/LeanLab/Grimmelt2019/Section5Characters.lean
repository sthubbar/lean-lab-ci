/-
AI wrote this Lean code for CODEX task03.
P0074, pages 11 to 14, the Section 5 input fields in their character form.
The analytic existence assertions remain cited hypotheses.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.ConvolutionSharp
import LeanLab.Grimmelt2019.Section5Small

namespace LeanLab.Grimmelt2019.Section5Characters
open LeanLab.Grimmelt2019.Prop21 LeanLab.Grimmelt2019.MainTerm
open LeanLab.Grimmelt2019.Section5Small
attribute [local instance] Classical.propDecidable

/-- Source-labelled Section 5 data with the literal character condition.
The legacy Q squared budget is retained for conversion to Section5InputsSmall. -/
structure Sec5ObjectsCharacter (X Y H K B A c : ℝ) where
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
  /-- The old arithmetic budget is explicit and is not inferred from the named lemmas. -/
  budget : c * Y ≤ cν * cω * Y * s0 - cν * (Q : ℝ) ^ 2 * (2 * E + |cω|)

/-- Convert the literal character data to the existing small-epsilon objects. -/
noncomputable def Sec5ObjectsCharacter.toMT {X Y H K B A c : ℝ}
    (o : Sec5ObjectsCharacter X Y H K B A c) : Sec5ObjectsMT X Y H K B A c where
  ν := o.ν
  ω := o.ω
  Tp := o.Tp
  cν := o.cν
  cω := o.cω
  Q := o.Q
  E := 2 * o.E + |o.cω|
  s0 := o.s0
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
  cnu_nonneg := by linarith [o.cnu_lower]
  comega_nonneg := by linarith [o.comega_lower]
  E_nonneg := by linarith [o.E_nonneg, abs_nonneg o.cω]
  ap29 := apEquidist_of_paperCondition29 o.Y_nonneg o.left_large o.H_lt_Y
    o.E_nonneg o.char29 o.rough
  singSeries := by simpa only [SQ_eq_abs_moebius] using o.singSeries
  budget := o.budget

/-- Cited analytic existence bundle with character data and an explicit legacy budget. -/
def Section5InputsCharacters : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 18 → ∃ B : ℝ, ∀ A : ℝ, 0 < A → ∃ K c X0 : ℝ, 0 ≤ K ∧ 0 < c ∧
    ∀ X : ℝ, X0 ≤ X →
      Nonempty (Sec5ObjectsCharacter X (X ^ (21 / 40 + ε))
        ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε)) K B A c)

/-- The character existence bundle gives the existing Section5InputsSmall bundle. -/
theorem section5InputsSmall_of_characters (h : Section5InputsCharacters) : Section5InputsSmall := by
  intro ε hε hεsmall
  obtain ⟨B, hB⟩ := h ε hε hεsmall
  refine ⟨B, fun A hA => ?_⟩
  obtain ⟨K, c, X0, hK, hc, ho⟩ := hB A hA
  refine ⟨K, c, X0, hK, hc, fun X hX => ?_⟩
  exact (ho X hX).map Sec5ObjectsCharacter.toMT

/-- Theorem 1.1 remains conditional on the analytic existence bundle and second moment. -/
theorem thm1_1_of_section5Characters
    (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (h : Section5InputsCharacters) : LeanLab.Grimmelt2019.ShortIntervalLogSaving (7 / 120) :=
  thm1_1_of_section5Small hMRT (section5InputsSmall_of_characters h)

#print axioms Sec5ObjectsCharacter.toMT
#print axioms section5InputsSmall_of_characters
#print axioms thm1_1_of_section5Characters
end LeanLab.Grimmelt2019.Section5Characters
