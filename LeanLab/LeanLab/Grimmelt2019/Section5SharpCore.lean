/-
AI wrote this Lean code for CODEX task03.
P0074 pages 12 to 14. Both conclusions are conditional on the named analytic inputs.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Section5Sharp

namespace LeanLab.Grimmelt2019.Section5Characters
open Real LeanLab.Grimmelt2019 LeanLab.Grimmelt2019.Prop21 LeanLab.Grimmelt2019.MainTerm
open LeanLab.Grimmelt2019.Section5Small
attribute [local instance] Classical.propDecidable

/-- Analytic existence at the small epsilon scales, with the sharp budget. -/
def Section5InputsSharp : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 18 → ∃ B : ℝ, ∀ A : ℝ, 0 < A → ∃ K c X0 : ℝ, 0 ≤ K ∧ 0 < c ∧
    ∀ X : ℝ, X0 ≤ X →
      Nonempty (Sec5ObjectsSharp X (X ^ (21 / 40 + ε))
        ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε)) K B A c)

/-- The single-length bound is conditional on sharp Section 5 existence and the second moment. -/
theorem core_of_section5Sharp (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (hS5 : Section5InputsSharp) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 18 → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (EXH X ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε)) : ℝ)
        ≤ C * (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) / Real.log X ^ A := by
  intro ε hε hεδ A' hA'
  obtain ⟨C0, hC0, hM⟩ := hMRT
  obtain ⟨B, hB⟩ := hS5 ε hε hεδ
  set B' : ℝ := max B 2 with hB'def
  have hB'2 : (2 : ℝ) ≤ B' := le_max_right _ _
  have hBB' : B ≤ B' := le_max_left _ _
  obtain ⟨K, c, X0, hK, hc, hobj⟩ := hB (A' + B') (by linarith)
  refine ⟨K + 16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A', max X0 (Real.exp 2), fun X hX => ?_⟩
  have hXX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hXe
  have hlogX2 : 2 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe
  have hX1 : 1 ≤ X := by have := Real.add_one_le_exp 2; linarith
  obtain ⟨o'⟩ := hobj X hXX0
  set Y := X ^ (21 / 40 + ε) with hYdef
  set H := Y ^ (1 / 9 + 2 * ε) with hHdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hX1 (by linarith)
  have hYpos : 0 < Y := by linarith
  have o := o'.toSec5
  have hH1 : 1 ≤ H := Real.one_le_rpow hY1 (by linarith)
  have hLY : Real.log X / 2 ≤ Real.log Y := logY_ge_half_logX hX1 hε.le
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hlXpos : 0 < Real.log X := by linarith
  have hP := prop21_finite hM (supp X) (LamCut X Y) (LamP X) o.ω o.ν o.T o.Tp X H
    (K * Y * L ^ (-(A' + B'))) (c * Y / 4) hH1 (by positivity)
    (LamCut_supp X Y) o.omega_supp o.nu_supp o.T_supp o.Tp_supp
    (LamCut_nonneg X Y) o.Tp_nonneg o.nu_le (omega_le_LamCut o) o.cor43 o.lemma42
  have hsplit := EXH_le_split X Y H c hc hYpos o.ω o.T
  have hmt := o.mainTerm
  have hsa : sqn (supp X) (LamCut X Y) ≤ 12 * Y * L ^ B' := by
    have h1 := sqn_LamCut_le hX1 hYpos.le
    have hlx : Real.log X ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    have hL2 : L ^ 2 ≤ L ^ B' := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hL1 hB'2
    calc sqn (supp X) (LamCut X Y) ≤ (2 * Y + 1) * Real.log X ^ 2 := h1
      _ ≤ (3 * Y) * (4 * L ^ B') :=
          mul_le_mul (by linarith) (by linarith) (sq_nonneg _) (by linarith)
      _ = 12 * Y * L ^ B' := by ring
  have hsω : sqn (supp X) o.ω ≤ K * Y * L ^ B' :=
    le_trans o.omega_norm (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 hBB') (mul_nonneg hK hYpos.le))
  have hH0 : 0 ≤ H := by linarith
  have hlXL : Real.log X ≤ 2 * L := by linarith
  have harith := final_arith hC0 hK hc hYpos hH0 hL1 hlXpos hlXL hA'.le hsa hsω
  have hmt' : K * H / Real.log X ^ (A' + B') ≤ K * H / Real.log X ^ A' := by
    apply div_le_div_of_nonneg_left (mul_nonneg hK (by linarith))
      (Real.rpow_pos_of_pos hlXpos _)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc (EXH X H : ℝ) ≤ _ := hsplit
    _ ≤ K * H / Real.log X ^ (A' + B') +
        C0 * H * (sqn (supp X) (LamCut X Y) + sqn (supp X) o.ω) *
          (K * Y * L ^ (-(A' + B'))) / (c * Y / 4) ^ 2 := add_le_add hmt hP
    _ ≤ K * H / Real.log X ^ A' +
        16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A' * H / Real.log X ^ A' :=
        add_le_add hmt' harith
    _ = (K + 16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A') * H / Real.log X ^ A' := by ring

/-- Theorem 1.1 remains conditional on the sharp analytic bundle and the second moment. -/
theorem thm1_1_of_section5Sharp (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (hS5 : Section5InputsSharp) : ShortIntervalLogSaving (7 / 120) := by
  apply LeanLab.Grimmelt2019.Section5Small.logSaving_of_below (δ := 1 / 18) (by norm_num)
  apply LeanLab.Grimmelt2019.Section5Small.logSavingBelow_of_exactLengthBelow (by norm_num) _
    LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving
  intro ε' hε' hε'δ A hA
  obtain ⟨ε, hε, hεeq⟩ := exists_lemma51_eps hε'
  have hεε' : ε ≤ ε' := by rw [lemma51_exponent] at hεeq; nlinarith
  obtain ⟨C, X0, hC⟩ := core_of_section5Sharp hMRT hS5 ε hε (by linarith) A hA
  refine ⟨C, max X0 0, fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
  have hrw : (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) = X ^ (7 / 120 + ε') := by
    rw [← Real.rpow_mul hX0, hεeq]
  have := hC X (le_trans (le_max_left _ _) hX)
  rwa [hrw] at this


#print axioms core_of_section5Sharp
#print axioms thm1_1_of_section5Sharp
end LeanLab.Grimmelt2019.Section5Characters
