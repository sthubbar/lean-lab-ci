/-
AI-written Lean code, Claude, 2026-10-19, PC run 20261019T0003Z-19699, unit U-0984, follow-up of
REQUEST U-0977. P0009 Bordignon, Johnston, Starichkova, arXiv 2207.09452v6, Section 9.

F0023.lean and F0023X3.lean, cloud units U-5023 and U-5024, PROVE FINDING F-0023 at the printed
`ε₀ = 10⁻⁴`. An expert's first reply would be: then pick another `ε₀`. Here: NO choice of `ε₀`
rescues case (b). `ε₀` enters only Theorem 51, through `(1 + ε₀)` in the main term and
`(1 + ε₀)/log(1 + ε₀) ≥ 1/ε₀` in the `m(X₃)` remainder, so the combination is at most
`C - (a ε₀ + b/ε₀)/2 ≤ C - √(ab)`, and `√(ab)` beats `C` by AM-GM.

PROVED, zero sorry, reusing the cloud definitions and bounds unchanged:
* `cBP_ge_all`: Theorem 51 lower bound for every `ε₀ > 0`.
* `amgm`: `a x + b/x ≥ c` when `c² ≤ 4ab`, `x > 0`.
* `f0023_all_eps_X3`: at the literally printed `X₂ = exp(exp 32.7)`, `X₃ = exp(exp 30.62)`,
  `δ = 1.478`, `α = 10⁻⁵`, for EVERY `ε₀ > 0` and every `N ≥ X₂`, the corrected case (b)
  combination is NEGATIVE. Section 9 needs at least `2·10⁻⁴`. Python: best `-1.46·10⁻³` at
  `ε₀ ≈ 8.2·10⁻⁴`, falsifier subagent; the Lean bound gives below `-7·10⁻⁴`.
* `f0023_all_eps`: the same with `X₃ = X₂^{1/8}`.
* `f0023_all_eps_X3_instance`: vacuity test, every hypothesis met.
Still Python only: varying `δ` and `α`. Rests on the lab's transcription of Theorems 44 (b), 50 (b),
51 in Section9.lean with F-0021 and F-0022 applied, as F0023.lean does.
Chen's theorem is not in doubt, only the explicit threshold exp(exp 32.7). Goldbach is open.
-/
import LeanLab.ChenExplicit.F0023X3

open Real

noncomputable section
namespace LeanLab.ChenExplicit.F0023AllEps

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.Section9
  LeanLab.ChenExplicit.F0023 LeanLab.ChenExplicit.F0023X3

/-- Theorem 51, corrected, lower bound for every `ε₀ > 0`, linear in `1 + ε₀` and in `1/ε₀`. -/
lemma cBP_ge_all (e0 g T e2 cb m L : ℝ) (hg : 0 ≤ g) (hT : 0 < T) (hT2 : T ≤ 0.6614)
    (he2 : e2 = 1 / 51) (hcb : 0.3630 ≤ cb) (hm : 1 / 10 ^ 8 ≤ m) (hL : 0 < L) (he0 : 0 < e0) :
    1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * (1 + e0) * 0.3630 +
      g / 1.3228 * (320 * (1 / 10 ^ 8) / 3) * (1 / e0) ≤ cBP e0 g T e2 cb m L := by
  unfold cBP
  subst he2
  have hl0 : 0 < log (1 + e0) := log_pos (by linarith)
  have hl1 : log (1 + e0) ≤ e0 := by
    have := log_le_sub_one_of_pos (x := 1 + e0) (by linarith); linarith
  have hh := h_nonneg (3 / 2 - 3 * α) (by norm_num)
  have h83 := log83_nonneg
  have hq1 : 0 ≤ 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α) := by positivity
  have hA : 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * (1 + e0) * 0.3630 ≤
      1.00005 * (1 + 1 / 51) * (1 + 4.51 / L ^ 2) *
        (2 / (1 / 2 - α) * g + 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α)) * (1 + e0 + 9 / L) *
        (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) := by
    have : 0 ≤ 4.51 / L ^ 2 := by positivity
    have : 0 ≤ 9 / L := by positivity
    have : 0 ≤ 36 / L ^ 2 := by positivity
    have : 0 ≤ (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) := by positivity
    have hg2 : 0 ≤ 2 / (1 / 2 - α) * g := by positivity
    have q1 : 1.00005 * (52 / 51 : ℝ) ≤ 1.00005 * (1 + 1 / 51) * (1 + 4.51 / L ^ 2) := by nlinarith
    have q2 : 2 / (1 / 2 - α) * g ≤
        2 / (1 / 2 - α) * g + 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α) := by linarith
    have q3 : 1 + e0 ≤ 1 + e0 + 9 / L := by linarith
    have q4 : (0.3630 : ℝ) ≤
        cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) := by
      linarith
    have q12 := mul_le_mul q1 q2 hg2 (by positivity)
    have q123 := mul_le_mul q12 q3 (by linarith) (le_trans (by positivity) q12)
    exact mul_le_mul q123 q4 (by norm_num) (le_trans (by positivity) q123)
  have hT' : g / 1.3228 ≤ g / (2 * T) := div_le_div_of_nonneg_left hg (by linarith) (by linarith)
  have hB1 : 320 * (1 / 10 ^ 8) / 3 * (1 / e0) ≤ 320 * m * (1 + e0) / (3 * log (1 + e0)) := by
    rw [div_mul_div_comm, mul_one]
    apply div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by linarith)
  have hB2 : 0 ≤ 0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)) := by
    have := exp_pos (L / 8); positivity
  have hB : g / 1.3228 * (320 * (1 / 10 ^ 8) / 3) * (1 / e0) ≤ g / (2 * T) *
      (320 * m * (1 + e0) / (3 * log (1 + e0)) +
        0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0))) := by
    rw [mul_assoc]
    apply mul_le_mul hT' (by linarith) (by positivity) (div_nonneg hg (by linarith))
  linarith

/-- `a x + b / x ≥ c` for `x > 0` when `c² ≤ 4ab`, the AM-GM step. -/
lemma amgm (a b c x : ℝ) (ha : 0 < a) (hx : 0 < x) (hc : c ^ 2 ≤ 4 * a * b) :
    c ≤ a * x + b / x := by
  have e : a * x + b / x = (a * x ^ 2 + b) / x := by field_simp
  rw [e, le_div_iff₀ hx]
  nlinarith [sq_nonneg (2 * a * x - c), sq_nonneg x]

/-- The arithmetic core: for every `ε₀ > 0`, from the three bounds, the combination is `< 0`. -/
lemma core (g e0 A Q B : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (he0 : 0 < e0)
    (hA : A ≤ 8 * (1 + 1 / 10 ^ 26) * ((61 / 57) * (g * 0.5493087) - 4 / 57))
    (hQ : 8.0004 * (58 / 57) * (g / 4 * 3.58365) ≤ Q)
    (hB : 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * (1 + e0) * 0.3630 +
      g / 1.3228 * (320 * (1 / 10 ^ 8) / 3) * (1 / e0) ≤ B) :
    A - Q / 2 - B / 2 < -7 / 10000 := by
  set a := 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * (1.781 : ℝ)) * 0.3630 with ha
  set b := (1.781 : ℝ) / 1.3228 * (320 * (1 / 10 ^ 8) / 3) with hb
  have hP : a * e0 ≤ 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * 0.3630 * e0 := by
    rw [ha]; gcongr
  have hR : b / e0 ≤ g / 1.3228 * (320 * (1 / 10 ^ 8) / 3) * (1 / e0) := by
    rw [hb, div_eq_mul_one_div]; gcongr
  have hAM := amgm a b 0.00388 e0 (by rw [ha]; norm_num) he0 (by rw [ha, hb]; norm_num)
  have hYZ : 0.00388 ≤ 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * 0.3630 * e0 +
      g / 1.3228 * (320 * (1 / 10 ^ 8) / 3) * (1 / e0) := by linarith
  have e1 : 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * (1 + e0) * 0.3630 =
      1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * 0.3630 +
      1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * 0.3630 * e0 := by ring
  rw [e1] at hB
  have hB' : 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * 0.3630 +
      (1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * 0.3630 * e0 +
      g / 1.3228 * (320 * (1 / 10 ^ 8) / 3) * (1 / e0)) ≤ B := by linarith
  generalize 1.00005 * (52 / 51) * (2 / (1 / 2 - α) * g) * 0.3630 * e0 +
      g / 1.3228 * (320 * (1 / 10 ^ 8) / 3) * (1 / e0) = Z at hYZ hB'
  clear hB hP hR hAM
  norm_num at hA hQ hB' hYZ ⊢
  linarith

/-- **F-0023, every `ε₀ > 0`, printed `X₃ = exp(exp 30.62)`.** -/
theorem f0023_all_eps_X3 (e0 a c4s w l1s ls L v : ℝ) (he0 : 0 < e0) (ha : 0 ≤ a) (hc4 : 0 ≤ c4s)
    (hw : 0 ≤ w) (hl1 : 0 ≤ l1s) (hls : 0 ≤ ls) (hL : exp ll ≤ L) (hv : φΛ Λp δ (ℓΛ Λp) ≤ v) :
    cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) a c4s w L (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) l1s ls L (exp ll) / 2 -
      cBP e0 (exp eulerMascheroniConstant) twinC (BJSEm.eps B2X3) BJS.cbar (mX3Λ Λp v) L / 2 <
      -7 / 10000 := by
  have hg1 := g_ge
  have hg2 := g_le
  have hT0 : 0 < twinC := by have := twinC_ge_065; linarith
  have hT := twinC_le_06614
  have hLX := LXp_ge
  have hA := cAbP_le (exp eulerMascheroniConstant) twinC _ a c4s w L (exp ll) hg1 hg2 hT0
    eps1_printed ha hc4 hw hLX hL
  have hQ := cQb_ge (exp eulerMascheroniConstant) twinC _ l1s ls L (exp ll) (by linarith) hT0
    eps1_printed hl1 hls hLX (by linarith)
  have hB := cBP_ge_all e0 (exp eulerMascheroniConstant) twinC _ BJS.cbar (mX3Λ Λp v) L
    (by linarith) hT0 (by norm_num at hT ⊢; linarith) eps2_X3
    (by have := BJS.cbar_gt; norm_num at this ⊢; linarith) (m_ge_X3 v hv) (by linarith) he0
  exact core _ e0 _ _ _ hg1 hg2 he0 hA hQ hB

/-- **F-0023, every `ε₀ > 0`, with `X₃ = X₂^{1/8}`.** -/
theorem f0023_all_eps (e0 a c4s w l1s ls L v : ℝ) (he0 : 0 < e0) (ha : 0 ≤ a) (hc4 : 0 ≤ c4s)
    (hw : 0 ≤ w) (hl1 : 0 ≤ l1s) (hls : 0 ≤ ls) (hL : exp ll ≤ L) (hv : φP ll δ (ℓP ll) ≤ v) :
    cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) a c4s w L (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) l1s ls L (exp ll) / 2 -
      cBP e0 (exp eulerMascheroniConstant) twinC (BJSEm.eps B2P) BJS.cbar (mX3P ll v) L / 2 <
      -7 / 10000 := by
  have hg1 := g_ge
  have hg2 := g_le
  have hT0 : 0 < twinC := by have := twinC_ge_065; linarith
  have hT := twinC_le_06614
  have hLX := LXp_ge
  have hA := cAbP_le (exp eulerMascheroniConstant) twinC _ a c4s w L (exp ll) hg1 hg2 hT0
    eps1_printed ha hc4 hw hLX hL
  have hQ := cQb_ge (exp eulerMascheroniConstant) twinC _ l1s ls L (exp ll) (by linarith) hT0
    eps1_printed hl1 hls hLX (by linarith)
  have hB := cBP_ge_all e0 (exp eulerMascheroniConstant) twinC _ BJS.cbar (mX3P ll v) L
    (by linarith) hT0 (by norm_num at hT ⊢; linarith) eps2_printed
    (by have := BJS.cbar_gt; norm_num at this ⊢; linarith) (m_ge v hv) (by linarith) he0
  exact core _ e0 _ _ _ hg1 hg2 he0 hA hQ hB

/-- So no `ε₀ > 0` meets Section 9's requirement `≥ 2·10⁻⁴` at the printed parameters. -/
theorem f0023_no_eps_X3 (a c4s w l1s ls L v : ℝ) (ha : 0 ≤ a) (hc4 : 0 ≤ c4s)
    (hw : 0 ≤ w) (hl1 : 0 ≤ l1s) (hls : 0 ≤ ls) (hL : exp ll ≤ L) (hv : φΛ Λp δ (ℓΛ Λp) ≤ v) :
    ¬ ∃ e0 : ℝ, 0 < e0 ∧ 2 / 10000 ≤
      cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) a c4s w L (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) l1s ls L (exp ll) / 2 -
      cBP e0 (exp eulerMascheroniConstant) twinC (BJSEm.eps B2X3) BJS.cbar (mX3Λ Λp v) L / 2 := by
  rintro ⟨e0, he0, h⟩
  have := f0023_all_eps_X3 e0 a c4s w l1s ls L v he0 ha hc4 hw hl1 hls hL hv
  linarith

/-- Vacuity test: every hypothesis met, at `ε₀ = 8.2·10⁻⁴`, the Python optimum. -/
theorem f0023_all_eps_X3_instance :
    cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) 0 0 0 (exp ll) (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) 0 0 (exp ll) (exp ll) / 2 -
      cBP (82 / 100000) (exp eulerMascheroniConstant) twinC (BJSEm.eps B2X3) BJS.cbar
        (mX3Λ Λp (φΛ Λp δ (ℓΛ Λp))) (exp ll) / 2 < -7 / 10000 :=
  f0023_all_eps_X3 _ 0 0 0 0 0 _ _ (by norm_num) le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl

#print axioms cBP_ge_all
#print axioms amgm
#print axioms core
#print axioms f0023_all_eps_X3
#print axioms f0023_all_eps
#print axioms f0023_no_eps_X3
#print axioms f0023_all_eps_X3_instance

end LeanLab.ChenExplicit.F0023AllEps
