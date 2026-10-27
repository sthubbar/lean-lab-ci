import LeanLab.Zhao2025.CaseMargins
import LeanLab.Zhao2025.SmallCaseBound

/-!
CaseInputs uses the named estimates 4.1, 4.3 and 4.4 in the small case.
Every Display110 result is CONDITIONAL ON those estimates in that case.
The other labels retain the explicit later case constants.
Source: Zhao 2025, display 1.10, page 3, and Section 4, pages 13 to 16.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025 LeanLab.Zhao2025.U6837 LeanLab.Zhao2025.U6900

/-- The small branch uses the paper cutoff and does not assume display 4.5. -/
def CaseInputs (k : Fin 11) (n : ℕ) (l11 : ℝ) (R T S : ℕ → ℝ) : Prop :=
  match k.val with
  | 0 => 0 < l11 ∧ l11 ≤ 0.01 ∧ SmallCaseZeroEstimates n l11 S
  | 1 => (0.01 ≤ l11 ∧ l11 ≤ 0.10 ∧ 0 ≤ S 0 ∧ S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.0042 ∧
    (∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0018) ∧
    ∑ i ∈ Finset.range n, S (i + 1) ≤ 0.6150)
  | 2 => (0.10 ≤ l11 ∧ l11 ≤ 0.30 ∧ 0 ≤ S 0 ∧ S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.0690 ∧
    (∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0464) ∧
    ∑ i ∈ Finset.range n, S (i + 1) ≤ 4.951)
  | 3 => (0.30 ≤ l11 ∧ l11 ≤ 0.40 ∧ 0 ≤ S 0 ∧ S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.1231 ∧
    (∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0971) ∧
    ∑ i ∈ Finset.range n, S (i + 1) ≤ 6.85)
  | 4 => (0.40 ≤ l11 ∧ l11 ≤ 0.60 ∧
    (0 ≤ S 0 ∧ S 0 ≤ 0.374 + 0.0808 ∧ 0 ≤ S 1 ∧ S 1 ≤ 0.374 + 0.0808 ∧
      (∀ i, i < n → 0 ≤ R i ∧ R i ≤ 0.157) ∧ (∀ i, i < n → 0 ≤ T i ∧ T i ≤ 0.0704) ∧
      ∑ i ∈ Finset.range n, R i ≤ 0.457 ∧ ∑ i ∈ Finset.range n, T i ≤ 6.33))
  | 5 => (0.40 ≤ l11 ∧ l11 ≤ 0.60 ∧
    (0 ≤ S 0 ∧ S 0 ≤ 0.556 + 0.0808 ∧
      (∀ i, i < n → 0 ≤ R i ∧ R i ≤ 0.157) ∧ (∀ i, i < n → 0 ≤ T i ∧ T i ≤ 0.0704) ∧
      ∑ i ∈ Finset.range n, R i ≤ 0.457 ∧ ∑ i ∈ Finset.range n, T i ≤ 6.33))
  | 6 => (0.60 ≤ l11 ∧ l11 ≤ 0.62 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.57982 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.6236 ∧
    ((∀ i, R i ≤ hd 0.29940 0.14790 0.14790 0.14790 0.14790 i ∧ T i ≤ hd 0.10023 0.09272 0.09272 0.09272 0.09272 i) ∨
     (∀ i, R i ≤ hd 0.23508 0.23508 0.14790 0.14790 0.14790 i ∧ T i ≤ hd 0.10023 0.10023 0.09272 0.09272 0.09272 i)))
  | 7 => (0.62 ≤ l11 ∧ l11 ≤ 0.64 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.59615 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.5381 ∧
    ((∀ i, R i ≤ hd 0.29306 0.19150 0.19150 0.19150 0.19150 i ∧ T i ≤ hd 0.09797 0.09241 0.09241 0.09241 0.09230 i) ∨
     (∀ i, R i ≤ hd 0.25205 0.25205 0.19150 0.19150 0.19150 i ∧ T i ≤ hd 0.09797 0.09797 0.09241 0.09241 0.09230 i)))
  | 8 => (0.64 ≤ l11 ∧ l11 ≤ 0.66 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.66426 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.4466 ∧
    ((∀ i, R i ≤ hd 0.29738 0.24889 0.24889 0.24889 0.24889 i ∧ T i ≤ hd 0.09572 0.09321 0.09321 0.09321 0.09063 i) ∨
     (∀ i, R i ≤ hd 0.27836 0.27836 0.24889 0.24889 0.24889 i ∧ T i ≤ hd 0.09572 0.09572 0.09321 0.09321 0.09063 i)))
  | 9 => (0.66 ≤ l11 ∧ l11 ≤ 0.68 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.64932 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.3632 ∧
    ((∀ i, R i ≤ hd 0.28824 0.25104 0.25104 0.25104 0.25104 i ∧ T i ≤ hd 0.09359 0.09166 0.09166 0.09166 0.08900 i) ∨
     (∀ i, R i ≤ hd 0.27380 0.27380 0.25104 0.25104 0.25104 i ∧ T i ≤ hd 0.09359 0.09359 0.09166 0.09166 0.08900 i)))
  | _ => (0.68 ≤ l11 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.67914 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.2739 ∧
    ((∀ i, R i ≤ hd 0.28735 0.27703 0.27703 0.27703 0.27703 i ∧ T i ≤ hd 0.09121 0.09112 0.09112 0.09112 0.08733 i) ∨
     (∀ i, R i ≤ hd 0.28342 0.28342 0.27703 0.27703 0.27703 i ∧ T i ≤ hd 0.09121 0.09121 0.09112 0.09112 0.08733 i)))

end LeanLab.Zhao2025.Task56
