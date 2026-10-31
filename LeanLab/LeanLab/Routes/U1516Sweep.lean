/-
Unit U-1516, T3 CONNECTION SWEEP, run PC 20261025T1203Z-19923, 2026-10-25.
AI-written Lean code, Claude. Checked only by the Lean kernel. KNOWN mathematics.
Binary Goldbach is OPEN; nothing here is progress on it.

I-0118. Plain statement, `kaniecki_of_helfgott`. Assume Helfgott's analytic range, every odd
n ≥ 10^27 is a sum of three primes, and the Helfgott-Platt check of ternary Goldbach up to
8.875 · 10^30. Then both parts of Kaniecki 1995's Main Theorem hold exactly as the lab states
them, `Kaniecki1995.TheoremOdd ∧ Kaniecki1995.TheoremEven`, with no use of RH, of the J_ψ
bound, of any zero count, of the 4 · 10^18 even check or of Liu-Wang.
CONDITIONAL ON `Ternary.helfgott_analytic` and `Verifications.helfgott_platt_ternary`, as
hypotheses by type.

I-0119. Plain statement, `kaniecki_u6806_gZ`. U-1515's `kaniecki1995_theorem_u6806_hsw`
specialised to the true ordinates γ = gZ, so one `Ordinates14 gZ` serves the J step and the θ
step. CONDITIONAL ON, under RH, `ExplicitA gZ Z`, `HadamardK gZ`, `BPTN gZ`; and
`Ordinates14 gZ`, `HSWN70 gZ`, `HSWHead14 gZ`, `EvenGoldbachUpTo (4 · 10^18)`,
`Ternary.TernaryAbove (exp 3100)`.
Also `kaniecki_u6806_gZ_helfgott`: the Liu-Wang input of that theorem replaced by Helfgott's
analytic range through `Ternary.liuWang_of_helfgott`.
-/
import Mathlib
import LeanLab.Kaniecki1995.U1513KanieckiU6806
import LeanLab.SchnirelmannBounds.Statements
import LeanLab.Ternary.Statements

namespace LeanLab.Routes.U1516
open Real LeanLab.ChirreHagen2025
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx)
open LeanLab.Dudek2014.SigmaH (HSWN70)

/-- I-0118. Kaniecki's Main Theorem, both parts, exact lab targets, CONDITIONAL ON Helfgott's
analytic range and the Helfgott-Platt check; RH is not used. -/
theorem kaniecki_of_helfgott (hA : LeanLab.Ternary.TernaryAbove (10 ^ 27))
    (hHP : TernaryGoldbachUpTo 8875694145621773516800000000000) :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven := by
  have hT := LeanLab.Ternary.helfgott_main_of hA hHP
  obtain ⟨hO, hE⟩ := LeanLab.SchnirelmannBounds.kaniecki_of_ternary hT
  exact ⟨fun _ => hO, fun _ _ => hE⟩

/-- The same with the lab's cited inputs plugged in; CONDITIONAL ON `helfgott_analytic` and
`helfgott_platt_ternary`, which appear in the axiom report only as `sorryAx`. -/
theorem kaniecki_of_helfgott_cited :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven :=
  kaniecki_of_helfgott LeanLab.Ternary.helfgott_analytic
    LeanLab.Verifications.helfgott_platt_ternary

/-- I-0119. U-1515's theorem at γ = gZ, one `Ordinates14 gZ` input. -/
theorem kaniecki_u6806_gZ {Z : ℕ → Finset ZIdx}
    (hA : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA gZ Z δ)
    (hK : RiemannHypothesis → SmoothT2.HadamardK gZ)
    (hB : RiemannHypothesis → Lemma26B.BPTN gZ)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hN : HSWN70 gZ) (hH : HSWHead14 gZ) (h14 : SmoothT2.Ordinates14 gZ) :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven :=
  LeanLab.Kaniecki1995.U1513.kaniecki1995_theorem_u6806_hsw hA hK h14 hB hE hLW hN hH h14

/-- I-0119 with Liu-Wang replaced by Helfgott's analytic range. -/
theorem kaniecki_u6806_gZ_helfgott {Z : ℕ → Finset ZIdx}
    (hA : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA gZ Z δ)
    (hK : RiemannHypothesis → SmoothT2.HadamardK gZ)
    (hB : RiemannHypothesis → Lemma26B.BPTN gZ)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hHA : LeanLab.Ternary.TernaryAbove (10 ^ 27))
    (hN : HSWN70 gZ) (hH : HSWHead14 gZ) (h14 : SmoothT2.Ordinates14 gZ) :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven :=
  kaniecki_u6806_gZ hA hK hB hE (LeanLab.Ternary.liuWang_of_helfgott hHA) hN hH h14

/-- Vacuity instance for the plain-math twin of I-0118: 9 = 2 + 7 is at most 4 primes and
7 is at most 5 primes, the shapes of the two conclusions, checked with no hypothesis. -/
example : LeanLab.SchnirelmannConstant.AtMostPrimes 4 9 ∧
    LeanLab.SchnirelmannConstant.AtMostPrimes 5 7 :=
  ⟨⟨[2, 7], by decide, by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num,
    by decide⟩,
   ⟨[7], by decide, by intro p hp; simp at hp; subst hp; norm_num, by decide⟩⟩

/-- I-0120, R-0052 smallest lemma. A J_θ bound of the U6806 shape `C δ log²(c/δ) X²` is the
U-1512 hypothesis `PCLoss Real.log A X₀ δ₀`, written out here since U1512LogLog is not imported,
with `A = C (1 + log c / log(1/δ₀))²`. PROVED, no hypothesis beyond the stated shape. -/
theorem pcloss_log_of_shape {C c X₀ δ₀ : ℝ} (hC : 0 ≤ C) (hc : 1 ≤ c) (hδ₀ : δ₀ < 1)
    (hJ : ∀ X δ : ℝ, X₀ ≤ X → 0 < δ → δ ≤ δ₀ → Jtheta X δ ≤ C * δ * Real.log (c / δ) ^ 2 * X ^ 2) :
    ∀ X δ : ℝ, X₀ ≤ X → 0 < δ → δ ≤ δ₀ →
      Jtheta X δ ≤ (C * (1 + Real.log c / Real.log (1 / δ₀)) ^ 2) * δ *
        (Real.log (1 / δ) * Real.log (1 / δ)) * X ^ 2 := by
  intro X δ hX hδ hδδ
  have hδ₀pos : 0 < δ₀ := lt_of_lt_of_le hδ hδδ
  have hL0 : 0 < Real.log (1 / δ₀) := Real.log_pos (by rw [lt_div_iff₀ hδ₀pos]; linarith)
  have hL : Real.log (1 / δ₀) ≤ Real.log (1 / δ) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδ hδδ)
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hsplit : Real.log (c / δ) = Real.log c + Real.log (1 / δ) := by
    rw [div_eq_mul_one_div, Real.log_mul (by linarith) (by positivity)]
  have hk : Real.log c ≤ Real.log c / Real.log (1 / δ₀) * Real.log (1 / δ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
    exact mul_le_mul_of_nonneg_left hL hlc
  have hle : Real.log (c / δ) ≤ (1 + Real.log c / Real.log (1 / δ₀)) * Real.log (1 / δ) := by
    rw [hsplit]; nlinarith
  have hpos : 0 ≤ Real.log (c / δ) := by rw [hsplit]; linarith
  have hsq : Real.log (c / δ) ^ 2 ≤
      ((1 + Real.log c / Real.log (1 / δ₀)) * Real.log (1 / δ)) ^ 2 :=
    pow_le_pow_left₀ hpos hle 2
  calc Jtheta X δ ≤ C * δ * Real.log (c / δ) ^ 2 * X ^ 2 := hJ X δ hX hδ hδδ
    _ ≤ C * δ * ((1 + Real.log c / Real.log (1 / δ₀)) * Real.log (1 / δ)) ^ 2 * X ^ 2 := by
        have : 0 ≤ C * δ := mul_nonneg hC hδ.le
        gcongr
    _ = _ := by ring

/-- Vacuity instance for `pcloss_log_of_shape`: the hypotheses are met at C = 0, c = 1,
δ₀ = 1/2 by any family with `Jtheta ≤ 0`; here only the arithmetic side, `log 2 > 0`. -/
example : 0 < Real.log (1 / (1 / 2 : ℝ)) := Real.log_pos (by norm_num)

end LeanLab.Routes.U1516

#print axioms LeanLab.Routes.U1516.pcloss_log_of_shape
#print axioms LeanLab.Routes.U1516.kaniecki_of_helfgott
#print axioms LeanLab.Routes.U1516.kaniecki_of_helfgott_cited
#print axioms LeanLab.Routes.U1516.kaniecki_u6806_gZ
#print axioms LeanLab.Routes.U1516.kaniecki_u6806_gZ_helfgott
