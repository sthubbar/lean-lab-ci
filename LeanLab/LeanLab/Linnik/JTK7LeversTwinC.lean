/-
Run 20261019T1902Z-2936, unit U-1105. AI-written Lean code, Claude. Checked only by the Lean kernel.
The three levers of JTK7Levers.lean took the twin prime constant only through the hypothesis
`C₀ ≤ 0.66017`. With `ChenExplicit.TwinCUpper.twinC_le_066017` that hypothesis is now a
theorem, so here C₀ is the twin prime constant itself and the hypothesis is gone. The levers
stay CONDITIONAL on their other cited inputs: JT's A(3), A(4), R₀, Theorem 2 and Pintz-Ruzsa's
criterion, and on the improvement each lever names. Goldbach is open.
-/
import LeanLab.Linnik.JTK7Levers
import LeanLab.ChenExplicit.TwinCUpper

open Real

noncomputable section
namespace LeanLab.Linnik.JT

lemma twinC_nonneg : 0 ≤ LeanLab.ChenExplicit.twinC :=
  le_trans (by norm_num) LeanLab.ChenExplicit.twinC_ge_065

lemma twinC_le : LeanLab.ChenExplicit.twinC ≤ 0.66017 := by
  have := LeanLab.ChenExplicit.TwinCUpper.twinC_le_066017
  norm_num at this ⊢; exact this

/-- Lever 1 with C₀ the twin prime constant: no C₀ hypothesis. -/
theorem k7_of_C1_twinC {C1 A3 A4 R0 ε lp c1 : ℝ} (hC1a : 2 ≤ C1) (hC1 : C1 ≤ 6.76)
    (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598) (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-6) (hl : 0.4444 ≤ lp) (hl1 : lp ≤ 1)
    (hc10 : 0 ≤ c1) (hc1 : c1 ≤ 0.7894009) :
    crit A4 A3 (C2p C1 ε R0 LeanLab.ChenExplicit.twinC lp) c1 4 3 < 1 :=
  k7_of_C1 hC1a hC1 hA30 hA3 hA40 hA4 hR0 hR twinC_nonneg twinC_le he0 he hl hl1 hc10 hc1

/-- Lever 2 with C₀ the twin prime constant. -/
theorem k7_of_c1_twinC {A3 A4 R0 ε lp c1 : ℝ}
    (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598) (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-6) (hl : 0.4444 ≤ lp) (hl1 : lp ≤ 1)
    (hc10 : 0 ≤ c1) (hc1 : c1 ≤ 0.7887) :
    crit A4 A3 (C2p 6.7814 ε R0 LeanLab.ChenExplicit.twinC lp) c1 4 3 < 1 :=
  k7_of_c1 hA30 hA3 hA40 hA4 hR0 hR twinC_nonneg twinC_le he0 he hl hl1 hc10 hc1

/-- Lever 3 with C₀ the twin prime constant. -/
theorem k7_of_lp_twinC {A3 A4 R0 ε lp c1 : ℝ}
    (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598) (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-6) (hl : 0.482 ≤ lp) (hl1 : lp ≤ 1)
    (hc10 : 0 ≤ c1) (hc1 : c1 ≤ 0.7894009) :
    crit A4 A3 (C2p 6.7814 ε R0 LeanLab.ChenExplicit.twinC lp) c1 4 3 < 1 :=
  k7_of_lp hA30 hA3 hA40 hA4 hR0 hR twinC_nonneg twinC_le he0 he hl hl1 hc10 hc1

end LeanLab.Linnik.JT
