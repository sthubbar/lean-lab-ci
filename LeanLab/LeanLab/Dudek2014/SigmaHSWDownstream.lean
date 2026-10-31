import LeanLab.PrimePowerWindow.Downstream
import LeanLab.Dudek2014.SigmaHSW

/-!
# Dudek 2014 Theorem 2 and its lab uses on the corrected `N(T)` bound

P0100, unit U-6650, CLOUD 20261020T1717Z-cloud47. AI wrote this file. Known mathematics.

The four results of PrimePowerWindow/Downstream.lean, which take `TrudgianN70`, Trudgian 2014's
`N(T)` bound, reported by Hasanalizade, Shen and Wong, arXiv 2107.06506, to rest on an error, now
on their corrected bound `HSWN70` instead, through `SigmaH.sigmaBd_of_hsw`:
* `theorem2_of_RH_hsw`: Dudek 2014 Theorem 2 under RH, CONDITIONAL ON `HSWN70` only;
* `theorem1_of_RH_hsw`: Ramaré-Saouter 2003 Theorem 1 under RH, on the same input;
* `goldbach_gap_1478_RH_hsw`: a Goldbach number in every `(x, x + 1478]`,
  `2 ≤ x ≤ 1.6·10^33`, under RH, CONDITIONAL ON `HSWN70`, the `4·10^18` even check and
  `GapBound1476`;
* `kaniecki_lemma6_RH_hsw`: Kaniecki 1995 Lemma 6 under RH, on `HSWN70` and `GapBound1476`.
Binary Goldbach is OPEN; these are conditional statements about short intervals.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open LeanLab.GoldbachGaps.Sumset (GapBound1476)

/-- **Dudek 2014 Theorem 2 under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)` only.** -/
theorem theorem2_of_RH_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) :
    ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x := by
  refine LeanLab.Dudek2014.Section22.theorem2_of_lemma4_window lemma4_Zpatch ?_
  have hS := LeanLab.Dudek2014.SigmaH.sigmaBd_of_hsw hN
  intro x hx
  obtain ⟨h0, h1⟩ := LeanLab.Dudek2014.Section22.hD_small hx
  have := hS x hx
  simp only at this ⊢
  rw [sigma_patch hx]
  rwa [Zr_eq_Zreal hRH (by linarith), Zr_eq_Zreal hRH (by linarith),
    Zr_eq_Zreal hRH (by linarith)] at this

/-- **A Goldbach number in every `(x, x + 1478]`, `2 ≤ x ≤ 1.6·10^33`**, under RH, CONDITIONAL ON
the Hasanalizade-Shen-Wong `N(T)`, the `4·10^18` even check and `GapBound1476`. -/
theorem goldbach_gap_1478_RH_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hG : GapBound1476)
    {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 1.6e33) :
    ∃ n : ℕ, LeanLab.GoldbachGaps.IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 :=
  LeanLab.GoldbachGaps.DudekRH.goldbach_gap_1478_RH hE hG (theorem2_of_RH_hsw hRH hN) hx hx'

/-- **Kaniecki 1995 Lemma 6** under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)` and
`GapBound1476`. -/
theorem kaniecki_lemma6_RH_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hG : GapBound1476)
    (x : ℕ) (hx : 23 * 10 ^ 8 ≤ x) :
    (LeanLab.KanieckiGap.lam x : ℝ) < 1 / (4 * Real.pi) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 :=
  LeanLab.KanieckiGap.lemma6_dudek (theorem2_of_RH_hsw hRH hN) hG x hx

end LeanLab.PNTPort.ExplicitPsi1.Trivial

namespace LeanLab.RamareSaouter2003

/-- **Ramaré-Saouter 2003 Theorem 1 under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong `N(T)`
only.** -/
theorem theorem1_of_RH_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ) :
    ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x - 8 / 5 * √x * Real.log x < p ∧ (p : ℝ) ≤ x :=
  theorem1_of_dudek (LeanLab.PNTPort.ExplicitPsi1.Trivial.theorem2_of_RH_hsw hRH hN)

end LeanLab.RamareSaouter2003
