import LeanLab.LZCesaroShort.Lemma3Parseval
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# P0058 Lemmas 1 and 3, stated as cited Props

Lab statements, unit U-5863, CLOUD 20261020T0014Z-cloud30. AI wrote this file.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 3, with `z = 1/N − 2πiα` and `S̃(α) = ∑ Λ(n) e^{−n/N} e(nα)`:
* Lemma 1, assuming RH: for `N` large and `0 ≤ ξ ≤ 1/2`,
  `∫_{−ξ}^{ξ} |S̃(α) − 1/z|² dα ≪ N ξ (1 + log²(2Nξ))`;
* Lemma 3, unconditional: `∫_{−1/2}^{1/2} |S̃(α) − 1/z|² dα = (N/2) log N + O(N (log N)^{1/2})`.
These are Prop definitions. Lemma 1 is proved from RH in Lemma1Proved.lean and its cited name
is exported by ResolvedStatements.lean. Lemma 3 remains an unproved cited Prop.
-/

namespace LeanLab.LZCesaroShort

open Complex MeasureTheory
open LeanLab.PNTPort.LargeSieve
open scoped ArithmeticFunction.vonMangoldt

/-- `S̃(α) = ∑ Λ(n) e^{−n/N} e(nα)`, the paper's (4). -/
noncomputable def St (N : ℕ) (α : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * e (n * α)

/-- `z = 1/N − 2πiα`, the paper's (5). -/
noncomputable def zz (N : ℕ) (α : ℝ) : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) - 2 * Real.pi * α * I

/-- Lemma 1, the RH mean square near `0`, as a Prop with an absolute constant and threshold. -/
def Lemma1 : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 / 2 →
    ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2
      ≤ K * N * ξ * (1 + Real.log (2 * N * ξ) ^ 2)

/-- Cited Lemma 3 on page 3 of arXiv 1606.00869v2, from Lemma 2.3 of the 2012 paper.
The full mean square is `(N/2) log N` within `K N √(log N)`.
This is an unproved Prop. No theorem asserting it is supplied here. -/
def Lemma3 : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖St N α - 1 / zz N α‖ ^ 2) - N / 2 * Real.log N|
      ≤ K * N * Real.sqrt (Real.log N)

/- The proved name lz_lemma1 is exported by ResolvedStatements.lean.
The unused sorry declaration lz_lemma3 is retired. The exact Lemma3 Prop is unchanged. -/


/-- Cited input restored exactly from main. It remains unproved. -/
theorem lz_lemma3 : Lemma3 := by sorry

end LeanLab.LZCesaroShort
