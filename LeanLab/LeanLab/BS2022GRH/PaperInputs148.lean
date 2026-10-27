/- AI wrote this Lean code for CODEX task148.
Recovered from recorded write commands after execution access failed.
These are cited paper statements, not new axioms. Each new Prop needs Claude review.
A fresh build and gate checks are required. Goldbach is open. -/
import LeanLab.BS2022GRH.RH148
import LeanLab.BS2022GRH.Lemma5Coeffs138
namespace LeanLab.BS2022GRH.PaperInputs148
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- Prime count at a real endpoint, journal Lemmas 1 and 3 p. 1215. -/
def primeCount (x : ℝ) : ℝ :=
  (((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime)).card : ℝ)
/-- Journal Lemma 1 p. 1215. CITED from Schoenfeld 1976 Corollary 1.
The logarithmic integral is the lab's principal value. -/
def Lemma1J : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 2657 ≤ x →
    |primeCount x - liPV x| ≤ √x * log x / (8 * π)
/-- Journal Lemma 2 p. 1215. CITED from Rosser and Schoenfeld 1975 Theorem 18. -/
def Lemma2J : Prop :=
  ∀ x : ℝ, 0 < x → x ≤ 1e8 → Chebyshev.theta x ≤ x
/-- Journal Lemma 4 p. 1216, display 1. CITED from Robin 1983 Theorem 11. -/
def Lemma4J : Prop :=
  ∀ n : ℕ, 3 ≤ n → (n.primeFactors.card : ℝ) < 1.3841 * log n / log (log n)
/-- Journal Lemma 5 first estimate p. 1216. CITED from Buthe 2014 display 4.6.
Squarefree support equals the square Mobius weight. -/
def Lemma5MuJ : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    (((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ) ≤ Lemma5Coeffs138.mMu x * x
/-- Journal Lemma 5 second estimate p. 1216. CITED from Ramare 2019 Theorem 3.1. -/
def Lemma5PhiJ : Prop :=
  ∀ x : ℝ, 1 < x →
    (∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n), (1 : ℝ) / n.totient) ≤ Mphi x * log x
/-- Lemma 1 under GRH, CONDITIONAL ON the cited Lemma1J and GRH. -/
theorem lemma1_of_grh (h1 : Lemma1J) (hG : GRH) (x : ℝ) (hx : 2657 ≤ x) :
    |primeCount x - liPV x| ≤ √x * log x / (8 * π) :=
  h1 (RH148.rh_of_grh hG) x hx
end
end LeanLab.BS2022GRH.PaperInputs148
#print axioms LeanLab.BS2022GRH.PaperInputs148.lemma1_of_grh
