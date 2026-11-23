/-
ROUTE BURST S76 burst-20261122, unit ep2022_wire. EP2022 Theorem 1, Ernvall-Hytonen and
Palojarvi, arXiv 2003.01925v4, p. 2, assembled exactly as in
`ProgressionEPS70.ep2022_theorem1_of_leaves`, with the two former LEAFs replaced by their
S76 proofs: Lemma 31 pp. 40 to 41 by `ProgressionLemma31S76.lemma31_S76` and the final
simplification pp. 45 to 46 by `ProgressionFinalS76.final_combination_S76`.
The one remaining EP2022 input on this path is the LEAF `ProgressionEPS70.thm3`, Theorem 3
p. 3, split further in `ProgressionThm3S76` but kept as one named input here.
AI wrote this Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.ProgressionEPS70
import LeanLab.BS2022GRH.ProgressionLemma31S76
import LeanLab.BS2022GRH.ProgressionFinalS76

namespace LeanLab.BS2022GRH.ProgressionWireS76
open Real Finset Classical ChenThresholdGRH LeanLab.BS2022GRH.ProgressionEPS70
noncomputable section

/-- EP2022 Theorem 1 p. 2 in the exact form of `ProgressionS63.ep2022_theorem1`.
CONDITIONAL ON GRH and the LEAF `ProgressionEPS70.thm3` only. -/
theorem ep2022_theorem1_S76 (hG : GRH) (q a : ℕ) (x : ℝ)
    (ha : Nat.Coprime a q) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    |((((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℕ) : ℝ)
        - liPV x / (q.totient : ℝ)| <
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [display_50_53 q a x hq hx2]
  have hA := ProgressionLemma31S76.lemma31_S76 q a x hq hx (fun t ht1 _ => thm3 hG q a t ha hq ht1)
  have hB := display_51 q a x hq hx2
  have hC := display_52 q a x hq hx2
  have hD : |(-liPV 2 + 2 / log 2) / (q.totient : ℝ)| = |-liPV 2 + 2 / log 2| / (q.totient : ℝ) := by
    rw [abs_div, abs_of_pos hphi]
  have hF := ProgressionFinalS76.final_combination_S76 q x hq hx
  calc _ ≤ |(psiAP q a x - x / (q.totient : ℝ)) / log x
          + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)|
        + |(thetaAP q a x - psiAP q a x) / log x|
        + |∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2)|
        + |(-liPV 2 + 2 / log 2) / (q.totient : ℝ)| := by
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          exact abs_add_le _ _
    _ < _ := by rw [hD]; linarith

end

end LeanLab.BS2022GRH.ProgressionWireS76

#print axioms LeanLab.BS2022GRH.ProgressionWireS76.ep2022_theorem1_S76
