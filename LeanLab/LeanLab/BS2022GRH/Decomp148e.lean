/- AI wrote this Lean code for CODEX task148.
Recovered from the recorded write commands. Fresh checks are required.
Journal Lemma 3, pp. 1215 and 1216. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC164a
namespace LeanLab.BS2022GRH.Decomp148e
open Real Finset Classical ChenThresholdGRH
/-- LEAF. Lemma 3 p. 1216, explicit progression estimate at the running endpoint.
CITED source is Ernvall-Hytonen and Palojarvi 2022 Theorem 1.
The source specialization and the sealed small endpoint range both remain OPEN. -/
theorem progression_at_endpoint (hG : GRH) (d a : ℕ) (N : ℝ)
    (hd : 3 ≤ d) (hdN : (d : ℝ) ≤ √N) (ha : Nat.Coprime a d) :
    |((((range (⌊N⌋₊ + 1)).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℕ) : ℝ)
        - liPV N / (d.totient : ℝ)| ≤ qG N * √N * log N := by
  exact DecompC164a.progression_at_endpoint hG d a N hd hdN ha
/-- LEAF. Coefficient domination in the proof of Lemma 3 p. 1216.
Check the negative final term together with the positive preceding terms. -/
theorem qG_antitone (X₂ N : ℝ) (hX : 9 ≤ X₂) (hXN : X₂ ≤ N) :
    qG N ≤ qG X₂ := by
  exact DecompC164a.qG_antitone X₂ N hX hXN
/-- Exact sealed Lemma3J. OPEN through the two leaves, with no direct sorry. -/
theorem lemma3J : Lemma3J := by
  intro hG d a X₂ N hd hdX hXN ha
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hspos : 0 < √X₂ := by linarith
  have hX0 : 0 ≤ X₂ := (sqrt_pos.mp hspos).le
  have hX9 : 9 ≤ X₂ := by nlinarith [sq_sqrt hX0]
  have hN9 : 9 ≤ N := hX9.trans hXN
  have hraw := progression_at_endpoint hG d a N hd (hdX.trans (sqrt_le_sqrt hXN)) ha
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (qG_antitone X₂ N hX9 hXN) (sqrt_nonneg N))
    (log_nonneg (by linarith)))
end LeanLab.BS2022GRH.Decomp148e
#print axioms LeanLab.BS2022GRH.Decomp148e.progression_at_endpoint
#print axioms LeanLab.BS2022GRH.Decomp148e.qG_antitone
#print axioms LeanLab.BS2022GRH.Decomp148e.lemma3J
