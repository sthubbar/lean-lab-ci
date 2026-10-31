/-
AI wrote this Lean code. CODEX task94.
P0009 Lemma 40, pages 38 and 39.
The existing Lemma40Core leaves the lower bounds on odd prime factors as hypotheses.
This file derives those bounds from the paper's decreasing odd prime sequence.
Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Lemma40Core
namespace LeanLab.ChenExplicit.Lemma40Full94
/-- A decreasing chain of n plus 1 odd integers at least 3 starts at least at 2n plus 3. -/
theorem odd_chain_head_ge (n : ℕ) (q : ℕ → ℕ)
    (hq : ∀ i ≤ n, 3 ≤ q i ∧ Odd (q i))
    (hdec : ∀ i < n, q (i + 1) < q i) : 2 * n + 3 ≤ q 0 := by
  induction n generalizing q with
  | zero => simpa using (hq 0 le_rfl).1
  | succ n ih =>
    have hs : 2 * n + 3 ≤ q 1 := by
      simpa using ih (fun i => q (i + 1))
        (fun i hi => hq (i + 1) (by omega))
        (fun i hi => hdec (i + 1) (by omega))
    have hlt := hdec 0 (by omega)
    obtain ⟨a, ha⟩ := (hq 0 (by omega)).2
    obtain ⟨b, hb⟩ := (hq 1 (by omega)).2
    simp only [zero_add] at hlt
    omega
/-- P0009 Lemma 40 with its odd prime ordering hypotheses discharged. -/
theorem lemma40 {ell : ℕ} (hell : 2 ≤ ell) (q : ℕ → ℕ)
    (hq : ∀ i, 2 ≤ i → i ≤ ell → (q i).Prime ∧ Odd (q i))
    (hdec : ∀ i, 2 ≤ i → i < ell → q (i + 1) < q i) :
    Lemma40Core.reciprocalPrefixes (ell - 1) (fun i => (q (i + 2) : ℝ) - 2) ≤ 1 := by
  have h3 (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ ell) : 3 ≤ q i := by
    have hp := (hq i hi hi').1.two_le
    obtain ⟨a, ha⟩ := (hq i hi hi').2
    omega
  apply Lemma40Core.lemma40_core hell q
  · intro i hi
    exact h3 (i + 2) (by omega) (by omega)
  · have hh := odd_chain_head_ge (ell - 2) (fun i => q (i + 2))
      (fun i hi => ⟨h3 (i + 2) (by omega) (by omega), (hq (i + 2) (by omega) (by omega)).2⟩)
      (fun i hi => hdec (i + 2) (by omega) (by omega))
    simp only [zero_add] at hh
    have hnat : 2 * ell ≤ q 2 + 1 := by omega
    have hr : 2 * (ell : ℝ) ≤ q 2 + 1 := by exact_mod_cast hnat
    linarith

#print axioms lemma40
#print axioms odd_chain_head_ge
end LeanLab.ChenExplicit.Lemma40Full94
