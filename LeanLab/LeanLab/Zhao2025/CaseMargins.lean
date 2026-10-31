import LeanLab.Zhao2025.Theorem12

/-!
Quantitative version of the layout C arithmetic.
Source: Zhao 2025, Section 4, pages 15 and 16, and the existing lab refinement.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6837 LeanLab.Zhao2025.U6900

/-- A common strict bound for both admissible layouts bounds their square sum. -/
theorem closes_below (n : ℕ) (R T : ℕ → ℝ) (rA rB r3 sR sT t1 t3 t5 b : ℝ)
    (h0 : 0 ≤ r3) (h1 : 0 ≤ t5) (h2 : r3 ≤ rA) (h3 : r3 ≤ rB) (h4 : t5 ≤ t1) (h5 : t5 ≤ t3)
    (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ sR) (hsT : ∑ i ∈ Finset.range n, T i ≤ sT)
    (hcfg : (∀ i, R i ≤ hd rA r3 r3 r3 r3 i ∧ T i ≤ hd t1 t3 t3 t3 t5 i) ∨
      (∀ i, R i ≤ hd rB rB r3 r3 r3 i ∧ T i ≤ hd t1 t1 t3 t3 t5 i))
    (ha : r3 * sR + t5 * (2 * sR + sT) +
      (ex r3 t5 rA t1 + ex r3 t5 r3 t3 + ex r3 t5 r3 t3 + ex r3 t5 r3 t3) < b)
    (hb : r3 * sR + t5 * (2 * sR + sT) +
      (ex r3 t5 rB t1 + ex r3 t5 rB t1 + ex r3 t5 r3 t3 + ex r3 t5 r3 t3) < b) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < b := by
  rcases hcfg with h | h
  · exact lt_of_le_of_lt (layout4 n R T r3 t5 sR sT rA r3 r3 r3 t1 t3 t3 t3 h0 h1 h2 le_rfl le_rfl
      le_rfl h4 h5 h5 h5 hR0 hT0 (fun i => (h i).1) (fun i => (h i).2) hsR hsT) ha
  · exact lt_of_le_of_lt (layout4 n R T r3 t5 sR sT rB rB r3 r3 t1 t1 t3 t3 h0 h1 h3 h3 le_rfl
      le_rfl h4 h4 h5 h5 hR0 hT0 (fun i => (h i).1) (fun i => (h i).2) hsR hsT) hb


#print axioms closes_below

end LeanLab.Zhao2025.Task56
