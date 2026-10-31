import Mathlib
import LeanLab.Zhao2025.Zhao2025U6906Sub

/-!
# Zhao 2025, the printed case `λ₁,₁ ∈ [0.30, 0.40]`, (4.7) to (4.9), through `layout47`

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6909, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

With Lemma 2.4 (4), `N(1.29) ≤ 1`, and the inputs of (4.8), `T₁ ≤ 0.1231`, `Tᵢ ≤ 0.0971`,
`Σ_{i≥2} Tᵢ ≤ 6.85`, certified in U-6904 and U-6905 as `p48a_ok`, `p48b_ok`, `p48sum_ok`
CONDITIONAL ON (3.15), (3.16), (3.26): `Σ Sᵢ² < 0.9063` for every `λ₁,₁ ≥ 0.30`, Zhao's (4.9).
Together with `sub010_closes`, `sub001_closes` of U-6906 and `case1_bound` of Section4.lean this
covers every case `λ₁,₁ ≤ 0.40` of Theorem 1.2 on the displays.
-/

namespace LeanLab.Zhao2025.U6900

theorem exp_one_le_q : Real.exp (-(1 : ℝ)) ≤ ((eupq 1 : ℚ) : ℝ) := by
  have := eupq_ge 1 (by norm_num); push_cast at this; exact this

set_option maxRecDepth 100000 in
theorem num030 : (eupq 1 + 1231 / 10000) ^ 2 + 971 / 10000 * (685 / 100) < (9063 / 10000 : ℚ) := by
  decide +kernel

/-- PROVED: the case `λ₁,₁ ∈ [0.30, 0.40]` closes, `Σ Sᵢ² < 0.9063`, given the (4.8) inputs. -/
theorem sub030_closes (n : ℕ) (S : ℕ → ℝ) (l11 : ℝ) (hl : 0.30 ≤ l11) (hS0 : 0 ≤ S 0)
    (h0 : S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.1231)
    (hS : ∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0971)
    (hsum : ∑ i ∈ Finset.range n, S (i + 1) ≤ 6.85) :
    ∑ i ∈ Finset.range (n + 1), S i ^ 2 < 0.9063 := by
  have he : Real.exp (-(10 / 3 * l11)) ≤ ((eupq 1 : ℚ) : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_one_le_q
  have h := layout47 n S (((eupq 1 : ℚ) : ℝ)) 0.1231 0.0971 6.85 hS0 (by linarith) hS hsum
    (by norm_num)
  have hn : (((eupq 1 + 1231 / 10000) ^ 2 + 971 / 10000 * (685 / 100) : ℚ) : ℝ) <
      ((9063 / 10000 : ℚ) : ℝ) := by exact_mod_cast num030
  push_cast at hn
  norm_num at h hn ⊢
  linarith

end LeanLab.Zhao2025.U6900

#print axioms LeanLab.Zhao2025.U6900.num030
#print axioms LeanLab.Zhao2025.U6900.sub030_closes
