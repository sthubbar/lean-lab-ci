/-
Split of `paper_dense_modular_progressions_input`, the modular output of the proof of
Theorem 1.3 on page 17 of Teravainen 2016, arXiv 1611.08585v2. Three LEAF lemmas follow the
three steps of the printed proof: the middle third density step, the pigeonhole display (4.6),
and the Green Tao transference step with the wraparound remark. The assembly
`paper_dense_modular_progressions_input_of_leaves` restates the sealed statement and chains the
leaves with no `sorry` of its own. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputs

namespace LeanLab.Teravainen2016

open Finset
open scoped Classical

/-- LEAF: page 17, proof of Theorem 1.3, first sentence. If `A ⊆ 𝒫*` has positive upper density
in `𝒫*`, there is `δ > 0` with `|A ∩ (N/3, 2N/3)| ≥ δ |𝒫* ∩ (N/3, 2N/3)|` for `N` in an infinite
set of positive integers. Class HARD: passing from initial segments to middle thirds uses the
order of magnitude of the count of `𝒫*` up to `x`. -/
theorem leaf_middle_third_density_T13 (A : Set ℕ) (hA : A ⊆ PStar)
    (hδ : PosUpperDensityIn A PStar) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ X : ℕ, ∃ N : ℕ, X ≤ N ∧
      δ * (#{n ∈ range N | N < 3 * n ∧ 3 * n < 2 * N ∧ n ∈ PStar} : ℝ) ≤
        (#{n ∈ range N | N < 3 * n ∧ 3 * n < 2 * N ∧ n ∈ A} : ℝ) := by
  sorry

/-- LEAF: page 17, proof of Theorem 1.3, display (4.6). With `W`, `w`, `J` as in (3.3) and
`J = ⌊10/δ⌋`, the pigeonhole principle over the amenable residues `1 ≤ B ≤ W`, the lower bound
for `|𝒫* ∩ (N/3, 2N/3)|` from Proposition 3.2 with `χ ≡ 1`, and the Chinese remainder count
of at most `10^10 W (log w)^(-3/2)` amenable residues give one amenable `B` and an infinite
set `𝒩'` with `|A_B ∩ (N/3, 2N/3)| ≥ δ₁ δ (log w)^(3/2) N / (W (log N)^(3/2))`, where
`A_B = A ∩ {W n + B : n ≥ 1}` and `δ₁ > 0` is absolute. Class HARD. -/
theorem leaf_pigeonhole_4_6_T13 :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ (A : Set ℕ), A ⊆ PStar → ∀ δ : ℝ, 0 < δ → δ < 1 →
      (∀ X : ℕ, ∃ N : ℕ, X ≤ N ∧
        δ * (#{n ∈ range N | N < 3 * n ∧ 3 * n < 2 * N ∧ n ∈ PStar} : ℝ) ≤
          (#{n ∈ range N | N < 3 * n ∧ 3 * n < 2 * N ∧ n ∈ A} : ℝ)) →
      ∃ w₁ : ℝ, ∀ w : ℕ, wBig ≤ w → w₁ ≤ w →
        ∃ B : ℤ, 1 ≤ B ∧ B ≤ WW (⌊10 / δ⌋₊) w ∧ Amenable (WW (⌊10 / δ⌋₊) w) B ∧
          ∀ X : ℕ, ∃ N : ℕ, X ≤ N ∧
            δ₁ * δ * Real.log w ^ ((3 : ℝ) / 2) * N /
                ((WW (⌊10 / δ⌋₊) w : ℝ) * Real.log N ^ ((3 : ℝ) / 2)) ≤
              (#{n ∈ range N | N < 3 * n ∧ 3 * n < 2 * N ∧ n ∈ A ∧
                  ∃ m : ℕ, 1 ≤ m ∧ (n : ℤ) = WW (⌊10 / δ⌋₊) w * m + B} : ℝ) := by
  sorry

/-- LEAF: page 17, proof of Theorem 1.3, last paragraph. For the weight
`g = δ₂ (log N)^(3/2) (log w)^(-3/2) 1_{A_B ∩ (N/3, 2N/3)}` and the majorant
`ν = β 1_[1,N]` of Proposition 4.1, extended periodically to `ℤ_N`, the conditions (5.3) to
(5.6) of Green and Tao, Restriction theory of the Selberg sieve, Proposition 5.1, hold: (5.3)
from Proposition 4.1, (5.6) from Proposition 3.3, (5.5) from properties (i) to (v) of `β`, and
(5.4) from display (4.6). That proposition then yields, for `N` in `𝒩'`, a nontrivial three
term progression of `ℤ_N` inside `A_B ∩ (N/3, 2N/3)`. Class HARD: this is the cited transference
principle together with the majorant checks of Section 4. -/
theorem leaf_transference_T13 (A : Set ℕ) (hA : A ⊆ PStar) (δ δ₁ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hδ₁ : 0 < δ₁) :
    ∃ w₂ : ℝ, ∀ w : ℕ, wBig ≤ w → w₂ ≤ w → ∀ B : ℤ, 1 ≤ B → B ≤ WW (⌊10 / δ⌋₊) w →
      Amenable (WW (⌊10 / δ⌋₊) w) B →
      (∀ X : ℕ, ∃ N : ℕ, X ≤ N ∧
        δ₁ * δ * Real.log w ^ ((3 : ℝ) / 2) * N /
            ((WW (⌊10 / δ⌋₊) w : ℝ) * Real.log N ^ ((3 : ℝ) / 2)) ≤
          (#{n ∈ range N | N < 3 * n ∧ 3 * n < 2 * N ∧ n ∈ A ∧
              ∃ m : ℕ, 1 ≤ m ∧ (n : ℤ) = WW (⌊10 / δ⌋₊) w * m + B} : ℝ)) →
      ∀ X : ℕ, ∃ N a b c : ℕ, X ≤ N ∧
        a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
        N < 3 * a ∧ 3 * a < 2 * N ∧
        N < 3 * b ∧ 3 * b < 2 * N ∧
        N < 3 * c ∧ 3 * c < 2 * N ∧
        a ≠ b ∧ (a : ZMod N) + c = 2 * b := by
  sorry

/-- The sealed modular output of Section 4, assembled from the three LEAF steps above.
CONDITIONAL ON those leaves. -/
theorem paper_dense_modular_progressions_input_of_leaves (A : Set ℕ)
    (hA : A ⊆ PStar) (hδ : PosUpperDensityIn A PStar) :
    ∀ X : ℕ, ∃ N a b c : ℕ, X ≤ N ∧
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
      N < 3 * a ∧ 3 * a < 2 * N ∧
      N < 3 * b ∧ 3 * b < 2 * N ∧
      N < 3 * c ∧ 3 * c < 2 * N ∧
      a ≠ b ∧ (a : ZMod N) + c = 2 * b := by
  obtain ⟨δ, hδ0, hδ1, hmid⟩ := leaf_middle_third_density_T13 A hA hδ
  obtain ⟨δ₁, hδ₁, hpig⟩ := leaf_pigeonhole_4_6_T13
  obtain ⟨w₁, hw₁⟩ := hpig A hA δ hδ0 hδ1 hmid
  obtain ⟨w₂, hw₂⟩ := leaf_transference_T13 A hA δ δ₁ hδ0 hδ1 hδ₁
  obtain ⟨w, hw⟩ := exists_nat_ge (max wBig (max w₁ w₂))
  have hwB : wBig ≤ w := le_trans (le_max_left _ _) hw
  have hw1 : w₁ ≤ w := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hw
  have hw2 : w₂ ≤ w := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hw
  obtain ⟨B, hB1, hBW, hBam, hcount⟩ := hw₁ w hwB hw1
  exact hw₂ w hwB hw2 B hB1 hBW hBam hcount

#print axioms paper_dense_modular_progressions_input_of_leaves

end LeanLab.Teravainen2016
