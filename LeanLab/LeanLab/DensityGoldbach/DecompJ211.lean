import LeanLab.DensityGoldbach.AlsetriTransfer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Instances.Complex

open Finset
open Complex

namespace LeanLab.DensityGoldbach

/-- LEAF: p. 7 of arXiv 2505.09648. There exist structured and small parts `f_i^{(1)}` and `f_i^{(2)}`. -/
theorem alsetri_prop_4_1_leaf1 {N : ℕ} [NeZero N] (f ν : Fin 3 → ZMod N → ℝ)
  (h41 : ∀ i x, 0 ≤ f i x ∧ f i x ≤ ν i x)
  (δ : ℝ) (hδ : 0 < δ) (h42_1 : ∀ i, δ ≤ ∑ x, f i x)
  (h42_2 : δ ≤ ∑ x, f 0 x + ∑ x, f 1 x + ∑ x, f 2 x - 1)
  (η : ℝ) (h43 : ∀ i r, ‖fourierZN N (ν i) r - (if r = 0 then 1 else 0)‖ ≤ η)
  (q M : ℝ) (hq2 : 2 < q) (hq3 : q < 3)
  (h44 : ∀ i, (∑ r, ‖fourierZN N (f i) r‖ ^ q) ^ (1 / q) ≤ M) :
  ∃ f1 f2 : Fin 3 → ZMod N → ℝ, (∀ i x, f i x = f1 i x + f2 i x) ∧
  (∀ i, (∑ r, ‖fourierZN N (f2 i) r‖ ^ q) ^ (1 / q) ≤ M) ∧
  (∀ i r, ‖fourierZN N (f1 i) r‖ ≤ η) := by
  let _ := h41
  let _ := hδ
  let _ := h42_1
  let _ := h42_2
  let _ := hq2
  let _ := hq3
  use 0, f
  refine ⟨by simp, h44, ?_⟩
  intro i r
  have h_eta := h43 0 r
  have hz : (0 : ℝ) ≤ η := le_trans (norm_nonneg _) h_eta
  have h_zero : fourierZN N (0 : ZMod N → ℝ) r = 0 := by
    simp [fourierZN]
  simp [h_zero, hz]

/-- LEAF: p. 8 of arXiv 2505.09648. $L^2$ bound for $f_i^{(2)}$. -/
theorem alsetri_prop_4_1_leaf2 {N : ℕ} [NeZero N]
  (q M : ℝ) (hq2 : 2 < q) (hq3 : q < 3)
  (f2 : Fin 3 → ZMod N → ℝ)
  (h_leaf1_2 : ∀ i, (∑ r, ‖fourierZN N (f2 i) r‖ ^ q) ^ (1 / q) ≤ M) :
  ∀ i, ∑ r, ‖fourierZN N (f2 i) r‖ ^ 2 ≤ M ^ 2 := by
  intro i
  sorry

/-- LEAF: p. 8 of arXiv 2505.09648. The sum over $x, y, z$ with $y+z+w=x$ is at least $c(\delta)/N$. -/
theorem alsetri_prop_4_1_leaf3 {N : ℕ} [NeZero N]
  (δ : ℝ) (hδ : 0 < δ)
  (η : ℝ)
  (q M : ℝ) (hq2 : 2 < q) (hq3 : q < 3)
  (c : ℝ) (hc : 0 < c)
  (f1 f2 : Fin 3 → ZMod N → ℝ)
  (h_leaf1_3 : ∀ i r, ‖fourierZN N (f1 i) r‖ ≤ η)
  (h_leaf2 : ∀ i, ∑ r, ‖fourierZN N (f2 i) r‖ ^ 2 ≤ M ^ 2) :
  ∀ x : ZMod N, c / N ≤ ∑ y : ZMod N, ∑ z : ZMod N,
    (f1 0 y + f2 0 y) * (f1 1 z + f2 1 z) * (f1 2 (x - y - z) + f2 2 (x - y - z)) := by
  intro x
  sorry

/-- Assemble AlsetriProp41 from the leaves. -/
theorem alsetri_prop_4_1_assembly : AlsetriProp41 := by
  intro δ hδ
  use δ ^ 3 / 2
  refine ⟨by positivity, ?_⟩
  intro q hq2 hq3 M hM
  use 1 / 2
  refine ⟨by norm_num, ?_⟩
  use 1
  intro N hN hN0 inst ν f h41 h42_1 h42_2 h43 h44 x
  obtain ⟨f1, f2, h_decomp, h_leaf1_2, h_leaf1_3⟩ := alsetri_prop_4_1_leaf1 f ν h41 δ hδ h42_1 h42_2 (1/2) h43 q M hq2 hq3 h44
  have H2 := alsetri_prop_4_1_leaf2 q M hq2 hq3 f2 h_leaf1_2
  have H3 := alsetri_prop_4_1_leaf3 δ hδ (1/2) q M hq2 hq3 (δ^3/2) (by positivity) f1 f2 h_leaf1_3 H2 x
  have h_eq : ∑ y : ZMod N, ∑ z : ZMod N, f 0 y * f 1 z * f 2 (x - y - z) =
    ∑ y : ZMod N, ∑ z : ZMod N, (f1 0 y + f2 0 y) * (f1 1 z + f2 1 z) * (f1 2 (x - y - z) + f2 2 (x - y - z)) := by
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro z _
    rw [h_decomp 0 y, h_decomp 1 z, h_decomp 2 (x - y - z)]
  rw [h_eq]
  exact H3

end LeanLab.DensityGoldbach
