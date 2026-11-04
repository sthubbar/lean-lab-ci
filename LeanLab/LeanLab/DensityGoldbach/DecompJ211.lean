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

/-- REFUTED, `Audit1614.old_alsetri_prop_4_1_leaf2_false`: for `q > 2` the `ℓ^q` norm does not bound the
`ℓ²` norm. Do not prove this. Unused since U-1614. Kept as text of record.
LEAF: p. 8 of arXiv 2505.09648. $L^2$ bound for $f_i^{(2)}$. -/
theorem alsetri_prop_4_1_leaf2 {N : ℕ} [NeZero N]
  (q M : ℝ) (hq2 : 2 < q) (hq3 : q < 3)
  (f2 : Fin 3 → ZMod N → ℝ)
  (h_leaf1_2 : ∀ i, (∑ r, ‖fourierZN N (f2 i) r‖ ^ q) ^ (1 / q) ≤ M) :
  ∀ i, ∑ r, ‖fourierZN N (f2 i) r‖ ^ 2 ≤ M ^ 2 := by
  intro i
  sorry

/-- REFUTED, `Audit1614.old_alsetri_prop_4_1_leaf3_false`: `f1 = f2 = 0` satisfies every hypothesis. Do not
prove this. Unused since U-1614. Kept as text of record.
LEAF: p. 8 of arXiv 2505.09648. The sum over $x, y, z$ with $y+z+w=x$ is at least $c(\delta)/N$. -/
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

/-- Proposition 4.1, the cited statement. DECISION U-1614: the old proof took `f1 = 0, f2 = f` from
`alsetri_prop_4_1_leaf1` and then the false leaves 2 and 3, a hollow split. Paper not in the copies. -/
theorem alsetri_prop_4_1_assembly : AlsetriProp41 := alsetri_prop_4_1

end LeanLab.DensityGoldbach
