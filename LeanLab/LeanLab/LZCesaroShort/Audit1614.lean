/-
Unit U-1614, run 20261104T0803Z-26516. Refutation of the old `lemma5_bound_TH_leaf`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.LZCesaroShort.Lemma5

namespace LeanLab.LZCesaroShort.Audit1614
open Finset

/-- The old leaf is false at `N = 2, H = 1, α = 0`: `1 / ‖0‖ = 0` makes the right side `0`, and
`TH 2 1 1 0 = 1`, from `lemma5_full_eq`, the Fejer kernel at `0`. -/
theorem old_lemma5_bound_TH_leaf_false :
    ¬ ∃ K : ℝ, ∀ N H : ℕ, ∀ α : ℝ, 2 ≤ N → 1 ≤ H → H ≤ N →
      ‖TH N H H α‖ ≤ K * min (H : ℝ) (1 / ‖α‖) := by
  rintro ⟨K, hK⟩
  have h := hK 2 1 0 (by norm_num) le_rfl (by norm_num)
  have hT : TH 2 1 (1 : ℕ) 0 ≠ 0 := by
    have := lemma5_full_eq (N := 2) (H := 1) (by norm_num) 0
    rw [this]
    simp [LeanLab.PNTPort.LargeSieve.e]
  simp only [norm_zero, div_zero] at h
  have hm : min ((1 : ℕ) : ℝ) 0 = 0 := by norm_num
  rw [hm, mul_zero] at h
  exact hT (norm_le_zero_iff.mp h)

end LeanLab.LZCesaroShort.Audit1614
#print axioms LeanLab.LZCesaroShort.Audit1614.old_lemma5_bound_TH_leaf_false
