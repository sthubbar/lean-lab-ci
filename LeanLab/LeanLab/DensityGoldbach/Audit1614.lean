/-
Unit U-1614, run 20261104T0803Z-26516. Refutations of `alsetri_prop_4_1_leaf2` and `leaf3`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.DensityGoldbach.AlsetriTransfer

namespace LeanLab.DensityGoldbach.Audit1614
open Finset

/-- `alsetri_prop_4_1_leaf3`, false: `f1 = f2 = 0`, `N = 1`, `c = 1`. -/
theorem old_alsetri_prop_4_1_leaf3_false :
    ¬ ∀ (N : ℕ) [NeZero N] (δ : ℝ) (_ : 0 < δ) (η q M : ℝ) (_ : 2 < q) (_ : q < 3) (c : ℝ) (_ : 0 < c)
      (f1 f2 : Fin 3 → ZMod N → ℝ) (_ : ∀ i r, ‖fourierZN N (f1 i) r‖ ≤ η)
      (_ : ∀ i, ∑ r, ‖fourierZN N (f2 i) r‖ ^ 2 ≤ M ^ 2),
      ∀ x : ZMod N, c / N ≤ ∑ y : ZMod N, ∑ z : ZMod N,
        (f1 0 y + f2 0 y) * (f1 1 z + f2 1 z) * (f1 2 (x - y - z) + f2 2 (x - y - z)) := by
  intro h
  have hz : ∀ r : ZMod 1, fourierZN 1 (fun _ => (0 : ℝ)) r = 0 := by
    intro r; simp [fourierZN]
  have := h 1 1 one_pos 0 (5 / 2) 0 (by norm_num) (by norm_num) 1 one_pos
    (fun _ _ => 0) (fun _ _ => 0) (fun _ r => by simp [hz r]) (fun _ => by simp [hz]) 0
  norm_num at this

/-- `alsetri_prop_4_1_leaf2`, false: `N = 2`, `f = δ₀` has `f̂ = 1` at both frequencies, so the
`ℓ²` sum is `2`, more than `M² = 2^{2/q}` with `M = 2^{1/q}`, as `q > 2`. -/
theorem old_alsetri_prop_4_1_leaf2_false :
    ¬ ∀ (N : ℕ) [NeZero N] (q M : ℝ) (_ : 2 < q) (_ : q < 3) (f2 : Fin 3 → ZMod N → ℝ)
      (_ : ∀ i, (∑ r, ‖fourierZN N (f2 i) r‖ ^ q) ^ (1 / q) ≤ M),
      ∀ i, ∑ r, ‖fourierZN N (f2 i) r‖ ^ 2 ≤ M ^ 2 := by
  intro h
  let f : ZMod 2 → ℝ := fun n => if n = 0 then 1 else 0
  have hf : ∀ r : ZMod 2, ‖fourierZN 2 f r‖ = 1 := by
    intro r
    have h0 : f 0 = 1 := by simp [f]
    have h1 : f 1 = 0 := by simp [f]
    have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    have : fourierZN 2 f r = 1 := by
      unfold fourierZN
      rw [hu, Finset.sum_pair (by decide)]
      simp [h0, h1, ZMod.val_zero]
    rw [this]; simp
  have e2 : ∑ _r : ZMod 2, (1 : ℝ) = 2 := by simp [ZMod.card]
  have := h 2 (5 / 2) ((2 : ℝ) ^ ((1 : ℝ) / (5 / 2))) (by norm_num) (by norm_num)
    (fun _ => f) (fun _ => by simp only [hf, Real.one_rpow, e2, le_refl]) 0
  simp only [hf, one_pow, e2] at this
  have h2 : ((2 : ℝ) ^ ((1 : ℝ) / (5 / 2))) ^ 2 = (2 : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h3 : (2 : ℝ) ^ ((4 : ℝ) / 5) < 2 := by
    calc (2 : ℝ) ^ ((4 : ℝ) / 5) < (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 2 := by norm_num
  rw [h2] at this
  linarith

end LeanLab.DensityGoldbach.Audit1614
#print axioms LeanLab.DensityGoldbach.Audit1614.old_alsetri_prop_4_1_leaf3_false
#print axioms LeanLab.DensityGoldbach.Audit1614.old_alsetri_prop_4_1_leaf2_false
