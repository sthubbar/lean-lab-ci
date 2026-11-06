/-
Audit of the old Shao decomposition, without using that decomposition as an input.
This is a lab statement error, not a paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Binary

namespace LeanLab.DensityGoldbach.Audit408

/-- Shao 1206.6139v2 page 2, Theorem 1.3 only concerns sufficiently large n.
The hypotheses of the old DecompJ616 leaf 3 hold at A = P, delta = 1/4,
but the odd integer 1 is not a sum of three primes. -/
theorem old_shao_leaf3_counterexample :
    (0 : ℝ) < 1 / 4 ∧ P ⊆ P ∧
    3 / 2 + (1 : ℝ) / 4 ≤ 2 * lowerDensityRes P 1 3 + lowerDensityRes P 2 3 ∧
    3 / 2 + (1 : ℝ) / 4 ≤ 2 * lowerDensityRes P 2 3 + lowerDensityRes P 1 3 ∧
    Odd (1 : ℕ) ∧ ¬ IsSum3 P P P 1 := by
  have h1 : lowerDensityRes P 1 3 = 1 := lowerDensityRes_P 1 3 (by norm_num) (by norm_num)
  have h2 : lowerDensityRes P 2 3 = 1 := lowerDensityRes_P 2 3 (by norm_num) (by norm_num)
  refine ⟨by norm_num, Set.Subset.refl _, by rw [h1, h2]; norm_num,
    by rw [h1, h2]; norm_num, by decide, ?_⟩
  rintro ⟨a, ha, b, hb, c, hc, he⟩
  have ha2 := ha.two_le
  have hb2 := hb.two_le
  have hc2 := hc.two_le
  omega

end LeanLab.DensityGoldbach.Audit408

#print axioms LeanLab.DensityGoldbach.Audit408.old_shao_leaf3_counterexample
