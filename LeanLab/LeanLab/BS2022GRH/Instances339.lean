/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Concrete finite witnesses for the rectangle on journal p. 1239. -/
import LeanLab.BS2022GRH.Bilinear339

namespace LeanLab.BS2022GRH.Instances339
open Real Finset Classical ChenThresholdGRH DecompC164c Bilinear339
noncomputable section

/-- At n equal to 256 the first small prime endpoint is exactly two.
Concrete instance of journal p. 1235 display 26. -/
theorem small_z : U7153.zz 256 = 2 := by
  unfold U7153.zz
  norm_num only [Nat.cast_ofNat]


/-- The large prime endpoint for the finite witness lies between three and seven.
Concrete instance of journal p. 1239. -/
theorem small_y : 3 < U7153.yy 256 ∧ U7153.yy 256 ≤ 7 := by
  have h0 : 0 ≤ U7153.yy 256 := rpow_nonneg (by norm_num) _
  have h3 : U7153.yy 256 ^ (3 : ℕ) = (256 : ℝ) := by
    unfold U7153.yy
    rw [← rpow_natCast, ← rpow_mul (by norm_num : (0 : ℝ) ≤ (256 : ℕ))]
    norm_num
  constructor
  · apply lt_of_pow_lt_pow_left₀ 3 h0
    rw [h3]
    norm_num
  · apply (pow_le_pow_iff_left₀ h0 (by norm_num : (0 : ℝ) ≤ 7) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [h3]
    norm_num

/-- The diagonal ordered pair seven, seven belongs to the relaxed product axis.
This checks that the sealed non-strict order is retained, journal p. 1239. -/
theorem diagonal_pair : (7, 7) ∈ pairSet 256 0 (3 / 4) := by
  have hy := small_y.2
  norm_num [pairSet, w, small_z, hy]

/-- The small prime axis is nonempty at the concrete finite witness, p. 1239. -/
theorem prime_axis :
    3 ∈ Decomp148a.pRange (min (U7153.yy 256) ((1 + (3 / 4 : ℝ)) * w 256 (3 / 4) 0))
      (w 256 (3 / 4) 0) := by
  apply (mem_prime_axis 256 0 3 (3 / 4)).mpr
  have hy := small_y.1
  norm_num [w, small_z, hy]

/-- A genuine triple belongs to the finite rectangle and the sealed slice, p. 1239. -/
theorem slice_member : ((3, 7), 7) ∈ slice 256 (3 / 4) 0 := by
  exact (mem_slice_rectangle (by norm_num : 0 < (256 : ℕ))
    (by norm_num : (0 : ℝ) < 3 / 4)).mpr ⟨diagonal_pair, prime_axis⟩

/-- The characteristic coefficient is one at a diagonal prime product, p. 1239. -/
theorem diagonal_coefficient : coefficient 256 0 (3 / 4) 49 = 1 := by
  have hm : 49 ∈ productSet 256 0 (3 / 4) :=
    mem_image.mpr ⟨(7, 7), diagonal_pair, by norm_num⟩
  simp [coefficient, hm]

/-- The residue maximum has a nonempty reduced residue domain for the finite witness.
Instance of display 11 p. 1222 as used in display 32 p. 1240. -/
theorem reduced_residue_domain :
    (256 : ℕ) % 3 ∈ (range 3).filter (fun b => Nat.Coprime b 3) ∧
      Nat.Coprime 256 3 := by
  norm_num

end
end LeanLab.BS2022GRH.Instances339
#print axioms LeanLab.BS2022GRH.Instances339.small_z
#print axioms LeanLab.BS2022GRH.Instances339.small_y
#print axioms LeanLab.BS2022GRH.Instances339.diagonal_pair
#print axioms LeanLab.BS2022GRH.Instances339.prime_axis
#print axioms LeanLab.BS2022GRH.Instances339.slice_member
#print axioms LeanLab.BS2022GRH.Instances339.diagonal_coefficient
#print axioms LeanLab.BS2022GRH.Instances339.reduced_residue_domain
