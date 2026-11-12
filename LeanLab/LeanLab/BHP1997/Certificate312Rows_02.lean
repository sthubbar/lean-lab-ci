/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 128 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 129 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 130 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 131 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 132 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 133 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 134 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 135 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_136 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 136 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_137 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 137 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_138 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 138 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_139 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 139 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_140 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 140 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_141 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 141 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_142 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 142 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_143 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 143 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_144 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 144 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_145 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 145 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_146 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 146 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_147 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 147 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_148 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 148 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_149 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 149 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_150 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 150 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_151 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 151 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_152 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 152 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_153 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 153 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_154 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 154 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_155 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 155 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_156 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 156 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_157 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 157 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_158 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 158 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_159 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 159 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_160 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 160 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_161 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 161 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_162 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 162 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_163 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 163 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_164 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 164 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_165 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 165 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_166 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 166 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_167 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 167 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_168 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 168 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_169 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 169 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_170 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 170 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_171 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 171 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_172 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 172 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_173 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 173 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_174 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 174 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_175 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 175 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_176 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 176 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_177 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 177 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_178 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 178 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_179 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 179 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_180 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 180 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_181 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 181 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_182 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 182 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_183 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 183 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_184 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 184 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_185 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 185 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_186 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 186 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_187 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 187 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_188 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 188 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_189 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 189 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_190 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 190 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_191 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 191 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
/-- Page 51. Exact E2 row block 128 through 191. -/
theorem lowerTwo_rows312_02 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (128+i) j) = 0 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_128, lowerTwo_row_129, lowerTwo_row_130, lowerTwo_row_131, lowerTwo_row_132, lowerTwo_row_133, lowerTwo_row_134, lowerTwo_row_135, lowerTwo_row_136, lowerTwo_row_137, lowerTwo_row_138, lowerTwo_row_139, lowerTwo_row_140, lowerTwo_row_141, lowerTwo_row_142, lowerTwo_row_143, lowerTwo_row_144, lowerTwo_row_145, lowerTwo_row_146, lowerTwo_row_147, lowerTwo_row_148, lowerTwo_row_149, lowerTwo_row_150, lowerTwo_row_151, lowerTwo_row_152, lowerTwo_row_153, lowerTwo_row_154, lowerTwo_row_155, lowerTwo_row_156, lowerTwo_row_157, lowerTwo_row_158, lowerTwo_row_159, lowerTwo_row_160, lowerTwo_row_161, lowerTwo_row_162, lowerTwo_row_163, lowerTwo_row_164, lowerTwo_row_165, lowerTwo_row_166, lowerTwo_row_167, lowerTwo_row_168, lowerTwo_row_169, lowerTwo_row_170, lowerTwo_row_171, lowerTwo_row_172, lowerTwo_row_173, lowerTwo_row_174, lowerTwo_row_175, lowerTwo_row_176, lowerTwo_row_177, lowerTwo_row_178, lowerTwo_row_179, lowerTwo_row_180, lowerTwo_row_181, lowerTwo_row_182, lowerTwo_row_183, lowerTwo_row_184, lowerTwo_row_185, lowerTwo_row_186, lowerTwo_row_187, lowerTwo_row_188, lowerTwo_row_189, lowerTwo_row_190, lowerTwo_row_191, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
