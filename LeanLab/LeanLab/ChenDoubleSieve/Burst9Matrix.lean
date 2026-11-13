import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Burst 9: the 81 entries of Wu's Section 7 matrix, one statement each

Source: Wu 2004, arXiv 0705.1652, displays 7.1 and 7.2, page 30: for the grid
`s₀ = 1, s_j = 2 + (j+1)/10`, the entries are `a_{i,j} = ∫_{s_{j−1}}^{s_j} Ξ(t; sᵢ) dt`, with
`Ξ₂` of display 3.22 for rows 1 to 4 and `Ξ₁` of display 3.21 for rows 5 to 9; Wu computed
them with Maple and printed the matrix `A` on page 31. `Wu04Table.IntegralMatrixBound` asks that
each rational candidate, the Maple value truncated to seven decimals, be a lower bound for the
true entry. `integral_matrix_bound_p3` proves that statement from the 81 single quadrature
statements below. Each is LEAF: every kernel contains the term `σ₀(t)`, itself an integral, and
the scipy recomputation leaves margins between 0 and 1.0e−7, see the note; no entry was
certified in Lean in this burst.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Burst9Matrix
open Wu04Table

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,1} = ∫_{1}^{2.2} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 1551926/10⁷`.
scipy value 0.1551926574, margin 0.57e−7. -/
theorem entry_0_0 : (candidateMatrixQ 0 0 : ℝ) ≤ integralMatrix 0 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 261910/10⁷`.
scipy value 0.0261910681, margin 0.68e−7. -/
theorem entry_0_1 : (candidateMatrixQ 0 1 : ℝ) ≤ integralMatrix 0 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 266515/10⁷`.
scipy value 0.0266515083, margin 0.08e−7. -/
theorem entry_0_2 : (candidateMatrixQ 0 2 : ℝ) ≤ integralMatrix 0 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 269346/10⁷`.
scipy value 0.0269346906, margin 0.91e−7. -/
theorem entry_0_3 : (candidateMatrixQ 0 3 : ℝ) ≤ integralMatrix 0 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 271084/10⁷`.
scipy value 0.0271084782, margin 0.78e−7. -/
theorem entry_0_4 : (candidateMatrixQ 0 4 : ℝ) ≤ integralMatrix 0 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 274861/10⁷`.
scipy value 0.0274861583, margin 0.58e−7. -/
theorem entry_0_5 : (candidateMatrixQ 0 5 : ℝ) ≤ integralMatrix 0 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 278478/10⁷`.
scipy value 0.0278478963, margin 0.96e−7. -/
theorem entry_0_6 : (candidateMatrixQ 0 6 : ℝ) ≤ integralMatrix 0 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 281663/10⁷`.
scipy value 0.0281663353, margin 0.35e−7. -/
theorem entry_0_7 : (candidateMatrixQ 0 7 : ℝ) ≤ integralMatrix 0 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,9} = ∫_{2.9}^{3} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 284464/10⁷`.
scipy value 0.0284464442, margin 0.44e−7. -/
theorem entry_0_8 : (candidateMatrixQ 0 8 : ℝ) ≤ integralMatrix 0 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,1} = ∫_{1}^{2.2} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 1537386/10⁷`.
scipy value 0.1537386795, margin 0.80e−7. -/
theorem entry_1_0 : (candidateMatrixQ 1 0 : ℝ) ≤ integralMatrix 1 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 255908/10⁷`.
scipy value 0.0255908608, margin 0.61e−7. -/
theorem entry_1_1 : (candidateMatrixQ 1 1 : ℝ) ≤ integralMatrix 1 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 260352/10⁷`.
scipy value 0.0260352023, margin 0.02e−7. -/
theorem entry_1_2 : (candidateMatrixQ 1 2 : ℝ) ≤ integralMatrix 1 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 262914/10⁷`.
scipy value 0.0262914366, margin 0.37e−7. -/
theorem entry_1_3 : (candidateMatrixQ 1 3 : ℝ) ≤ integralMatrix 1 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 265826/10⁷`.
scipy value 0.0265826524, margin 0.52e−7. -/
theorem entry_1_4 : (candidateMatrixQ 1 4 : ℝ) ≤ integralMatrix 1 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 270061/10⁷`.
scipy value 0.0270061132, margin 0.13e−7. -/
theorem entry_1_5 : (candidateMatrixQ 1 5 : ℝ) ≤ integralMatrix 1 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 273794/10⁷`.
scipy value 0.0273794440, margin 0.44e−7. -/
theorem entry_1_6 : (candidateMatrixQ 1 6 : ℝ) ≤ integralMatrix 1 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 277085/10⁷`.
scipy value 0.0277085524, margin 0.52e−7. -/
theorem entry_1_7 : (candidateMatrixQ 1 7 : ℝ) ≤ integralMatrix 1 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,9} = ∫_{2.9}^{3} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 279985/10⁷`.
scipy value 0.0279985116, margin 0.12e−7. -/
theorem entry_1_8 : (candidateMatrixQ 1 8 : ℝ) ≤ integralMatrix 1 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,1} = ∫_{1}^{2.2} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 1525199/10⁷`.
scipy value 0.1525199200, margin 0.20e−7. -/
theorem entry_2_0 : (candidateMatrixQ 2 0 : ℝ) ≤ integralMatrix 2 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 250515/10⁷`.
scipy value 0.0250515037, margin 0.04e−7. -/
theorem entry_2_1 : (candidateMatrixQ 2 1 : ℝ) ≤ integralMatrix 2 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 254743/10⁷`.
scipy value 0.0254743353, margin 0.35e−7. -/
theorem entry_2_2 : (candidateMatrixQ 2 2 : ℝ) ≤ integralMatrix 2 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 257327/10⁷`.
scipy value 0.0257327789, margin 0.79e−7. -/
theorem entry_2_3 : (candidateMatrixQ 2 3 : ℝ) ≤ integralMatrix 2 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 261548/10⁷`.
scipy value 0.0261548552, margin 0.55e−7. -/
theorem entry_2_4 : (candidateMatrixQ 2 4 : ℝ) ≤ integralMatrix 2 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 265892/10⁷`.
scipy value 0.0265892899, margin 0.90e−7. -/
theorem entry_2_5 : (candidateMatrixQ 2 5 : ℝ) ≤ integralMatrix 2 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 269726/10⁷`.
scipy value 0.0269726868, margin 0.87e−7. -/
theorem entry_2_6 : (candidateMatrixQ 2 6 : ℝ) ≤ integralMatrix 2 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 273110/10⁷`.
scipy value 0.0273110594, margin 0.59e−7. -/
theorem entry_2_7 : (candidateMatrixQ 2 7 : ℝ) ≤ integralMatrix 2 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,9} = ∫_{2.9}^{3} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 276095/10⁷`.
scipy value 0.0276095716, margin 0.72e−7. -/
theorem entry_2_8 : (candidateMatrixQ 2 8 : ℝ) ≤ integralMatrix 2 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,1} = ∫_{1}^{2.2} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 1549103/10⁷`.
scipy value 0.1549103474, margin 0.47e−7. -/
theorem entry_3_0 : (candidateMatrixQ 3 0 : ℝ) ≤ integralMatrix 3 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 239617/10⁷`.
scipy value 0.0239617849, margin 0.85e−7. -/
theorem entry_3_1 : (candidateMatrixQ 3 1 : ℝ) ≤ integralMatrix 3 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 246126/10⁷`.
scipy value 0.0246126132, margin 0.13e−7. -/
theorem entry_3_2 : (candidateMatrixQ 3 2 : ℝ) ≤ integralMatrix 3 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 251857/10⁷`.
scipy value 0.0251857826, margin 0.83e−7. -/
theorem entry_3_3 : (candidateMatrixQ 3 3 : ℝ) ≤ integralMatrix 3 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 256913/10⁷`.
scipy value 0.0256913054, margin 0.05e−7. -/
theorem entry_3_4 : (candidateMatrixQ 3 4 : ℝ) ≤ integralMatrix 3 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 261376/10⁷`.
scipy value 0.0261376312, margin 0.31e−7. -/
theorem entry_3_5 : (candidateMatrixQ 3 5 : ℝ) ≤ integralMatrix 3 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 265319/10⁷`.
scipy value 0.0265319355, margin 0.35e−7. -/
theorem entry_3_6 : (candidateMatrixQ 3 6 : ℝ) ≤ integralMatrix 3 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 268803/10⁷`.
scipy value 0.0268803466, margin 0.47e−7. -/
theorem entry_3_7 : (candidateMatrixQ 3 7 : ℝ) ≤ integralMatrix 3 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,9} = ∫_{2.9}^{3} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 271881/10⁷`.
scipy value 0.0271881266, margin 0.27e−7. -/
theorem entry_3_8 : (candidateMatrixQ 3 8 : ℝ) ≤ integralMatrix 3 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,1} = ∫_{1}^{2.2} Ξ₁(t; 2.6, 3.58) dt ≥ 1594156/10⁷`.
scipy value 0.1594156990, margin 0.99e−7. -/
theorem entry_4_0 : (candidateMatrixQ 4 0 : ℝ) ≤ integralMatrix 4 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.6, 3.58) dt ≥ 238776/10⁷`.
scipy value 0.0238776167, margin 0.17e−7. -/
theorem entry_4_1 : (candidateMatrixQ 4 1 : ℝ) ≤ integralMatrix 4 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.6, 3.58) dt ≥ 245310/10⁷`.
scipy value 0.0245310629, margin 0.63e−7. -/
theorem entry_4_2 : (candidateMatrixQ 4 2 : ℝ) ≤ integralMatrix 4 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.6, 3.58) dt ≥ 251066/10⁷`.
scipy value 0.0251066062, margin 0.06e−7. -/
theorem entry_4_3 : (candidateMatrixQ 4 3 : ℝ) ≤ integralMatrix 4 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.6, 3.58) dt ≥ 256142/10⁷`.
scipy value 0.0256142905, margin 0.91e−7. -/
theorem entry_4_4 : (candidateMatrixQ 4 4 : ℝ) ≤ integralMatrix 4 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.6, 3.58) dt ≥ 260625/10⁷`.
scipy value 0.0260625919, margin 0.92e−7. -/
theorem entry_4_5 : (candidateMatrixQ 4 5 : ℝ) ≤ integralMatrix 4 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.6, 3.58) dt ≥ 264587/10⁷`.
scipy value 0.0264587083, margin 0.08e−7. -/
theorem entry_4_6 : (candidateMatrixQ 4 6 : ℝ) ≤ integralMatrix 4 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.6, 3.58) dt ≥ 268087/10⁷`.
scipy value 0.0268087872, margin 0.87e−7. -/
theorem entry_4_7 : (candidateMatrixQ 4 7 : ℝ) ≤ integralMatrix 4 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,9} = ∫_{2.9}^{3} Ξ₁(t; 2.6, 3.58) dt ≥ 271181/10⁷`.
scipy value 0.0271181070, margin 0.07e−7. -/
theorem entry_4_8 : (candidateMatrixQ 4 8 : ℝ) ≤ integralMatrix 4 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,1} = ∫_{1}^{2.2} Ξ₁(t; 2.7, 3.47) dt ≥ 1602317/10⁷`.
scipy value 0.1602317488, margin 0.49e−7. -/
theorem entry_5_0 : (candidateMatrixQ 5 0 : ℝ) ≤ integralMatrix 5 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.7, 3.47) dt ≥ 234607/10⁷`.
scipy value 0.0234607924, margin 0.92e−7. -/
theorem entry_5_1 : (candidateMatrixQ 5 1 : ℝ) ≤ integralMatrix 5 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.7, 3.47) dt ≥ 241272/10⁷`.
scipy value 0.0241272031, margin 0.03e−7. -/
theorem entry_5_2 : (candidateMatrixQ 5 2 : ℝ) ≤ integralMatrix 5 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.7, 3.47) dt ≥ 247145/10⁷`.
scipy value 0.0247145026, margin 0.03e−7. -/
theorem entry_5_3 : (candidateMatrixQ 5 3 : ℝ) ≤ integralMatrix 5 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.7, 3.47) dt ≥ 252328/10⁷`.
scipy value 0.0252328911, margin 0.91e−7. -/
theorem entry_5_4 : (candidateMatrixQ 5 4 : ℝ) ≤ integralMatrix 5 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.7, 3.47) dt ≥ 256909/10⁷`.
scipy value 0.0256909762, margin 0.76e−7. -/
theorem entry_5_5 : (candidateMatrixQ 5 5 : ℝ) ≤ integralMatrix 5 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.7, 3.47) dt ≥ 260960/10⁷`.
scipy value 0.0260960669, margin 0.67e−7. -/
theorem entry_5_6 : (candidateMatrixQ 5 6 : ℝ) ≤ integralMatrix 5 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.7, 3.47) dt ≥ 264544/10⁷`.
scipy value 0.0264544053, margin 0.05e−7. -/
theorem entry_5_7 : (candidateMatrixQ 5 7 : ℝ) ≤ integralMatrix 5 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,9} = ∫_{2.9}^{3} Ξ₁(t; 2.7, 3.47) dt ≥ 267713/10⁷`.
scipy value 0.0267713505, margin 0.50e−7. -/
theorem entry_5_8 : (candidateMatrixQ 5 8 : ℝ) ≤ integralMatrix 5 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,1} = ∫_{1}^{2.2} Ξ₁(t; 2.8, 3.34) dt ≥ 1649911/10⁷`.
scipy value 0.1649911916, margin 0.92e−7. -/
theorem entry_6_0 : (candidateMatrixQ 6 0 : ℝ) ≤ integralMatrix 6 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.8, 3.34) dt ≥ 233852/10⁷`.
scipy value 0.0233852365, margin 0.36e−7. -/
theorem entry_6_1 : (candidateMatrixQ 6 1 : ℝ) ≤ integralMatrix 6 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.8, 3.34) dt ≥ 240539/10⁷`.
scipy value 0.0240539971, margin 0.97e−7. -/
theorem entry_6_2 : (candidateMatrixQ 6 2 : ℝ) ≤ integralMatrix 6 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.8, 3.34) dt ≥ 246434/10⁷`.
scipy value 0.0246434276, margin 0.28e−7. -/
theorem entry_6_3 : (candidateMatrixQ 6 3 : ℝ) ≤ integralMatrix 6 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.8, 3.34) dt ≥ 251637/10⁷`.
scipy value 0.0251637564, margin 0.56e−7. -/
theorem entry_6_4 : (candidateMatrixQ 6 4 : ℝ) ≤ integralMatrix 6 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.8, 3.34) dt ≥ 256236/10⁷`.
scipy value 0.0256236150, margin 0.15e−7. -/
theorem entry_6_5 : (candidateMatrixQ 6 5 : ℝ) ≤ integralMatrix 6 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.8, 3.34) dt ≥ 260303/10⁷`.
scipy value 0.0260303325, margin 0.32e−7. -/
theorem entry_6_6 : (candidateMatrixQ 6 6 : ℝ) ≤ integralMatrix 6 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.8, 3.34) dt ≥ 263901/10⁷`.
scipy value 0.0263901680, margin 0.68e−7. -/
theorem entry_6_7 : (candidateMatrixQ 6 7 : ℝ) ≤ integralMatrix 6 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,9} = ∫_{2.9}^{3} Ξ₁(t; 2.8, 3.34) dt ≥ 267084/10⁷`.
scipy value 0.0267084954, margin 0.95e−7. -/
theorem entry_6_8 : (candidateMatrixQ 6 8 : ℝ) ≤ integralMatrix 6 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,1} = ∫_{1}^{2.2} Ξ₁(t; 2.9, 3.19) dt ≥ 1737478/10⁷`.
scipy value 0.1737478561, margin 0.56e−7. -/
theorem entry_7_0 : (candidateMatrixQ 7 0 : ℝ) ≤ integralMatrix 7 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.9, 3.19) dt ≥ 236829/10⁷`.
scipy value 0.0236829970, margin 0.97e−7. -/
theorem entry_7_1 : (candidateMatrixQ 7 1 : ℝ) ≤ integralMatrix 7 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.9, 3.19) dt ≥ 243424/10⁷`.
scipy value 0.0243424965, margin 0.96e−7. -/
theorem entry_7_2 : (candidateMatrixQ 7 2 : ℝ) ≤ integralMatrix 7 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.9, 3.19) dt ≥ 249235/10⁷`.
scipy value 0.0249235289, margin 0.29e−7. -/
theorem entry_7_3 : (candidateMatrixQ 7 3 : ℝ) ≤ integralMatrix 7 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.9, 3.19) dt ≥ 254362/10⁷`.
scipy value 0.0254362110, margin 0.11e−7. -/
theorem entry_7_4 : (candidateMatrixQ 7 4 : ℝ) ≤ integralMatrix 7 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.9, 3.19) dt ≥ 258890/10⁷`.
scipy value 0.0258890806, margin 0.81e−7. -/
theorem entry_7_5 : (candidateMatrixQ 7 5 : ℝ) ≤ integralMatrix 7 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.9, 3.19) dt ≥ 262893/10⁷`.
scipy value 0.0262893872, margin 0.87e−7. -/
theorem entry_7_6 : (candidateMatrixQ 7 6 : ℝ) ≤ integralMatrix 7 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.9, 3.19) dt ≥ 266433/10⁷`.
scipy value 0.0266433225, margin 0.23e−7. -/
theorem entry_7_7 : (candidateMatrixQ 7 7 : ℝ) ≤ integralMatrix 7 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,9} = ∫_{2.9}^{3} Ξ₁(t; 2.9, 3.19) dt ≥ 269562/10⁷`.
scipy value 0.0269562027, margin 0.03e−7. -/
theorem entry_7_8 : (candidateMatrixQ 7 8 : ℝ) ≤ integralMatrix 7 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,1} = ∫_{1}^{2.2} Ξ₁(t; 3.0, 3.00) dt ≥ 1910519/10⁷`.
scipy value 0.1910519781, margin 0.78e−7. -/
theorem entry_8_0 : (candidateMatrixQ 8 0 : ℝ) ≤ integralMatrix 8 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,2} = ∫_{2.2}^{2.3} Ξ₁(t; 3.0, 3.00) dt ≥ 246475/10⁷`.
scipy value 0.0246475178, margin 0.18e−7. -/
theorem entry_8_1 : (candidateMatrixQ 8 1 : ℝ) ≤ integralMatrix 8 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,3} = ∫_{2.3}^{2.4} Ξ₁(t; 3.0, 3.00) dt ≥ 252770/10⁷`.
scipy value 0.0252770177, margin 0.18e−7. -/
theorem entry_8_2 : (candidateMatrixQ 8 2 : ℝ) ≤ integralMatrix 8 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,4} = ∫_{2.4}^{2.5} Ξ₁(t; 3.0, 3.00) dt ≥ 258308/10⁷`.
scipy value 0.0258308467, margin 0.47e−7. -/
theorem entry_8_3 : (candidateMatrixQ 8 3 : ℝ) ≤ integralMatrix 8 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,5} = ∫_{2.5}^{2.6} Ξ₁(t; 3.0, 3.00) dt ≥ 263187/10⁷`.
scipy value 0.0263187595, margin 0.60e−7. -/
theorem entry_8_4 : (candidateMatrixQ 8 4 : ℝ) ≤ integralMatrix 8 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,6} = ∫_{2.6}^{2.7} Ξ₁(t; 3.0, 3.00) dt ≥ 267489/10⁷`.
scipy value 0.0267489897, margin 0.90e−7. -/
theorem entry_8_5 : (candidateMatrixQ 8 5 : ℝ) ≤ integralMatrix 8 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,7} = ∫_{2.7}^{2.8} Ξ₁(t; 3.0, 3.00) dt ≥ 271285/10⁷`.
scipy value 0.0271285300, margin 0.30e−7. -/
theorem entry_8_6 : (candidateMatrixQ 8 6 : ℝ) ≤ integralMatrix 8 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,8} = ∫_{2.8}^{2.9} Ξ₁(t; 3.0, 3.00) dt ≥ 274633/10⁷`.
scipy value 0.0274633532, margin 0.53e−7. -/
theorem entry_8_7 : (candidateMatrixQ 8 7 : ℝ) ≤ integralMatrix 8 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,9} = ∫_{2.9}^{3} Ξ₁(t; 3.0, 3.00) dt ≥ 277585/10⁷`.
scipy value 0.0277585884, margin 0.88e−7. -/
theorem entry_8_8 : (candidateMatrixQ 8 8 : ℝ) ≤ integralMatrix 8 8 := by
  sorry

/-- **Displays 7.1 and 7.2 of Wu 2004, page 30**: the statement of the leaf
`Burst4Split.integral_matrix_bound`, proved from the 81 single entry statements.
CONDITIONAL ON the 81 LEAF entries. -/
theorem integral_matrix_bound_p3 : IntegralMatrixBound := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact entry_0_0
  · exact entry_0_1
  · exact entry_0_2
  · exact entry_0_3
  · exact entry_0_4
  · exact entry_0_5
  · exact entry_0_6
  · exact entry_0_7
  · exact entry_0_8
  · exact entry_1_0
  · exact entry_1_1
  · exact entry_1_2
  · exact entry_1_3
  · exact entry_1_4
  · exact entry_1_5
  · exact entry_1_6
  · exact entry_1_7
  · exact entry_1_8
  · exact entry_2_0
  · exact entry_2_1
  · exact entry_2_2
  · exact entry_2_3
  · exact entry_2_4
  · exact entry_2_5
  · exact entry_2_6
  · exact entry_2_7
  · exact entry_2_8
  · exact entry_3_0
  · exact entry_3_1
  · exact entry_3_2
  · exact entry_3_3
  · exact entry_3_4
  · exact entry_3_5
  · exact entry_3_6
  · exact entry_3_7
  · exact entry_3_8
  · exact entry_4_0
  · exact entry_4_1
  · exact entry_4_2
  · exact entry_4_3
  · exact entry_4_4
  · exact entry_4_5
  · exact entry_4_6
  · exact entry_4_7
  · exact entry_4_8
  · exact entry_5_0
  · exact entry_5_1
  · exact entry_5_2
  · exact entry_5_3
  · exact entry_5_4
  · exact entry_5_5
  · exact entry_5_6
  · exact entry_5_7
  · exact entry_5_8
  · exact entry_6_0
  · exact entry_6_1
  · exact entry_6_2
  · exact entry_6_3
  · exact entry_6_4
  · exact entry_6_5
  · exact entry_6_6
  · exact entry_6_7
  · exact entry_6_8
  · exact entry_7_0
  · exact entry_7_1
  · exact entry_7_2
  · exact entry_7_3
  · exact entry_7_4
  · exact entry_7_5
  · exact entry_7_6
  · exact entry_7_7
  · exact entry_7_8
  · exact entry_8_0
  · exact entry_8_1
  · exact entry_8_2
  · exact entry_8_3
  · exact entry_8_4
  · exact entry_8_5
  · exact entry_8_6
  · exact entry_8_7
  · exact entry_8_8

end LeanLab.ChenDoubleSieve.Burst9Matrix

