/-
The total variation form of Helfgott Lemma A.6.
Source: https://arxiv.org/abs/1205.5252v4, page 77, equation A.18.
The identification with the norm of a distributional second derivative is plain math.
AI wrote this Lean code for CODEX task62. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Eta2TV

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real Filter Topology

/-- The actual derivative of log times eta2 has total variation 96 log 2. -/
theorem eVariation_deriv_log_eta2 :
    eVariationOn (deriv (eta2rho 1)) univ = ENNReal.ofReal (96 * Real.log 2) := by
  let D := deriv (eta2rho 1)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : eta2 (1 / 4) = 0 := by
    rw [eta2_of_mem_left le_rfl (by norm_num)]
    norm_num
  have dout : ∀ t : ℝ, t < 1 / 4 ∨ 1 < t → D t = 0 := by
    intro t ht
    exact (eta2rho_hasDerivAt_out ht).deriv
  have dz : D 0 = 0 := dout 0 (Or.inl (by norm_num))
  have d2 : D 2 = 0 := dout 2 (Or.inr (by norm_num))
  have dq : D (1 / 4) = 0 := by
    have hd : HasDerivWithinAt (eta2rho 1) 0 (Icc 0 (1 / 4)) (1 / 4) := by
      refine (hasDerivWithinAt_const (1 / 4 : ℝ) (Icc 0 (1 / 4)) (0 : ℝ)).congr ?_ ?_
      · intro s hs
        change Real.log (1 * s) * eta2 s = 0
        rcases hs.2.lt_or_eq with h | h
        · rw [eta2_of_lt h, mul_zero]
        · rw [h, hq, mul_zero]
      · change Real.log (1 * (1 / 4)) * eta2 (1 / 4) = 0
        rw [hq, mul_zero]
    rcases deriv_eq_zero_or_of_hasDerivWithinAt (by norm_num) hd with h | h <;> exact h
  have dh : D (1 / 2) = 0 := by
    have hd : HasDerivWithinAt (eta2rho 1) (gL 1 (1 / 2))
        (Icc (1 / 4) (1 / 2)) (1 / 2) := by
      refine (FL_hasDerivAt (by norm_num) (by norm_num)).hasDerivWithinAt.congr ?_ ?_
      · intro s hs
        simp only [eta2rho]
        rw [eta2_of_mem_left hs.1 hs.2]
      · simp only [eta2rho]
        rw [eta2_of_mem_left (by norm_num) le_rfl]
    rcases deriv_eq_zero_or_of_hasDerivWithinAt (by norm_num) hd with h | h
    · exact h
    · rw [gL_half, Real.log_one, mul_zero] at h
      exact h
  have d1 : D 1 = 0 := by
    have hd : HasDerivWithinAt (eta2rho 1) (gR 1 1) (Icc (1 / 2) 1) 1 := by
      refine (FR_hasDerivAt (by norm_num) (by norm_num)).hasDerivWithinAt.congr ?_ ?_
      · intro s hs
        simp only [eta2rho]
        rw [eta2_of_mem_right hs.1 hs.2]
      · simp only [eta2rho]
        rw [eta2_of_mem_right (by norm_num) le_rfl]
    rcases deriv_eq_zero_or_of_hasDerivWithinAt (by norm_num) hd with h | h
    · exact h
    · simpa [gR_one] using h
  have Lq : gL 1 (1 / 4) = -32 * Real.log 2 := by
    rw [gL_quarter, Real.log_div (by norm_num) (by norm_num), Real.log_one, log_four_eq]
    ring
  have Lh : gL 1 (1 / 2) = 0 := by rw [gL_half, Real.log_one]; ring
  have Rh : gR 1 (1 / 2) = 16 * Real.log 2 := by
    rw [gR_half, Real.log_div (by norm_num) (by norm_num), Real.log_one, log_four_eq]
    ring
  have R1 : gR 1 1 = 0 := by rw [gR_one, Real.log_one]; ring
  have he : (1 : ℝ) ≤ Real.exp 2 := by linarith [four_le_exp_two]
  have P0 : eVariationOn D (Icc 0 (1 / 4)) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ : ℝ => (0 : ℝ))]
    · exact eVar_const_zero _
    · intro t ht
      rcases ht.2.lt_or_eq with h | h
      · exact dout t (Or.inl h)
      · rw [h]; exact dq
  have P3 : eVariationOn D (Icc 1 2) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ : ℝ => (0 : ℝ))]
    · exact eVar_const_zero _
    · intro t ht
      rcases ht.1.lt_or_eq with h | h
      · exact dout t (Or.inr h)
      · rw [← h]; exact d1
  have P1 : eVariationOn D (Icc (1 / 4) (1 / 2)) = ENNReal.ofReal (64 * Real.log 2) := by
    rw [eVar_Icc_of_eqOn_Ioo (F := D) (φ := gL 1) (by norm_num) (gL_continuousOn (by norm_num))
      (fun t ht => (eta2rho_hasDerivAt_left (by norm_num) ht.1 ht.2).deriv),
      dq, dh, VL_lo (by norm_num) he, Lq, Lh]
    simp only [edist_dist, Real.dist_eq, zero_sub, sub_zero, abs_neg, abs_mul,
      abs_of_pos hl]
    norm_num
    ring
  have P2 : eVariationOn D (Icc (1 / 2) 1) = ENNReal.ofReal (32 * Real.log 2) := by
    rw [eVar_Icc_of_eqOn_Ioo (F := D) (φ := gR 1) (by norm_num) (gR_continuousOn (by norm_num))
      (fun t ht => (eta2rho_hasDerivAt_right (by norm_num) ht.1 ht.2).deriv),
      dh, d1, VR_lo (by norm_num) he, Rh, R1]
    simp only [edist_dist, Real.dist_eq, zero_sub, sub_zero, abs_neg, abs_mul,
      abs_of_pos hl]
    norm_num
    ring
  have s1 := eVariationOn.Icc_add_Icc D (a := 0) (b := 1 / 4) (c := 2)
    (by norm_num) (by norm_num) (mem_univ _)
  have s2 := eVariationOn.Icc_add_Icc D (a := 1 / 4) (b := 1 / 2) (c := 2)
    (by norm_num) (by norm_num) (mem_univ _)
  have s3 := eVariationOn.Icc_add_Icc D (a := 1 / 2) (b := 1) (c := 2)
    (by norm_num) (by norm_num) (mem_univ _)
  simp only [univ_inter] at s1 s2 s3
  have vI : eVariationOn D (Icc 0 2) = ENNReal.ofReal (96 * Real.log 2) := by
    rw [← s1, ← s2, ← s3, P0, P1, P2, P3, zero_add, add_zero,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have u1 := eVariationOn.union D (isGreatest_Iic (a := (0 : ℝ))) (isLeast_Ici (a := 0))
  have u2 := eVariationOn.union D (isGreatest_Icc (by norm_num : (0 : ℝ) ≤ 2))
    (isLeast_Ici (a := 2))
  rw [Iic_union_Ici] at u1
  rw [Icc_union_Ici_eq_Ici (by norm_num)] at u2
  have z1 : eVariationOn D (Iic 0) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ : ℝ => (0 : ℝ)) (s := Iic 0)
      (fun t (ht : t ≤ 0) => dout t (Or.inl (by linarith))), eVar_const_zero]
  have z2 : eVariationOn D (Ici 2) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ : ℝ => (0 : ℝ)) (s := Ici 2)
      (fun t (ht : 2 ≤ t) => dout t (Or.inr (by linarith))), eVar_const_zero]
  change eVariationOn D univ = _
  rw [u1, z1, zero_add, u2, z2, add_zero, vI]

end LeanLab.HelfgottArcs
