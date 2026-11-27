/-
P0068 Zhan 1991, page 263 display (3.3): the LEAF `perron_gt_log_leaf_ps1` of
PerronSingle1122d.lean, split. Burst 20261124, session S9, unit A-extra-7. Davenport, Multiplicative
Number Theory, chapter 17, the lemma, case `y > 1`: the segment is moved to `Re s = -R` across the
pole `s = 0` of residue `1`. The side bounds are PROVED here: each horizontal side at most
`y^c/(T log y)`, the left side at most `2T y^{-R}/R`; the statement of `perron_gt_log_leaf_ps1`
is PROVED from them and one LEAF, the residue theorem on the rectangle, `rect_residue_leaf_A2`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PerronLtLogProof_A2

namespace LeanLab.Zhan1991
open Real

noncomputable section

/-- LEAF: page 263 display (3.3), Davenport, Multiplicative Number Theory, chapter 17, the
lemma, case `y > 1`: the residue theorem for `y^s/s` on the rectangle with corners `-R - iT`
and `c + iT`, `R > 0`, `c > 0`, `T > 0`, which encloses the simple pole `s = 0` of residue `1`;
the boundary integral, taken counterclockwise, is `2πi`. Class MEDIUM. -/
theorem rect_residue_leaf_A2 : ∀ c T y R : ℝ, 0 < c → 0 < T → 0 < y → 0 < R →
    (((∫ x : ℝ in (-R)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        ∫ x : ℝ in (-R)..c, (y : ℂ) ^ ((x : ℂ) + (T : ℂ) * Complex.I) /
          ((x : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • ∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
          ((c : ℂ) + t * Complex.I)) -
      Complex.I • ∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-R : ℝ) : ℂ) + t * Complex.I) /
          (((-R : ℝ) : ℂ) + t * Complex.I) = 2 * π * Complex.I := by
  sorry

/-- Page 263 display (3.3), a horizontal side of the left rectangle, `Im s = u`, `|u| = T`:
`|∫_{-R}^c y^s/s dσ| ≤ y^c/(T log y)` for `y > 1`. -/
theorem horiz_bound_gt_A2 (c T y R u : ℝ) (hT : 0 < T) (hy1 : 1 < y)
    (hcR : -R ≤ c) (hu : |u| = T) :
    ‖∫ x : ℝ in (-R)..c, (y : ℂ) ^ ((x : ℂ) + (u : ℂ) * Complex.I) /
        ((x : ℂ) + (u : ℂ) * Complex.I)‖ ≤ y ^ c / (T * |Real.log y|) := by
  have hy : 0 < y := by linarith
  set L := Real.log y with hL
  have hL0 : 0 < L := Real.log_pos hy1
  have habs : |L| = L := abs_of_pos hL0
  have hpt : ∀ x : ℝ, ‖(y : ℂ) ^ ((x : ℂ) + (u : ℂ) * Complex.I) /
      ((x : ℂ) + (u : ℂ) * Complex.I)‖ ≤ Real.exp (L * x) / T := by
    intro x
    rw [norm_ypow_div_A2 y hy]
    have hre : ((x : ℂ) + (u : ℂ) * Complex.I).re = x := by simp
    have him : T ≤ ‖(x : ℂ) + (u : ℂ) * Complex.I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + (u : ℂ) * Complex.I)
      simp at this; linarith
    rw [hre, Real.rpow_def_of_pos hy]
    exact div_le_div_of_nonneg_left (by positivity) hT him
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (L * x) / T) MeasureTheory.volume (-R) c :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (L * x) / T)).intervalIntegrable _ _
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le hcR
    (Filter.Eventually.of_forall (fun x _ => hpt x)) hint) ?_
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (L * x) / (L * T))
      (Real.exp (L * x) / T) x := by
    intro x
    have := ((hasDerivAt_id x).const_mul L).exp.div_const (L * T)
    simp only [id] at this
    convert this using 1
    field_simp [hL0.ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint]
  rw [Real.rpow_def_of_pos hy, habs, mul_comm (Real.log y) c, ← hL]
  have hR : 0 < Real.exp (L * -R) := Real.exp_pos _
  rw [mul_comm L T]
  have : 0 < Real.exp (L * -R) / (T * L) := by positivity
  linarith

/-- Page 263 display (3.3), the left side `Re s = -R` of the rectangle: at most
`2T y^{-R}/R`. -/
theorem left_bound_A2 (T y R : ℝ) (hT : 0 < T) (hy : 0 < y) (hR : 0 < R) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-R : ℝ) : ℂ) + t * Complex.I) /
        (((-R : ℝ) : ℂ) + t * Complex.I)‖ ≤ y ^ (-R) / R * (2 * T) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := y ^ (-R) / R)
    (f := fun t : ℝ => (y : ℂ) ^ (((-R : ℝ) : ℂ) + t * Complex.I) /
      (((-R : ℝ) : ℂ) + t * Complex.I)) ?_
  · rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith)] at h
    exact h
  · intro t _
    rw [norm_ypow_div_A2 y hy]
    have hre : (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = -R := by simp
    have hn : R ≤ ‖((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := by
      have := Complex.abs_re_le_norm (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      rw [hre, abs_neg, abs_of_pos hR] at this; exact this
    rw [hre]
    exact div_le_div_of_nonneg_left (by positivity) hR hn

/-- The statement of the LEAF `perron_gt_log_leaf_ps1`, page 263 display (3.3), from the
residue LEAF `rect_residue_leaf_A2` and the PROVED side bounds. -/
theorem perron_gt_log_of_leaf_A2 : ∀ c T y : ℝ, 0 < c → 0 < T → 1 < y →
    ‖(1 : ℂ) - (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)‖ ≤
      y ^ c * (1 / (T * |Real.log y|)) := by
  intro c T y hc hT hy1
  have hy : 0 < y := by linarith
  set B := y ^ c / (T * |Real.log y|) with hB
  have hL : 0 < |Real.log y| := abs_pos.mpr (Real.log_pos hy1).ne'
  have hBpos : 0 < B := by positivity
  have hpi := Real.pi_gt_three
  set V := ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)
  have hyi0 : 0 < y⁻¹ := inv_pos.mpr hy
  have hyi1 : y⁻¹ < 1 := inv_lt_one_of_one_lt₀ hy1
  have hev := (tendsto_rpow_atTop_of_base_lt_one y⁻¹ (by linarith) hyi1).eventually
    (gt_mem_nhds (show (0 : ℝ) < (1 - 1 / π) * B * π / T by
      have : 0 < 1 - 1 / π := by rw [sub_pos, div_lt_one (by linarith)]; linarith
      positivity))
  obtain ⟨R, hR1, hR2⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  have hRpos : 0 < R := by linarith
  have hyR : y ^ (-R) = y⁻¹ ^ R := by rw [Real.rpow_neg hy.le, Real.inv_rpow hy.le]
  have hres := rect_residue_leaf_A2 c T y R hc hT hy hRpos
  set H1 := ∫ x : ℝ in (-R)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  set H2 := ∫ x : ℝ in (-R)..c, (y : ℂ) ^ ((x : ℂ) + (T : ℂ) * Complex.I) /
          ((x : ℂ) + (T : ℂ) * Complex.I)
  set VL := ∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-R : ℝ) : ℂ) + t * Complex.I) /
          (((-R : ℝ) : ℂ) + t * Complex.I)
  have hid : Complex.I • ((2 * π : ℂ) - V) = (H1 - H2) - Complex.I • VL := by
    have hres' : H1 - H2 + Complex.I * V - Complex.I * VL = 2 * π * Complex.I := hres
    simp only [smul_eq_mul]
    linear_combination -hres'
  have hVn : ‖(2 * π : ℂ) - V‖ ≤ B + B + y ^ (-R) / R * (2 * T) := by
    have h1 : ‖(2 * π : ℂ) - V‖ = ‖Complex.I • ((2 * π : ℂ) - V)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [h1, hid]
    refine le_trans (norm_sub_le _ _) ?_
    have hA : ‖Complex.I • VL‖ ≤ y ^ (-R) / R * (2 * T) := by
      rw [norm_smul, Complex.norm_I, one_mul]; exact left_bound_A2 T y R hT hy hRpos
    have hB1 := horiz_bound_gt_A2 c T y R (-T) hT hy1 (by linarith) (by rw [abs_neg, abs_of_pos hT])
    have hB2 := horiz_bound_gt_A2 c T y R T hT hy1 (by linarith) (abs_of_pos hT)
    have := norm_sub_le H1 H2
    linarith
  have hyRb : y ^ (-R) / R * (2 * T) ≤ 2 * (1 - 1 / π) * B * π := by
    rw [hyR]
    have h1 : y⁻¹ ^ R / R ≤ y⁻¹ ^ R := div_le_self (by positivity) hR2
    have h2 : y⁻¹ ^ R * T < (1 - 1 / π) * B * π := by rwa [lt_div_iff₀ hT] at hR1
    have h3 : y⁻¹ ^ R / R * T ≤ y⁻¹ ^ R * T := by gcongr
    nlinarith
  have e : (1 : ℂ) - (1 / (2 * π) : ℂ) * V = ((1 / (2 * π) : ℝ) : ℂ) * ((2 * π : ℂ) - V) := by
    push_cast; field_simp
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : y ^ c * (1 / (T * |Real.log y|)) = B := by rw [hB]; ring
  rw [this]
  calc 1 / (2 * π) * ‖(2 * π : ℂ) - V‖ ≤ 1 / (2 * π) * (B + B + 2 * (1 - 1 / π) * B * π) := by
        gcongr; linarith
    _ = B := by field_simp; ring

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.horiz_bound_gt_A2
#print axioms LeanLab.Zhan1991.left_bound_A2
#print axioms LeanLab.Zhan1991.perron_gt_log_of_leaf_A2
