/-
P0068 Zhan 1991, page 263 display (3.3): the LEAF `perron_lt_log_leaf_ps1` of
PerronSingle1122d.lean, PROVED as `perron_lt_log_proof_A2`. Burst 20261124, session S9, unit
A-extra-6. Davenport, Multiplicative Number Theory, chapter 17, the lemma, case `0 < y < 1`:
`y^s/s` is holomorphic on `Re s ≥ c`, so its integral round the rectangle `c - iT, R - iT,
R + iT, c + iT` is `0`, Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`;
each horizontal side is at most `∫_c^∞ y^σ/T dσ = y^c/(T |log y|)`, the right side at most
`2T y^R/R`, which is small for large `R`; so the integral is at most `y^c/(π T |log y|)`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PerronSingle1122d

namespace LeanLab.Zhan1991
open Real

noncomputable section

/-- `|y^s/s| = y^{Re s}/|s|` for `y > 0`. -/
theorem norm_ypow_div_A2 (y : ℝ) (hy : 0 < y) (s : ℂ) :
    ‖(y : ℂ) ^ s / s‖ = y ^ s.re / ‖s‖ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]

/-- Page 263 display (3.3), a horizontal side of the rectangle, `Im s = u`, `|u| = T`:
`|∫_c^R y^s/s dσ| ≤ y^c/(T |log y|)` for `0 < y < 1`. -/
theorem horiz_bound_A2 (c T y R u : ℝ) (_hc : 0 < c) (hT : 0 < T) (hy : 0 < y) (hy1 : y < 1)
    (hcR : c ≤ R) (hu : |u| = T) :
    ‖∫ x : ℝ in c..R, (y : ℂ) ^ ((x : ℂ) + (u : ℂ) * Complex.I) /
        ((x : ℂ) + (u : ℂ) * Complex.I)‖ ≤ y ^ c / (T * |Real.log y|) := by
  set L := Real.log y with hL
  have hL0 : L < 0 := Real.log_neg hy hy1
  have habs : |L| = -L := abs_of_neg hL0
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
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (L * x) / T) MeasureTheory.volume c R :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (L * x) / T)).intervalIntegrable _ _
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le hcR
    (Filter.Eventually.of_forall (fun x _ => hpt x)) hint) ?_
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (L * x) / (L * T))
      (Real.exp (L * x) / T) x := by
    intro x
    have := ((hasDerivAt_id x).const_mul L).exp.div_const (L * T)
    simp only [id] at this
    convert this using 1
    field_simp [hL0.ne]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint]
  rw [Real.rpow_def_of_pos hy, habs]
  have hR : 0 < Real.exp (L * R) := Real.exp_pos _
  have e1 : Real.exp (L * R) / (L * T) - Real.exp (L * c) / (L * T) =
      (Real.exp (L * c) - Real.exp (L * R)) / (-L * T) := by
    field_simp; ring
  rw [e1, mul_comm (-L) T, mul_comm (Real.log y) c, ← hL]
  apply div_le_div_of_nonneg_right _ (by nlinarith)
  linarith

/-- Page 263 display (3.3), the right side `Re s = R` of the rectangle: at most `2T y^R/R`. -/
theorem right_bound_A2 (T y R : ℝ) (hT : 0 < T) (hy : 0 < y) (hR : 0 < R) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((R : ℂ) + t * Complex.I) / ((R : ℂ) + t * Complex.I)‖
      ≤ y ^ R / R * (2 * T) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := y ^ R / R)
    (f := fun t : ℝ => (y : ℂ) ^ ((R : ℂ) + t * Complex.I) / ((R : ℂ) + t * Complex.I)) ?_
  · rw [show T - -T = 2 * T by ring, abs_of_pos (by linarith)] at h
    exact h
  · intro t _
    rw [norm_ypow_div_A2 y hy]
    have hre : ((R : ℂ) + (t : ℂ) * Complex.I).re = R := by simp
    have hn : R ≤ ‖(R : ℂ) + (t : ℂ) * Complex.I‖ := by
      have := Complex.re_le_norm ((R : ℂ) + (t : ℂ) * Complex.I)
      rwa [hre] at this
    rw [hre]
    exact div_le_div_of_nonneg_left (by positivity) hR hn

/-- Cauchy's theorem for `y^s/s` on the rectangle `c - iT, R + iT`, `0 < c ≤ R`. -/
theorem rect_zero_A2 (c T y R : ℝ) (hc : 0 < c) (hy : 0 < y) (hcR : c ≤ R) :
    (((∫ x : ℝ in c..R, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        ∫ x : ℝ in c..R, (y : ℂ) ^ ((x : ℂ) + (T : ℂ) * Complex.I) /
          ((x : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • ∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((R : ℂ) + t * Complex.I) /
          ((R : ℂ) + t * Complex.I)) -
      Complex.I • ∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
          ((c : ℂ) + t * Complex.I) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun s : ℂ => (y : ℂ) ^ s / s) ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
    ((R : ℂ) + (T : ℂ) * Complex.I) ?_
  · simpa using h
  · intro s hs
    have hre : c ≤ s.re := by
      have := (Complex.mem_reProdIm.mp hs).1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero] at this
      rw [Set.uIcc_of_le (by simpa using hcR)] at this
      simpa using this.1
    have hs0 : s ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hre; linarith
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    apply DifferentiableAt.differentiableWithinAt
    exact (differentiableAt_id.const_cpow (Or.inl hy0)).div differentiableAt_id hs0

/-- The same statement as the LEAF `perron_lt_log_leaf_ps1`, page 263 display (3.3). -/
theorem perron_lt_log_proof_A2 : ∀ c T y : ℝ, 0 < c → 0 < T → 0 < y → y < 1 →
    ‖(1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)‖ ≤
      y ^ c * (1 / (T * |Real.log y|)) := by
  intro c T y hc hT hy hy1
  set B := y ^ c / (T * |Real.log y|) with hB
  have hL : 0 < |Real.log y| := abs_pos.mpr (Real.log_neg hy hy1).ne
  have hBpos : 0 < B := by positivity
  have hpi := Real.pi_gt_three
  set V := ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)
  -- choose `R ≥ c` with `T y^R / (π c) ≤ (1 - 1/π) B`
  have hev := (tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy1).eventually
    (gt_mem_nhds (show (0 : ℝ) < (1 - 1 / π) * B * (π * c) / T by
      have : 0 < 1 - 1 / π := by rw [sub_pos, div_lt_one (by linarith)]; linarith
      positivity))
  obtain ⟨R, hR1, hR2⟩ := (hev.and (Filter.eventually_ge_atTop c)).exists
  have hRpos : 0 < R := by linarith
  have hrect := rect_zero_A2 c T y R hc hy hR2
  have hIV : Complex.I • V =
      ((∫ x : ℝ in c..R, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        ∫ x : ℝ in c..R, (y : ℂ) ^ ((x : ℂ) + (T : ℂ) * Complex.I) /
          ((x : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • ∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((R : ℂ) + t * Complex.I) /
          ((R : ℂ) + t * Complex.I) := by
    exact (sub_eq_zero.mp hrect).symm
  have hVn : ‖V‖ ≤ B + B + y ^ R / R * (2 * T) := by
    have h1 : ‖V‖ = ‖Complex.I • V‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [h1, hIV]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)) ?_
    · exact horiz_bound_A2 c T y R (-T) hc hT hy hy1 hR2 (by rw [abs_neg, abs_of_pos hT])
    · exact horiz_bound_A2 c T y R T hc hT hy hy1 hR2 (abs_of_pos hT)
    · rw [norm_smul, Complex.norm_I, one_mul]
      exact right_bound_A2 T y R hT hy hRpos
  have hyR : y ^ R / R * (2 * T) ≤ 2 * (1 - 1 / π) * B * π := by
    have h1 : y ^ R / R ≤ y ^ R / c := div_le_div_of_nonneg_left (by positivity) hc hR2
    have h2 : y ^ R * T < (1 - 1 / π) * B * (π * c) := by
      rwa [lt_div_iff₀ hT] at hR1
    have h3 : y ^ R / c * (2 * T) ≤ 2 * (1 - 1 / π) * B * π := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc]; nlinarith
    calc y ^ R / R * (2 * T) ≤ y ^ R / c * (2 * T) := by gcongr
      _ ≤ _ := h3
  have hn : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hn]
  have : y ^ c * (1 / (T * |Real.log y|)) = B := by rw [hB]; ring
  rw [this]
  calc 1 / (2 * π) * ‖V‖ ≤ 1 / (2 * π) * (B + B + 2 * (1 - 1 / π) * B * π) := by gcongr; linarith
    _ = B := by field_simp; ring
end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.rect_zero_A2
#print axioms LeanLab.Zhan1991.perron_lt_log_proof_A2
