import Mathlib

/-!
Backlund pp. 363 through 368 displays 57 through 73.
The normalized boundary estimates and the half-strip principle are distinct.
No target file or descendant is imported.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp563c
open Real Complex Set Filter Metric
open scoped Topology

/-- Backlund p. 363 display 57, the factor multiplying the actual zeta function. -/
noncomputable def normalizer (s : ℂ) : ℂ :=
  (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
    Complex.sqrt (Complex.sin (π * s / 2)) / Complex.log (-s * I)

/-- LEAF. Backlund pp. 365 and 366 displays 67 through 72.
The right boundary saving and functional symmetry control both vertical edges.
Only boundary points of the normalized function occur here. -/
theorem normalized_vertical_boundary
    (h54 : ∀ σ t : ℝ, 1 ≤ σ → 50 ≤ t →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048)
    (t : ℝ) (ht : 50 ≤ t) :
    ‖normalizer (t * I) * riemannZeta (t * I)‖ ≤ 1 ∧
    ‖normalizer (1 + t * I) * riemannZeta (1 + t * I)‖ ≤ 1 := by
  sorry

/-- LEAF. Backlund pp. 366 through 368 displays 70, 71 and 73.
The height-fifty half-edge and normalized symmetry control the bottom edge.
No point above the bottom edge occurs here. -/
theorem normalized_bottom_boundary
    (h50 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
        0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50)
    (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizer ((σ : ℂ) + 50 * I) * riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 1 := by
  sorry

/-- Backlund p. 368, the half-strip maximum argument with explicit damping.
The regularity, three boundary edges and damped top bounds are premises.
This isolates the maximum principle from every zeta and Gamma estimate. -/
theorem half_strip_of_damped_top (f : ℂ → ℂ)
    (hd : DiffContOnCl ℂ f (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioi (50 : ℝ)))
    (hv : ∀ t : ℝ, 50 ≤ t → ‖f (t * I)‖ ≤ 1 ∧ ‖f (1 + t * I)‖ ≤ 1)
    (hb : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ‖f ((σ : ℂ) + 50 * I)‖ ≤ 1)
    (hT : ∀ ε : ℝ, 0 < ε → ∀ H : ℝ, ∃ T : ℝ, max 50 H < T ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) 1,
        ‖Complex.exp ((ε : ℂ) * ((σ : ℂ) + T * I) ^ 2) * f ((σ : ℂ) + T * I)‖ ≤ 1)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖f ((σ : ℂ) + t * I)‖ ≤ 1 := by
  let z : ℂ := (σ : ℂ) + t * I
  have hεbound (ε : ℝ) (hε : 0 < ε) : ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ ≤ 1 := by
    obtain ⟨T, hTbig, htop⟩ := hT ε hε t
    have h50T : (50 : ℝ) < T := (le_max_left _ _).trans_lt hTbig
    have htT : t < T := (le_max_right _ _).trans_lt hTbig
    let g : ℂ → ℂ := fun w => Complex.exp ((ε : ℂ) * w ^ 2) * f w
    have hgd : Differentiable ℂ (fun w : ℂ => Complex.exp ((ε : ℂ) * w ^ 2)) := by fun_prop
    have hdg : DiffContOnCl ℂ g (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (50 : ℝ) T) := by
      exact (hgd.diffContOnCl.smul hd).mono (by intro w hw; exact ⟨hw.1, hw.2.1⟩)
    have hsmall (w : ℂ) (hw : w.re ∈ Set.Icc (0 : ℝ) 1) (hwt : 50 ≤ w.im) :
        ‖Complex.exp ((ε : ℂ) * w ^ 2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have he : ((ε : ℂ) * w ^ 2).re = ε * (w.re ^ 2 - w.im ^ 2) := by
        simp [pow_two, Complex.mul_re]
      rw [he]
      apply mul_nonpos_of_nonneg_of_nonpos hε.le
      nlinarith [hw.1, hw.2]
    have hboundary : ∀ w ∈ frontier (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (50 : ℝ) T), ‖g w‖ ≤ 1 := by
      intro w hw
      rw [frontier_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
        frontier_Ioo h50T, closure_Ioo h50T.ne, frontier_Ioo (by norm_num : (0 : ℝ) < 1)] at hw
      have hbnd (hwσ : w.re ∈ Set.Icc (0 : ℝ) 1) (hwt : 50 ≤ w.im) (hf : ‖f w‖ ≤ 1) : ‖g w‖ ≤ 1 := by
        dsimp [g]
        rw [norm_mul]
        exact (mul_le_mul (hsmall w hwσ hwt) hf (norm_nonneg _) (by norm_num)).trans (by norm_num)
      rcases hw with hw | hw
      · have hy : w.im = 50 ∨ w.im = T := by
          have hy : w.im ∈ ({50, T} : Set ℝ) := hw.2
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
        rcases hy with hy | hy
        · apply hbnd hw.1 (by linarith)
          have h := hb w.re hw.1
          have he := Complex.re_add_im w
          norm_num only [hy, Complex.ofReal_ofNat] at he
          rw [he] at h
          exact h
        · have h := htop w.re hw.1
          have he : (w.re : ℂ) + (T : ℂ) * I = w := by
            rw [← hy]
            exact Complex.re_add_im w
          simpa only [he, g] using h
      · have hx : w.re = 0 ∨ w.re = 1 := by
          have hx : w.re ∈ ({0, 1} : Set ℝ) := hw.1
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
        have hwt : w.im ∈ Set.Icc (50 : ℝ) T := hw.2
        rcases hx with hx | hx
        · apply hbnd (by constructor <;> linarith) hwt.1
          have h := (hv w.im hwt.1).1
          have he : (w.im : ℂ) * I = w := by simpa [hx] using Complex.re_add_im w
          simpa only [he] using h
        · apply hbnd (by constructor <;> linarith) hwt.1
          have h := (hv w.im hwt.1).2
          have he : 1 + (w.im : ℂ) * I = w := by simpa [hx] using Complex.re_add_im w
          simpa only [he] using h
    have hz : z ∈ closure (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (50 : ℝ) T) := by
      rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioo h50T.ne]
      change z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (50 : ℝ) T
      simpa [z] using (show σ ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (50 : ℝ) T from ⟨hσ, ht, htT.le⟩)
    exact Complex.norm_le_of_forall_mem_frontier_norm_le
      ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) hdg hboundary hz
  have hc : Continuous (fun ε : ℝ => ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖) := by fun_prop
  have hlim : Tendsto (fun ε : ℝ => ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖f z‖) := by
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hεbound ε hε
  simpa [z] using le_of_tendsto hlim hle

/-- Backlund p. 363 display 57, regularity of the actual normalized function.
The sine stays away from its branch cut in the open half-strip.
Gamma has no poles and the logarithm denominator is nonzero there. -/
theorem normalized_regular :
    DiffContOnCl ℂ (fun s : ℂ => normalizer s * riemannZeta s)
      (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioi (50 : ℝ)) := by
  have hpoint (z : ℂ) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hzt : 50 ≤ z.im) :
      DifferentiableAt ℂ (fun s : ℂ => normalizer s * riemannZeta s) z := by
    have hargre : (π * z / 2 : ℂ).re = π * z.re / 2 := by simp [Complex.mul_re]
    have hargim : (π * z / 2 : ℂ).im = π * z.im / 2 := by simp [Complex.mul_im]
    have hsinR (w : ℂ) : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
      rw [Complex.sin_eq]
      simp only [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
        ← Complex.ofReal_sinh, Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, mul_one, add_zero]
    have hsinI (w : ℂ) : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
      rw [Complex.sin_eq]
      simp only [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
        ← Complex.ofReal_sinh, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add]
    have hsinre : (Complex.sin (π * z / 2)).re =
        Real.sin (π * z.re / 2) * Real.cosh (π * z.im / 2) := by rw [hsinR, hargre, hargim]
    have hsinim : (Complex.sin (π * z / 2)).im =
        Real.cos (π * z.re / 2) * Real.sinh (π * z.im / 2) := by rw [hsinI, hargre, hargim]
    have hslit : Complex.sin (π * z / 2) ∈ Complex.slitPlane := by
      change 0 < (Complex.sin (π * z / 2)).re ∨ (Complex.sin (π * z / 2)).im ≠ 0
      by_cases hzpos : 0 < z.re
      · left
        rw [hsinre]
        apply mul_pos _ (Real.cosh_pos _)
        apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
        nlinarith [Real.pi_pos]
      · right
        have hz : z.re = 0 := le_antisymm (le_of_not_gt hzpos) hz0
        rw [hsinim, hz]
        simp only [mul_zero, zero_div, Real.cos_zero, one_mul]
        exact ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
    have harg : DifferentiableAt ℂ (fun s : ℂ => π * s / 2) z := by fun_prop
    have hsinD : DifferentiableAt ℂ (fun s : ℂ => Complex.sin (π * s / 2)) z :=
      Complex.differentiableAt_sin.comp z harg
    have hsqrt := (Complex.differentiableAt_sqrt hslit).comp z hsinD
    have hgamma := (Complex.differentiableAt_Gamma (z / 2) (by
      intro m h
      have hi := congrArg Complex.im h
      simp at hi
      linarith)).comp z ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const (2 : ℂ))
    have hpow := ((differentiableAt_id (𝕜 := ℂ) (x := z)).neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (show (π : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero))
    have hlogslit : -z * I ∈ Complex.slitPlane := by
      left
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg]
      linarith
    have hlog := (Complex.differentiableAt_log hlogslit).comp z
      (differentiableAt_id.neg.mul_const I)
    have hln : Complex.log (-z * I) ≠ 0 := by
      have hlower : (50 : ℝ) ≤ ‖-z * I‖ := by
        have h := Complex.re_le_norm (-z * I)
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg] at h
        exact hzt.trans h
      have hp : 0 < (Complex.log (-z * I)).re := by
        rw [Complex.log_re]
        exact Real.log_pos (by linarith)
      intro h
      rw [h, Complex.zero_re] at hp
      exact lt_irrefl 0 hp
    have hnorm : DifferentiableAt ℂ normalizer z := by
      exact ((hpow.mul hgamma).mul hsqrt).div hlog hln
    have hzeta : z ≠ 1 := by
      intro h
      rw [h] at hzt
      norm_num at hzt
    exact hnorm.mul (differentiableAt_riemannZeta hzeta)
  apply DifferentiableOn.diffContOnCl
  rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi]
  intro z hz
  exact (hpoint z hz.1.1 hz.1.2 hz.2).differentiableWithinAt

/-- LEAF. Backlund p. 368, polynomial growth from displays 13 and 67.
Gaussian damping gives an arbitrarily high horizontal top with norm at most one.
No boundary estimate or maximum principle is assumed. -/
theorem normalized_damped_top (ε : ℝ) (hε : 0 < ε) (H : ℝ) :
    ∃ T : ℝ, max 50 H < T ∧ ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      ‖Complex.exp ((ε : ℂ) * ((σ : ℂ) + T * I) ^ 2) *
        (normalizer ((σ : ℂ) + T * I) * riemannZeta ((σ : ℂ) + T * I))‖ ≤ 1 := by
  sorry

/-- Backlund p. 368, the Phragmen Lindelof step after display 73.
CONDITIONAL ON normalized_damped_top. Regularity is proved.
The actual normalized function has polynomial growth by display 13 and 67.
Boundary bounds are explicit premises. Gamma and sine boundary estimates
are absent from this leaf. -/
theorem normalized_half_strip
    (hv : ∀ t : ℝ, 50 ≤ t →
      ‖normalizer (t * I) * riemannZeta (t * I)‖ ≤ 1 ∧
      ‖normalizer (1 + t * I) * riemannZeta (1 + t * I)‖ ≤ 1)
    (hb : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      ‖normalizer ((σ : ℂ) + 50 * I) * riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 1)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖normalizer ((σ : ℂ) + t * I) * riemannZeta ((σ : ℂ) + t * I)‖ ≤ 1 := by
  exact half_strip_of_damped_top (fun s : ℂ => normalizer s * riemannZeta s)
    normalized_regular hv hb normalized_damped_top σ t hσ ht

/-- LEAF. Backlund p. 365 displays 60 through 68, lower normalization bound.
This involves only Gamma, sine, logarithm and powers, with no zeta value.
The factor one minus four over t squared is inverted algebraically. -/
theorem normalizer_lower (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    1 ≤ ‖normalizer ((σ : ℂ) + t * I)‖ *
      (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t) := by
  sorry

/-- Backlund p. 363 display 56, the exact original strip implication.
CONDITIONAL ON the remaining strictly smaller normalized analytic leaves. -/
theorem strip56_of_boundary
    (h54 : ∀ σ t : ℝ, 1 ≤ σ → 50 ≤ t →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048)
    (h50 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
        0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t := by
  have hp := normalized_half_strip (normalized_vertical_boundary h54)
    (normalized_bottom_boundary h50) σ t hσ ht
  rw [norm_mul] at hp
  have hw := normalizer_lower σ t hσ ht
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have hm : 0 ≤ t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t := by
    exact mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) hd.le)
      (Real.rpow_nonneg (by positivity) _)) (Real.log_nonneg (by linarith))
  calc
    _ = 1 * ‖riemannZeta ((σ : ℂ) + t * I)‖ := by ring
    _ ≤ (‖normalizer ((σ : ℂ) + t * I)‖ *
        (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t)) *
        ‖riemannZeta ((σ : ℂ) + t * I)‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = (t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t) *
        (‖normalizer ((σ : ℂ) + t * I)‖ * ‖riemannZeta ((σ : ℂ) + t * I)‖) := by ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hp hm

end LeanLab.RamareSaouter2003.Decomp563c

#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalizer
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_vertical_boundary
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_bottom_boundary
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_half_strip
#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalizer_lower
#print axioms LeanLab.RamareSaouter2003.Decomp563c.strip56_of_boundary

#print axioms LeanLab.RamareSaouter2003.Decomp563c.half_strip_of_damped_top

#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_regular

#print axioms LeanLab.RamareSaouter2003.Decomp563c.normalized_damped_top
