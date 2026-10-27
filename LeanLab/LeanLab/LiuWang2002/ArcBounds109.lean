import LeanLab.LiuWang2002.Constants

/-! Endpoint interpolation in the proof of Theorem 1, page 174.
AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.ArcBounds109
open Real Set

/-- Convexity supplies the maximum of the two endpoint estimates on page 174. -/
theorem reciprocal_endpoint (a b d l u t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : 0 < l) (hlt : l ≤ t) (htu : t ≤ u) :
    a / t + b * t + d ≤ max (a / l + b * l + d) (a / u + b * u + d) := by
  have hi : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x⁻¹) := by
    simpa using (convexOn_zpow (𝕜 := ℝ) (-1 : ℤ))
  have hf : ConvexOn ℝ (Ioi 0) (fun x : ℝ => a / x + b * x + d) := by
    convert ((hi.smul ha).add ((convexOn_id (convex_Ioi (0 : ℝ))).smul hb)).add_const d using 1
    ext x
    simp [smul_eq_mul, div_eq_mul_inv]
  apply hf.le_on_segment hl (hl.trans_le (hlt.trans htu))
  rw [segment_eq_Icc (hlt.trans htu)]
  exact ⟨hlt, htu⟩

/-- The interpolation written with the powers of q in the paper, page 174. -/
theorem sqrt_endpoint (a b d l u q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : 0 < l) (hlq : l ≤ q) (hqu : q ≤ u) :
    a * q ^ (-(1 / 2) : ℝ) + b * q ^ (1 / 2 : ℝ) + d ≤
      max (a * l ^ (-(1 / 2) : ℝ) + b * l ^ (1 / 2 : ℝ) + d)
        (a * u ^ (-(1 / 2) : ℝ) + b * u ^ (1 / 2 : ℝ) + d) := by
  have hq : 0 ≤ q := hl.le.trans hlq
  have hu : 0 ≤ u := hq.trans hqu
  have h := reciprocal_endpoint a b d (l ^ (1 / 2 : ℝ)) (u ^ (1 / 2 : ℝ))
    (q ^ (1 / 2 : ℝ)) ha hb (rpow_pos_of_pos hl _)
    (rpow_le_rpow hl.le hlq (by norm_num)) (rpow_le_rpow hq hqu (by norm_num))
  simpa [div_eq_mul_inv, rpow_neg hl.le, rpow_neg hq, rpow_neg hu] using h

/-- The full interior M4 estimate on page 174, from the two endpoint certificates. -/
theorem m4_bound (L q : ℝ) (hL : 3100 ≤ L) (hqlo : L ^ 6 ≤ q)
    (hqhi : q ≤ exp L / L ^ 7) :
    0.28 * exp L * q ^ (-(1 / 2) : ℝ) * L ^ 2 +
      4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ) +
      0.09 * (exp L) ^ (1 / 2 : ℝ) * q ^ (1 / 2 : ℝ) * L ^ (2.5 : ℝ)
      ≤ 0.3 * exp L / L := by
  have hLp : 0 < L := by linarith
  have hEp : 0 < exp L := exp_pos L
  have he := sqrt_endpoint (0.28 * exp L * L ^ 2)
    (0.09 * (exp L) ^ (1 / 2 : ℝ) * L ^ (2.5 : ℝ))
    (4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ)) (L ^ 6) (exp L / L ^ 7) q
    (by positivity) (by positivity) (by positivity) hqlo hqhi
  have hlow :
      0.28 * exp L * L ^ 2 * (L ^ 6) ^ (-(1 / 2) : ℝ) +
        0.09 * (exp L) ^ (1 / 2 : ℝ) * L ^ (2.5 : ℝ) * (L ^ 6) ^ (1 / 2 : ℝ) +
        4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ) ≤ 0.3 * exp L / L := by
    convert Constants.m4_bound_P1 L hL using 1 <;> ring
  have hroot : (exp L / L ^ 7) ^ (1 / 2 : ℝ) =
      (exp L) ^ (1 / 2 : ℝ) / L ^ (3.5 : ℝ) := by
    rw [div_rpow hEp.le (by positivity), ← rpow_natCast L 7, ← rpow_mul hLp.le]
    norm_num
  have hsq : ((exp L) ^ (1 / 2 : ℝ)) ^ 2 = exp L := by
    rw [← rpow_natCast _ 2, ← rpow_mul hEp.le]
    norm_num
  have hp55 : L ^ (5.5 : ℝ) = L ^ 2 * L ^ (3.5 : ℝ) := by
    rw [← rpow_natCast L 2, ← rpow_add hLp]
    norm_num
  have hp35 : L ^ (3.5 : ℝ) = L ^ (2.5 : ℝ) * L := by
    convert rpow_add hLp (2.5 : ℝ) (1 : ℝ) using 1 <;> norm_num
  have hup_eq :
      0.28 * exp L * L ^ 2 * (exp L / L ^ 7) ^ (-(1 / 2) : ℝ) +
        0.09 * (exp L) ^ (1 / 2 : ℝ) * L ^ (2.5 : ℝ) * (exp L / L ^ 7) ^ (1 / 2 : ℝ) +
        4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ) =
      0.28 * (exp L) ^ (1 / 2 : ℝ) * L ^ (5.5 : ℝ) +
        4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ) + 0.09 * exp L / L := by
    rw [rpow_neg (by positivity : 0 ≤ exp L / L ^ 7), hroot, hp55]
    have hsn : (exp L) ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (rpow_pos_of_pos hEp _)
    have hln : L ^ (3.5 : ℝ) ≠ 0 := ne_of_gt (rpow_pos_of_pos hLp _)
    field_simp
    generalize (exp L) ^ (1 / 2 : ℝ) = s at hsq ⊢
    rw [← hsq, hp35]
    ring
  have hupp :
      0.28 * exp L * L ^ 2 * (exp L / L ^ 7) ^ (-(1 / 2) : ℝ) +
        0.09 * (exp L) ^ (1 / 2 : ℝ) * L ^ (2.5 : ℝ) * (exp L / L ^ 7) ^ (1 / 2 : ℝ) +
        4 * (exp L) ^ (4 / 5 : ℝ) * L ^ (1.4 : ℝ) ≤ 0.3 * exp L / L := by
    rw [hup_eq]
    exact Constants.m4_bound_Q L hL
  have hm := he.trans (max_le hlow hupp)
  convert hm using 1 <;> ring

/-- The denominator separation stated before display 3.3, page 144. -/
theorem denominator_separation (L : ℝ) (hL : 3100 ≤ L) :
    L ^ 6 < (exp L / L ^ 7) / 2 := by
  have hLp : 0 < L := by linarith
  have hh := Constants.aux_half L hL
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 9 * L ^ 7) hh 2
  have he : (exp (L / 2)) ^ 2 = exp L := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [he] at hs
  have hp : 0 < L ^ 13 := by positivity
  have hpoly : 2 * L ^ 13 < 81 * L ^ 14 := by
    have hmul := mul_pos hp (show 0 < 81 * L - 2 by linarith)
    nlinarith
  have hmain : 2 * L ^ 13 < exp L := by nlinarith
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), lt_div_iff₀ (pow_pos hLp 7)]
  nlinarith

end LeanLab.LiuWang2002.ArcBounds109

#print axioms LeanLab.LiuWang2002.ArcBounds109.reciprocal_endpoint
#print axioms LeanLab.LiuWang2002.ArcBounds109.sqrt_endpoint

#print axioms LeanLab.LiuWang2002.ArcBounds109.m4_bound

#print axioms LeanLab.LiuWang2002.ArcBounds109.denominator_separation
