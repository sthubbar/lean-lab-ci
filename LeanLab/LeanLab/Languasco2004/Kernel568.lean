/-
Jia 1996 page 279, Lemma 26 after displays 53 to 56.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Numeric30_548
namespace LeanLab.Languasco2004.Kernel568
open Real Numeric30_548 Kernel548 BuchstabInitial316
noncomputable section
/-- Page 279: the full closed Omega4 domain uses the second initial formula. -/
theorem region4_argument (t u : ℝ) (htl : 41 / 180 ≤ t) (htu : t ≤ 8 / 33)
    (hul : 41 / 90 - t ≤ u) (huu : u ≤ t) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧
      2 ≤ (1 - t - u) / u ∧ (1 - t - u) / u ≤ 3 := by
  have ht : 0 < t := by linarith
  have hu : 0 < u := by linarith
  refine ⟨ht, hu, by linarith, ?_, ?_⟩
  · apply (le_div_iff₀ hu).mpr
    linarith
  · apply (div_le_iff₀ hu).mpr
    linarith
/-- Page 279: the complete Omega4 Buchstab integral has the printed logarithmic kernel. -/
theorem region4_kernel (t u : ℝ) (htl : 41 / 180 ≤ t) (htu : t ≤ 8 / 33)
    (hul : 41 / 90 - t ≤ u) (huu : u ≤ t) :
    buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, hs, _⟩ := region4_argument t u htl htu hul huu
  exact initial_kernel_high t u ht hu hv hs
/-- Page 279 numerical support: Mathlib's first three positive series terms bound the logarithm. -/
theorem log_three_terms (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) :
    2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 ≤ Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz hz1 3
  norm_num [Finset.sum_range_succ] at h
  linarith
/-- Page 279 numerical support: a polynomial minorant of the full Omega4 kernel. -/
def polynomial4 (t u : ℝ) : ℝ :=
  let v := invPoly3 (1 - t - u) (49 / 90)
  let z := (1 - t - 3 * u) * v
  invPoly3 t (8 / 33) * invPoly3 u (8 / 33) * v *
    (1 + 2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5)

/-- Numeric helper: the polynomial lower bounds sit on the correct side of the
reciprocals throughout the closed Omega4 domain. -/
private theorem poly4_aux (t u v z : ℝ) (ht : 0 < t) (hu : 0 < u) (hv : 0 < 1 - t - u)
    (htu : t ≤ 8 / 33) (huu : u ≤ t) (hvc : 1 - t - u ≤ 49 / 90)
    (hvdef : v = invPoly3 (1 - t - u) (49 / 90))
    (hzdef : z = (1 - t - 3 * u) * v) :
    0 ≤ v ∧ v * (1 - t - u) ≤ 1 ∧ 0 ≤ z ∧ z * (1 - t - u) ≤ 1 - t - 3 * u ∧ z < 1 := by
  obtain ⟨hP0, hPB⟩ := invPoly3_bounds (1 - t - u) (49 / 90) hv (by norm_num) hvc
  have hv0 : 0 ≤ v := by rw [hvdef]; exact hP0
  have hvB : v ≤ 1 / (1 - t - u) := by rw [hvdef]; exact hPB
  have hmul : v * (1 - t - u) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hvB (le_of_lt hv)
    rwa [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hv)] at h
  have hw : 0 < 1 - t - 3 * u := by linarith
  have hz0 : 0 ≤ z := by
    rw [hzdef]
    exact mul_nonneg (le_of_lt hw) hv0
  have hzkey : z * (1 - t - u) ≤ 1 - t - 3 * u := by
    rw [hzdef]
    have hk := mul_le_mul_of_nonneg_left hmul (le_of_lt hw)
    nlinarith [hk]
  refine ⟨hv0, hmul, hz0, hzkey, ?_⟩
  have h1 : z * (1 - t - u) < 1 * (1 - t - u) := by nlinarith [hzkey, hv]
  exact lt_of_mul_lt_mul_right h1 (le_of_lt hv)

/-- LEAF. Page 279: the polynomial is below the source logarithmic kernel on the whole closed domain. -/
theorem polynomial4_le (t u : ℝ) (htl : 41 / 180 ≤ t) (htu : t ≤ 8 / 33)
    (hul : 41 / 90 - t ≤ u) (huu : u ≤ t) :
    polynomial4 t u ≤
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, _hs2, _hs3⟩ := region4_argument t u htl htu hul huu
  have hvc : 1 - t - u ≤ 49 / 90 := by linarith
  set v := invPoly3 (1 - t - u) (49 / 90) with hvdef
  set z := (1 - t - 3 * u) * v with hzdef
  obtain ⟨ht0, htB⟩ := invPoly3_bounds t (8 / 33) ht (by norm_num) htu
  have hu8 : u ≤ 8 / 33 := by linarith
  obtain ⟨hu0, huB⟩ := invPoly3_bounds u (8 / 33) hu (by norm_num) hu8
  obtain ⟨hv0, hvkey, hz0, hzkey, hz1⟩ := poly4_aux t u v z ht hu hv htu huu hvc hvdef hzdef
  have hvB : v ≤ 1 / (1 - t - u) := by
    rw [le_div_iff₀ hv]
    exact hvkey
  have hzkey' : z * (1 - t - u) ≤ 1 - t - 3 * u := hzkey
  -- the reciprocal ratio of the truncated logarithm
  have hratio : (1 + z) / (1 - z) ≤ (1 - t - 2 * u) / u := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 - z) hu]
    nlinarith [hzkey']
  have hlog : Real.log ((1 + z) / (1 - z)) ≤ Real.log ((1 - t) / u - 2) := by
    have hpos : 0 < (1 + z) / (1 - z) := by
      apply div_pos (by linarith) (by linarith)
    have h := Real.log_le_log hpos hratio
    have heq : (1 - t - 2 * u) / u = (1 - t) / u - 2 := by
      field_simp
    rwa [heq] at h
  have hbr : 1 + 2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 ≤
      1 + Real.log ((1 - t) / u - 2) := by
    have h3 := log_three_terms z hz0 hz1
    linarith
  have hbr0 : 0 ≤ 1 + 2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 := by positivity
  have hmul : invPoly3 t (8 / 33) * invPoly3 u (8 / 33) * v ≤
      (1 / t) * (1 / u) * (1 / (1 - t - u)) := by
    have h1 : invPoly3 t (8 / 33) * invPoly3 u (8 / 33) ≤ (1 / t) * (1 / u) :=
      mul_le_mul htB huB hu0 (by positivity)
    exact mul_le_mul h1 hvB hv0 (by positivity)
  have hfac : 0 ≤ (1 / t) * (1 / u) * (1 / (1 - t - u)) := by positivity
  calc polynomial4 t u
      = invPoly3 t (8 / 33) * invPoly3 u (8 / 33) * v *
          (1 + 2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5) := by
        simp only [polynomial4, hvdef, hzdef]
    _ ≤ ((1 / t) * (1 / u) * (1 / (1 - t - u))) *
          (1 + 2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5) :=
        mul_le_mul_of_nonneg_right hmul hbr0
    _ ≤ ((1 / t) * (1 / u) * (1 / (1 - t - u))) *
          (1 + Real.log ((1 - t) / u - 2)) :=
        mul_le_mul_of_nonneg_left hbr hfac
    _ = (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
        field_simp

#print axioms region4_argument
#print axioms region4_kernel
#print axioms log_three_terms
#print axioms polynomial4_le
end
end LeanLab.Languasco2004.Kernel568
