import LeanLab.ChenDoubleSieve.Task562Envelope

/-!
Polynomial majorants for the rational D2,16 certificate of Wu 2004 page 26.
Source: https://arxiv.org/pdf/0705.1652, Table 1 row four page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- Cubic reciprocal enclosure with a uniform rational remainder.
Wu 2004 page 26, derived local polynomial for the D2,16 kernel. -/
def g3 (z : ℝ) : ℝ := 1 - z + z ^ 2 - z ^ 3 + 2825761 / 79170210500

/-- Degree five geometric enclosure with a uniform rational remainder.
Wu 2004 page 26, derived polynomial for the sum denominator. -/
def p5 (t : ℝ) : ℝ := 1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 +
  304006671424 / 2101053678330063

/-- An explicit polynomial upper candidate for the rational kernel.
Wu 2004 page 26, derived from four cubic enclosures and one geometric enclosure. -/
def r3Poly (x : Fin 4 → ℝ) : ℝ :=
  (1 / ((541 / 1455 : ℝ) ^ 4 * (746 / 1455 : ℝ))) *
    (∏ j, g3 ((x j - 541 / 1455) / (541 / 1455))) *
    p5 (((∑ j, x j) - 4 * (541 / 1455)) / (746 / 1455))

/-- The cubic polynomial bounds the reciprocal on the full coordinate range.
Wu 2004 page 26, derived geometric remainder estimate. -/
theorem reciprocal_le_g3 {z : ℝ} (hz : |z| ≤ (41 / 541 : ℝ)) :
    1 / (1 + z) ≤ g3 z := by
  obtain ⟨hl, hu⟩ := abs_le.mp hz
  have hz2 : z ^ 2 ≤ (41 / 541 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ 41 / 541 + z)]
  have hz4 : z ^ 4 ≤ (41 / 541 : ℝ) ^ 4 := by
    convert mul_self_le_mul_self (sq_nonneg z) hz2 using 1 <;> ring
  rw [div_le_iff₀ (by linarith : 0 < 1 + z)]
  unfold g3
  nlinarith

/-- The geometric polynomial bounds the reciprocal on the full sum range.
Wu 2004 page 26, derived sixth-order remainder estimate. -/
theorem reciprocal_le_p5 {t : ℝ} (ht : |t| ≤ (82 / 373 : ℝ)) :
    1 / (1 - t) ≤ p5 t := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  have ht2 : t ^ 2 ≤ (82 / 373 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ 82 / 373 + t)]
  have ht6 : t ^ 6 ≤ (82 / 373 : ℝ) ^ 6 := by
    have hh := pow_le_pow_left₀ (sq_nonneg t) ht2 3
    simpa only [← pow_mul] using hh
  rw [div_le_iff₀ (by linarith : 0 < 1 - t)]
  unfold p5
  nlinarith

/-- The explicit degree seventeen polynomial dominates the rational kernel on D2,16.
Wu 2004 page 26, derived pointwise certificate with no quadrature input. -/
theorem r3Base_le_polynomial {x : Fin 4 → ℝ}
    (hx : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    r3Base x ≤ r3Poly x := by
  let c : ℝ := 541 / 1455
  let d : ℝ := 746 / 1455
  let z : Fin 4 → ℝ := fun j => (x j - c) / c
  let t : ℝ := ((∑ j, x j) - 4 * c) / d
  have hc : 0 < c := by norm_num [c]
  have hd : 0 < d := by norm_num [d]
  have hxpos (j : Fin 4) : 0 < x j := lt_of_lt_of_le (by norm_num) (hx.2 j).1
  have hz (j : Fin 4) : |z j| ≤ (41 / 541 : ℝ) := by
    have hl := (hx.2 j).1
    have hu := (hx.2 j).2
    apply abs_le.mpr
    constructor
    · rw [le_div_iff₀ hc]
      dsimp [c] at *
      linarith
    · rw [div_le_iff₀ hc]
      dsimp [c] at *
      linarith
  have ht : |t| ≤ (82 / 373 : ℝ) := by
    have hl : (∑ _ : Fin 4, (100 / 291 : ℝ)) ≤ ∑ j, x j :=
      sum_le_sum fun j _ => (hx.2 j).1
    have hu : (∑ j, x j) ≤ ∑ _ : Fin 4, (2 / 5 : ℝ) :=
      sum_le_sum fun j _ => (hx.2 j).2
    norm_num at hl hu
    apply abs_le.mpr
    constructor
    · rw [le_div_iff₀ hd]
      dsimp [c, d] at *
      linarith
    · rw [div_le_iff₀ hd]
      dsimp [c, d] at *
      linarith
  have hcoord (j : Fin 4) : 1 / x j ≤ g3 (z j) / c := by
    have hh := div_le_div_of_nonneg_right (reciprocal_le_g3 (hz j)) hc.le
    have he : (1 / (1 + z j)) / c = 1 / x j := by
      dsimp [z]
      field_simp [hc.ne', (hxpos j).ne']
      <;> ring
    rwa [he] at hh
  have hlast : 1 / (2 - ∑ j, x j) ≤ p5 t / d := by
    have hh := div_le_div_of_nonneg_right (reciprocal_le_p5 ht) hd.le
    have he : (1 / (1 - t)) / d = 1 / (2 - ∑ j, x j) := by
      have hearg : 1 - t = (2 - ∑ j, x j) / d := by
        dsimp [t, c, d]
        ring
      rw [hearg]
      field_simp [hd.ne', (r3_sum_gap_pos hx).ne']
    rwa [he] at hh
  have hprod : (∏ j, 1 / x j) ≤ ∏ j, g3 (z j) / c :=
    prod_le_prod₀ (fun j _ => (one_div_pos.mpr (hxpos j)).le) (fun j _ => hcoord j)
  calc r3Base x = (∏ j, 1 / x j) * (1 / (2 - ∑ j, x j)) := by
        simp [r3Base, prod_div_distrib, one_div_mul_one_div]
        ring
    _ ≤ (∏ j, g3 (z j) / c) * (p5 t / d) :=
        mul_le_mul hprod hlast (one_div_pos.mpr (r3_sum_gap_pos hx)).le
          (prod_nonneg fun j _ => (one_div_pos.mpr (hxpos j)).le.trans (hcoord j))
    _ = r3Poly x := by
        simp [r3Poly, z, t, c, d, prod_div_distrib]
        ring

/-- The polynomial is integrable on the ordered compact domain.
Wu 2004 page 26, derived finite polynomial certificate preparation. -/
theorem r3Poly_integrable : IntegrableOn r3Poly
    (domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  unfold r3Poly g3 p5
  fun_prop

/-- The rational integral is at most the integral of the explicit polynomial.
Wu 2004 page 26, derived reduction to exact polynomial integration. -/
theorem r3_integral_le_polynomial :
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Base x) ≤
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Poly x) := by
  exact setIntegral_mono_on r3Base_integrable r3Poly_integrable
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => r3Base_le_polynomial hx)

/-- This exact rational candidate fits the remaining integral budget.
The identification of the candidate with the polynomial integral is not asserted here.
Wu 2004 page 26, derived arithmetic certificate only. -/
theorem polynomial_candidate_fits :
    (1331032446698958906352180399753674063507603432285078448678967637782243 /
      30833552085189034950799979968436065035185877655749765190333493625000000000 : ℝ) ≤
      (43179 / 1000000000 : ℝ) := by
  norm_num

end LeanLab.ChenDoubleSieve.Task562
