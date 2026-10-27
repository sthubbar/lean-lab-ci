import LeanLab.HelfgottMajor.BookL1523

/-!
P0014 Lemma 3.3, pages 29 and 30, displays 3.79 and 3.80.
AI wrote this Lean code. Binary Goldbach is open.
This decomposition reuses the proved half-angle parametrization of BookL1523.
-/

namespace LeanLab.HelfgottMajor.Decomp123b
open Real Set
open LeanLab.HelfgottMajor.BookE
open LeanLab.HelfgottMajor.BookL1523

/-- CITED. P0014 Lemma 3.3, page 29, displays 3.79 and 3.80. -/
def Lemma33 : Prop :=
  ∀ r : ℝ, 0 < r → r / 8 - 5 * r ^ 3 / 384 ≤ E r ∧
    E r = π / 4 - arcsin (1 / ups r) / 2 -
      sin (2 * arcsin (1 / ups r)) / (4 * (1 + sin (arcsin (1 / ups r))))

/-- LEAF. P0014 page 30, display 3.83 and Appendix A display A.37 on page 68.
In the half-angle coordinate, the cubic lower bound reduces to a rational inequality.
The proof uses the standard arctan cubic bound rather than the paper's fifth derivative check.
-/
theorem rational_lower {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Rt t / 8 - 5 * Rt t ^ 3 / 384 ≤ Ft t := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  let P : ℝ := 24 * (1 - t ^ 2) ^ 6 +
    219 * t ^ 2 * (1 - t ^ 2) ^ 5 +
    633 * (t ^ 2) ^ 2 * (1 - t ^ 2) ^ 4 +
    960 * (t ^ 2) ^ 3 * (1 - t ^ 2) ^ 3 +
    840 * (t ^ 2) ^ 4 * (1 - t ^ 2) ^ 2 +
    400 * (t ^ 2) ^ 5 * (1 - t ^ 2) + 80 * (t ^ 2) ^ 6
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hid : t - t ^ 3 / 3 - gt t - Rt t / 8 + 5 * Rt t ^ 3 / 384 =
      t ^ 5 * P / (6 * (1 - t ^ 2) ^ 6 * (1 + t ^ 2)) := by
    dsimp [gt, Rt, P]
    field_simp
    <;> ring
  have hnonneg : 0 ≤ t - t ^ 3 / 3 - gt t - Rt t / 8 + 5 * Rt t ^ 3 / 384 := by
    rw [hid]
    positivity
  have ha := LeanLab.HelfgottMajor.BookL1614.arctan_ge_sub_cube h0.le
  unfold Ft
  linarith

/-- LEAF. P0014 page 30, display 3.82. The square root defining ups obeys this algebraic relation. -/
theorem radius_identity {r : ℝ} (hr : 0 < r) :
    1 ≤ ups r ∧ r ^ 2 = 4 * (ups r) ^ 2 * ((ups r) ^ 2 - 1) := by
  have hs0 : 0 ≤ 1 + r ^ 2 := by positivity
  have hs := sq_sqrt hs0
  have hs1 : 1 ≤ sqrt (1 + r ^ 2) := by
    rw [le_sqrt (by norm_num) hs0]
    nlinarith
  have hu : (ups r) ^ 2 = (1 + sqrt (1 + r ^ 2)) / 2 := by
    unfold ups
    exact sq_sqrt (by positivity)
  constructor
  · unfold ups
    rw [le_sqrt (by norm_num) (by positivity)]
    linarith
  · nlinarith

/-- LEAF. P0014 page 30, last step of display 3.83 with beta = pi/2 - alpha.
This proves the alternate expression in display 3.80 on page 29.
-/
theorem complementary_angle {r : ℝ} (hr : 0 < r) :
    E r = π / 4 - arcsin (1 / ups r) / 2 -
      sin (2 * arcsin (1 / ups r)) / (4 * (1 + sin (arcsin (1 / ups r)))) := by
  obtain ⟨hu, hrel⟩ := radius_identity hr
  have hu0 : 0 < ups r := by linarith
  have hx0 : 0 ≤ 1 / ups r := by positivity
  have hx1 : 1 / ups r ≤ 1 := by rw [div_le_one hu0]; exact hu
  have hsin : sin (arcsin (1 / ups r)) = 1 / ups r :=
    sin_arcsin (by linarith) hx1
  have hcos : cos (arcsin (1 / ups r)) = r / (2 * (ups r) ^ 2) := by
    rw [cos_arcsin]
    rw [sqrt_eq_iff_eq_sq (by nlinarith : 0 ≤ 1 - (1 / ups r) ^ 2) (by positivity)]
    field_simp
    nlinarith [hrel]
  have hfrac : sin (2 * arcsin (1 / ups r)) /
      (4 * (1 + sin (arcsin (1 / ups r)))) = (ups r - 1) / r := by
    rw [sin_two_mul, hsin, hcos]
    have hp : 0 < ups r + 1 := by linarith
    field_simp
    nlinarith [hrel]
  unfold E
  rw [arccos_eq_pi_div_two_sub_arcsin, hfrac]
  ring

/-- P0014 Lemma 3.3 assembled from the leaves and the existing exact parametrization. -/
theorem lemma_3_3 : Lemma33 := by
  intro r hr
  refine ⟨?_, complementary_angle hr⟩
  obtain ⟨t, ht, hRt⟩ := Rt_surj hr
  rw [← hRt, E_Rt ht.1 ht.2]
  exact rational_lower ht.1 ht.2

/-- The exponent E is strictly positive on positive radii, from display 3.2 on page 10. -/
theorem E_positive {r : ℝ} (hr : 0 < r) : 0 < E r := by
  obtain ⟨t, ht, hRt⟩ := Rt_surj hr
  rw [← hRt, E_Rt ht.1 ht.2]
  have hg : 0 < gt t := by
    have ht0 : 0 < t := ht.1
    have hq : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    unfold gt
    positivity
  have ha := arctan_ge_two_g ht.1.le
  unfold Ft
  linarith

/-- The exponent E is below pi/4, from display 3.2 on page 10. -/
theorem E_lt_pi_quarter {r : ℝ} (hr : 0 < r) : E r < π / 4 := by
  have hu := (radius_identity hr).1
  have hu0 : 0 < ups r := by linarith
  have ha : arccos (1 / ups r) < π / 2 :=
    arccos_lt_pi_div_two.mpr (by positivity)
  have hn : 0 ≤ (ups r - 1) / r := div_nonneg (by linarith) hr.le
  unfold E
  linarith

/-- Display 3.81 on page 29, obtained by multiplying display 3.79 by abs tau. -/
theorem exponent_cubic {τ δ : ℝ} (hτ : τ ≠ 0) (hδ : δ ≠ 0) :
    1 / 2 * (τ / (2 * π * δ)) ^ 2 * (1 - 5 / (48 * π ^ 4) * (τ / δ ^ 2) ^ 2) ≤
      E (|τ| / (π * δ) ^ 2) * |τ| := by
  have hr : 0 < |τ| / (π * δ) ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_right ((lemma_3_3 (|τ| / (π * δ) ^ 2) hr).1) (abs_nonneg τ)
  have ha4 : |τ| ^ 4 = τ ^ 4 := by
    calc |τ| ^ 4 = (|τ| ^ 2) ^ 2 := by ring
      _ = (τ ^ 2) ^ 2 := by rw [sq_abs]
      _ = τ ^ 4 := by ring
  have he : (|τ| / (π * δ) ^ 2 / 8 - 5 * (|τ| / (π * δ) ^ 2) ^ 3 / 384) * |τ| =
      1 / 2 * (τ / (2 * π * δ)) ^ 2 * (1 - 5 / (48 * π ^ 4) * (τ / δ ^ 2) ^ 2) := by
    field_simp
    ring_nf
    simp only [sq_abs, ha4]
    ring
  rwa [he] at h

end LeanLab.HelfgottMajor.Decomp123b
