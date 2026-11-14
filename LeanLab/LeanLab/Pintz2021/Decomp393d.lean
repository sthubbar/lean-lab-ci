import Mathlib

/-!
Elementary phase estimates in the written proof of the difference kernel tail.
Source: arXiv:1804.05561v1 page 12 Lemmas 4.5 and 4.6,
and pages 46 and 47 displays 12.3 to 12.11.
The interval lower endpoint here is X over four, as in display 12.3.
No estimate for the complete weighted kernel or exceptional zero mass is asserted.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Decomp393d

/-- The logarithmic phase has the derivative in display 12.5. -/
theorem phase_hasDerivAt (γ1 γ2 m y : ℝ) (hy : y ≠ 0) (hym : y + m ≠ 0) :
    HasDerivAt (fun t : ℝ => γ1 * Real.log t - γ2 * Real.log (t + m))
      (γ1 / y - γ2 / (y + m)) y := by
  have h1 : HasDerivAt (fun t : ℝ => γ1 * Real.log t) (γ1 / y) y := by
    simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log hy).const_mul γ1
  have h2 : HasDerivAt (fun t : ℝ => γ2 * Real.log (t + m)) (γ2 / (y + m)) y := by
    simpa only [div_eq_mul_inv, mul_one, one_mul, id_eq] using
      (((hasDerivAt_id y).add_const m).log hym).const_mul γ2
  exact h1.sub h2

/-- The rational form of the phase derivative exposes its unique stationary point. -/
theorem phase_fraction_identity (γ1 γ2 m y : ℝ) (hy : y ≠ 0) (hym : y + m ≠ 0) :
    γ1 / y - γ2 / (y + m) = (γ1 * m - (γ2 - γ1) * y) / (y * (y + m)) := by
  field_simp
  <;> ring

/-- Opposite frequency signs give the first lower bound in display 12.6. -/
theorem phase_opposite_sign_lower {γ1 γ2 m y X : ℝ}
    (hγ1 : 0 ≤ γ1) (hγ2 : γ2 ≤ 0) (hy : 0 < y) (hym : 0 < y + m)
    (hyX : y ≤ X) (hymX : y + m ≤ X) :
    max |γ1| |γ2| / X ≤ γ1 / y - γ2 / (y + m) := by
  have hX : 0 < X := hy.trans_le hyX
  rw [abs_of_nonneg hγ1, abs_of_nonpos hγ2]
  have hmax : max γ1 (-γ2) ≤ γ1 + (-γ2) := max_le (by linarith) (by linarith)
  have h1 := div_le_div_of_nonneg_left hγ1 hy hyX
  have h2 := div_le_div_of_nonneg_left (neg_nonneg.mpr hγ2) hym hymX
  calc
    _ ≤ (γ1 + (-γ2)) / X := div_le_div_of_nonneg_right hmax hX.le
    _ ≤ _ := by
      simp only [neg_div] at h2
      rw [add_div, neg_div]
      linarith

/-- Frequencies between zero and gamma one give the second bound in display 12.6. -/
theorem phase_same_sign_lower {γ1 γ2 m y X : ℝ}
    (hX : 0 < X) (hγ1 : 0 ≤ γ1) (hγ2 : 0 ≤ γ2) (hγ21 : γ2 ≤ γ1)
    (hm : X / 4 ≤ m) (hy : 0 < y) (hymX : y + m ≤ X) :
    γ1 / (4 * X) ≤ γ1 / y - γ2 / (y + m) := by
  have hm0 : 0 ≤ m := (by positivity : (0 : ℝ) ≤ X / 4).trans hm
  have hym : 0 < y + m := by linarith
  have hyX : y ≤ X := by linarith
  have hden : y * (y + m) ≤ X * X :=
    mul_le_mul hyX hymX hym.le hX.le
  have hnum : γ1 * (X / 4) ≤ γ1 * m := mul_le_mul_of_nonneg_left hm hγ1
  calc
    _ = (γ1 * (X / 4)) / (X * X) := by field_simp
    _ ≤ γ1 * m / (y * (y + m)) :=
      div_le_div₀ (mul_nonneg hγ1 hm0) hnum (mul_pos hy hym) hden
    _ = γ1 / y - γ1 / (y + m) := by field_simp; ring
    _ ≤ _ := by
      have hdiv := div_le_div_of_nonneg_right hγ21 hym.le
      linarith

/-- Nearby ordered frequencies give the third lower bound in display 12.6. -/
theorem phase_close_frequencies_lower {γ1 γ2 m y X : ℝ}
    (hX : 0 < X) (hγ1 : 0 ≤ γ1) (hγ12 : γ1 ≤ γ2) (hγ2 : γ2 ≤ (7 / 6 : ℝ) * γ1)
    (hm : X / 4 ≤ m) (hy : 0 < y) (hymX : y + m ≤ X) :
    γ2 / (7 * X) ≤ γ1 / y - γ2 / (y + m) := by
  have hm0 : 0 ≤ m := (by positivity : (0 : ℝ) ≤ X / 4).trans hm
  have hym : 0 < y + m := by linarith
  have hγ20 : 0 ≤ γ2 := hγ1.trans hγ12
  have hratio : (4 : ℝ) / (3 * (y + m)) ≤ 1 / y := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * (y + m)) hy).mpr
    nlinarith
  have hmain := mul_le_mul_of_nonneg_left hratio hγ1
  have hcoef : γ2 / 7 ≤ 4 * γ1 / 3 - γ2 := by linarith
  calc
    _ ≤ γ2 / (7 * (y + m)) :=
      div_le_div_of_nonneg_left hγ20 (by positivity) (by linarith)
    _ = (γ2 / 7) / (y + m) := by rw [div_div]
    _ ≤ (4 * γ1 / 3 - γ2) / (y + m) :=
      div_le_div_of_nonneg_right hcoef hym.le
    _ = γ1 * (4 / (3 * (y + m))) - γ2 / (y + m) := by field_simp
    _ ≤ _ := by simpa only [← mul_div_assoc, mul_one] using sub_le_sub_right hmain (γ2 / (y + m))

/-- All three nonstationary frequency cases have the common denominator seven X. -/
theorem phase_small_frequency_ratio_lower {γ1 γ2 m y X : ℝ}
    (hX : 0 < X) (hγ1 : 0 ≤ γ1) (hγ2 : γ2 ≤ (7 / 6 : ℝ) * γ1)
    (hm : X / 4 ≤ m) (hy : 0 < y) (hymX : y + m ≤ X) :
    max |γ1| |γ2| / (7 * X) ≤ γ1 / y - γ2 / (y + m) := by
  have hm0 : 0 ≤ m := (by positivity : (0 : ℝ) ≤ X / 4).trans hm
  have hym : 0 < y + m := by linarith
  by_cases hneg : γ2 ≤ 0
  · apply le_trans _ (phase_opposite_sign_lower hγ1 hneg hy hym (by linarith) hymX)
    exact div_le_div_of_nonneg_left (le_max_of_le_left (abs_nonneg _)) hX (by linarith)
  · have hγ20 : 0 ≤ γ2 := (lt_of_not_ge hneg).le
    rw [abs_of_nonneg hγ1, abs_of_nonneg hγ20]
    by_cases hle : γ2 ≤ γ1
    · rw [max_eq_left hle]
      apply le_trans _ (phase_same_sign_lower hX hγ1 hγ20 hle hm hy hymX)
      exact div_le_div_of_nonneg_left hγ1 (by positivity) (by linarith)
    · rw [max_eq_right (le_of_lt (lt_of_not_ge hle))]
      exact phase_close_frequencies_lower hX hγ1 (le_of_lt (lt_of_not_ge hle)) hγ2 hm hy hymX

/-- Left of the stationary window the derivative exceeds D over X. -/
theorem phase_left_of_window {γ1 γ2 m y X D : ℝ}
    (hX : 0 < X) (hD : 0 < D) (hy : 0 < y) (hym : 0 < y + m)
    (hden : y * (y + m) ≤ X * X) (hγ : γ1 < γ2)
    (hout : y < (m * γ1 - D * X) / (γ2 - γ1)) :
    D / X < γ1 / y - γ2 / (y + m) := by
  have hnum : D * X < γ1 * m - (γ2 - γ1) * y := by
    have := (lt_div_iff₀ (sub_pos.mpr hγ)).mp hout
    nlinarith
  have hbase : D / X ≤ D * X / (y * (y + m)) := by
    apply (div_le_div_iff₀ hX (mul_pos hy hym)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden hD.le]
  rw [phase_fraction_identity _ _ _ _ hy.ne' hym.ne']
  exact hbase.trans_lt (div_lt_div_of_pos_right hnum (mul_pos hy hym))

/-- Right of the stationary window the derivative is below minus D over X. -/
theorem phase_right_of_window {γ1 γ2 m y X D : ℝ}
    (hX : 0 < X) (hD : 0 < D) (hy : 0 < y) (hym : 0 < y + m)
    (hden : y * (y + m) ≤ X * X) (hγ : γ1 < γ2)
    (hout : (m * γ1 + D * X) / (γ2 - γ1) < y) :
    γ1 / y - γ2 / (y + m) < -D / X := by
  have hnum : γ1 * m - (γ2 - γ1) * y < -(D * X) := by
    have := (div_lt_iff₀ (sub_pos.mpr hγ)).mp hout
    nlinarith
  have hbase : D / X ≤ D * X / (y * (y + m)) := by
    apply (div_le_div_iff₀ hX (mul_pos hy hym)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden hD.le]
  rw [phase_fraction_identity _ _ _ _ hy.ne' hym.ne']
  have hlt := div_lt_div_of_pos_right hnum (mul_pos hy hym)
  rw [neg_div] at hlt ⊢
  exact hlt.trans_le (neg_le_neg hbase)

/-- The positive source interval bounds the absolute derivative by eight M over X. -/
theorem phase_abs_derivative_le {γ1 γ2 m y X M : ℝ}
    (hX : 0 < X) (hm : 0 ≤ m) (hy : X / 4 ≤ y)
    (hγ1 : |γ1| ≤ M) (hγ2 : |γ2| ≤ M) :
    |γ1 / y - γ2 / (y + m)| ≤ 8 * M / X := by
  have hq : 0 < X / 4 := by positivity
  have hy0 : 0 < y := hq.trans_le hy
  have hym : 0 < y + m := by linarith
  have hM : 0 ≤ M := (abs_nonneg γ1).trans hγ1
  calc
    _ ≤ |γ1 / y| + |γ2 / (y + m)| := abs_sub _ _
    _ = |γ1| / y + |γ2| / (y + m) := by
      rw [abs_div, abs_div, abs_of_pos hy0, abs_of_pos hym]
    _ ≤ M / (X / 4) + M / (X / 4) :=
      add_le_add (div_le_div₀ hM hγ1 hq hy)
        (div_le_div₀ hM hγ2 hq (by linarith))
    _ = _ := by field_simp; ring

/-- Exceptional heights at most square root X give an absolute derivative bound. -/
theorem phase_abs_derivative_le_sqrt {γ1 γ2 m y X : ℝ}
    (hX : 0 < X) (hm : 0 ≤ m) (hy : X / 4 ≤ y)
    (hγ1 : |γ1| ≤ Real.sqrt X) (hγ2 : |γ2| ≤ Real.sqrt X) :
    |γ1 / y - γ2 / (y + m)| ≤ 8 / Real.sqrt X := by
  apply (phase_abs_derivative_le hX hm hy hγ1 hγ2).trans_eq
  apply (div_eq_div_iff hX.ne' (Real.sqrt_pos.mpr hX).ne').mpr
  nlinarith [Real.sq_sqrt hX.le]

/-- Above X equal to 256 the phase derivative has absolute value at most one half. -/
theorem phase_abs_derivative_le_half {γ1 γ2 m y X : ℝ}
    (hX : 256 ≤ X) (hm : 0 ≤ m) (hy : X / 4 ≤ y)
    (hγ1 : |γ1| ≤ Real.sqrt X) (hγ2 : |γ2| ≤ Real.sqrt X) :
    |γ1 / y - γ2 / (y + m)| ≤ 1 / 2 := by
  have hX0 : 0 < X := by linarith
  apply (phase_abs_derivative_le_sqrt hX0 hm hy hγ1 hγ2).trans
  have hs : 16 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0.le).mpr (by linarith)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hX0)).mpr
  linarith

/-- The stationary window has length at most fourteen X over square root gamma two. -/
theorem stationary_window_length_le {γ1 γ2 X : ℝ} (m : ℝ)
    (hγ1 : 0 ≤ γ1) (hγ2 : (7 / 6 : ℝ) * γ1 < γ2) (hX : 0 ≤ X) :
    (m * γ1 + Real.sqrt γ2 * X) / (γ2 - γ1) -
      (m * γ1 - Real.sqrt γ2 * X) / (γ2 - γ1) ≤ 14 * X / Real.sqrt γ2 := by
  have hg : 0 < γ2 := by linarith
  have hgap : γ2 / 7 ≤ γ2 - γ1 := by linarith
  have hs : 0 < Real.sqrt γ2 := Real.sqrt_pos.mpr hg
  calc
    _ = (2 * Real.sqrt γ2 * X) / (γ2 - γ1) := by ring
    _ ≤ (2 * Real.sqrt γ2 * X) / (γ2 / 7) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hgap
    _ = _ := by
      apply (div_eq_div_iff (by positivity : γ2 / 7 ≠ 0) hs.ne').mpr
      have heq := congrArg (fun t : ℝ => t * X) (Real.sq_sqrt hg.le)
      nlinarith

/-- A trivial X majorant cannot give a uniform square root saving in the source height range. -/
theorem trivial_X_bound_insufficient (C : ℝ) (hC : 0 < C) :
    ∃ X M : ℝ, 0 < X ∧ 1 ≤ M ∧ M ≤ Real.sqrt X ∧
      C * (X / Real.sqrt M) < X := by
  let M : ℝ := (C + 1) ^ 2
  let X : ℝ := M ^ 2
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
  have hM0 : 0 < M := by linarith
  have hX : 0 < X := by dsimp [X]; positivity
  refine ⟨X, M, hX, hM, ?_, ?_⟩
  · dsimp [X]
    rw [Real.sqrt_sq hM0.le]
  · have hs : Real.sqrt M = C + 1 := by
      dsimp [M]
      exact Real.sqrt_sq (by linarith)
    rw [hs, ← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr
    calc
      C * X < (C + 1) * X := mul_lt_mul_of_pos_right (by linarith) hX
      _ = X * (C + 1) := mul_comm _ _

/-- Differentiating the phase derivative gives its curvature. -/
theorem phase_derivative_hasDerivAt (γ1 γ2 m y : ℝ) (hy : y ≠ 0) (hym : y + m ≠ 0) :
    HasDerivAt (fun t : ℝ => γ1 / t - γ2 / (t + m))
      (-γ1 / y ^ 2 + γ2 / (y + m) ^ 2) y := by
  have h1 : HasDerivAt (fun t : ℝ => γ1 / t) (-γ1 / y ^ 2) y := by
    convert! (hasDerivAt_const y γ1).div (hasDerivAt_id y) hy using 1 <;> simp [Pi.div_apply, id_eq]
  have h2 : HasDerivAt (fun t : ℝ => γ2 / (t + m)) (-γ2 / (y + m) ^ 2) y := by
    convert! (hasDerivAt_const y γ2).div ((hasDerivAt_id y).add_const m) hym using 1 <;> simp [Pi.div_apply, id_eq]
  convert! h1.sub h2 using 1 <;> simp [neg_div, sub_neg_eq_add, Pi.sub_apply]

/-- In the remaining frequency case the curvature changes sign at one explicit point. -/
theorem phase_curvature_signs {γ1 γ2 m y : ℝ}
    (hγ1 : 0 ≤ γ1) (hγ2 : γ1 < γ2) (hm : 0 ≤ m) (hy : 0 < y) :
    (0 ≤ -γ1 / y ^ 2 + γ2 / (y + m) ^ 2 ↔
      m * Real.sqrt γ1 / (Real.sqrt γ2 - Real.sqrt γ1) ≤ y) ∧
    (-γ1 / y ^ 2 + γ2 / (y + m) ^ 2 ≤ 0 ↔
      y ≤ m * Real.sqrt γ1 / (Real.sqrt γ2 - Real.sqrt γ1)) := by
  have hγ20 : 0 ≤ γ2 := hγ1.trans hγ2.le
  have hym : 0 < y + m := by linarith
  have hgap : 0 < Real.sqrt γ2 - Real.sqrt γ1 :=
    sub_pos.mpr (Real.sqrt_lt_sqrt hγ1 hγ2)
  have hA : 0 ≤ Real.sqrt γ1 * (y + m) := mul_nonneg (Real.sqrt_nonneg _) hym.le
  have hB : 0 ≤ Real.sqrt γ2 * y := mul_nonneg (Real.sqrt_nonneg _) hy.le
  have hAB : γ1 * (y + m) ^ 2 ≤ γ2 * y ^ 2 ↔
      Real.sqrt γ1 * (y + m) ≤ Real.sqrt γ2 * y := by
    rw [← sq_le_sq₀ hA hB, mul_pow, mul_pow, Real.sq_sqrt hγ1, Real.sq_sqrt hγ20]
  have hBA : γ2 * y ^ 2 ≤ γ1 * (y + m) ^ 2 ↔
      Real.sqrt γ2 * y ≤ Real.sqrt γ1 * (y + m) := by
    rw [← sq_le_sq₀ hB hA, mul_pow, mul_pow, Real.sq_sqrt hγ20, Real.sq_sqrt hγ1]
  have hform : -γ1 / y ^ 2 + γ2 / (y + m) ^ 2 =
      γ2 / (y + m) ^ 2 - γ1 / y ^ 2 := by ring
  constructor
  · rw [hform, sub_nonneg, div_le_div_iff₀ (sq_pos_of_pos hy) (sq_pos_of_pos hym), hAB,
      div_le_iff₀ hgap]
    constructor <;> intro h <;> nlinarith
  · rw [hform, sub_nonpos, div_le_div_iff₀ (sq_pos_of_pos hym) (sq_pos_of_pos hy), hBA,
      le_div_iff₀ hgap]
    constructor <;> intro h <;> nlinarith

/-- The phase derivative is monotone above its curvature transition on every positive interval. -/
theorem phase_derivative_monotone {γ1 γ2 m a b : ℝ}
    (hγ1 : 0 ≤ γ1) (hγ2 : γ1 < γ2) (hm : 0 ≤ m) (ha : 0 < a)
    (hroot : m * Real.sqrt γ1 / (Real.sqrt γ2 - Real.sqrt γ1) ≤ a) :
    MonotoneOn (fun y : ℝ => γ1 / y - γ2 / (y + m)) (Set.Icc a b) := by
  have hd : ∀ y ∈ Set.Icc a b, HasDerivAt (fun t : ℝ => γ1 / t - γ2 / (t + m))
      (-γ1 / y ^ 2 + γ2 / (y + m) ^ 2) y := by
    intro y hy
    exact phase_derivative_hasDerivAt _ _ _ _ (ne_of_gt (ha.trans_le hy.1))
      (ne_of_gt (by linarith [hy.1]))
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
  intro y hy
  have hmem := interior_subset hy
  rw [(hd y hmem).deriv]
  exact (phase_curvature_signs hγ1 hγ2 hm (ha.trans_le hmem.1)).1.mpr (hroot.trans hmem.1)

/-- The phase derivative is antitone below its curvature transition on every positive interval. -/
theorem phase_derivative_antitone {γ1 γ2 m a b : ℝ}
    (hγ1 : 0 ≤ γ1) (hγ2 : γ1 < γ2) (hm : 0 ≤ m) (ha : 0 < a)
    (hroot : b ≤ m * Real.sqrt γ1 / (Real.sqrt γ2 - Real.sqrt γ1)) :
    AntitoneOn (fun y : ℝ => γ1 / y - γ2 / (y + m)) (Set.Icc a b) := by
  have hd : ∀ y ∈ Set.Icc a b, HasDerivAt (fun t : ℝ => γ1 / t - γ2 / (t + m))
      (-γ1 / y ^ 2 + γ2 / (y + m) ^ 2) y := by
    intro y hy
    exact phase_derivative_hasDerivAt _ _ _ _ (ne_of_gt (ha.trans_le hy.1))
      (ne_of_gt (by linarith [hy.1]))
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
  intro y hy
  have hmem := interior_subset hy
  rw [(hd y hmem).deriv]
  exact (phase_curvature_signs hγ1 hγ2 hm (ha.trans_le hmem.1)).2.mpr (hmem.2.trans hroot)

/-- A general positive lower cutoff gives an absolute phase derivative bound. -/
theorem phase_abs_derivative_le_cutoff {γ1 γ2 m y Y M : ℝ}
    (hY : 0 < Y) (hm : 0 ≤ m) (hy : Y ≤ y)
    (hγ1 : |γ1| ≤ M) (hγ2 : |γ2| ≤ M) :
    |γ1 / y - γ2 / (y + m)| ≤ 2 * M / Y := by
  have hb := phase_abs_derivative_le (X := 4 * Y) (by positivity) hm
    (by simpa using hy) hγ1 hγ2
  convert hb using 1 <;> field_simp <;> ring

/-- The original power cutoff exceeds four square root X at every sufficiently large scale. -/
theorem power_cutoff_eventually_large {ε : ℝ} (hε : ε < 1 / 2) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X → 4 * Real.sqrt X ≤ X ^ (1 - ε) := by
  have hδ : 0 < (1 / 2 : ℝ) - ε := by linarith
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop 4)
  refine ⟨max B 1, le_max_right _ _, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := by linarith
  have hscale : (4 : ℝ) ≤ X ^ ((1 / 2 : ℝ) - ε) := hB X ((le_max_left _ _).trans hX)
  have heq : X ^ (1 - ε) = Real.sqrt X * X ^ ((1 / 2 : ℝ) - ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXp]
    congr 1 <;> ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hscale (Real.sqrt_nonneg X)
  linarith

/-- The absolute derivative bound also holds at the original power cutoff once it is large. -/
theorem phase_abs_derivative_le_half_of_cutoff {γ1 γ2 m y X Y : ℝ}
    (hX : 0 < X) (hm : 0 ≤ m) (hy : Y ≤ y) (hY : 4 * Real.sqrt X ≤ Y)
    (hγ1 : |γ1| ≤ Real.sqrt X) (hγ2 : |γ2| ≤ Real.sqrt X) :
    |γ1 / y - γ2 / (y + m)| ≤ 1 / 2 := by
  have hYp : 0 < Y := (by positivity : (0 : ℝ) < 4 * Real.sqrt X).trans_le hY
  apply (phase_abs_derivative_le_cutoff hYp hm hy hγ1 hγ2).trans
  apply (div_le_iff₀ hYp).mpr
  linarith

end LeanLab.Pintz2021.Decomp393d

#print axioms LeanLab.Pintz2021.Decomp393d.phase_hasDerivAt
#print axioms LeanLab.Pintz2021.Decomp393d.phase_fraction_identity
#print axioms LeanLab.Pintz2021.Decomp393d.phase_opposite_sign_lower
#print axioms LeanLab.Pintz2021.Decomp393d.phase_same_sign_lower
#print axioms LeanLab.Pintz2021.Decomp393d.phase_close_frequencies_lower
#print axioms LeanLab.Pintz2021.Decomp393d.phase_small_frequency_ratio_lower
#print axioms LeanLab.Pintz2021.Decomp393d.phase_left_of_window
#print axioms LeanLab.Pintz2021.Decomp393d.phase_right_of_window

#print axioms LeanLab.Pintz2021.Decomp393d.phase_abs_derivative_le

#print axioms LeanLab.Pintz2021.Decomp393d.phase_abs_derivative_le_sqrt

#print axioms LeanLab.Pintz2021.Decomp393d.phase_abs_derivative_le_half

#print axioms LeanLab.Pintz2021.Decomp393d.stationary_window_length_le

#print axioms LeanLab.Pintz2021.Decomp393d.trivial_X_bound_insufficient

#print axioms LeanLab.Pintz2021.Decomp393d.phase_derivative_hasDerivAt

#print axioms LeanLab.Pintz2021.Decomp393d.phase_curvature_signs

#print axioms LeanLab.Pintz2021.Decomp393d.phase_derivative_monotone

#print axioms LeanLab.Pintz2021.Decomp393d.phase_derivative_antitone

#print axioms LeanLab.Pintz2021.Decomp393d.phase_abs_derivative_le_cutoff

#print axioms LeanLab.Pintz2021.Decomp393d.power_cutoff_eventually_large

#print axioms LeanLab.Pintz2021.Decomp393d.phase_abs_derivative_le_half_of_cutoff
