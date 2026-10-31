/- AI wrote the Lean code for CODEX task164.
Journal Lemma 8, pp. 1222 to 1226. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148b
import LeanLab.BS2022GRH.Decomp148c
namespace LeanLab.BS2022GRH.DecompC164b
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp148b Decomp148c
/-- Positivity of the printed coefficient on the Lemma 8 range, p. 1222. -/
theorem qG_positive (Y : ℝ) (hY : 25 ≤ Y) : 0 < qG Y := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hl : 1 ≤ log Y := by
    rw [le_log_iff_exp_le hY0]
    linarith [exp_one_lt_d9]
  have hll : 0 ≤ log (log Y) := log_nonneg hl
  have h4 : 0 < Y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hY0 _
  have hs : Y ^ (1 / 4 : ℝ) ≤ √Y := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hneg : 237.934 / (√Y * log Y) ≤ 939.260 / (Y ^ (1 / 4 : ℝ) * log Y) := by
    apply div_le_div₀ (by norm_num) (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_right hs (by linarith)
  have hrest : 0 ≤ 12.683 / log Y + 254.980 / log Y ^ 2 + 2607.854 / log Y ^ 3 +
      11605.056 / log Y ^ 4 + 1.314 * log Y / Y ^ (1 / 4 : ℝ) +
      0.092 * log (log Y) / Y ^ (1 / 4 : ℝ) + 60.883 / Y ^ (1 / 4 : ℝ) +
      8.250 * log (log Y) / (Y ^ (1 / 4 : ℝ) * log Y) := by positivity
  unfold qG
  linarith
/-- The cube root cutoff in separated powers, p. 1226. -/
theorem cutoff_powers (Y : ℝ) (hY : 25 ≤ Y) :
    cutoff Y = Y ^ (1 / 6 : ℝ) /
      ((2 * qG Y * log 2) ^ (1 / 3 : ℝ) * log Y ^ (1 / 3 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hq : 0 < qG Y := qG_positive Y hY
  have hl : 0 < log Y := log_pos (by linarith)
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  unfold cutoff
  rw [div_rpow (sqrt_nonneg Y) (by positivity), sqrt_eq_rpow,
    ← rpow_mul hY0.le]
  have he : (1 / 2 : ℝ) * (1 / 3) = 1 / 6 := by norm_num
  rw [he]
  have hb : 2 * log 2 * qG Y * log Y = (2 * qG Y * log 2) * log Y := by ring
  rw [hb, mul_rpow (by positivity) hl.le]
/-- The balanced coefficient expressed using the common cube root, p. 1226. -/
theorem balance_powers (X Y D : ℝ) (hY : 25 ≤ Y) :
    balance X Y D = (2 * qG Y * log 2) ^ (1 / 3 : ℝ) *
      (X ^ (1 / 2 : ℝ) * Y ^ (1 / 3 : ℝ) * log Y ^ (1 / 3 : ℝ)) /
        (2 * log 2 * D) := by
  have hq : 0 < qG Y := qG_positive Y hY
  have h2 : 0 < (2 : ℝ) * log 2 := by positivity
  have he : (2 * log 2) ^ (-(2 / 3) : ℝ) = (2 * log 2) ^ (1 / 3 : ℝ) / (2 * log 2) := by
    convert rpow_sub_one h2.ne' (1 / 3 : ℝ) using 1 <;> norm_num
  unfold balance
  rw [he]
  have hp : (2 * qG Y * log 2) ^ (1 / 3 : ℝ) =
      qG Y ^ (1 / 3 : ℝ) * (2 * log 2) ^ (1 / 3 : ℝ) := by
    rw [show 2 * qG Y * log 2 = qG Y * (2 * log 2) by ring,
      mul_rpow hq.le h2.le]
  rw [hp]
  ring
/-- LEAF. Exact normalization of display 13 to display 17, p. 1226.
This isolates real power algebra from the analytic conductor estimates. -/
theorem small_identity (X Y D : ℝ) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hD : 1 < D) (hDX : D < √(X * Y))
    (hbal : √(X * Y) / D ≤ cutoff Y) (hcutD : cutoff Y ≤ D) :
    smallBound X Y D (cutoff Y) = smallCoeff X Y D * scale X Y D := by
  have hx : 0 < X := by linarith
  have hy : 0 < Y := by linarith
  have hd : D ≠ 0 := by linarith
  have h2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  have hq : 0 < qG Y := qG_positive Y hY
  have hl : 0 < log Y := log_pos (by linarith)
  have hb : 0 < 2 * qG Y * log 2 := by positivity
  have hy3 : (Y ^ (1 / 6 : ℝ)) ^ 3 = √Y := by
    rw [← rpow_natCast, ← rpow_mul hy.le, sqrt_eq_rpow]
    norm_num
  have hy2 : (Y ^ (1 / 6 : ℝ)) ^ 2 = Y ^ (1 / 3 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hy.le]
    norm_num
  have hl2 : (log Y ^ (1 / 3 : ℝ)) ^ 2 = log Y ^ (2 / 3 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hl.le]
    norm_num
  have hl3 : (log Y ^ (1 / 3 : ℝ)) ^ 3 = log Y := by
    rw [← rpow_natCast, ← rpow_mul hl.le]
    norm_num
  have hk3 : ((2 * qG Y * log 2) ^ (1 / 3 : ℝ)) ^ 3 = 2 * qG Y * log 2 := by
    rw [← rpow_natCast, ← rpow_mul hb.le]
    norm_num
  have hn2 : (2 * qG Y * log 2) ^ (-(2 / 3) : ℝ) =
      (((2 * qG Y * log 2) ^ (1 / 3 : ℝ)) ^ 2)⁻¹ := by
    rw [rpow_neg hb.le]
    congr 1
    rw [← rpow_natCast, ← rpow_mul hb.le]
    norm_num
  have hn1 : (2 * qG Y * log 2) ^ (-(1 / 3) : ℝ) =
      ((2 * qG Y * log 2) ^ (1 / 3 : ℝ))⁻¹ := rpow_neg hb.le _
  have hM : Mphi0 Y = Mphi (cutoff Y) := rfl
  unfold smallBound smallCoeff scale
  rw [hM, balance_powers X Y D hY, hn2, hn1]
  rw [cutoff_powers Y hY, sqrt_mul hx.le Y, ← hy3, ← hy2, ← hl2, ← sqrt_eq_rpow]
  generalize hk : (2 * qG Y * log 2) ^ (1 / 3 : ℝ) = k at *
  generalize hys : Y ^ (1 / 6 : ℝ) = y at *
  generalize hls : log Y ^ (1 / 3 : ℝ) = l at *
  generalize hxs : √X = x at *
  have hx2 : X = x ^ 2 := by rw [← hxs, sq_sqrt hx.le]
  have hqe : qG Y = k ^ 3 / (2 * log 2) := by
    rw [hk3]
    field_simp
    <;> ring
  rw [hx2, hqe, ← hl3]
  have hk0 : k ≠ 0 := by rw [← hk]; positivity
  have hy0 : y ≠ 0 := by rw [← hys]; positivity
  have hl0 : l ≠ 0 := by rw [← hls]; positivity
  by_cases hh : log (log D) = 0
  · simp only [hh, mul_zero, div_zero, mul_zero, add_zero]
    field_simp [hk0, hy0, hl0]
    <;> ring
  · field_simp [hk0, hy0, hl0]
    <;> ring

/-- LEAF. Exact normalization of display 16 to display 18, p. 1226.
The chosen cutoff makes the final reciprocal term equal to balance. -/
theorem large_identity (X Y D : ℝ) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hD : 1 < D) (hDX : D < √(X * Y))
    (hbal : √(X * Y) / D ≤ cutoff Y) (hcutD : cutoff Y ≤ D) :
    largeBound X Y D (cutoff Y) = largeCoeff X Y D * scale X Y D := by
  have hx : 0 < X := by linarith
  have hy : 0 < Y := by linarith
  have hd : D ≠ 0 := by linarith
  have h2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  have hq : 0 < qG Y := qG_positive Y hY
  have hl : 0 < log Y := log_pos (by linarith)
  have hy3 : (Y ^ (1 / 6 : ℝ)) ^ 3 = √Y := by
    rw [← rpow_natCast, ← rpow_mul hy.le, sqrt_eq_rpow]
    norm_num
  have hy2 : (Y ^ (1 / 6 : ℝ)) ^ 2 = Y ^ (1 / 3 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hy.le]
    norm_num
  have hxy : X * Y = (√X * √Y) ^ 2 := by
    rw [mul_pow, sq_sqrt hx.le, sq_sqrt hy.le]
  unfold largeBound largeCoeff scale
  rw [balance_powers X Y D hY, cutoff_powers Y hY]
  rw [sqrt_mul hx.le Y, hxy, ← hy3, ← hy2, ← sqrt_eq_rpow]
  field_simp
  <;> ring

/-- Exact existing Lemma8J from conductor reduction and the two normalizations.
The cited character and large sieve estimates remain OPEN in Decomp148. -/
theorem lemma8J : Lemma8J := by
  intro hG c X Y Z D a hc hX hY hZ hZY hD hDX hbal hcutD ha
  have hcut : 1 < cutoff Y :=
    lt_of_lt_of_le ((one_lt_div (by linarith : 0 < D)).2 hDX) hbal
  have hs := (small_at_cutoff hG c X Y Z D a hc hX hY hZ hZY hD hcut hcutD hbal ha).trans
    ((small_identity X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _))).le)
  have hl := (large_at_cutoff c X Y Z D a hc hX hY hZ hZY hD hDX hcut hcutD hbal ha).trans
    ((large_identity X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _))).le)
  calc bilinear c X Y Z D a
      ≤ smallMass c X Y Z D (cutoff Y) a + largeMass c X Y Z D (cutoff Y) a :=
        split_reduction c X Y Z D (cutoff Y) a hD ha
    _ ≤ smallCoeff X Y D * scale X Y D + largeCoeff X Y D * scale X Y D := add_le_add hs hl
    _ = mJ X Y D * scale X Y D := by rw [mJ, add_mul]
end LeanLab.BS2022GRH.DecompC164b
#print axioms LeanLab.BS2022GRH.DecompC164b.qG_positive
#print axioms LeanLab.BS2022GRH.DecompC164b.cutoff_powers
#print axioms LeanLab.BS2022GRH.DecompC164b.balance_powers
#print axioms LeanLab.BS2022GRH.DecompC164b.small_identity
#print axioms LeanLab.BS2022GRH.DecompC164b.large_identity
#print axioms LeanLab.BS2022GRH.DecompC164b.lemma8J
