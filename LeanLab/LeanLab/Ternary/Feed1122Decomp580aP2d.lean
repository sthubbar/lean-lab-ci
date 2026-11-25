/-
Arithmetic half of the LEAF `prop52_farey_arcs_le_circle`, burst-20261122 session S144 wave 2.
Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, page 35: the arcs around
`b/q` of half width `δ₀Q/2qx` for odd `q ≤ Q` and `δ₀Q/qx` for even `q ≤ 2Q` do not overlap,
because distinct fractions are `1/qq'` apart, or `2/qq'` apart when both denominators are even,
and `δ₀Q² = x/2` for `Q = √(x/2δ₀)`. Both facts are PROVED here; the measure step that turns
them into the LEAF stays open in `Feed1122Decomp580aP2c.lean`.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp580aP2c

namespace LeanLab.Ternary.Task580

/-- Separation of distinct fractions, Helfgott 1312.7748v2 page 35:
`|u/q − v/q'| ≥ 1/qq'` when `uq' ≠ vq`. The shift by an integer `k` is covered by taking
`v = b' + kq'`. -/
theorem farey_separation (u v : ℤ) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hne : u * q' ≠ v * q) :
    1 / ((q : ℝ) * q') ≤ |(u : ℝ) / q - (v : ℝ) / q'| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hd : (u : ℝ) / q - (v : ℝ) / q' = ((u * q' - v * q : ℤ) : ℝ) / ((q : ℝ) * q') := by
    push_cast; field_simp
  have hint : (1 : ℝ) ≤ |((u * q' - v * q : ℤ) : ℝ)| := by
    have h0 : u * q' - v * q ≠ 0 := sub_ne_zero.mpr hne
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs h0
  rw [hd, abs_div, abs_of_pos (mul_pos hqr hqr')]
  exact div_le_div_of_nonneg_right hint (mul_pos hqr hqr').le

/-- Separation of distinct fractions with even denominators, Helfgott 1312.7748v2 page 35:
`|u/q − v/q'| ≥ 2/qq'` when `q, q'` are even and `uq' ≠ vq`, since `uq' − vq` is even. -/
theorem farey_separation_even (u v : ℤ) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (he : Even q) (he' : Even q') (hne : u * q' ≠ v * q) :
    2 / ((q : ℝ) * q') ≤ |(u : ℝ) / q - (v : ℝ) / q'| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hd : (u : ℝ) / q - (v : ℝ) / q' = ((u * q' - v * q : ℤ) : ℝ) / ((q : ℝ) * q') := by
    push_cast; field_simp
  have hint : (2 : ℝ) ≤ |((u * q' - v * q : ℤ) : ℝ)| := by
    have h0 : u * q' - v * q ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨r, hr⟩ := he
    obtain ⟨r', hr'⟩ := he'
    have hev : u * q' - v * q = 2 * (u * r' - v * r) := by
      rw [hr, hr']; push_cast; ring
    have h1 : u * r' - v * r ≠ 0 := by
      intro h; apply h0; rw [hev, h]; ring
    rw [← Int.cast_abs, hev, abs_mul]
    have := Int.one_le_abs h1
    have h2 : (2 : ℤ) ≤ |(2 : ℤ)| * |u * r' - v * r| := by
      rw [abs_two]; linarith
    exact_mod_cast h2
  rw [hd, abs_div, abs_of_pos (mul_pos hqr hqr')]
  exact div_le_div_of_nonneg_right hint (mul_pos hqr hqr').le

/-- The identity `δ₀Q² = x/2` for `Q = √(x/2δ₀)`, Helfgott 1312.7748v2 page 33. -/
theorem delta_Q_sq (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) :
    δ * Real.sqrt (x / (2 * δ)) ^ 2 = x / 2 := by
  rw [Real.sq_sqrt (by positivity)]; field_simp

/-- Width budget for two odd denominators, Helfgott 1312.7748v2 page 35:
`δ₀Q/2qx + δ₀Q/2q'x ≤ 1/qq'` for `q, q' ≤ Q`. -/
theorem farey_width_odd_odd (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hqQ : (q : ℝ) ≤ Real.sqrt (x / (2 * δ)))
    (hqQ' : (q' : ℝ) ≤ Real.sqrt (x / (2 * δ))) :
    δ * Real.sqrt (x / (2 * δ)) / (2 * q * x) + δ * Real.sqrt (x / (2 * δ)) / (2 * q' * x) ≤
      1 / ((q : ℝ) * q') := by
  set Q := Real.sqrt (x / (2 * δ))
  have hQ2 := delta_Q_sq x δ hx hδ
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have e : δ * Q / (2 * q * x) + δ * Q / (2 * q' * x) =
      δ * Q * (q + q') / (2 * x) * (1 / ((q : ℝ) * q')) := by
    field_simp; try ring
  rw [e]
  apply mul_le_of_le_one_left (by positivity)
  rw [div_le_one (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hqQ hqQ') (mul_nonneg hδ.le hQ0)]

/-- Width budget for an odd `q ≤ Q` against an even `q' ≤ 2Q`, Helfgott 1312.7748v2 page 35:
`δ₀Q/2qx + δ₀Q/q'x ≤ 1/qq'`. -/
theorem farey_width_odd_even (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hqQ : (q : ℝ) ≤ Real.sqrt (x / (2 * δ)))
    (hqQ' : (q' : ℝ) ≤ 2 * Real.sqrt (x / (2 * δ))) :
    δ * Real.sqrt (x / (2 * δ)) / (2 * q * x) + δ * Real.sqrt (x / (2 * δ)) / (q' * x) ≤
      1 / ((q : ℝ) * q') := by
  set Q := Real.sqrt (x / (2 * δ))
  have hQ2 := delta_Q_sq x δ hx hδ
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have e : δ * Q / (2 * q * x) + δ * Q / (q' * x) =
      δ * Q * (q' + 2 * q) / (2 * x) * (1 / ((q : ℝ) * q')) := by
    field_simp; try ring
  rw [e]
  apply mul_le_of_le_one_left (by positivity)
  rw [div_le_one (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hqQ' (mul_le_mul_of_nonneg_left hqQ
    (by norm_num : (0:ℝ) ≤ 2))) (mul_nonneg hδ.le hQ0)]

/-- Width budget for two even denominators `q, q' ≤ 2Q`, Helfgott 1312.7748v2 page 35:
`δ₀Q/qx + δ₀Q/q'x ≤ 2/qq'`. -/
theorem farey_width_even_even (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hqQ : (q : ℝ) ≤ 2 * Real.sqrt (x / (2 * δ)))
    (hqQ' : (q' : ℝ) ≤ 2 * Real.sqrt (x / (2 * δ))) :
    δ * Real.sqrt (x / (2 * δ)) / (q * x) + δ * Real.sqrt (x / (2 * δ)) / (q' * x) ≤
      2 / ((q : ℝ) * q') := by
  set Q := Real.sqrt (x / (2 * δ))
  have hQ2 := delta_Q_sq x δ hx hδ
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have e : δ * Q / (q * x) + δ * Q / (q' * x) =
      δ * Q * (q + q') / (2 * x) * (2 / ((q : ℝ) * q')) := by
    field_simp; try ring
  rw [e]
  apply mul_le_of_le_one_left (by positivity)
  rw [div_le_one (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hqQ hqQ') (mul_nonneg hδ.le hQ0)]

end LeanLab.Ternary.Task580
