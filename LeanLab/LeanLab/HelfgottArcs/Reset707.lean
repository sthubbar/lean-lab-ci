/-
An error preserving approximation reset for P0013 page 70.
Every statement here is a derived elementary input.
The strict eight y inference is not assumed. The analytic leaves remain open.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.ResetInterior325

namespace LeanLab.HelfgottArcs.Decomp119

/-- A reduced fraction and a fraction with smaller positive denominator have determinant of absolute value at least one.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem reset_determinant_lower707 (a b : ℤ) (q r : ℕ) (hr : 0 < r) (hrq : r < q) (ha : Int.gcd a q = 1) :
    (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by
  have hne : a * (r : ℤ) - b * (q : ℤ) ≠ 0 := by
    intro he
    have hd : (q : ℤ) ∣ a * (r : ℤ) := by
      rw [sub_eq_zero.mp he]
      exact dvd_mul_left _ _
    have hcop : Int.gcd (q : ℤ) a = 1 := by rw [Int.gcd_comm]; exact ha
    have hdr := Int.dvd_of_dvd_mul_right_of_gcd_one hd hcop
    have hn : q ∣ r := by exact_mod_cast hdr
    exact (Nat.not_dvd_of_pos_of_lt hr hrq) hn
  exact_mod_cast Int.one_le_abs hne

example := reset_determinant_lower707 1 0 2 1 (by norm_num) (by norm_num) (by norm_num)

/-- Two representations of twice alpha retain the original error in the reset lower bound.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem approximation_error_separation707 (x α δ ε : ℝ) (a b : ℤ) (q r : ℕ)
    (hx : 0 < x) (hr : 0 < r) (hrq : r < q) (ha : Int.gcd a q = 1)
    (hfirst : 2 * α = (a : ℝ) / q + δ / x)
    (hsecond : 2 * α = (b : ℝ) / r + ε / x)
    :
    x / q - |δ| * r ≤ |ε * r| := by
  have hdet := reset_determinant_lower707 a b q r hr hrq ha
  have hq : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hphase : ((a : ℝ) * r - (b : ℝ) * q) * x =
      (ε * r - δ * r) * q := by
    have hf := hfirst
    have hs := hsecond
    field_simp at hf hs
    nlinarith [congrArg (fun z : ℝ => z * (r : ℝ)) hf,
      congrArg (fun z : ℝ => z * (q : ℝ)) hs]
  have hscale := mul_le_mul_of_nonneg_right hdet hx.le
  rw [one_mul, ← abs_of_pos hx, ← abs_mul, hphase, abs_mul, abs_of_pos hq] at hscale
  have habs := abs_sub (ε * (r : ℝ)) (δ * (r : ℝ))
  have hs := mul_le_mul_of_nonneg_right habs hq.le
  have hbound : x / q ≤ |ε * r| + |δ * r| := by
    apply (div_le_iff₀ hq).mpr
    simpa only [abs_of_pos hx] using hscale.trans hs
  rw [abs_mul δ, abs_of_pos hr0] at hbound
  linarith

example := approximation_error_separation707 2 (1 / 4) 0 1 1 0 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- An original denominator at most Q gives a quantitative reset bound with its error allowance retained.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem approximation_reset_lower707 (x α Q δ ε : ℝ) (a b : ℤ) (q r : ℕ)
    (hx : 0 < x) (hQ : 0 < Q) (hq : 0 < (q : ℝ)) (hqQ : (q : ℝ) ≤ Q)
    (hr : 0 < r) (hrq : r < q) (ha : Int.gcd a q = 1)
    (hfirst : 2 * α = (a : ℝ) / q + δ / x)
    (hsecond : 2 * α = (b : ℝ) / r + ε / x)
    (herror : |δ / x| ≤ 1 / ((q : ℝ) * Q))
    :
    x / Q * (1 - (r : ℝ) / Q) ≤ |ε * r| := by
  have hgap := approximation_error_separation707 x α δ ε a b q r hx hr hrq ha hfirst hsecond
  have herr : |δ| * (q : ℝ) ≤ x / Q := by
    apply (le_div_iff₀ hQ).mpr
    have hh : |δ| / x ≤ 1 / ((q : ℝ) * Q) := by
      simpa only [abs_div, abs_of_pos hx] using herror
    have hh' := (div_le_div_iff₀ hx (mul_pos hq hQ)).mp hh
    simpa only [one_mul, mul_assoc] using hh'
  have hg := (div_le_iff₀ hq).mp
    (show x / q ≤ |ε * r| + |δ| * r by linarith)
  have he := mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have heQ := mul_le_mul_of_nonneg_left hqQ (abs_nonneg (ε * (r : ℝ)))
  have hh : x - (x / Q) * r ≤ Q * |ε * r| := by nlinarith
  have hid : Q * (x / Q * (1 - (r : ℝ) / Q)) = x - (x / Q) * r := by
    field_simp
  apply le_of_mul_le_mul_left (a := Q) ?_ hQ
  rw [hid]
  exact hh

example := approximation_reset_lower707 2 (1 / 4) 2 0 1 1 0 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A seven y product lower bound suffices for the inverse denominator factor in the Type I estimates.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem reset_typeI_kernel707 (y q δ c : ℝ) (hy : 0 < y) (hq : 0 < q) (hc : c ≤ 49)
    (hcase : y < q ∨ 7 * y ≤ |δ * q|) :
    min 1 (c / δ ^ 2) / q ≤ 1 / y := by
  by_cases hqy : y < q
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) hq.le).trans
      (one_div_le_one_div_of_le hy hqy.le)
  · have hqy' : q ≤ y := le_of_not_gt hqy
    have hdq : 7 * y ≤ |δ| * q := by
      simpa only [abs_mul, abs_of_pos hq] using hcase.resolve_left hqy
    have hd : 7 ≤ |δ| := by nlinarith
    have hd0 : 0 < δ ^ 2 := by nlinarith [sq_abs δ]
    have hp := mul_le_mul hd hdq (by positivity : (0 : ℝ) ≤ 7 * y) (abs_nonneg δ)
    have hden : 49 * y ≤ δ ^ 2 * q := by nlinarith [sq_abs δ]
    calc
      _ ≤ (c / δ ^ 2) / q := div_le_div_of_nonneg_right (min_le_right _ _) hq.le
      _ = c / (δ ^ 2 * q) := div_div _ _ _
      _ ≤ 1 / y := (div_le_div_iff₀ (mul_pos hd0 hq) hy).mpr (by nlinarith)

example := reset_typeI_kernel707 1 1 7 49 (by norm_num) (by norm_num) le_rfl (Or.inr (by norm_num))

/-- Under the large denominator MinorHyp, any reset denominator at most y has scaled error strictly above seven y.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem minor_reset_mass707 (x α δ ε : ℝ) (a b : ℤ) (q r : ℕ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < (q : ℝ))
    (hr : 0 < r) (hsecond : 2 * α = (b : ℝ) / r + ε / x) :
    (r : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6 →
      7 * (x ^ ((1 : ℝ) / 3) / 6) < |ε * r| := by
  have hx := h.1
  have hx0 : 0 < x := by linarith
  intro hrle
  have hrq : r < q := by exact_mod_cast (hrle.trans_lt hq)
  have hlower := approximation_reset_lower707 x α (3 / 4 * x ^ ((2 : ℝ) / 3)) δ ε
    a b q r hx0 (by positivity) (by exact_mod_cast h.2.1) h.2.2.2.1 hr hrq
    h.2.2.2.2.1 h.2.2.1 hsecond h.2.2.2.2.2
  let t := x ^ ((1 : ℝ) / 3)
  let Q := 3 / 4 * x ^ ((2 : ℝ) / 3)
  let y := t / 6
  have ht : 6e6 ≤ t := by
    calc
      _ = (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) := MinorQAMGM.x0_cbrt.symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have ht0 : 0 < t := by linarith
  have hy : 0 < y := by dsimp [y]; positivity
  have hpow : x ^ ((2 : ℝ) / 3) = t ^ 2 := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQy : 8 * y < Q := by
    dsimp [Q, y]
    rw [hpow]
    nlinarith
  have hprod : t * x ^ ((2 : ℝ) / 3) = x := by
    dsimp [t]
    rw [← Real.rpow_add hx0]
    norm_num
  have hscale : x / Q = 8 * y := by
    dsimp [Q, y]
    apply (div_eq_iff (by positivity : 3 / 4 * x ^ ((2 : ℝ) / 3) ≠ 0)).mpr
    nlinarith [hprod]
  change x / Q * (1 - (r : ℝ) / Q) ≤ |ε * r| at hlower
  rw [hscale] at hlower
  change (r : ℝ) ≤ y at hrle
  have hratio : (r : ℝ) / Q < 1 / 8 := by
    apply (div_lt_iff₀ hQ).mpr
    linarith
  change 7 * y < |ε * r|
  nlinarith

example : 7 * ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6) < |(8000000 - 1 / 10000000 : ℝ) * (1 : ℕ)| := by
  rcases reset_strict_interior_counterexample325 with ⟨h, hq, he, _, _, hr, _⟩
  exact minor_reset_mass707 _ _ _ _ 1 0 27000000000000 1 h hq (by norm_num) (by simpa only [Int.cast_zero, Nat.cast_one] using he) (by simpa only [Nat.cast_one] using hr.le)

/-- The Type I inverse denominator factor is bounded for every positive reset denominator under the exact MinorHyp.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem minor_reset_typeI_kernel707 (x α δ ε c : ℝ) (a b : ℤ) (q r : ℕ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < (q : ℝ))
    (hr : 0 < r) (hsecond : 2 * α = (b : ℝ) / r + ε / x) (hc : c ≤ 49) :
    min 1 (c / ε ^ 2) / (r : ℝ) ≤ 6 / x ^ ((1 : ℝ) / 3) := by
  have hx0 : 0 < x := by linarith [h.1]
  have hy : 0 < x ^ ((1 : ℝ) / 3) / 6 := by positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hcase : x ^ ((1 : ℝ) / 3) / 6 < (r : ℝ) ∨
      7 * (x ^ ((1 : ℝ) / 3) / 6) ≤ |ε * (r : ℝ)| := by
    by_cases hrsmall : (r : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6
    · exact Or.inr (minor_reset_mass707 x α δ ε a b q r h hq hr hsecond hrsmall).le
    · exact Or.inl (lt_of_not_ge hrsmall)
  have hb := reset_typeI_kernel707 (x ^ ((1 : ℝ) / 3) / 6) r ε c hy hr0 hc hcase
  simpa only [one_div_div, one_mul] using hb

example : min 1 (0.798437 / (8000000 - 1 / 10000000 : ℝ) ^ 2) / (1 : ℕ) ≤ 6 / (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) := by
  rcases reset_strict_interior_counterexample325 with ⟨h, hq, he, _, _, _, _⟩
  exact minor_reset_typeI_kernel707 _ _ _ _ _ 1 0 27000000000000 1 h hq (by norm_num) (by simpa only [Int.cast_zero, Nat.cast_one] using he) (by norm_num)

/-- Dirichlet approximation with real Q gives a coprime fraction and the scaled error used on page 70.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem scaled_dirichlet707 (α x Q : ℝ) (hx : 0 < x) (hQ : 1 ≤ Q) :
    ∃ b : ℤ, ∃ r : ℕ, ∃ ε : ℝ,
      1 ≤ r ∧ (r : ℝ) ≤ Q ∧ Int.gcd b r = 1 ∧
        2 * α = (b : ℝ) / r + ε / x ∧ |ε / x| ≤ 1 / ((r : ℝ) * Q) := by
  have hn : 0 < ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  obtain ⟨z, hz, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le (2 * α) hn
  have hr : (0 : ℝ) < z.den := by exact_mod_cast z.pos
  have hQ0 : 0 < Q := by linarith
  have hdenQ : (z.den : ℝ) ≤ Q :=
    (Nat.cast_le.mpr hden).trans (Nat.floor_le (by linarith : 0 ≤ Q))
  have hcast : (z : ℝ) = (z.num : ℝ) / z.den := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
      congrArg (fun z : ℚ => (z : ℝ)) (Rat.num_div_den z).symm
  refine ⟨z.num, z.den, x * (2 * α - (z : ℝ)), z.pos, hdenQ, ?_, ?_, ?_⟩
  · simpa only [Int.gcd, Int.natAbs_natCast] using z.reduced
  · rw [mul_div_cancel_left₀ _ hx.ne', ← hcast]
    ring
  · rw [mul_div_cancel_left₀ _ hx.ne']
    apply hz.trans
    apply one_div_le_one_div_of_le (mul_pos hr hQ0)
    have hh := Nat.lt_floor_add_one Q
    nlinarith

example := scaled_dirichlet707 0 2 1 (by norm_num) le_rfl

/-- A reduced reset approximation exists at the page 70 Q and satisfies the weaker seven y Type II cover.
Source: P0013 page 70, a derived input for equations 5.58 to 5.60. -/
theorem minor_reset_exists707 (x α δ : ℝ) (a : ℤ) (q : ℕ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < (q : ℝ)) :
    ∃ b : ℤ, ∃ r : ℕ, ∃ ε : ℝ,
      1 ≤ r ∧ (r : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) ∧
      Int.gcd b r = 1 ∧ 2 * α = (b : ℝ) / r + ε / x ∧
      |ε / x| ≤ 1 / ((r : ℝ) * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))) ∧
      (x ^ ((1 : ℝ) / 3) / 24 < (r : ℝ) ∨
        (8 < |ε| ∧ 7 * (x ^ ((1 : ℝ) / 3) / 6) < |ε * r|)) := by
  have hx0 : 0 < x := by linarith [h.1]
  have ht : 6e6 ≤ x ^ ((1 : ℝ) / 3) := by
    calc
      _ = (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) := MinorQAMGM.x0_cbrt.symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) h.1 (by norm_num)
  have hpow : x ^ ((2 : ℝ) / 3) = (x ^ ((1 : ℝ) / 3)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hQ : 1 ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hs : Real.sqrt (6 : ℝ) ≤ 3 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    rw [hpow]
    nlinarith
  obtain ⟨b, r, ε, hr, hrQ, hcop, he, herr⟩ :=
    scaled_dirichlet707 α x (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6)) hx0 hQ
  refine ⟨b, r, ε, hr, hrQ, hcop, he, herr, ?_⟩
  by_cases hrlarge : x ^ ((1 : ℝ) / 3) / 24 < (r : ℝ)
  · exact Or.inl hrlarge
  · have hrsmall : (r : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6 := by
      have := le_of_not_gt hrlarge
      linarith
    have hmass := minor_reset_mass707 x α δ ε a b q r h hq (by omega) he hrsmall
    refine Or.inr ⟨?_, hmass⟩
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] at hmass
    by_contra hε
    have hεle : |ε| ≤ 8 := le_of_not_gt hε
    have hh := mul_le_mul_of_nonneg_right hεle (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have := le_of_not_gt hrlarge
    nlinarith

example := minor_reset_exists707 _ _ _ 1 27000000000000 reset_strict_interior_counterexample325.1 reset_strict_interior_counterexample325.2.1

end LeanLab.HelfgottArcs.Decomp119
