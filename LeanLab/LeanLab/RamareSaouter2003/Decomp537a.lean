import LeanLab.RamareSaouter2003.Circle419

/-!
Backlund pp. 362 to 369, displays 54, 56 and 77.
Rosser 1941 p. 224 uses these bounds on his actual circle.
The far right arc follows from the Dirichlet series.
The three other arcs retain the printed bounds and explicit height-50 data.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex MeasureTheory Circle419

theorem zeta_norm_le_tsum_re (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = (n : ℝ) ^ (-s.re) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hs0 : s ≠ 0 := by
        intro h; rw [h] at hs; simp only [Complex.zero_re] at hs; linarith
      have h0 : ((0 : ℂ)) ^ s = 0 := Complex.zero_cpow hs0
      have hr0 : -s.re ≠ 0 := by intro h; linarith [neg_eq_zero.mp h]
      simp only [Nat.cast_zero]
      rw [h0, div_zero, Real.zero_rpow hr0]
      simp
    · have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn, one_div, Real.rpow_neg hn']
  have hsummable : Summable fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ s‖ := by
    have h : Summable fun n : ℕ => (n : ℝ) ^ (-s.re) :=
      Real.summable_nat_rpow.2 (by linarith)
    exact h.congr (fun n => (hterm n).symm)
  calc ‖riemannZeta s‖
      = ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ s‖ := by rw [zeta_eq_tsum_one_div_nat_cpow hs]
    _ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsummable
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) := tsum_congr hterm

/-- One term of the real Dirichlet series as a complex number. -/
theorem div_cpow_ofReal (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    (1 : ℂ) / (n : ℂ) ^ ((σ : ℝ) : ℂ) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow : (n : ℂ) ^ ((σ : ℝ) : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hn' σ).symm
  rw [hpow, show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div]
  congr 1
  rw [Real.rpow_neg hn', one_div]

/-- The zeta value at a real point above one is the real Dirichlet series. -/
theorem zeta_ofReal_eq_tsum_rpow (σ : ℝ) (hσ : 1 < σ) :
    riemannZeta ((σ : ℝ) : ℂ) = ((∑' n : ℕ, (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hσ0 : ((σ : ℂ)) ≠ 0 := by
    intro h
    rw [Complex.ofReal_eq_zero] at h
    linarith
  have hterm : ∀ n : ℕ, (1 : ℂ) / (n : ℂ) ^ ((σ : ℝ) : ℂ) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hr0 : -σ ≠ 0 := by intro h; linarith [neg_eq_zero.mp h]
      simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hσ0, div_zero, Real.zero_rpow hr0]
      simp
    · exact div_cpow_ofReal n hn σ
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ),
    show (∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ ((σ : ℝ) : ℂ))
        = ∑' n : ℕ, ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) from tsum_congr hterm,
    Complex.ofReal_tsum]

/-- On `Re > 1` the modulus of zeta is the real Dirichlet series. -/
theorem zeta_abs_ofReal (σ : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℝ) : ℂ)‖ = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  rw [zeta_ofReal_eq_tsum_rpow σ hσ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun n => by positivity)]

/-- Rosser p. 224 and Backlund p. 362, the far right arc at every height. -/
theorem far_right (s : ℂ) (hs : 5 / 4 ≤ s.re) :
    ‖riemannZeta s‖ ≤ max 1 ‖riemannZeta (s.re : ℂ)‖ := by
  have h : 1 < s.re := by linarith
  exact (zeta_norm_le_tsum_re s h).trans
    ((zeta_abs_ofReal s.re h).symm.le.trans (le_max_right _ _))

/-- Backlund pp. 363 and 369, positivity of the height-50 correction. -/
theorem correction_pos (t : ℝ) (ht : 50 ≤ t) :
    0 < t ^ 2 - 4 := by nlinarith

/-- Backlund display 56, the critical-strip correction decreases with height. -/
theorem correction_antitone (a b : ℝ) (ha : 50 ≤ a) (hab : a ≤ b) :
    b ^ 2 / (b ^ 2 - 4) ≤ a ^ 2 / (a ^ 2 - 4) := by
  apply (div_le_div_iff₀ (correction_pos b (ha.trans hab)) (correction_pos a ha)).mpr
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
  nlinarith

/-- Backlund display 56, its explicit height-50 correction. -/
theorem correction_at_fifty :
    (50 : ℝ) ^ 2 / ((50 : ℝ) ^ 2 - 4) = 625 / 624 := by norm_num



/-- Backlund p. 367, the finite sum H with n equal to ten. -/
noncomputable def boundaryH (σ : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc (1 : ℕ) 9, (1 : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 50 * I)) +
    1 / (2 * (10 : ℂ) ^ ((σ : ℂ) + 50 * I))


end LeanLab.RamareSaouter2003.Decomp537a


open Real Complex
namespace LeanLab.RamareSaouter2003.Table537

/-- Backlund p. 367, a derived logarithm enclosure for the height-50 table. -/
theorem log_three_bounds : (1.0986122 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0986124 := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 5 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (3 : ℝ) = Real.log ((3 : ℝ) / 2) + Real.log 2 := by
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Backlund p. 367, a derived logarithm enclosure for the height-50 table. -/
theorem log_five_bounds : (1.6094378 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ 1.6094380 := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 9 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (5 : ℝ) = Real.log ((5 : ℝ) / 4) + 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    have hh : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hh]
    ring
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Backlund p. 367, a lower bound for the positive imaginary contribution at two. -/
theorem imaginary_two : (0.070 : ℝ) ≤ -Real.sin (50 * Real.log 2) / Real.sqrt 2 := by
  set r : ℝ := 50 * Real.log 2 - 11 * π with hr
  have hrlo : 0.0995 ≤ r := by dsimp [r]; linarith [Real.log_two_gt_d9, Real.pi_lt_d6]
  have hrhi : r ≤ 0.1000 := by dsimp [r]; linarith [Real.log_two_lt_d9, Real.pi_gt_d6]
  have hs := Real.sin_ge_sub_cube (show 0 ≤ r by linarith)
  have hc := pow_le_pow_left₀ (show 0 ≤ r by linarith) hrhi 3
  have heq : Real.sin (50 * Real.log 2) = -Real.sin r := by
    have h := Real.sin_add_nat_mul_pi r 11
    norm_num at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [heq, neg_neg, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  have hsq : Real.sqrt (2 : ℝ) ≤ 1.415 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  nlinarith

/-- Backlund p. 367, a lower bound for the positive imaginary contribution at three. -/
theorem imaginary_three : (0.576 : ℝ) ≤ -Real.sin (50 * Real.log 3) / Real.sqrt 3 := by
  set r : ℝ := 50 * Real.log 3 - (35 / 2) * π with hr
  have hrlo : -0.048 ≤ r := by dsimp [r]; linarith [log_three_bounds.1, Real.pi_lt_d6]
  have hrhi : r ≤ 0.048 := by dsimp [r]; linarith [log_three_bounds.2, Real.pi_gt_d6]
  have hs := Real.one_sub_sq_div_two_le_cos (x := r)
  have hc : r ^ 2 ≤ (0.048 : ℝ) ^ 2 := by nlinarith
  have heq : Real.sin (50 * Real.log 3) = -Real.cos r := by
    have h := Real.sin_add_nat_mul_pi (r + π / 2) 17
    norm_num [Real.sin_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [heq, neg_neg, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
  have hsq : Real.sqrt (3 : ℝ) ≤ 1.733 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  nlinarith

/-- Backlund p. 367, a lower bound for the positive imaginary contribution at five. -/
theorem imaginary_five : (0.4175 : ℝ) ≤ -Real.sin (50 * Real.log 5) / Real.sqrt 5 := by
  set r : ℝ := 50 * Real.log 5 - (51 / 2) * π with hr
  have hrlo : 0 ≤ r := by dsimp [r]; linarith [log_five_bounds.1, Real.pi_lt_d6]
  have hrhi : r ≤ 0.362 := by dsimp [r]; linarith [log_five_bounds.2, Real.pi_gt_d6]
  have hs := Real.one_sub_sq_div_two_le_cos (x := r)
  have hc : r ^ 2 ≤ (0.362 : ℝ) ^ 2 := pow_le_pow_left₀ hrlo hrhi 2
  have heq : Real.sin (50 * Real.log 5) = -Real.cos r := by
    have h := Real.sin_add_nat_mul_pi (r + π / 2) 25
    norm_num [Real.sin_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [heq, neg_neg, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5))]
  have hsq : Real.sqrt (5 : ℝ) ≤ 2.237 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  nlinarith

/-- Backlund p. 367, the positive imaginary summands in H at real part one half. -/
noncomputable def imaginaryPositiveAtHalf : ℝ :=
  (∑ n ∈ Finset.Icc (1 : ℕ) 9,
    max 0 (-Real.sin (50 * Real.log n) / Real.sqrt n)) +
      max 0 (-Real.sin (50 * Real.log 10) / (2 * Real.sqrt 10))

/-- Backlund p. 367, QUESTION about the printed bound A prime below 1.061.
Three of the actual positive summands already total at least 1.0635.
This does not assert that the final H norm or display 56 is false. -/
theorem positive_table_exceeds_printed : (1.061 : ℝ) < imaginaryPositiveAtHalf := by
  have hsub : ({2, 3, 5} : Finset ℕ) ⊆ Finset.Icc 1 9 := by decide
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun n : ℕ => max 0 (-Real.sin (50 * Real.log n) / Real.sqrt n))
    (fun n _ _ => le_max_left _ _)
  norm_num [Finset.sum_insert, Finset.sum_singleton] at hsum
  have htwo := imaginary_two.trans (le_max_right 0 _)
  have hthree := imaginary_three.trans (le_max_right 0 _)
  have hfiv := imaginary_five.trans (le_max_right 0 _)
  unfold imaginaryPositiveAtHalf
  linarith [le_max_left (0 : ℝ) (-Real.sin (50 * Real.log 10) / (2 * Real.sqrt 10))]

end LeanLab.RamareSaouter2003.Table537

namespace LeanLab.RamareSaouter2003.Table537

/-- Backlund p. 368, the R two majorant from displays 10 and 12 at sigma one half.
The denominator uses B three equal to one over forty two and six factorial. -/
noncomputable def remainder12Budget : ℝ :=
  let s : ℂ := 1 / 2 + 50 * I
  ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5)‖ /
    (30240 * (Real.sqrt 10 * 10 ^ 5) * (11 / 2))

/-- Backlund p. 368, the norm of each factor in the printed remainder product exceeds fifty. -/
theorem boundary_factor_norm (k : ℕ) :
    (50 : ℝ) ≤ ‖(1 / 2 : ℂ) + 50 * I + k‖ := by
  have h := Complex.abs_im_le_norm ((1 / 2 : ℂ) + 50 * I + k)
  simpa using h

/-- Backlund p. 368, a lower bound for the printed R two majorant. -/
theorem remainder12_floor :
    (50 : ℝ) ^ 6 / (30240 * (Real.sqrt 10 * 10 ^ 5) * (11 / 2)) ≤ remainder12Budget := by
  have hd : 0 ≤ 30240 * (Real.sqrt (10 : ℝ) * 10 ^ 5) * (11 / 2) := by positivity
  apply div_le_div_of_nonneg_right _ hd
  simp only [norm_mul]
  have h0 := boundary_factor_norm 0
  have h1 := boundary_factor_norm 1
  have h2 := boundary_factor_norm 2
  have h3 := boundary_factor_norm 3
  have h4 := boundary_factor_norm 4
  have h5 := boundary_factor_norm 5
  norm_num only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2 h3 h4 h5
  calc
    (50 : ℝ) ^ 6 = 50 * 50 * 50 * 50 * 50 * 50 := by norm_num
    _ ≤ _ := by gcongr

/-- Backlund p. 368, QUESTION about the application of display 12.
Its remainder majorant alone exceeds the printed 0.281 budget for K.
This does not assert that the actual K norm exceeds that budget. -/
theorem remainder12_budget_exceeds_printed : (0.281 : ℝ) < remainder12Budget := by
  have hs : Real.sqrt (10 : ℝ) ≤ 3.2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hd : 0 < 30240 * (Real.sqrt (10 : ℝ) * 10 ^ 5) * (11 / 2) := by positivity
  have hlo : (0.281 : ℝ) <
      50 ^ 6 / (30240 * (Real.sqrt 10 * 10 ^ 5) * (11 / 2)) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  exact hlo.trans_le remainder12_floor

end LeanLab.RamareSaouter2003.Table537

namespace LeanLab.RamareSaouter2003.Table537

/-- Backlund p. 362, the Euler constant bound used in display 54. -/
theorem euler_constant_upper : Real.eulerMascheroniConstant < (0.578 : ℝ) := by
  have hq : harmonic 1000 ≤ (7.485471 : ℚ) := by decide +kernel
  have hr : (harmonic 1000 : ℝ) ≤ 7.485471 := by
    calc
      _ ≤ ((7.485471 : ℚ) : ℝ) := Rat.cast_le.mpr hq
      _ = _ := by norm_num
  have hl : Real.log (1000 : ℝ) = 3 * (Real.log 2 + Real.log 5) := by
    rw [show (1000 : ℝ) = (2 * 5) ^ 3 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    norm_num
  have he := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1000
  change Real.eulerMascheroniConstant < (harmonic 1000 : ℝ) - Real.log 1000 at he
  linarith [Real.log_two_gt_d9, log_five_bounds.1]

/-- Backlund p. 362, the elementary error budget for the right strip.
The two square roots uniformly cover real part one through three halves.
The remaining analytic input is the Euler summation estimate itself. -/
theorem right54_error_budget (t : ℝ) (ht : 50 ≤ t) :
    -Real.log 3 + Real.eulerMascheroniConstant + 4 / t +
      3 / (4 * t) * Real.sqrt (1 + 9 / (4 * t ^ 2)) +
      (3 / 8) * Real.sqrt ((1 + 9 / (4 * t ^ 2)) * (1 + 25 / (4 * t ^ 2))) ≤
        (-0.048 : ℝ) := by
  have htpos : 0 < t := by linarith
  have hsq : (2500 : ℝ) ≤ t ^ 2 := by nlinarith
  have ha : 9 / (4 * t ^ 2) ≤ (9 / 10000 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * t ^ 2)).mpr
    nlinarith
  have hb : 25 / (4 * t ^ 2) ≤ (25 / 10000 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * t ^ 2)).mpr
    nlinarith
  have hs1 : Real.sqrt (1 + 9 / (4 * t ^ 2)) ≤ 1.001 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · linarith
  have hs2 : Real.sqrt ((1 + 9 / (4 * t ^ 2)) * (1 + 25 / (4 * t ^ 2))) ≤ 1.002 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · have hp := mul_le_mul (show 1 + 9 / (4 * t ^ 2) ≤ 1 + (9 / 10000 : ℝ) by linarith)
          (show 1 + 25 / (4 * t ^ 2) ≤ 1 + (25 / 10000 : ℝ) by linarith)
          (by positivity : 0 ≤ 1 + 25 / (4 * t ^ 2)) (by norm_num : 0 ≤ 1 + (9 / 10000 : ℝ))
      linarith
  have h4 : 4 / t ≤ (0.08 : ℝ) := by
    apply (div_le_iff₀ htpos).mpr
    linarith
  have h3 : 3 / (4 * t) ≤ (0.015 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * t)).mpr
    linarith
  have hmul := mul_le_mul h3 hs1 (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.015)
  linarith [log_three_bounds.1, euler_constant_upper]

/-- Backlund display 54, the explicit right-strip scalar calculation at height fifty. -/
theorem right54_budget_at_fifty :
    -Real.log 3 + Real.eulerMascheroniConstant + 4 / (50 : ℝ) +
      3 / (4 * 50) * Real.sqrt (1 + 9 / (4 * (50 : ℝ) ^ 2)) +
      (3 / 8) * Real.sqrt ((1 + 9 / (4 * (50 : ℝ) ^ 2)) * (1 + 25 / (4 * (50 : ℝ) ^ 2))) ≤
        (-0.048 : ℝ) := right54_error_budget 50 (by norm_num)

end LeanLab.RamareSaouter2003.Table537


namespace LeanLab.RamareSaouter2003.Table537

/-- Backlund p. 367, a derived logarithm enclosure for the finite H calculation. -/
theorem log_seven_bounds : (1.9459100 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ 1.9459103 := by
  have h := Real.sum_range_sub_log_div_le (x := (-1 / 15 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (7 : ℝ) = Real.log ((7 : ℝ) / 8) + 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
    have hh : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [hh]
    ring
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Backlund p. 367, rational interval certificates from Mathlib's trigonometric errors. -/
theorem trig_enclosure (x l u : ℝ) (hl : 0 ≤ l) (hlx : l ≤ x) (hxu : x ≤ u) (hu : u ≤ 1) :
    (1 - u ^ 2 / 2 ≤ Real.cos x ∧
      Real.cos x ≤ 1 - l ^ 2 / 2 + u ^ 4 * (5 / 96)) ∧
    (l - u ^ 3 / 6 ≤ Real.sin x ∧
      Real.sin x ≤ u - l ^ 3 / 6 + u ^ 5 / 100) := by
  have hx : 0 ≤ x := hl.trans hlx
  have ha : |x| ≤ 1 := by rw [abs_of_nonneg hx]; exact hxu.trans hu
  have hc := (abs_le.mp (Real.cos_bound ha)).2
  rw [abs_of_nonneg hx] at hc
  have hs := (abs_le.mp (Real.sin_bound ha)).2
  rw [abs_of_nonneg hx] at hs
  have h2l := pow_le_pow_left₀ hl hlx 2
  have h2u := pow_le_pow_left₀ hx hxu 2
  have h3l := pow_le_pow_left₀ hl hlx 3
  have h3u := pow_le_pow_left₀ hx hxu 3
  have h4u := pow_le_pow_left₀ hx hxu 4
  have h5u := pow_le_pow_left₀ hx hxu 5
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  · linarith
  · linarith [Real.sin_ge_sub_cube hx]
  · linarith

end LeanLab.RamareSaouter2003.Table537

namespace LeanLab.RamareSaouter2003.Table537

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 2. -/
theorem phase_2 :
    Real.cos (50 * Real.log 2) ∈ Set.Icc (-497511 / 500000 : ℝ) (-199003 / 200000 : ℝ) ∧
    Real.sin (50 * Real.log 2) ∈ Set.Icc (-3987 / 40000 : ℝ) (-99673 / 1000000 : ℝ) := by
  set r : ℝ := 50 * Real.log 2 - (22 / 2) * π with hr
  have hrlo : (99839 / 1000000 : ℝ) ≤ r := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (312 / 3125 : ℝ) := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (99839 / 1000000 : ℝ) (312 / 3125 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 2) = -Real.cos r := by
    have h := Real.cos_add_nat_mul_pi (r) 11
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 2) = -Real.sin r := by
    have h := Real.sin_add_nat_mul_pi (r) 11
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 3. -/
theorem phase_3 :
    Real.cos (50 * Real.log 3) ∈ Set.Icc (-9449 / 200000 : ℝ) (-47233 / 1000000 : ℝ) ∧
    Real.sin (50 * Real.log 3) ∈ Set.Icc (-249721 / 250000 : ℝ) (-998883 / 1000000 : ℝ) := by
  set r : ℝ := (35 / 2) * π - 50 * Real.log 3 with hr
  have hrlo : (47251 / 1000000 : ℝ) ≤ r := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (23631 / 500000 : ℝ) := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (47251 / 1000000 : ℝ) (23631 / 500000 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 3) = -Real.sin r := by
    have h := Real.cos_add_nat_mul_pi (-r + π / 2) 17
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 3) = -Real.cos r := by
    have h := Real.sin_add_nat_mul_pi (-r + π / 2) 17
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 4. -/
theorem phase_4 :
    Real.cos (50 * Real.log 4) ∈ Set.Icc (980063 / 1000000 : ℝ) (980147 / 1000000 : ℝ) ∧
    Real.sin (50 * Real.log 4) ∈ Set.Icc (12397 / 62500 : ℝ) (198357 / 1000000 : ℝ) := by
  set r : ℝ := 50 * Real.log 4 - (44 / 2) * π with hr
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hrlo : (199679 / 1000000 : ℝ) ≤ r := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (624 / 3125 : ℝ) := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (199679 / 1000000 : ℝ) (624 / 3125 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 4) = Real.cos r := by
    have h := Real.cos_add_nat_mul_pi (r) 22
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 4) = Real.sin r := by
    have h := Real.sin_add_nat_mul_pi (r) 22
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 5. -/
theorem phase_5 :
    Real.cos (50 * Real.log 5) ∈ Set.Icc (353417 / 1000000 : ℝ) (353491 / 1000000 : ℝ) ∧
    Real.sin (50 * Real.log 5) ∈ Set.Icc (-935627 / 1000000 : ℝ) (-186947 / 200000 : ℝ) := by
  set r : ℝ := 50 * Real.log 5 - (51 / 2) * π with hr
  have hrlo : (361277 / 1000000 : ℝ) ≤ r := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (45161 / 125000 : ℝ) := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (361277 / 1000000 : ℝ) (45161 / 125000 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 5) = Real.sin r := by
    have h := Real.cos_add_nat_mul_pi (r + π / 2) 25
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 5) = -Real.cos r := by
    have h := Real.sin_add_nat_mul_pi (r + π / 2) 25
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 6. -/
theorem phase_6 :
    Real.cos (50 * Real.log 6) ∈ Set.Icc (-10513 / 200000 : ℝ) (-52553 / 1000000 : ℝ) ∧
    Real.sin (50 * Real.log 6) ∈ Set.Icc (998617 / 1000000 : ℝ) (998619 / 1000000 : ℝ) := by
  set r : ℝ := 50 * Real.log 6 - (57 / 2) * π with hr
  have hlog : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hrlo : (26289 / 500000 : ℝ) ≤ r := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (52589 / 1000000 : ℝ) := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (26289 / 500000 : ℝ) (52589 / 1000000 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 6) = -Real.sin r := by
    have h := Real.cos_add_nat_mul_pi (r + π / 2) 28
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 6) = Real.cos r := by
    have h := Real.sin_add_nat_mul_pi (r + π / 2) 28
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 7. -/
theorem phase_7 :
    Real.cos (50 * Real.log 7) ∈ Set.Icc (-2489 / 2500 : ℝ) (-995593 / 1000000 : ℝ) ∧
    Real.sin (50 * Real.log 7) ∈ Set.Icc (93719 / 1000000 : ℝ) (11717 / 125000 : ℝ) := by
  set r : ℝ := (62 / 2) * π - 50 * Real.log 7 with hr
  have hrlo : (93857 / 1000000 : ℝ) ≤ r := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (93873 / 1000000 : ℝ) := by
    dsimp [r]
    skip
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (93857 / 1000000 : ℝ) (93873 / 1000000 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 7) = -Real.cos r := by
    have h := Real.cos_add_nat_mul_pi (-r) 31
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 7) = Real.sin r := by
    have h := Real.sin_add_nat_mul_pi (-r) 31
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 8. -/
theorem phase_8 :
    Real.cos (50 * Real.log 8) ∈ Set.Icc (-238891 / 250000 : ℝ) (-955143 / 1000000 : ℝ) ∧
    Real.sin (50 * Real.log 8) ∈ Set.Icc (-147533 / 500000 : ℝ) (-922 / 3125 : ℝ) := by
  set r : ℝ := 50 * Real.log 8 - (66 / 2) * π with hr
  have hlog : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hrlo : (299519 / 1000000 : ℝ) ≤ r := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (936 / 3125 : ℝ) := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (299519 / 1000000 : ℝ) (936 / 3125 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 8) = -Real.cos r := by
    have h := Real.cos_add_nat_mul_pi (r) 33
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 8) = -Real.sin r := by
    have h := Real.sin_add_nat_mul_pi (r) 33
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 9. -/
theorem phase_9 :
    Real.cos (50 * Real.log 9) ∈ Set.Icc (-995539 / 1000000 : ℝ) (-248883 / 250000 : ℝ) ∧
    Real.sin (50 * Real.log 9) ∈ Set.Icc (94361 / 1000000 : ℝ) (94383 / 1000000 : ℝ) := by
  set r : ℝ := (70 / 2) * π - 50 * Real.log 9 with hr
  have hlog : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hrlo : (47251 / 500000 : ℝ) ≤ r := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (94523 / 1000000 : ℝ) := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (47251 / 500000 : ℝ) (94523 / 1000000 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 9) = -Real.cos r := by
    have h := Real.cos_add_nat_mul_pi (-r) 35
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 9) = Real.sin r := by
    have h := Real.sin_add_nat_mul_pi (-r) 35
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

/-- Backlund p. 367, certified trigonometric enclosure for the summand at 10. -/
theorem phase_10 :
    Real.cos (50 * Real.log 10) ∈ Set.Icc (-111249 / 250000 : ℝ) (-222387 / 500000 : ℝ) ∧
    Real.sin (50 * Real.log 10) ∈ Set.Icc (11171 / 12500 : ℝ) (896041 / 1000000 : ℝ) := by
  set r : ℝ := 50 * Real.log 10 - (73 / 2) * π with hr
  have hlog : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hrlo : (461117 / 1000000 : ℝ) ≤ r := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hrhi : r ≤ (57641 / 125000 : ℝ) := by
    dsimp [r]
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_bounds.1, log_three_bounds.2, log_five_bounds.1, log_five_bounds.2, log_seven_bounds.1, log_seven_bounds.2, Real.pi_gt_d20, Real.pi_lt_d20]
  have hh := trig_enclosure r (461117 / 1000000 : ℝ) (57641 / 125000 : ℝ) (by norm_num) hrlo hrhi (by norm_num)
  have hcos : Real.cos (50 * Real.log 10) = -Real.sin r := by
    have h := Real.cos_add_nat_mul_pi (r + π / 2) 36
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  have hsin : Real.sin (50 * Real.log 10) = Real.cos r := by
    have h := Real.sin_add_nat_mul_pi (r + π / 2) 36
    norm_num [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    convert h using 1 <;> dsimp [r] <;> ring
  rw [hcos, hsin]
  constructor <;> constructor <;> norm_num at * <;> linarith [hh.1.1, hh.1.2, hh.2.1, hh.2.2]

end LeanLab.RamareSaouter2003.Table537


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex

/-- Backlund p. 367, real and imaginary coefficients of the actual reciprocal power. -/
theorem boundary_term_re_im (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    ((1 : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 50 * I)).re =
      (n : ℝ) ^ (-σ) * Real.cos (50 * Real.log n) ∧
    ((1 : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 50 * I)).im =
      -(n : ℝ) ^ (-σ) * Real.sin (50 * Real.log n) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    simpa using (Complex.natCast_log (n := n)).symm
  have hexp : (1 : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 50 * I) =
      Complex.exp (((-σ * Real.log n : ℝ) : ℂ) + ((-50 * Real.log n : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hnc, one_div, ← Complex.exp_neg, hlog]
    congr 1
    push_cast
    ring
  rw [hexp]
  simp only [Complex.exp_re, Complex.exp_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, one_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg,
    Real.cos_neg, Real.sin_neg, Real.rpow_def_of_pos hnpos, mul_comm, and_self]

/-- Backlund p. 367, uniform amplitude bounds on the half-edge of the critical strip. -/
theorem boundary_amplitude_bounds (n : ℕ) (hn : 1 ≤ n) (σ : ℝ)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    1 / (n : ℝ) ≤ (n : ℝ) ^ (-σ) ∧
      (n : ℝ) ^ (-σ) ≤ 1 / Real.sqrt (n : ℝ) := by
  have hbase : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hlo := Real.rpow_le_rpow_of_exponent_le hbase (show (-1 : ℝ) ≤ -σ by linarith [hσ.2])
  have hhi := Real.rpow_le_rpow_of_exponent_le hbase
    (show -σ ≤ -(1 / 2 : ℝ) by linarith [hσ.1])
  constructor
  · simpa only [Real.rpow_neg_one, one_div] using hlo
  · rw [Real.sqrt_eq_rpow]
    simpa only [Real.rpow_neg hnpos.le, one_div] using hhi

end LeanLab.RamareSaouter2003.Decomp537a


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 2. -/
theorem term_2_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (2 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (-1759 / 2500 : ℝ) (0 / 1 : ℝ) ∧
    ((1 : ℂ) / (2 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (0 / 1 : ℝ) (71 / 1000 : ℝ) := by
  have ha := boundary_amplitude_bounds 2 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (2828427 / 2000000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 2 ≤ (7071069 / 10000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    nlinarith
  have hau : (2 : ℝ) ^ (-σ) ≤ (7071069 / 10000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (2 : ℝ) ≤ (2 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_2
  have hslo : (99673 / 1000000 : ℝ) ≤ -Real.sin (50 * Real.log 2) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 2) ≤ (3987 / 40000 : ℝ) := by linarith [hc.2.1]
  have hrl : (7071069 / 10000000 : ℝ) * (-497511 / 500000 : ℝ) ≤ (2 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 2)) := by
    calc
      _ ≤ (2 : ℝ) ^ (-σ) * (-497511 / 500000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc.1.1) ha0
  have hru : (2 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 2)) ≤ (1 / (2 : ℝ)) * (-199003 / 200000 : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (-σ) * (-199003 / 200000 : ℝ) := mul_le_mul_of_nonneg_left (hc.1.2) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have hil : (1 / (2 : ℝ)) * (99673 / 1000000 : ℝ) ≤ (2 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 2)) :=
    mul_le_mul hal (hslo) (by norm_num) ha0
  have hiu : (2 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 2)) ≤ (7071069 / 10000000 : ℝ) * (3987 / 40000 : ℝ) :=
    mul_le_mul hau (hshi) (by linarith [hslo]) (by norm_num)
  have ht := boundary_term_re_im 2 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 3. -/
theorem term_3_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (3 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (-273 / 10000 : ℝ) (0 / 1 : ℝ) ∧
    ((1 : ℂ) / (3 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (3 / 10 : ℝ) (289 / 500 : ℝ) := by
  have ha := boundary_amplitude_bounds 3 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (4330127 / 2500000 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 3 ≤ (5773503 / 10000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr
    nlinarith
  have hau : (3 : ℝ) ^ (-σ) ≤ (5773503 / 10000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (3 : ℝ) ≤ (3 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (3 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_3
  have hslo : (998883 / 1000000 : ℝ) ≤ -Real.sin (50 * Real.log 3) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 3) ≤ (249721 / 250000 : ℝ) := by linarith [hc.2.1]
  have hrl : (5773503 / 10000000 : ℝ) * (-9449 / 200000 : ℝ) ≤ (3 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 3)) := by
    calc
      _ ≤ (3 : ℝ) ^ (-σ) * (-9449 / 200000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc.1.1) ha0
  have hru : (3 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 3)) ≤ (1 / (3 : ℝ)) * (-47233 / 1000000 : ℝ) := by
    calc
      _ ≤ (3 : ℝ) ^ (-σ) * (-47233 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left (hc.1.2) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have hil : (1 / (3 : ℝ)) * (998883 / 1000000 : ℝ) ≤ (3 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 3)) :=
    mul_le_mul hal (hslo) (by norm_num) ha0
  have hiu : (3 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 3)) ≤ (5773503 / 10000000 : ℝ) * (249721 / 250000 : ℝ) :=
    mul_le_mul hau (hshi) (by linarith [hslo]) (by norm_num)
  have ht := boundary_term_re_im 3 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 4. -/
theorem term_4_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (4 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (0 / 1 : ℝ) (4901 / 10000 : ℝ) ∧
    ((1 : ℂ) / (4 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (-1 / 10 : ℝ) (0 / 1 : ℝ) := by
  have ha := boundary_amplitude_bounds 4 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (2 / 1 : ℝ) ≤ Real.sqrt 4 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 4 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 4))).mpr
    nlinarith
  have hau : (4 : ℝ) ^ (-σ) ≤ (1 / 2 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (4 : ℝ) ≤ (4 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (4 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_4
  have hslo : (-198357 / 1000000 : ℝ) ≤ -Real.sin (50 * Real.log 4) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 4) ≤ (-12397 / 62500 : ℝ) := by linarith [hc.2.1]
  have hrl : (1 / (4 : ℝ)) * (980063 / 1000000 : ℝ) ≤ (4 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 4)) :=
    mul_le_mul hal (hc.1.1) (by norm_num) ha0
  have hru : (4 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 4)) ≤ (1 / 2 : ℝ) * (980147 / 1000000 : ℝ) :=
    mul_le_mul hau (hc.1.2) (by linarith [hc.1.1]) (by norm_num)
  have hil : (1 / 2 : ℝ) * (-198357 / 1000000 : ℝ) ≤ (4 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 4)) := by
    calc
      _ ≤ (4 : ℝ) ^ (-σ) * (-198357 / 1000000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hslo) ha0
  have hiu : (4 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 4)) ≤ (1 / (4 : ℝ)) * (-12397 / 62500 : ℝ) := by
    calc
      _ ≤ (4 : ℝ) ^ (-σ) * (-12397 / 62500 : ℝ) := mul_le_mul_of_nonneg_left (hshi) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have ht := boundary_term_re_im 4 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 5. -/
theorem term_5_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (5 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (0 / 1 : ℝ) (1581 / 10000 : ℝ) ∧
    ((1 : ℂ) / (5 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (0 / 1 : ℝ) (21 / 50 : ℝ) := by
  have ha := boundary_amplitude_bounds 5 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (22360679 / 10000000 : ℝ) ≤ Real.sqrt 5 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 5 ≤ (4472137 / 10000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5))).mpr
    nlinarith
  have hau : (5 : ℝ) ^ (-σ) ≤ (4472137 / 10000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (5 : ℝ) ≤ (5 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (5 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_5
  have hslo : (186947 / 200000 : ℝ) ≤ -Real.sin (50 * Real.log 5) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 5) ≤ (935627 / 1000000 : ℝ) := by linarith [hc.2.1]
  have hrl : (1 / (5 : ℝ)) * (353417 / 1000000 : ℝ) ≤ (5 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 5)) :=
    mul_le_mul hal (hc.1.1) (by norm_num) ha0
  have hru : (5 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 5)) ≤ (4472137 / 10000000 : ℝ) * (353491 / 1000000 : ℝ) :=
    mul_le_mul hau (hc.1.2) (by linarith [hc.1.1]) (by norm_num)
  have hil : (1 / (5 : ℝ)) * (186947 / 200000 : ℝ) ≤ (5 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 5)) :=
    mul_le_mul hal (hslo) (by norm_num) ha0
  have hiu : (5 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 5)) ≤ (4472137 / 10000000 : ℝ) * (935627 / 1000000 : ℝ) :=
    mul_le_mul hau (hshi) (by linarith [hslo]) (by norm_num)
  have ht := boundary_term_re_im 5 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 6. -/
theorem term_6_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (6 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (-43 / 2000 : ℝ) (0 / 1 : ℝ) ∧
    ((1 : ℂ) / (6 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (-409 / 1000 : ℝ) (-4 / 25 : ℝ) := by
  have ha := boundary_amplitude_bounds 6 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (24494897 / 10000000 : ℝ) ≤ Real.sqrt 6 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 6 ≤ (4082483 / 10000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6))).mpr
    nlinarith
  have hau : (6 : ℝ) ^ (-σ) ≤ (4082483 / 10000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (6 : ℝ) ≤ (6 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (6 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_6
  have hslo : (-998619 / 1000000 : ℝ) ≤ -Real.sin (50 * Real.log 6) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 6) ≤ (-998617 / 1000000 : ℝ) := by linarith [hc.2.1]
  have hrl : (4082483 / 10000000 : ℝ) * (-10513 / 200000 : ℝ) ≤ (6 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 6)) := by
    calc
      _ ≤ (6 : ℝ) ^ (-σ) * (-10513 / 200000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc.1.1) ha0
  have hru : (6 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 6)) ≤ (1 / (6 : ℝ)) * (-52553 / 1000000 : ℝ) := by
    calc
      _ ≤ (6 : ℝ) ^ (-σ) * (-52553 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left (hc.1.2) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have hil : (4082483 / 10000000 : ℝ) * (-998619 / 1000000 : ℝ) ≤ (6 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 6)) := by
    calc
      _ ≤ (6 : ℝ) ^ (-σ) * (-998619 / 1000000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hslo) ha0
  have hiu : (6 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 6)) ≤ (1 / (6 : ℝ)) * (-998617 / 1000000 : ℝ) := by
    calc
      _ ≤ (6 : ℝ) ^ (-σ) * (-998617 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left (hshi) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have ht := boundary_term_re_im 6 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 7. -/
theorem term_7_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (7 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (-941 / 2500 : ℝ) (0 / 1 : ℝ) ∧
    ((1 : ℂ) / (7 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (-9 / 250 : ℝ) (0 / 1 : ℝ) := by
  have ha := boundary_amplitude_bounds 7 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (26457513 / 10000000 : ℝ) ≤ Real.sqrt 7 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 7 ≤ (755929 / 2000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 7))).mpr
    nlinarith
  have hau : (7 : ℝ) ^ (-σ) ≤ (755929 / 2000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (7 : ℝ) ≤ (7 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (7 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_7
  have hslo : (-11717 / 125000 : ℝ) ≤ -Real.sin (50 * Real.log 7) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 7) ≤ (-93719 / 1000000 : ℝ) := by linarith [hc.2.1]
  have hrl : (755929 / 2000000 : ℝ) * (-2489 / 2500 : ℝ) ≤ (7 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 7)) := by
    calc
      _ ≤ (7 : ℝ) ^ (-σ) * (-2489 / 2500 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc.1.1) ha0
  have hru : (7 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 7)) ≤ (1 / (7 : ℝ)) * (-995593 / 1000000 : ℝ) := by
    calc
      _ ≤ (7 : ℝ) ^ (-σ) * (-995593 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left (hc.1.2) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have hil : (755929 / 2000000 : ℝ) * (-11717 / 125000 : ℝ) ≤ (7 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 7)) := by
    calc
      _ ≤ (7 : ℝ) ^ (-σ) * (-11717 / 125000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hslo) ha0
  have hiu : (7 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 7)) ≤ (1 / (7 : ℝ)) * (-93719 / 1000000 : ℝ) := by
    calc
      _ ≤ (7 : ℝ) ^ (-σ) * (-93719 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left (hshi) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have ht := boundary_term_re_im 7 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 8. -/
theorem term_8_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (8 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (-3379 / 10000 : ℝ) (0 / 1 : ℝ) ∧
    ((1 : ℂ) / (8 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (0 / 1 : ℝ) (53 / 500 : ℝ) := by
  have ha := boundary_amplitude_bounds 8 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (28284271 / 10000000 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 8 ≤ (1767767 / 5000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8))).mpr
    nlinarith
  have hau : (8 : ℝ) ^ (-σ) ≤ (1767767 / 5000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (8 : ℝ) ≤ (8 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (8 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_8
  have hslo : (922 / 3125 : ℝ) ≤ -Real.sin (50 * Real.log 8) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 8) ≤ (147533 / 500000 : ℝ) := by linarith [hc.2.1]
  have hrl : (1767767 / 5000000 : ℝ) * (-238891 / 250000 : ℝ) ≤ (8 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 8)) := by
    calc
      _ ≤ (8 : ℝ) ^ (-σ) * (-238891 / 250000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc.1.1) ha0
  have hru : (8 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 8)) ≤ (1 / (8 : ℝ)) * (-955143 / 1000000 : ℝ) := by
    calc
      _ ≤ (8 : ℝ) ^ (-σ) * (-955143 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left (hc.1.2) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have hil : (1 / (8 : ℝ)) * (922 / 3125 : ℝ) ≤ (8 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 8)) :=
    mul_le_mul hal (hslo) (by norm_num) ha0
  have hiu : (8 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 8)) ≤ (1767767 / 5000000 : ℝ) * (147533 / 500000 : ℝ) :=
    mul_le_mul hau (hshi) (by linarith [hslo]) (by norm_num)
  have ht := boundary_term_re_im 8 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 9. -/
theorem term_9_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (9 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (-3319 / 10000 : ℝ) (0 / 1 : ℝ) ∧
    ((1 : ℂ) / (9 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (-33 / 1000 : ℝ) (0 / 1 : ℝ) := by
  have ha := boundary_amplitude_bounds 9 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (3 / 1 : ℝ) ≤ Real.sqrt 9 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 9 ≤ (1666667 / 5000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 9))).mpr
    nlinarith
  have hau : (9 : ℝ) ^ (-σ) ≤ (1666667 / 5000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (9 : ℝ) ≤ (9 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (9 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_9
  have hslo : (-94383 / 1000000 : ℝ) ≤ -Real.sin (50 * Real.log 9) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 9) ≤ (-94361 / 1000000 : ℝ) := by linarith [hc.2.1]
  have hrl : (1666667 / 5000000 : ℝ) * (-995539 / 1000000 : ℝ) ≤ (9 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 9)) := by
    calc
      _ ≤ (9 : ℝ) ^ (-σ) * (-995539 / 1000000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc.1.1) ha0
  have hru : (9 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 9)) ≤ (1 / (9 : ℝ)) * (-248883 / 250000 : ℝ) := by
    calc
      _ ≤ (9 : ℝ) ^ (-σ) * (-248883 / 250000 : ℝ) := mul_le_mul_of_nonneg_left (hc.1.2) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have hil : (1666667 / 5000000 : ℝ) * (-94383 / 1000000 : ℝ) ≤ (9 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 9)) := by
    calc
      _ ≤ (9 : ℝ) ^ (-σ) * (-94383 / 1000000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hslo) ha0
  have hiu : (9 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 9)) ≤ (1 / (9 : ℝ)) * (-94361 / 1000000 : ℝ) := by
    calc
      _ ≤ (9 : ℝ) ^ (-σ) * (-94361 / 1000000 : ℝ) := mul_le_mul_of_nonneg_left (hshi) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have ht := boundary_term_re_im 9 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

/-- Backlund p. 367, certified uniform real and imaginary bounds for summand 10. -/
theorem term_10_bounds (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((1 : ℂ) / (10 : ℂ) ^ ((σ : ℂ) + 50 * I)).re ∈ Set.Icc (-88 / 625 : ℝ) (0 / 1 : ℝ) ∧
    ((1 : ℂ) / (10 : ℂ) ^ ((σ : ℂ) + 50 * I)).im ∈ Set.Icc (-143 / 500 : ℝ) (0 / 1 : ℝ) := by
  have ha := boundary_amplitude_bounds 10 (by norm_num) σ hσ
  norm_num only [Nat.cast_ofNat] at ha
  have hroot : (3952847 / 1250000 : ℝ) ≤ Real.sqrt 10 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcap : 1 / Real.sqrt 10 ≤ (1581139 / 5000000 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 10))).mpr
    nlinarith
  have hau : (10 : ℝ) ^ (-σ) ≤ (1581139 / 5000000 : ℝ) := by
    exact ha.2.trans (by convert hcap using 1 <;> norm_num)
  have hal : 1 / (10 : ℝ) ≤ (10 : ℝ) ^ (-σ) := ha.1
  have ha0 : 0 ≤ (10 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hc := Table537.phase_10
  have hslo : (-896041 / 1000000 : ℝ) ≤ -Real.sin (50 * Real.log 10) := by linarith [hc.2.2]
  have hshi : -Real.sin (50 * Real.log 10) ≤ (-11171 / 12500 : ℝ) := by linarith [hc.2.1]
  have hrl : (1581139 / 5000000 : ℝ) * (-111249 / 250000 : ℝ) ≤ (10 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 10)) := by
    calc
      _ ≤ (10 : ℝ) ^ (-σ) * (-111249 / 250000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc.1.1) ha0
  have hru : (10 : ℝ) ^ (-σ) * (Real.cos (50 * Real.log 10)) ≤ (1 / (10 : ℝ)) * (-222387 / 500000 : ℝ) := by
    calc
      _ ≤ (10 : ℝ) ^ (-σ) * (-222387 / 500000 : ℝ) := mul_le_mul_of_nonneg_left (hc.1.2) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have hil : (1581139 / 5000000 : ℝ) * (-896041 / 1000000 : ℝ) ≤ (10 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 10)) := by
    calc
      _ ≤ (10 : ℝ) ^ (-σ) * (-896041 / 1000000 : ℝ) := mul_le_mul_of_nonpos_right hau (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hslo) ha0
  have hiu : (10 : ℝ) ^ (-σ) * (-Real.sin (50 * Real.log 10)) ≤ (1 / (10 : ℝ)) * (-11171 / 12500 : ℝ) := by
    calc
      _ ≤ (10 : ℝ) ^ (-σ) * (-11171 / 12500 : ℝ) := mul_le_mul_of_nonneg_left (hshi) ha0
      _ ≤ _ := mul_le_mul_of_nonpos_right hal (by norm_num)
  have ht := boundary_term_re_im 10 (by norm_num) σ
  norm_num only [Nat.cast_ofNat] at ht
  rw [ht.1, ht.2]
  constructor <;> constructor <;> nlinarith [hrl, hru, hil, hiu]

end LeanLab.RamareSaouter2003.Decomp537a


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex

/-- Backlund p. 367, the final H rectangle from certified finite summands.
The disputed positive-part table is replaced by rational trigonometric bounds.
All real parts from one half through one are covered. -/
theorem finiteH_components (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (boundaryH σ).re ∈ Set.Icc (-0.870 : ℝ) 1.649 ∧
    (boundaryH σ).im ∈ Set.Icc (-0.684 : ℝ) 1.061 := by
  rcases term_2_bounds σ hσ with ⟨⟨r2l, r2u⟩, ⟨i2l, i2u⟩⟩
  rcases term_3_bounds σ hσ with ⟨⟨r3l, r3u⟩, ⟨i3l, i3u⟩⟩
  rcases term_4_bounds σ hσ with ⟨⟨r4l, r4u⟩, ⟨i4l, i4u⟩⟩
  rcases term_5_bounds σ hσ with ⟨⟨r5l, r5u⟩, ⟨i5l, i5u⟩⟩
  rcases term_6_bounds σ hσ with ⟨⟨r6l, r6u⟩, ⟨i6l, i6u⟩⟩
  rcases term_7_bounds σ hσ with ⟨⟨r7l, r7u⟩, ⟨i7l, i7u⟩⟩
  rcases term_8_bounds σ hσ with ⟨⟨r8l, r8u⟩, ⟨i8l, i8u⟩⟩
  rcases term_9_bounds σ hσ with ⟨⟨r9l, r9u⟩, ⟨i9l, i9u⟩⟩
  rcases term_10_bounds σ hσ with ⟨⟨r10l, r10u⟩, ⟨i10l, i10u⟩⟩
  have hset : Finset.Icc (1 : ℕ) 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  have hlast : (1 : ℂ) / (2 * (10 : ℂ) ^ ((σ : ℂ) + 50 * I)) =
      ((1 : ℂ) / (10 : ℂ) ^ ((σ : ℂ) + 50 * I)) / 2 := by ring
  unfold boundaryH
  rw [hset, hlast]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Complex.add_re, Complex.add_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im] at *
  constructor <;> constructor <;> linarith

end LeanLab.RamareSaouter2003.Decomp537a


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex MeasureTheory Circle419

/-- Backlund p. 367, the exact final rectangular enclosure of the actual H sum.
The finite summand certificates prove this enclosure independently of the
disputed positive-part table. -/
theorem boundaryH_components (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (boundaryH σ).re ∈ Set.Icc (-0.870 : ℝ) 1.649 ∧
    (boundaryH σ).im ∈ Set.Icc (-0.684 : ℝ) 1.061 := by
  exact finiteH_components σ hσ

/-- Backlund p. 367, deriving the H modulus from its rectangular enclosure. -/
theorem norm_of_boundary_components (z : ℂ)
    (hr : z.re ∈ Set.Icc (-0.870 : ℝ) 1.649)
    (hi : z.im ∈ Set.Icc (-0.684 : ℝ) 1.061) : ‖z‖ ≤ 1.962 := by
  have hreal : z.re ^ 2 ≤ (1.649 : ℝ) ^ 2 := by
    nlinarith [hr.1, hr.2]
  have himag : z.im ^ 2 ≤ (1.061 : ℝ) ^ 2 := by
    nlinarith [hi.1, hi.2]
  have hs := Complex.sq_norm z
  rw [Complex.normSq_apply] at hs
  nlinarith [norm_nonneg z]


end LeanLab.RamareSaouter2003.Decomp537a

namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex MeasureTheory

/-- Backlund p. 362, the Dirichlet series on the far right is at most three. -/
theorem tsum_rpow_le_three (σ : ℝ) (hσ : (3 / 2 : ℝ) ≤ σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 3 := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici (1 : ℝ)) := by
    intro x hx y hy hxy
    change 1 ≤ x at hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx]) hxy (by linarith)
  have hi : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hn : ∀ x ∈ Set.Ioi (1 : ℝ), 0 ≤ x ^ (-σ) := by
    intro x hx
    change 1 < x at hx
    exact Real.rpow_nonneg (by linarith [hx]) _
  have hcast : (((2 : ℕ) : ℝ) - 1) = 1 := by norm_num
  have hkey := AntitoneOn.abs_tsum_sub_sum_range_le_integral (f := fun x : ℝ => x ^ (-σ))
    (N := 2) (by norm_num) (by simpa only [hcast] using hanti) (by simpa only [hcast] using hi) (by simpa only [hcast] using hn)
  have hsum : (∑ n ∈ Finset.range 2, (n : ℝ) ^ (-σ)) = 1 := by
    have hz : -σ ≠ 0 := by linarith
    norm_num [Finset.sum_range_succ, Real.zero_rpow hz]
  have hval : (∫ x : ℝ in Set.Ioi (1 : ℝ), x ^ (-σ)) = 1 / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.one_rpow]
    rw [show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq]
  rw [hcast, hsum, hval] at hkey
  have hup := (abs_le.mp hkey).2
  have htail : 1 / (σ - 1) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < σ - 1)).mpr
    linarith
  linarith

/-- Backlund p. 362, the Dirichlet-series fallback beyond real part three halves. -/
theorem zeta_norm_le_three (σ t : ℝ) (hσ : (3 / 2 : ℝ) ≤ σ) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ 3 := by
  have hz := zeta_norm_le_tsum_re ((σ : ℂ) + t * I) (by simpa using (show 1 < σ by linarith))
  have hs := tsum_rpow_le_three σ hσ
  have hz' : ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
    simpa using hz
  exact hz'.trans hs

/-- Backlund display 54, the logarithmic majorant exceeds three from height fifty. -/
theorem right54_log_room (t : ℝ) (ht : 50 ≤ t) :
    (3 : ℝ) ≤ Real.log t - 0.048 := by
  have hlog50 : Real.log (50 : ℝ) = Real.log 2 + 2 * Real.log 5 := by
    rw [show (50 : ℝ) = 2 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 50) ht
  linarith [Real.log_two_gt_d9, Table537.log_five_bounds.1]

/-- Backlund p. 362, the positive square root separates its height factor. -/
theorem sqrt_height_scale (t a : ℝ) (ht : 0 < t) (ha : 0 ≤ a) :
    Real.sqrt (t ^ 2 + a / 4) = t * Real.sqrt (1 + a / (4 * t ^ 2)) := by
  symm
  calc
    t * Real.sqrt (1 + a / (4 * t ^ 2)) =
        Real.sqrt (t ^ 2) * Real.sqrt (1 + a / (4 * t ^ 2)) := by
      rw [Real.sqrt_sq ht.le]
    _ = Real.sqrt (t ^ 2 * (1 + a / (4 * t ^ 2))) :=
      (Real.sqrt_mul (sq_nonneg t) _).symm
    _ = Real.sqrt (t ^ 2 + a / 4) := by
      congr 1
      field_simp [ht.ne']
      <;> ring

/-- Backlund p. 362, the product of two square roots separates the squared height. -/
theorem sqrt_height_product (t : ℝ) (ht : 0 < t) :
    Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) =
      t ^ 2 * Real.sqrt ((1 + 9 / (4 * t ^ 2)) * (1 + 25 / (4 * t ^ 2))) := by
  rw [Real.sqrt_mul (by positivity), sqrt_height_scale t 9 ht (by norm_num),
    sqrt_height_scale t 25 ht (by norm_num), Real.sqrt_mul (by positivity)]
  ring

/-- Backlund p. 362, the elementary cutoff n equal to floor of t over three plus one. -/
theorem euler_cutoff_bounds (t : ℝ) (ht : 50 ≤ t) :
    1 ≤ Nat.floor (t / 3) + 1 ∧
    t / 3 < ((Nat.floor (t / 3) + 1 : ℕ) : ℝ) ∧
    ((Nat.floor (t / 3) + 1 : ℕ) : ℝ) ≤ t / 3 + 1 := by
  constructor
  · omega
  constructor
  · simpa using Nat.lt_floor_add_one (t / 3)
  · have h := Nat.floor_le (show 0 ≤ t / 3 by linarith)
    simpa using add_le_add_right h 1

/-- Backlund p. 362, the logarithm of the chosen cutoff has the printed loss. -/
theorem euler_cutoff_log (t n : ℝ) (ht : 50 ≤ t) (hn : 0 < n) (hhi : n ≤ t / 3 + 1) :
    Real.log n ≤ Real.log t - Real.log 3 + 3 / t := by
  have htpos : 0 < t := by linarith
  have hlog := Real.log_le_log hn hhi
  have hp : t / 3 + 1 = (t / 3) * (1 + 3 / t) := by field_simp [htpos.ne'] <;> ring
  rw [hp, Real.log_mul (by positivity) (by positivity),
    Real.log_div htpos.ne' (by norm_num : (3 : ℝ) ≠ 0)] at hlog
  have hsmall := Real.log_le_sub_one_of_pos (show 0 < 1 + 3 / t by positivity)
  linarith

/-- Backlund p. 362, inverse-square loss for the chosen cutoff. -/
theorem euler_cutoff_inverse (t n : ℝ) (ht : 0 < t) (hn : 0 < n) (hlo : t / 3 ≤ n) :
    1 / n ^ 2 ≤ 9 / t ^ 2 := by
  apply (div_le_div_iff₀ (by positivity : 0 < n ^ 2) (by positivity : 0 < t ^ 2)).mpr
  have h := pow_le_pow_left₀ ht.le (show t ≤ 3 * n by linarith) 2
  nlinarith

end LeanLab.RamareSaouter2003.Decomp537a


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex Filter
open scoped Topology

/-- Backlund p. 361, the elementary trapezoid bound underlying the harmonic half-term. -/
theorem log_trapezoid_bound (x : ℝ) (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / (2 * x) + 1 / (2 * (x + 1)) := by
  set y : ℝ := 1 / (2 * x + 1)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y < 1 := by
    dsimp [y]
    apply (div_lt_one (by linarith : 0 < 2 * x + 1)).mpr
    linarith
  have hyd : 1 - y ≠ 0 := by linarith
  have hyd2 : 1 - y ^ 2 ≠ 0 := by nlinarith
  have hd : 2 * x + 1 ≠ 0 := by linarith
  have hratio : (1 + y) / (1 - y) = (x + 1) / x := by
    dsimp [y] at *
    field_simp [hx.ne', hd, hyd]
    <;> ring
  have hrem : y / (1 - y ^ 2) = 1 / (4 * x) + 1 / (4 * (x + 1)) := by
    apply (div_eq_iff hyd2).mpr
    dsimp [y]
    field_simp [hx.ne', hd, show x + 1 ≠ 0 by linarith]
    <;> ring
  have h := Real.log_div_le_sum_range_add hy0 hy1 0
  norm_num only [Finset.sum_range_zero, zero_add, mul_zero, zero_add, pow_one] at h
  rw [hratio, Real.log_div (by linarith : x + 1 ≠ 0) hx.ne', hrem] at h
  convert (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;>
    field_simp <;> ring

/-- Backlund p. 361, the harmonic sum with its half endpoint is below log plus C. -/
theorem harmonic_half_bound (n : ℕ) :
    (harmonic n : ℝ) + 1 / (2 * ((n + 1 : ℕ) : ℝ)) ≤
      Real.log ((n + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant := by
  let F : ℕ → ℝ := fun k =>
    (harmonic (k + 1) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ) -
      1 / (2 * ((k + 1 : ℕ) : ℝ))
  have hmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro k
    have hlog := log_trapezoid_bound ((k + 1 : ℕ) : ℝ) (by positivity)
    dsimp [F]
    simp only [harmonic_succ]
    push_cast
    norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at hlog ⊢
    linarith
  have hnat : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv0 := (tendsto_inv_atTop_zero.comp hnat).div_const (2 : ℝ)
  have hinv : Tendsto (fun k : ℕ => 1 / (2 * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, mul_inv_rev, div_eq_mul_inv, zero_mul, Function.comp_apply, one_mul] using hinv0
  have hseq := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto F atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [F, Function.comp_apply, sub_zero] using hseq.sub hinv
  have hb := hmono.ge_of_tendsto hlim n
  dsimp [F] at hb
  rw [harmonic_succ] at hb
  push_cast at hb
  norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at hb ⊢
  linarith

/-- Backlund p. 361, the exact harmonic endpoint form used in display 52. -/
theorem harmonic_endpoint_bound (n : ℕ) (hn : 1 ≤ n) :
    (harmonic (n - 1) : ℝ) + 1 / (2 * (n : ℝ)) ≤
      Real.log (n : ℝ) + Real.eulerMascheroniConstant := by
  have h := harmonic_half_bound (n - 1)
  simpa only [Nat.sub_add_cancel hn] using h

/-- Backlund p. 361, the pointwise absolute bound for the periodic second Bernoulli polynomial. -/
theorem bernoulli_two_bound (x : ℝ) :
    |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| ≤ (1 / 6 : ℝ) := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
  · nlinarith

end LeanLab.RamareSaouter2003.Decomp537a


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex MeasureTheory

/-! ## Euler–Maclaurin bricks for the leaf `euler8_bernoulli_bound`. -/

open Set Filter
open scoped Topology

set_option maxHeartbeats 2000000

private theorem hasDerivWithinAt_fract537 (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => Int.fract y) 1 (Set.Ioi x) x := by
  have hfloor : ∀ᶠ y in 𝓝[Set.Ioi x] x, (⌊y⌋ : ℝ) = (⌊x⌋ : ℝ) := by
    have hopen : Set.Iio ((⌊x⌋ : ℝ) + 1) ∈ 𝓝 (x : ℝ) :=
      isOpen_Iio.mem_nhds (Int.lt_floor_add_one x)
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with y hy hyx
    have hyx' : x < y := hyx
    have h : ⌊y⌋ = ⌊x⌋ :=
      Int.floor_eq_iff.mpr ⟨by linarith [Int.floor_le x], hy⟩
    exact_mod_cast h
  have heq : (fun y : ℝ => y - (⌊x⌋ : ℝ)) =ᶠ[𝓝[Set.Ioi x] x] (fun y : ℝ => Int.fract y) := by
    filter_upwards [hfloor] with y hy
    rw [← hy]
    exact Int.self_sub_floor y
  have hpt : x - (⌊x⌋ : ℝ) = Int.fract x := Int.self_sub_floor x
  exact (heq.hasDerivWithinAt_iff hpt).mp ((hasDerivAt_id x).sub_const (⌊x⌋ : ℝ)).hasDerivWithinAt


private theorem hasDerivWithinAt_q537 (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => Int.fract y ^ 2 / 2 - Int.fract y / 2 + 1 / 12)
      (Int.fract x - 1 / 2) (Set.Ioi x) x := by
  have h := hasDerivWithinAt_fract537 x
  have h2 : HasDerivWithinAt (fun y : ℝ => Int.fract y ^ 2 / 2) (Int.fract x) (Set.Ioi x) x := by
    have hp := h.pow 2
    have hd := hp.div_const 2
    convert hd using 1
    ring
  have h3 : HasDerivWithinAt (fun y : ℝ => Int.fract y / 2) (1 / 2) (Set.Ioi x) x := by
    have hd := h.div_const 2
    simpa using hd
  have h4 := (h2.sub h3).add_const (1 / 12)
  convert h4 using 1


private theorem continuous_q_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 := by
  have h : ContinuousOn (fun y : ℝ => y ^ 2 / 2 - y / 2 + 1 / 12) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hf : (fun y : ℝ => y ^ 2 / 2 - y / 2 + 1 / 12) 0
      = (fun y : ℝ => y ^ 2 / 2 - y / 2 + 1 / 12) 1 := by norm_num
  simpa [Function.comp_def] using h.comp_fract'' hf

private theorem abs_q_le537 (x : ℝ) :
    |Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12| ≤ 1 / 12 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have h2 : Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12
      = (Int.fract x - 1 / 2) ^ 2 / 2 - 1 / 24 := by ring
  rw [h2, abs_le]
  have h3 : (Int.fract x - 1 / 2) ^ 2 ≤ 1 / 4 := by
    nlinarith [h0, h1, mul_nonneg h0 (sub_nonneg.mpr h1.le)]
  constructor <;> nlinarith

private theorem intervalIntegrable_b537 (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => ((Int.fract x - 1 / 2 : ℝ) : ℂ)) volume a b := by
  rw [intervalIntegrable_iff']
  refine Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1) ?_
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

private theorem intervalIntegrable_q537 (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  exact (Complex.continuous_ofReal.comp continuous_q_fract537).continuousOn

private theorem ibp_q537 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in a..b, ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))
      = ((Int.fract b ^ 2 / 2 - Int.fract b / 2 + 1 / 12 : ℝ) : ℂ) * (b : ℂ) ^ (-(s + 1))
        - ((Int.fract a ^ 2 / 2 - Int.fract a / 2 + 1 / 12 : ℝ) : ℂ) * (a : ℂ) ^ (-(s + 1))
        + (s + 1) * ∫ x in a..b,
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
  have hne : (-(s + 1) : ℂ) ≠ 0 := by
    intro h
    have h0 : (-(s + 1) : ℂ).re = 0 := by rw [h]; simp
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re] at h0
    linarith
  have hpos : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  have hu : ContinuousOn
      (fun y : ℝ => ((Int.fract y ^ 2 / 2 - Int.fract y / 2 + 1 / 12 : ℝ) : ℂ)) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp continuous_q_fract537).continuousOn
  have hv : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (-(s + 1))) (Set.uIcc a b) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).continuousWithinAt
  have huu' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt
        (fun y : ℝ => ((Int.fract y ^ 2 / 2 - Int.fract y / 2 + 1 / 12 : ℝ) : ℂ))
        ((Int.fract x - 1 / 2 : ℝ) : ℂ) (Set.Ioi x) x := fun x _ =>
    (hasDerivWithinAt_q537 x).ofReal_comp
  have hvv' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + 1)))
        ((-(s + 1)) * (x : ℂ) ^ (-(s + 2))) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hd : HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + 1)))
        ((-(s + 1)) * (x : ℂ) ^ (-(s + 1) - 1)) (Set.Ioi x) x :=
      (hasDerivAt_ofReal_cpow_const hx0 hne).hasDerivWithinAt
    convert hd using 1
    ring
  have hu' : IntervalIntegrable (fun x : ℝ => ((Int.fract x - 1 / 2 : ℝ) : ℂ)) volume a b :=
    intervalIntegrable_b537 a b
  have hv' : IntervalIntegrable (fun y : ℝ => (-(s + 1)) * (y : ℂ) ^ (-(s + 2))) volume a b := by
    refine ContinuousOn.intervalIntegrable (u := fun y : ℝ => (-(s + 1)) * (y : ℂ) ^ (-(s + 2))) ?_
    intro x hx
    exact ((Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).const_mul
      (-(s + 1))).continuousWithinAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu hv huu' hvv' hu' hv'
  have hleft : ∫ x in a..b,
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) *
        ((-(s + 1)) * (x : ℂ) ^ (-(s + 2)))
      = -(s + 1) * ∫ x in a..b,
          ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hleft] at key
  linear_combination key


private theorem integrable_b_Ioi537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNR
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith
  have hmble : AEStronglyMeasurable
      (fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2)) (volume.restrict (Set.Ioi (N : ℝ))) := by
    have hmeas : Measurable fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2) :=
      (Complex.continuous_ofReal.measurable.comp measurable_fract).sub measurable_const
    exact hmeas.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioi (N : ℝ))),
      ‖(((Int.fract x : ℝ) : ℂ) - 1 / 2)‖ ≤ 1 := by
    filter_upwards with x
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    have he : (((Int.fract x : ℝ) : ℂ) - 1 / 2) = ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  exact (hcp.bdd_mul hmble hbdd).congr (ae_of_all _ (fun x => by ring))


private theorem floor_kernel_eq537 (x : ℝ) :
    (((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - ((x : ℝ) : ℂ)) = -((((Int.fract x : ℝ)) : ℂ) - 1 / 2) := by
  have h : ((Int.fract x : ℝ)) = x - ((⌊x⌋ : ℤ) : ℝ) := Int.self_sub_floor x
  rw [h]
  push_cast
  ring

/-- The `q`-kernel is integrable against `x ^ (-(s+2))` on `Ioi N`. -/
private theorem integrable_q_Ioi537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ =>
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))
      (Set.Ioi (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(s + 2))) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNR
    simp only [Complex.neg_re, Complex.add_re]
    norm_num
    linarith
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ))
      (volume.restrict (Set.Ioi (N : ℝ))) :=
    Complex.continuous_ofReal.measurable.comp continuous_q_fract537.measurable |>.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioi (N : ℝ))),
      ‖((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ)‖ ≤ 1 := by
    filter_upwards with x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_q_le537 x).trans (by norm_num)
  exact (hcp.bdd_mul hmeas hbdd).congr (ae_of_all _ (fun x => by ring))

/-- The second-order Euler–Maclaurin formula on a finite interval `[N, M]`. -/
private theorem em_one_interval537 (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) {s : ℂ}
    (hs : 0 < s.re) :
    ∫ x in (N : ℝ)..(M : ℝ), (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1))
      = (1 / 12) * (((M : ℝ) : ℂ) ^ (-(s + 1)) - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * ∫ x in (N : ℝ)..(M : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hq := ibp_q537 (N : ℝ) (M : ℝ) hNR hNMR hs
  have hgoal : (∫ x in (N : ℝ)..(M : ℝ),
        (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      = ∫ x in (N : ℝ)..(M : ℝ),
          ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    push_cast
    ring
  rw [hgoal, hq]
  have e1 : ((Int.fract ((M : ℝ)) ^ 2 / 2 - Int.fract ((M : ℝ)) / 2 + 1 / 12 : ℝ) : ℂ)
      = (1 / 12 : ℂ) := by rw [Int.fract_natCast]; norm_num
  have e2 : ((Int.fract ((N : ℝ)) ^ 2 / 2 - Int.fract ((N : ℝ)) / 2 + 1 / 12 : ℝ) : ℂ)
      = (1 / 12 : ℂ) := by rw [Int.fract_natCast]; norm_num
  rw [e1, e2]
  ring

/-- The `b`-kernel integral on `Ioi N` in terms of the `q`-kernel. -/
private theorem em_one_Ioi537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Set.Ioi (N : ℝ), (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      = -(1 / 12) * ((N : ℝ) : ℂ) ^ (-(s + 1))
        + (s + 1) * (∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))) := by
  have hlim_b := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
    (b := fun n : ℕ => ((n : ℝ)))
    (f := fun x : ℝ => (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
    ((N : ℝ)) (integrable_b_Ioi537 N hN hs) tendsto_natCast_atTop_atTop
  have hlim_q := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
    (b := fun n : ℕ => ((n : ℝ)))
    (f := fun x : ℝ =>
      ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))
    ((N : ℝ)) (integrable_q_Ioi537 N hN hs) tendsto_natCast_atTop_atTop
  have hM : Tendsto (fun M : ℕ => (((M : ℝ) : ℂ)) ^ (-(s + 1))) Filter.atTop (𝓝 0) := by
    have h := Complex.cpow_tendsto (s := s + 2)
      (show (1 : ℝ) < (s + 2).re by simp only [Complex.add_re]; norm_num; linarith)
    refine h.congr (fun M => ?_)
    push_cast
    congr 1
    ring
  have hlim_c : Tendsto (fun M : ℕ =>
      (1 / 12) * ((((M : ℝ) : ℂ)) ^ (-(s + 1)) - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * (∫ x in (N : ℝ)..((M : ℝ)),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))))
      Filter.atTop
      (𝓝 ((1 / 12) * (0 - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * (∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))))) :=
    ((hM.sub_const _).const_mul _).add (hlim_q.const_mul _)
  have heq : (fun M : ℕ => ∫ x in (N : ℝ)..((M : ℝ)),
      (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1)))
      =ᶠ[Filter.atTop] (fun M : ℕ =>
      (1 / 12) * ((((M : ℝ) : ℂ)) ^ (-(s + 1)) - ((N : ℝ) : ℂ) ^ (-(s + 1)))
        + (s + 1) * (∫ x in (N : ℝ)..((M : ℝ)),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))) := by
    filter_upwards [Filter.eventually_ge_atTop N] with M hM'
    exact em_one_interval537 N M hN hM' hs
  have hfin := tendsto_nhds_unique hlim_b (hlim_c.congr' heq.symm)
  rw [hfin]
  ring

/-- Second-order Euler–Maclaurin for `ζ` with the `q`-kernel remainder, on `Re s > 0`. -/
private theorem em_q_zeta537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s
      = (∑ n ∈ Finset.range (N + 1), (1 : ℂ) / (n : ℂ) ^ s)
        + (-(N : ℂ) ^ (1 - s)) / (1 - s) + (-(N : ℂ) ^ (-s)) / 2
        + s * (1 / 12) * (N : ℂ) ^ (-(s + 1))
        - s * (s + 1) * (∫ x in Set.Ioi (N : ℝ),
            ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))) := by
  have hz : riemannZeta0 N s = riemannZeta s := Zeta0EqZeta hN hs h1
  rw [← hz, riemannZeta0_apply]
  have hker : (∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
      = -(∫ x in Set.Ioi (N : ℝ),
          (((Int.fract x : ℝ) : ℂ) - 1 / 2) * (x : ℂ) ^ (-(s + 1))) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [floor_kernel_eq537]
    ring
  rw [hker, em_one_Ioi537 N hN hs]
  push_cast
  ring

private theorem hasDerivAt_fract_comp537 (u w : ℝ → ℝ)
    (hw' : ∀ t : ℝ, HasDerivAt w (u t) t) (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => ((w (Int.fract y) : ℝ) : ℂ))
      ((u (Int.fract x) : ℝ) : ℂ) (Set.Ioi x) x := by
  have h := (hw' (Int.fract x)).comp_hasDerivWithinAt x (hasDerivWithinAt_fract537 x)
  rw [mul_one] at h
  exact h.ofReal_comp

private theorem ibp_interval_gen537 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (k : ℂ)
    (hk : 1 < (s + k).re) (u w : ℝ → ℝ)
    (hu_c : Continuous fun x : ℝ => u (Int.fract x))
    (hw_c : Continuous fun x : ℝ => w (Int.fract x))
    (hw' : ∀ t : ℝ, HasDerivAt w (u t) t) :
    ∫ x in a..b, ((u (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k))
      = ((w (Int.fract b) : ℝ) : ℂ) * (b : ℂ) ^ (-(s + k))
        - ((w (Int.fract a) : ℝ) : ℂ) * (a : ℂ) ^ (-(s + k))
        + (s + k) * ∫ x in a..b, ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k + 1)) := by
  have hne : (-(s + k) : ℂ) ≠ 0 := by
    intro h
    have h0 : (-(s + k) : ℂ).re = 0 := by rw [h]; simp
    simp only [Complex.neg_re] at h0
    linarith
  have hpos : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  have hu : ContinuousOn (fun y : ℝ => ((w (Int.fract y) : ℝ) : ℂ)) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp hw_c).continuousOn
  have hv : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (-(s + k))) (Set.uIcc a b) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).continuousWithinAt
  have huu' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt (fun y : ℝ => ((w (Int.fract y) : ℝ) : ℂ))
        ((u (Int.fract x) : ℝ) : ℂ) (Set.Ioi x) x := fun x _ =>
    hasDerivAt_fract_comp537 u w hw' x
  have hvv' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + k)))
        ((-(s + k)) * (x : ℂ) ^ (-(s + k + 1))) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hd : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-(s + k)))
        ((-(s + k)) * (x : ℂ) ^ (-(s + k) - 1)) x :=
      hasDerivAt_ofReal_cpow_const (x := x) (r := -(s + k)) hx0 hne
    have hd2 : HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + k)))
        ((-(s + k)) * (x : ℂ) ^ (-(s + k) - 1)) (Set.Ioi x) x := hd.hasDerivWithinAt
    convert hd2 using 2
    ring
  have hu' : IntervalIntegrable (fun x : ℝ => ((u (Int.fract x) : ℝ) : ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp hu_c).continuousOn.intervalIntegrable
  have hv' : IntervalIntegrable (fun y : ℝ => (-(s + k)) * (y : ℂ) ^ (-(s + k + 1)))
      volume a b := by
    refine ContinuousOn.intervalIntegrable
      (u := fun y : ℝ => (-(s + k)) * (y : ℂ) ^ (-(s + k + 1))) ?_
    intro x hx
    exact ((Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hpos x hx))).const_mul
      (-(s + k))).continuousWithinAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu hv huu' hvv' hu' hv'
  have hleft : ∫ x in a..b,
      ((w (Int.fract x) : ℝ) : ℂ) * ((-(s + k)) * (x : ℂ) ^ (-(s + k + 1)))
      = -(s + k) * ∫ x in a..b,
          ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k + 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hleft] at key
  linear_combination key

private theorem integrable_fract_cpow537 (N : ℕ) (hN : 1 ≤ N) (u : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    {s : ℂ} (k : ℂ) (hk : 1 < (s + k).re)
    (hu_c : Continuous fun x : ℝ => u (Int.fract x))
    (hu_b : ∀ x : ℝ, |u (Int.fract x)| ≤ c) :
    IntegrableOn (fun x : ℝ => ((u (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k)))
      (Set.Ioi (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(s + k))) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNR
    simp only [Complex.neg_re]
    linarith
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ((u (Int.fract x) : ℝ) : ℂ))
      (volume.restrict (Set.Ioi (N : ℝ))) :=
    (Complex.continuous_ofReal.comp hu_c).measurable.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Ioi (N : ℝ))),
      ‖((u (Int.fract x) : ℝ) : ℂ)‖ ≤ c := by
    filter_upwards with x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hu_b x
  exact hcp.bdd_mul hmeas hbdd

private theorem ibp_Ioi_gen537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ}
    (k : ℕ) (hk : 1 < (s + (k : ℂ)).re) (u w : ℝ → ℝ)
    (hu_c : Continuous fun x : ℝ => u (Int.fract x))
    (hw_c : Continuous fun x : ℝ => w (Int.fract x))
    (hw' : ∀ t : ℝ, HasDerivAt w (u t) t)
    (hu_int : IntegrableOn (fun x : ℝ => ((u (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ))))
      (Set.Ioi (N : ℝ)))
    (hw_int : IntegrableOn (fun x : ℝ =>
        ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ))))
      (Set.Ioi (N : ℝ))) :
    (∫ x in Set.Ioi (N : ℝ), ((u (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ))))
      = -(((w 0 : ℝ) : ℂ)) * (N : ℂ) ^ (-(s + (k : ℂ)))
        + (s + (k : ℂ)) * (∫ x in Set.Ioi (N : ℝ),
            ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ)))) := by
  rw [show (-(s + ((k + 1 : ℕ) : ℂ)) : ℂ) = -(s + (k : ℂ) + 1) by push_cast; ring] at hw_int ⊢
  have hlim_u := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
    (b := fun n : ℕ => ((n : ℝ)))
    (f := fun x : ℝ => ((u (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k)))
    ((N : ℝ)) hu_int tendsto_natCast_atTop_atTop
  have hlim_w := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := Filter.atTop)
    (b := fun n : ℕ => ((n : ℝ)))
    (f := fun x : ℝ => ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k + 1)))
    ((N : ℝ)) hw_int tendsto_natCast_atTop_atTop
  have hM : Tendsto (fun M : ℕ => ((w (Int.fract ((M : ℝ))) : ℝ) : ℂ) *
      (((M : ℝ) : ℂ)) ^ (-(s + k))) Filter.atTop (𝓝 0) := by
    have hbase : Tendsto (fun M : ℕ => (((M : ℝ)) : ℂ) ^ (-(s + k))) Filter.atTop (𝓝 0) := by
      have hk1 : (1 : ℝ) < (s + k + 1).re := by
        have e : (s + k + 1).re = (s + k).re + 1 := by simp
        rw [e]; linarith
      have h := Complex.cpow_tendsto (s := s + k + 1) hk1
      refine h.congr (fun M => ?_)
      push_cast
      congr 1
      ring
    have h0 : ∀ M : ℕ, (Int.fract ((M : ℝ))) = 0 := fun M => Int.fract_natCast M
    have := hbase.const_mul (((w 0 : ℝ) : ℂ))
    simpa only [h0, mul_zero] using this
  have hlim_c : Tendsto (fun M : ℕ =>
      ((w (Int.fract ((M : ℝ))) : ℝ) : ℂ) * (((M : ℝ) : ℂ)) ^ (-(s + k))
        - ((w (Int.fract ((N : ℝ))) : ℝ) : ℂ) * ((N : ℂ)) ^ (-(s + k))
        + (s + k) * (∫ x in (N : ℝ)..((M : ℝ)),
            ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k + 1))))
      Filter.atTop (𝓝 (0 - ((w (Int.fract ((N : ℝ))) : ℝ) : ℂ) * ((N : ℂ)) ^ (-(s + k))
        + (s + k) * (∫ x in Set.Ioi (N : ℝ),
            ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k + 1))))) :=
    (hM.sub_const _).add (hlim_w.const_mul _)
  have heq : (fun M : ℕ => ∫ x in (N : ℝ)..((M : ℝ)),
      ((u (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k)))
      =ᶠ[Filter.atTop] (fun M : ℕ =>
      ((w (Int.fract ((M : ℝ))) : ℝ) : ℂ) * (((M : ℝ) : ℂ)) ^ (-(s + k))
        - ((w (Int.fract ((N : ℝ))) : ℝ) : ℂ) * ((N : ℂ)) ^ (-(s + k))
        + (s + k) * (∫ x in (N : ℝ)..((M : ℝ)),
            ((w (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + k + 1)))) := by
    filter_upwards [Filter.eventually_ge_atTop N] with M hMN
    exact ibp_interval_gen537 (N : ℝ) (M : ℝ) (by exact_mod_cast hN)
      (by exact_mod_cast hMN) (k := k) hk u w hu_c hw_c hw'
  have hfin := tendsto_nhds_unique hlim_u (hlim_c.congr' heq.symm)
  rw [hfin]
  simp only [Int.fract_natCast]
  push_cast
  ring

/-- `10 ^ (-1/2) ≤ 0.3163`. -/
private theorem pow10_neg_half_le537 : (10 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 0.3163 := by
  have h : (10 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 10 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  rw [h, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  have h2 : (3.1622 : ℝ) ≤ Real.sqrt 10 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  nlinarith

/-- `10 ^ (-Re s) ≤ 0.3163` for `Re s ≥ 1/2`. -/
private theorem pow10_neg_re_le537 {s : ℂ} (hσ : (1 / 2 : ℝ) ≤ s.re) :
    (10 : ℝ) ^ (-s.re) ≤ 0.3163 := by
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 10) (by linarith)).trans
    pow10_neg_half_le537

/-- `‖10 ^ (-(s+k))‖ ≤ 0.3163 · 10 ^ (-k)`. -/
private theorem norm_pow10_le537 {s : ℂ} (hσ : (1 / 2 : ℝ) ≤ s.re) (k : ℕ) :
    ‖(10 : ℂ) ^ (-(s + (k : ℂ)))‖ ≤ 0.3163 * (10 : ℝ) ^ (-(k : ℝ)) := by
  rw [show (10 : ℂ) = ((10 : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 10)]
  have hre : (-(s + (k : ℂ))).re = -(s.re + (k : ℝ)) := by simp
  rw [hre]
  have hmono : (10 : ℝ) ^ (-(s.re + (k : ℝ))) ≤ (10 : ℝ) ^ (-((1 / 2 : ℝ) + (k : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hsplit : (10 : ℝ) ^ (-((1 / 2 : ℝ) + (k : ℝ)))
      = (10 : ℝ) ^ (-(1 / 2 : ℝ)) * (10 : ℝ) ^ (-(k : ℝ)) := by
    rw [show (-((1 / 2 : ℝ) + (k : ℝ))) = -(1 / 2 : ℝ) + (-(k : ℝ)) by ring,
      Real.rpow_add (by norm_num)]
  calc (10 : ℝ) ^ (-(s.re + (k : ℝ)))
      ≤ (10 : ℝ) ^ (-((1 / 2 : ℝ) + (k : ℝ))) := hmono
    _ = (10 : ℝ) ^ (-(1 / 2 : ℝ)) * (10 : ℝ) ^ (-(k : ℝ)) := hsplit
    _ ≤ 0.3163 * (10 : ℝ) ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right pow10_neg_half_le537 (Real.rpow_nonneg (by norm_num) _)

private theorem continuous_u2_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 2 / 2 - Int.fract x / 2 + (1/12:ℝ) := by
  have h : ContinuousOn (fun y : ℝ => y ^ 2 / 2 - y / 2 + (1/12:ℝ)) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 2 / 2 - y / 2 + (1/12:ℝ)) 0 = (fun y : ℝ => y ^ 2 / 2 - y / 2 + (1/12:ℝ)) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u3_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 3 / 6 - Int.fract x ^ 2 / 4 + Int.fract x / 12 := by
  have h : ContinuousOn (fun y : ℝ => y ^ 3 / 6 - y ^ 2 / 4 + y / 12) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 3 / 6 - y ^ 2 / 4 + y / 12) 0 = (fun y : ℝ => y ^ 3 / 6 - y ^ 2 / 4 + y / 12) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u4_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 4 / 24 - Int.fract x ^ 3 / 12 + Int.fract x ^ 2 / 24 - (1/720:ℝ) := by
  have h : ContinuousOn (fun y : ℝ => y ^ 4 / 24 - y ^ 3 / 12 + y ^ 2 / 24 - (1/720:ℝ)) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 4 / 24 - y ^ 3 / 12 + y ^ 2 / 24 - (1/720:ℝ)) 0 = (fun y : ℝ => y ^ 4 / 24 - y ^ 3 / 12 + y ^ 2 / 24 - (1/720:ℝ)) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u5_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 5 / 120 - Int.fract x ^ 4 / 48 + Int.fract x ^ 3 / 72 - Int.fract x / 720 := by
  have h : ContinuousOn (fun y : ℝ => y ^ 5 / 120 - y ^ 4 / 48 + y ^ 3 / 72 - y / 720) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 5 / 120 - y ^ 4 / 48 + y ^ 3 / 72 - y / 720) 0 = (fun y : ℝ => y ^ 5 / 120 - y ^ 4 / 48 + y ^ 3 / 72 - y / 720) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u6_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 6 / 720 - Int.fract x ^ 5 / 240 + Int.fract x ^ 4 / 288 - Int.fract x ^ 2 / 1440 + (1/30240:ℝ) := by
  have h : ContinuousOn (fun y : ℝ => y ^ 6 / 720 - y ^ 5 / 240 + y ^ 4 / 288 - y ^ 2 / 1440 + (1/30240:ℝ)) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 6 / 720 - y ^ 5 / 240 + y ^ 4 / 288 - y ^ 2 / 1440 + (1/30240:ℝ)) 0 = (fun y : ℝ => y ^ 6 / 720 - y ^ 5 / 240 + y ^ 4 / 288 - y ^ 2 / 1440 + (1/30240:ℝ)) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u7_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 7 / 5040 - Int.fract x ^ 6 / 1440 + Int.fract x ^ 5 / 1440 - Int.fract x ^ 3 / 4320 + Int.fract x / 30240 := by
  have h : ContinuousOn (fun y : ℝ => y ^ 7 / 5040 - y ^ 6 / 1440 + y ^ 5 / 1440 - y ^ 3 / 4320 + y / 30240) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 7 / 5040 - y ^ 6 / 1440 + y ^ 5 / 1440 - y ^ 3 / 4320 + y / 30240) 0 = (fun y : ℝ => y ^ 7 / 5040 - y ^ 6 / 1440 + y ^ 5 / 1440 - y ^ 3 / 4320 + y / 30240) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u8_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 8 / 40320 - Int.fract x ^ 7 / 10080 + Int.fract x ^ 6 / 8640 - Int.fract x ^ 4 / 17280 + Int.fract x ^ 2 / 60480 - (1/1209600:ℝ) := by
  have h : ContinuousOn (fun y : ℝ => y ^ 8 / 40320 - y ^ 7 / 10080 + y ^ 6 / 8640 - y ^ 4 / 17280 + y ^ 2 / 60480 - (1/1209600:ℝ)) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 8 / 40320 - y ^ 7 / 10080 + y ^ 6 / 8640 - y ^ 4 / 17280 + y ^ 2 / 60480 - (1/1209600:ℝ)) 0 = (fun y : ℝ => y ^ 8 / 40320 - y ^ 7 / 10080 + y ^ 6 / 8640 - y ^ 4 / 17280 + y ^ 2 / 60480 - (1/1209600:ℝ)) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u9_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 9 / 362880 - Int.fract x ^ 8 / 80640 + Int.fract x ^ 7 / 60480 - Int.fract x ^ 5 / 86400 + Int.fract x ^ 3 / 181440 - Int.fract x / 1209600 := by
  have h : ContinuousOn (fun y : ℝ => y ^ 9 / 362880 - y ^ 8 / 80640 + y ^ 7 / 60480 - y ^ 5 / 86400 + y ^ 3 / 181440 - y / 1209600) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 9 / 362880 - y ^ 8 / 80640 + y ^ 7 / 60480 - y ^ 5 / 86400 + y ^ 3 / 181440 - y / 1209600) 0 = (fun y : ℝ => y ^ 9 / 362880 - y ^ 8 / 80640 + y ^ 7 / 60480 - y ^ 5 / 86400 + y ^ 3 / 181440 - y / 1209600) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u10_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 10 / 3628800 - Int.fract x ^ 9 / 725760 + Int.fract x ^ 8 / 483840 - Int.fract x ^ 6 / 518400 + Int.fract x ^ 4 / 725760 - Int.fract x ^ 2 / 2419200 + (1/47900160:ℝ) := by
  have h : ContinuousOn (fun y : ℝ => y ^ 10 / 3628800 - y ^ 9 / 725760 + y ^ 8 / 483840 - y ^ 6 / 518400 + y ^ 4 / 725760 - y ^ 2 / 2419200 + (1/47900160:ℝ)) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 10 / 3628800 - y ^ 9 / 725760 + y ^ 8 / 483840 - y ^ 6 / 518400 + y ^ 4 / 725760 - y ^ 2 / 2419200 + (1/47900160:ℝ)) 0 = (fun y : ℝ => y ^ 10 / 3628800 - y ^ 9 / 725760 + y ^ 8 / 483840 - y ^ 6 / 518400 + y ^ 4 / 725760 - y ^ 2 / 2419200 + (1/47900160:ℝ)) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u11_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 11 / 39916800 - Int.fract x ^ 10 / 7257600 + Int.fract x ^ 9 / 4354560 - Int.fract x ^ 7 / 3628800 + Int.fract x ^ 5 / 3628800 - Int.fract x ^ 3 / 7257600 + Int.fract x / 47900160 := by
  have h : ContinuousOn (fun y : ℝ => y ^ 11 / 39916800 - y ^ 10 / 7257600 + y ^ 9 / 4354560 - y ^ 7 / 3628800 + y ^ 5 / 3628800 - y ^ 3 / 7257600 + y / 47900160) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 11 / 39916800 - y ^ 10 / 7257600 + y ^ 9 / 4354560 - y ^ 7 / 3628800 + y ^ 5 / 3628800 - y ^ 3 / 7257600 + y / 47900160) 0 = (fun y : ℝ => y ^ 11 / 39916800 - y ^ 10 / 7257600 + y ^ 9 / 4354560 - y ^ 7 / 3628800 + y ^ 5 / 3628800 - y ^ 3 / 7257600 + y / 47900160) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem continuous_u12_fract537 :
    Continuous fun x : ℝ => Int.fract x ^ 12 / 479001600 - Int.fract x ^ 11 / 79833600 + Int.fract x ^ 10 / 43545600 - Int.fract x ^ 8 / 29030400 + Int.fract x ^ 6 / 21772800 - Int.fract x ^ 4 / 29030400 + Int.fract x ^ 2 / 95800320 - (691/1307674368000:ℝ) := by
  have h : ContinuousOn (fun y : ℝ => y ^ 12 / 479001600 - y ^ 11 / 79833600 + y ^ 10 / 43545600 - y ^ 8 / 29030400 + y ^ 6 / 21772800 - y ^ 4 / 29030400 + y ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hf : (fun y : ℝ => y ^ 12 / 479001600 - y ^ 11 / 79833600 + y ^ 10 / 43545600 - y ^ 8 / 29030400 + y ^ 6 / 21772800 - y ^ 4 / 29030400 + y ^ 2 / 95800320 - (691/1307674368000:ℝ)) 0 = (fun y : ℝ => y ^ 12 / 479001600 - y ^ 11 / 79833600 + y ^ 10 / 43545600 - y ^ 8 / 29030400 + y ^ 6 / 21772800 - y ^ 4 / 29030400 + y ^ 2 / 95800320 - (691/1307674368000:ℝ)) 1 := by norm_num
  exact h.comp_fract'' hf

private theorem abs_u2_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 2 / 2 - t / 2 + (1/12:ℝ)| ≤ (41666667/50000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (41666667/50000000:ℝ) - (t ^ 2 / 2 - t / 2 + (1/12:ℝ)) =(112500001/150000000:ℝ) * (1 - t) ^ 2 + (150000001/75000000:ℝ) * t * (1 - t) + (112500001/150000000:ℝ) * t ^ 2 := by ring
  have e2 : (41666667/50000000:ℝ) + (t ^ 2 / 2 - t / 2 + (1/12:ℝ)) =(137500001/150000000:ℝ) * (1 - t) ^ 2 + (100000001/75000000:ℝ) * t * (1 - t) + (137500001/150000000:ℝ) * t ^ 2 := by ring
  have p1 : (0:ℝ) ≤ (112500001/150000000:ℝ) * (1 - t) ^ 2 + (150000001/75000000:ℝ) * t * (1 - t) + (112500001/150000000:ℝ) * t ^ 2 := by
    have ht0 : (0:ℝ) ≤ (112500001/150000000:ℝ) * (1 - t) ^ 2 := mul_nonneg (by norm_num : (0:ℝ) ≤ (112500001/150000000:ℝ)) (pow_nonneg hone 2)
    have ht1 : (0:ℝ) ≤ (150000001/75000000:ℝ) * t * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (150000001/75000000:ℝ)) (h0)) (hone)
    have ht2 : (0:ℝ) ≤ (112500001/150000000:ℝ) * t ^ 2 := mul_nonneg (by norm_num : (0:ℝ) ≤ (112500001/150000000:ℝ)) (pow_nonneg h0 2)
    linarith
  have p2 : (0:ℝ) ≤ (137500001/150000000:ℝ) * (1 - t) ^ 2 + (100000001/75000000:ℝ) * t * (1 - t) + (137500001/150000000:ℝ) * t ^ 2 := by
    have ht0 : (0:ℝ) ≤ (137500001/150000000:ℝ) * (1 - t) ^ 2 := mul_nonneg (by norm_num : (0:ℝ) ≤ (137500001/150000000:ℝ)) (pow_nonneg hone 2)
    have ht1 : (0:ℝ) ≤ (100000001/75000000:ℝ) * t * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (100000001/75000000:ℝ)) (h0)) (hone)
    have ht2 : (0:ℝ) ≤ (137500001/150000000:ℝ) * t ^ 2 := mul_nonneg (by norm_num : (0:ℝ) ≤ (137500001/150000000:ℝ)) (pow_nonneg h0 2)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u3_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 3 / 6 - t ^ 2 / 4 + t / 12| ≤ (4009377/50000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (4009377/50000000:ℝ) - (t ^ 3 / 6 - t ^ 2 / 4 + t / 12) =(4009377/50000000:ℝ) * (1 - t) ^ 3 + (23584393/150000000:ℝ) * t * (1 - t) ^ 2 + (48584393/150000000:ℝ) * t ^ 2 * (1 - t) + (4009377/50000000:ℝ) * t ^ 3 := by ring
  have e2 : (4009377/50000000:ℝ) + (t ^ 3 / 6 - t ^ 2 / 4 + t / 12) =(4009377/50000000:ℝ) * (1 - t) ^ 3 + (48584393/150000000:ℝ) * t * (1 - t) ^ 2 + (23584393/150000000:ℝ) * t ^ 2 * (1 - t) + (4009377/50000000:ℝ) * t ^ 3 := by ring
  have p1 : (0:ℝ) ≤ (4009377/50000000:ℝ) * (1 - t) ^ 3 + (23584393/150000000:ℝ) * t * (1 - t) ^ 2 + (48584393/150000000:ℝ) * t ^ 2 * (1 - t) + (4009377/50000000:ℝ) * t ^ 3 := by
    have ht0 : (0:ℝ) ≤ (4009377/50000000:ℝ) * (1 - t) ^ 3 := mul_nonneg (by norm_num : (0:ℝ) ≤ (4009377/50000000:ℝ)) (pow_nonneg hone 3)
    have ht1 : (0:ℝ) ≤ (23584393/150000000:ℝ) * t * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (23584393/150000000:ℝ)) (h0)) (pow_nonneg hone 2)
    have ht2 : (0:ℝ) ≤ (48584393/150000000:ℝ) * t ^ 2 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (48584393/150000000:ℝ)) (pow_nonneg h0 2)) (hone)
    have ht3 : (0:ℝ) ≤ (4009377/50000000:ℝ) * t ^ 3 := mul_nonneg (by norm_num : (0:ℝ) ≤ (4009377/50000000:ℝ)) (pow_nonneg h0 3)
    linarith
  have p2 : (0:ℝ) ≤ (4009377/50000000:ℝ) * (1 - t) ^ 3 + (48584393/150000000:ℝ) * t * (1 - t) ^ 2 + (23584393/150000000:ℝ) * t ^ 2 * (1 - t) + (4009377/50000000:ℝ) * t ^ 3 := by
    have ht0 : (0:ℝ) ≤ (4009377/50000000:ℝ) * (1 - t) ^ 3 := mul_nonneg (by norm_num : (0:ℝ) ≤ (4009377/50000000:ℝ)) (pow_nonneg hone 3)
    have ht1 : (0:ℝ) ≤ (48584393/150000000:ℝ) * t * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (48584393/150000000:ℝ)) (h0)) (pow_nonneg hone 2)
    have ht2 : (0:ℝ) ≤ (23584393/150000000:ℝ) * t ^ 2 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (23584393/150000000:ℝ)) (pow_nonneg h0 2)) (hone)
    have ht3 : (0:ℝ) ≤ (4009377/50000000:ℝ) * t ^ 3 := mul_nonneg (by norm_num : (0:ℝ) ≤ (4009377/50000000:ℝ)) (pow_nonneg h0 3)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u4_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)| ≤ (1388889/100000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (1388889/100000000:ℝ) - (t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) =(13750001/900000000:ℝ) * (1 - t) ^ 4 + (13750001/225000000:ℝ) * t * (1 - t) ^ 3 + (7500001/150000000:ℝ) * t ^ 2 * (1 - t) ^ 2 + (13750001/225000000:ℝ) * t ^ 3 * (1 - t) + (13750001/900000000:ℝ) * t ^ 4 := by ring
  have e2 : (1388889/100000000:ℝ) + (t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) =(11250001/900000000:ℝ) * (1 - t) ^ 4 + (11250001/225000000:ℝ) * t * (1 - t) ^ 3 + (17500001/150000000:ℝ) * t ^ 2 * (1 - t) ^ 2 + (11250001/225000000:ℝ) * t ^ 3 * (1 - t) + (11250001/900000000:ℝ) * t ^ 4 := by ring
  have p1 : (0:ℝ) ≤ (13750001/900000000:ℝ) * (1 - t) ^ 4 + (13750001/225000000:ℝ) * t * (1 - t) ^ 3 + (7500001/150000000:ℝ) * t ^ 2 * (1 - t) ^ 2 + (13750001/225000000:ℝ) * t ^ 3 * (1 - t) + (13750001/900000000:ℝ) * t ^ 4 := by
    have ht0 : (0:ℝ) ≤ (13750001/900000000:ℝ) * (1 - t) ^ 4 := mul_nonneg (by norm_num : (0:ℝ) ≤ (13750001/900000000:ℝ)) (pow_nonneg hone 4)
    have ht1 : (0:ℝ) ≤ (13750001/225000000:ℝ) * t * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (13750001/225000000:ℝ)) (h0)) (pow_nonneg hone 3)
    have ht2 : (0:ℝ) ≤ (7500001/150000000:ℝ) * t ^ 2 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (7500001/150000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 2)
    have ht3 : (0:ℝ) ≤ (13750001/225000000:ℝ) * t ^ 3 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (13750001/225000000:ℝ)) (pow_nonneg h0 3)) (hone)
    have ht4 : (0:ℝ) ≤ (13750001/900000000:ℝ) * t ^ 4 := mul_nonneg (by norm_num : (0:ℝ) ≤ (13750001/900000000:ℝ)) (pow_nonneg h0 4)
    linarith
  have p2 : (0:ℝ) ≤ (11250001/900000000:ℝ) * (1 - t) ^ 4 + (11250001/225000000:ℝ) * t * (1 - t) ^ 3 + (17500001/150000000:ℝ) * t ^ 2 * (1 - t) ^ 2 + (11250001/225000000:ℝ) * t ^ 3 * (1 - t) + (11250001/900000000:ℝ) * t ^ 4 := by
    have ht0 : (0:ℝ) ≤ (11250001/900000000:ℝ) * (1 - t) ^ 4 := mul_nonneg (by norm_num : (0:ℝ) ≤ (11250001/900000000:ℝ)) (pow_nonneg hone 4)
    have ht1 : (0:ℝ) ≤ (11250001/225000000:ℝ) * t * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (11250001/225000000:ℝ)) (h0)) (pow_nonneg hone 3)
    have ht2 : (0:ℝ) ≤ (17500001/150000000:ℝ) * t ^ 2 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (17500001/150000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 2)
    have ht3 : (0:ℝ) ≤ (11250001/225000000:ℝ) * t ^ 3 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (11250001/225000000:ℝ)) (pow_nonneg h0 3)) (hone)
    have ht4 : (0:ℝ) ≤ (11250001/900000000:ℝ) * t ^ 4 := mul_nonneg (by norm_num : (0:ℝ) ≤ (11250001/900000000:ℝ)) (pow_nonneg h0 4)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u5_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720| ≤ (203819/100000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (203819/100000000:ℝ) - (t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) =(203819/100000000:ℝ) * (1 - t) ^ 5 + (2084371/180000000:ℝ) * t * (1 - t) ^ 4 + (2334371/90000000:ℝ) * t ^ 2 * (1 - t) ^ 3 + (1334371/90000000:ℝ) * t ^ 3 * (1 - t) ^ 2 + (1584371/180000000:ℝ) * t ^ 4 * (1 - t) + (203819/100000000:ℝ) * t ^ 5 := by ring
  have e2 : (203819/100000000:ℝ) + (t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) =(203819/100000000:ℝ) * (1 - t) ^ 5 + (1584371/180000000:ℝ) * t * (1 - t) ^ 4 + (1334371/90000000:ℝ) * t ^ 2 * (1 - t) ^ 3 + (2334371/90000000:ℝ) * t ^ 3 * (1 - t) ^ 2 + (2084371/180000000:ℝ) * t ^ 4 * (1 - t) + (203819/100000000:ℝ) * t ^ 5 := by ring
  have p1 : (0:ℝ) ≤ (203819/100000000:ℝ) * (1 - t) ^ 5 + (2084371/180000000:ℝ) * t * (1 - t) ^ 4 + (2334371/90000000:ℝ) * t ^ 2 * (1 - t) ^ 3 + (1334371/90000000:ℝ) * t ^ 3 * (1 - t) ^ 2 + (1584371/180000000:ℝ) * t ^ 4 * (1 - t) + (203819/100000000:ℝ) * t ^ 5 := by
    have ht0 : (0:ℝ) ≤ (203819/100000000:ℝ) * (1 - t) ^ 5 := mul_nonneg (by norm_num : (0:ℝ) ≤ (203819/100000000:ℝ)) (pow_nonneg hone 5)
    have ht1 : (0:ℝ) ≤ (2084371/180000000:ℝ) * t * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2084371/180000000:ℝ)) (h0)) (pow_nonneg hone 4)
    have ht2 : (0:ℝ) ≤ (2334371/90000000:ℝ) * t ^ 2 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2334371/90000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 3)
    have ht3 : (0:ℝ) ≤ (1334371/90000000:ℝ) * t ^ 3 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1334371/90000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 2)
    have ht4 : (0:ℝ) ≤ (1584371/180000000:ℝ) * t ^ 4 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1584371/180000000:ℝ)) (pow_nonneg h0 4)) (hone)
    have ht5 : (0:ℝ) ≤ (203819/100000000:ℝ) * t ^ 5 := mul_nonneg (by norm_num : (0:ℝ) ≤ (203819/100000000:ℝ)) (pow_nonneg h0 5)
    linarith
  have p2 : (0:ℝ) ≤ (203819/100000000:ℝ) * (1 - t) ^ 5 + (1584371/180000000:ℝ) * t * (1 - t) ^ 4 + (1334371/90000000:ℝ) * t ^ 2 * (1 - t) ^ 3 + (2334371/90000000:ℝ) * t ^ 3 * (1 - t) ^ 2 + (2084371/180000000:ℝ) * t ^ 4 * (1 - t) + (203819/100000000:ℝ) * t ^ 5 := by
    have ht0 : (0:ℝ) ≤ (203819/100000000:ℝ) * (1 - t) ^ 5 := mul_nonneg (by norm_num : (0:ℝ) ≤ (203819/100000000:ℝ)) (pow_nonneg hone 5)
    have ht1 : (0:ℝ) ≤ (1584371/180000000:ℝ) * t * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1584371/180000000:ℝ)) (h0)) (pow_nonneg hone 4)
    have ht2 : (0:ℝ) ≤ (1334371/90000000:ℝ) * t ^ 2 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1334371/90000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 3)
    have ht3 : (0:ℝ) ≤ (2334371/90000000:ℝ) * t ^ 3 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2334371/90000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 2)
    have ht4 : (0:ℝ) ≤ (2084371/180000000:ℝ) * t ^ 4 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2084371/180000000:ℝ)) (pow_nonneg h0 4)) (hone)
    have ht5 : (0:ℝ) ≤ (203819/100000000:ℝ) * t ^ 5 := mul_nonneg (by norm_num : (0:ℝ) ≤ (203819/100000000:ℝ)) (pow_nonneg h0 5)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u6_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)| ≤ (33069/100000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (33069/100000000:ℝ) - (t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) =(5625041/18900000000:ℝ) * (1 - t) ^ 6 + (5625041/3150000000:ℝ) * t * (1 - t) ^ 5 + (6500041/1260000000:ℝ) * t ^ 2 * (1 - t) ^ 4 + (8250041/945000000:ℝ) * t ^ 3 * (1 - t) ^ 3 + (6500041/1260000000:ℝ) * t ^ 4 * (1 - t) ^ 2 + (5625041/3150000000:ℝ) * t ^ 5 * (1 - t) + (5625041/18900000000:ℝ) * t ^ 6 := by ring
  have e2 : (33069/100000000:ℝ) + (t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) =(6875041/18900000000:ℝ) * (1 - t) ^ 6 + (6875041/3150000000:ℝ) * t * (1 - t) ^ 5 + (6000041/1260000000:ℝ) * t ^ 2 * (1 - t) ^ 4 + (4250041/945000000:ℝ) * t ^ 3 * (1 - t) ^ 3 + (6000041/1260000000:ℝ) * t ^ 4 * (1 - t) ^ 2 + (6875041/3150000000:ℝ) * t ^ 5 * (1 - t) + (6875041/18900000000:ℝ) * t ^ 6 := by ring
  have p1 : (0:ℝ) ≤ (5625041/18900000000:ℝ) * (1 - t) ^ 6 + (5625041/3150000000:ℝ) * t * (1 - t) ^ 5 + (6500041/1260000000:ℝ) * t ^ 2 * (1 - t) ^ 4 + (8250041/945000000:ℝ) * t ^ 3 * (1 - t) ^ 3 + (6500041/1260000000:ℝ) * t ^ 4 * (1 - t) ^ 2 + (5625041/3150000000:ℝ) * t ^ 5 * (1 - t) + (5625041/18900000000:ℝ) * t ^ 6 := by
    have ht0 : (0:ℝ) ≤ (5625041/18900000000:ℝ) * (1 - t) ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (5625041/18900000000:ℝ)) (pow_nonneg hone 6)
    have ht1 : (0:ℝ) ≤ (5625041/3150000000:ℝ) * t * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (5625041/3150000000:ℝ)) (h0)) (pow_nonneg hone 5)
    have ht2 : (0:ℝ) ≤ (6500041/1260000000:ℝ) * t ^ 2 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (6500041/1260000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 4)
    have ht3 : (0:ℝ) ≤ (8250041/945000000:ℝ) * t ^ 3 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (8250041/945000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 3)
    have ht4 : (0:ℝ) ≤ (6500041/1260000000:ℝ) * t ^ 4 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (6500041/1260000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 2)
    have ht5 : (0:ℝ) ≤ (5625041/3150000000:ℝ) * t ^ 5 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (5625041/3150000000:ℝ)) (pow_nonneg h0 5)) (hone)
    have ht6 : (0:ℝ) ≤ (5625041/18900000000:ℝ) * t ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (5625041/18900000000:ℝ)) (pow_nonneg h0 6)
    linarith
  have p2 : (0:ℝ) ≤ (6875041/18900000000:ℝ) * (1 - t) ^ 6 + (6875041/3150000000:ℝ) * t * (1 - t) ^ 5 + (6000041/1260000000:ℝ) * t ^ 2 * (1 - t) ^ 4 + (4250041/945000000:ℝ) * t ^ 3 * (1 - t) ^ 3 + (6000041/1260000000:ℝ) * t ^ 4 * (1 - t) ^ 2 + (6875041/3150000000:ℝ) * t ^ 5 * (1 - t) + (6875041/18900000000:ℝ) * t ^ 6 := by
    have ht0 : (0:ℝ) ≤ (6875041/18900000000:ℝ) * (1 - t) ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (6875041/18900000000:ℝ)) (pow_nonneg hone 6)
    have ht1 : (0:ℝ) ≤ (6875041/3150000000:ℝ) * t * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (6875041/3150000000:ℝ)) (h0)) (pow_nonneg hone 5)
    have ht2 : (0:ℝ) ≤ (6000041/1260000000:ℝ) * t ^ 2 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (6000041/1260000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 4)
    have ht3 : (0:ℝ) ≤ (4250041/945000000:ℝ) * t ^ 3 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (4250041/945000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 3)
    have ht4 : (0:ℝ) ≤ (6000041/1260000000:ℝ) * t ^ 4 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (6000041/1260000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 2)
    have ht5 : (0:ℝ) ≤ (6875041/3150000000:ℝ) * t ^ 5 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (6875041/3150000000:ℝ)) (pow_nonneg h0 5)) (hone)
    have ht6 : (0:ℝ) ≤ (6875041/18900000000:ℝ) * t ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (6875041/18900000000:ℝ)) (pow_nonneg h0 6)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u7_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240| ≤ (1293/25000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (1293/25000000:ℝ) - (t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) =(1293/25000000:ℝ) * (1 - t) ^ 7 + (1554389/4725000000:ℝ) * t * (1 - t) ^ 6 + (1398139/1575000000:ℝ) * t ^ 2 * (1 - t) ^ 5 + (1460639/945000000:ℝ) * t ^ 3 * (1 - t) ^ 4 + (1960639/945000000:ℝ) * t ^ 4 * (1 - t) ^ 3 + (2023139/1575000000:ℝ) * t ^ 5 * (1 - t) ^ 2 + (1866889/4725000000:ℝ) * t ^ 6 * (1 - t) + (1293/25000000:ℝ) * t ^ 7 := by ring
  have e2 : (1293/25000000:ℝ) + (t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) =(1293/25000000:ℝ) * (1 - t) ^ 7 + (1866889/4725000000:ℝ) * t * (1 - t) ^ 6 + (2023139/1575000000:ℝ) * t ^ 2 * (1 - t) ^ 5 + (1960639/945000000:ℝ) * t ^ 3 * (1 - t) ^ 4 + (1460639/945000000:ℝ) * t ^ 4 * (1 - t) ^ 3 + (1398139/1575000000:ℝ) * t ^ 5 * (1 - t) ^ 2 + (1554389/4725000000:ℝ) * t ^ 6 * (1 - t) + (1293/25000000:ℝ) * t ^ 7 := by ring
  have p1 : (0:ℝ) ≤ (1293/25000000:ℝ) * (1 - t) ^ 7 + (1554389/4725000000:ℝ) * t * (1 - t) ^ 6 + (1398139/1575000000:ℝ) * t ^ 2 * (1 - t) ^ 5 + (1460639/945000000:ℝ) * t ^ 3 * (1 - t) ^ 4 + (1960639/945000000:ℝ) * t ^ 4 * (1 - t) ^ 3 + (2023139/1575000000:ℝ) * t ^ 5 * (1 - t) ^ 2 + (1866889/4725000000:ℝ) * t ^ 6 * (1 - t) + (1293/25000000:ℝ) * t ^ 7 := by
    have ht0 : (0:ℝ) ≤ (1293/25000000:ℝ) * (1 - t) ^ 7 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1293/25000000:ℝ)) (pow_nonneg hone 7)
    have ht1 : (0:ℝ) ≤ (1554389/4725000000:ℝ) * t * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1554389/4725000000:ℝ)) (h0)) (pow_nonneg hone 6)
    have ht2 : (0:ℝ) ≤ (1398139/1575000000:ℝ) * t ^ 2 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1398139/1575000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 5)
    have ht3 : (0:ℝ) ≤ (1460639/945000000:ℝ) * t ^ 3 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1460639/945000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 4)
    have ht4 : (0:ℝ) ≤ (1960639/945000000:ℝ) * t ^ 4 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1960639/945000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 3)
    have ht5 : (0:ℝ) ≤ (2023139/1575000000:ℝ) * t ^ 5 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2023139/1575000000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 2)
    have ht6 : (0:ℝ) ≤ (1866889/4725000000:ℝ) * t ^ 6 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1866889/4725000000:ℝ)) (pow_nonneg h0 6)) (hone)
    have ht7 : (0:ℝ) ≤ (1293/25000000:ℝ) * t ^ 7 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1293/25000000:ℝ)) (pow_nonneg h0 7)
    linarith
  have p2 : (0:ℝ) ≤ (1293/25000000:ℝ) * (1 - t) ^ 7 + (1866889/4725000000:ℝ) * t * (1 - t) ^ 6 + (2023139/1575000000:ℝ) * t ^ 2 * (1 - t) ^ 5 + (1960639/945000000:ℝ) * t ^ 3 * (1 - t) ^ 4 + (1460639/945000000:ℝ) * t ^ 4 * (1 - t) ^ 3 + (1398139/1575000000:ℝ) * t ^ 5 * (1 - t) ^ 2 + (1554389/4725000000:ℝ) * t ^ 6 * (1 - t) + (1293/25000000:ℝ) * t ^ 7 := by
    have ht0 : (0:ℝ) ≤ (1293/25000000:ℝ) * (1 - t) ^ 7 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1293/25000000:ℝ)) (pow_nonneg hone 7)
    have ht1 : (0:ℝ) ≤ (1866889/4725000000:ℝ) * t * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1866889/4725000000:ℝ)) (h0)) (pow_nonneg hone 6)
    have ht2 : (0:ℝ) ≤ (2023139/1575000000:ℝ) * t ^ 2 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2023139/1575000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 5)
    have ht3 : (0:ℝ) ≤ (1960639/945000000:ℝ) * t ^ 3 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1960639/945000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 4)
    have ht4 : (0:ℝ) ≤ (1460639/945000000:ℝ) * t ^ 4 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1460639/945000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 3)
    have ht5 : (0:ℝ) ≤ (1398139/1575000000:ℝ) * t ^ 5 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1398139/1575000000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 2)
    have ht6 : (0:ℝ) ≤ (1554389/4725000000:ℝ) * t ^ 6 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1554389/4725000000:ℝ)) (pow_nonneg h0 6)) (hone)
    have ht7 : (0:ℝ) ≤ (1293/25000000:ℝ) * t ^ 7 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1293/25000000:ℝ)) (pow_nonneg h0 7)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u8_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)| ≤ (827/100000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (827/100000000:ℝ) - (t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) =(21491/2362500000:ℝ) * (1 - t) ^ 8 + (21491/295312500:ℝ) * t * (1 - t) ^ 7 + (1125371/4725000000:ℝ) * t ^ 2 * (1 - t) ^ 6 + (969121/2362500000:ℝ) * t ^ 3 * (1 - t) ^ 5 + (844121/1890000000:ℝ) * t ^ 4 * (1 - t) ^ 4 + (969121/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 3 + (1125371/4725000000:ℝ) * t ^ 6 * (1 - t) ^ 2 + (21491/295312500:ℝ) * t ^ 7 * (1 - t) + (21491/2362500000:ℝ) * t ^ 8 := by ring
  have e2 : (827/100000000:ℝ) + (t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) =(70339/9450000000:ℝ) * (1 - t) ^ 8 + (70339/1181250000:ℝ) * t * (1 - t) ^ 7 + (1062871/4725000000:ℝ) * t ^ 2 * (1 - t) ^ 6 + (1219121/2362500000:ℝ) * t ^ 3 * (1 - t) ^ 5 + (1344121/1890000000:ℝ) * t ^ 4 * (1 - t) ^ 4 + (1219121/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 3 + (1062871/4725000000:ℝ) * t ^ 6 * (1 - t) ^ 2 + (70339/1181250000:ℝ) * t ^ 7 * (1 - t) + (70339/9450000000:ℝ) * t ^ 8 := by ring
  have p1 : (0:ℝ) ≤ (21491/2362500000:ℝ) * (1 - t) ^ 8 + (21491/295312500:ℝ) * t * (1 - t) ^ 7 + (1125371/4725000000:ℝ) * t ^ 2 * (1 - t) ^ 6 + (969121/2362500000:ℝ) * t ^ 3 * (1 - t) ^ 5 + (844121/1890000000:ℝ) * t ^ 4 * (1 - t) ^ 4 + (969121/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 3 + (1125371/4725000000:ℝ) * t ^ 6 * (1 - t) ^ 2 + (21491/295312500:ℝ) * t ^ 7 * (1 - t) + (21491/2362500000:ℝ) * t ^ 8 := by
    have ht0 : (0:ℝ) ≤ (21491/2362500000:ℝ) * (1 - t) ^ 8 := mul_nonneg (by norm_num : (0:ℝ) ≤ (21491/2362500000:ℝ)) (pow_nonneg hone 8)
    have ht1 : (0:ℝ) ≤ (21491/295312500:ℝ) * t * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (21491/295312500:ℝ)) (h0)) (pow_nonneg hone 7)
    have ht2 : (0:ℝ) ≤ (1125371/4725000000:ℝ) * t ^ 2 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1125371/4725000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 6)
    have ht3 : (0:ℝ) ≤ (969121/2362500000:ℝ) * t ^ 3 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (969121/2362500000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 5)
    have ht4 : (0:ℝ) ≤ (844121/1890000000:ℝ) * t ^ 4 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (844121/1890000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 4)
    have ht5 : (0:ℝ) ≤ (969121/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (969121/2362500000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 3)
    have ht6 : (0:ℝ) ≤ (1125371/4725000000:ℝ) * t ^ 6 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1125371/4725000000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 2)
    have ht7 : (0:ℝ) ≤ (21491/295312500:ℝ) * t ^ 7 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (21491/295312500:ℝ)) (pow_nonneg h0 7)) (hone)
    have ht8 : (0:ℝ) ≤ (21491/2362500000:ℝ) * t ^ 8 := mul_nonneg (by norm_num : (0:ℝ) ≤ (21491/2362500000:ℝ)) (pow_nonneg h0 8)
    linarith
  have p2 : (0:ℝ) ≤ (70339/9450000000:ℝ) * (1 - t) ^ 8 + (70339/1181250000:ℝ) * t * (1 - t) ^ 7 + (1062871/4725000000:ℝ) * t ^ 2 * (1 - t) ^ 6 + (1219121/2362500000:ℝ) * t ^ 3 * (1 - t) ^ 5 + (1344121/1890000000:ℝ) * t ^ 4 * (1 - t) ^ 4 + (1219121/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 3 + (1062871/4725000000:ℝ) * t ^ 6 * (1 - t) ^ 2 + (70339/1181250000:ℝ) * t ^ 7 * (1 - t) + (70339/9450000000:ℝ) * t ^ 8 := by
    have ht0 : (0:ℝ) ≤ (70339/9450000000:ℝ) * (1 - t) ^ 8 := mul_nonneg (by norm_num : (0:ℝ) ≤ (70339/9450000000:ℝ)) (pow_nonneg hone 8)
    have ht1 : (0:ℝ) ≤ (70339/1181250000:ℝ) * t * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (70339/1181250000:ℝ)) (h0)) (pow_nonneg hone 7)
    have ht2 : (0:ℝ) ≤ (1062871/4725000000:ℝ) * t ^ 2 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1062871/4725000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 6)
    have ht3 : (0:ℝ) ≤ (1219121/2362500000:ℝ) * t ^ 3 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1219121/2362500000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 5)
    have ht4 : (0:ℝ) ≤ (1344121/1890000000:ℝ) * t ^ 4 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1344121/1890000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 4)
    have ht5 : (0:ℝ) ≤ (1219121/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1219121/2362500000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 3)
    have ht6 : (0:ℝ) ≤ (1062871/4725000000:ℝ) * t ^ 6 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1062871/4725000000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 2)
    have ht7 : (0:ℝ) ≤ (70339/1181250000:ℝ) * t ^ 7 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (70339/1181250000:ℝ)) (pow_nonneg h0 7)) (hone)
    have ht8 : (0:ℝ) ≤ (70339/9450000000:ℝ) * t ^ 8 := mul_nonneg (by norm_num : (0:ℝ) ≤ (70339/9450000000:ℝ)) (pow_nonneg h0 8)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u9_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600| ≤ (33/25000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (33/25000000:ℝ) - (t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) =(33/25000000:ℝ) * (1 - t) ^ 9 + (240157/18900000000:ℝ) * t * (1 - t) ^ 8 + (127891/2362500000:ℝ) * t ^ 2 * (1 - t) ^ 7 + (455431/3543750000:ℝ) * t ^ 3 * (1 - t) ^ 6 + (424181/2362500000:ℝ) * t ^ 4 * (1 - t) ^ 5 + (361681/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 4 + (330431/3543750000:ℝ) * t ^ 6 * (1 - t) ^ 3 + (96641/2362500000:ℝ) * t ^ 7 * (1 - t) ^ 2 + (208907/18900000000:ℝ) * t ^ 8 * (1 - t) + (33/25000000:ℝ) * t ^ 9 := by ring
  have e2 : (33/25000000:ℝ) + (t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) =(33/25000000:ℝ) * (1 - t) ^ 9 + (208907/18900000000:ℝ) * t * (1 - t) ^ 8 + (96641/2362500000:ℝ) * t ^ 2 * (1 - t) ^ 7 + (330431/3543750000:ℝ) * t ^ 3 * (1 - t) ^ 6 + (361681/2362500000:ℝ) * t ^ 4 * (1 - t) ^ 5 + (424181/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 4 + (455431/3543750000:ℝ) * t ^ 6 * (1 - t) ^ 3 + (127891/2362500000:ℝ) * t ^ 7 * (1 - t) ^ 2 + (240157/18900000000:ℝ) * t ^ 8 * (1 - t) + (33/25000000:ℝ) * t ^ 9 := by ring
  have p1 : (0:ℝ) ≤ (33/25000000:ℝ) * (1 - t) ^ 9 + (240157/18900000000:ℝ) * t * (1 - t) ^ 8 + (127891/2362500000:ℝ) * t ^ 2 * (1 - t) ^ 7 + (455431/3543750000:ℝ) * t ^ 3 * (1 - t) ^ 6 + (424181/2362500000:ℝ) * t ^ 4 * (1 - t) ^ 5 + (361681/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 4 + (330431/3543750000:ℝ) * t ^ 6 * (1 - t) ^ 3 + (96641/2362500000:ℝ) * t ^ 7 * (1 - t) ^ 2 + (208907/18900000000:ℝ) * t ^ 8 * (1 - t) + (33/25000000:ℝ) * t ^ 9 := by
    have ht0 : (0:ℝ) ≤ (33/25000000:ℝ) * (1 - t) ^ 9 := mul_nonneg (by norm_num : (0:ℝ) ≤ (33/25000000:ℝ)) (pow_nonneg hone 9)
    have ht1 : (0:ℝ) ≤ (240157/18900000000:ℝ) * t * (1 - t) ^ 8 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (240157/18900000000:ℝ)) (h0)) (pow_nonneg hone 8)
    have ht2 : (0:ℝ) ≤ (127891/2362500000:ℝ) * t ^ 2 * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (127891/2362500000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 7)
    have ht3 : (0:ℝ) ≤ (455431/3543750000:ℝ) * t ^ 3 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (455431/3543750000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 6)
    have ht4 : (0:ℝ) ≤ (424181/2362500000:ℝ) * t ^ 4 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (424181/2362500000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 5)
    have ht5 : (0:ℝ) ≤ (361681/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (361681/2362500000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 4)
    have ht6 : (0:ℝ) ≤ (330431/3543750000:ℝ) * t ^ 6 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (330431/3543750000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 3)
    have ht7 : (0:ℝ) ≤ (96641/2362500000:ℝ) * t ^ 7 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (96641/2362500000:ℝ)) (pow_nonneg h0 7)) (pow_nonneg hone 2)
    have ht8 : (0:ℝ) ≤ (208907/18900000000:ℝ) * t ^ 8 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (208907/18900000000:ℝ)) (pow_nonneg h0 8)) (hone)
    have ht9 : (0:ℝ) ≤ (33/25000000:ℝ) * t ^ 9 := mul_nonneg (by norm_num : (0:ℝ) ≤ (33/25000000:ℝ)) (pow_nonneg h0 9)
    linarith
  have p2 : (0:ℝ) ≤ (33/25000000:ℝ) * (1 - t) ^ 9 + (208907/18900000000:ℝ) * t * (1 - t) ^ 8 + (96641/2362500000:ℝ) * t ^ 2 * (1 - t) ^ 7 + (330431/3543750000:ℝ) * t ^ 3 * (1 - t) ^ 6 + (361681/2362500000:ℝ) * t ^ 4 * (1 - t) ^ 5 + (424181/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 4 + (455431/3543750000:ℝ) * t ^ 6 * (1 - t) ^ 3 + (127891/2362500000:ℝ) * t ^ 7 * (1 - t) ^ 2 + (240157/18900000000:ℝ) * t ^ 8 * (1 - t) + (33/25000000:ℝ) * t ^ 9 := by
    have ht0 : (0:ℝ) ≤ (33/25000000:ℝ) * (1 - t) ^ 9 := mul_nonneg (by norm_num : (0:ℝ) ≤ (33/25000000:ℝ)) (pow_nonneg hone 9)
    have ht1 : (0:ℝ) ≤ (208907/18900000000:ℝ) * t * (1 - t) ^ 8 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (208907/18900000000:ℝ)) (h0)) (pow_nonneg hone 8)
    have ht2 : (0:ℝ) ≤ (96641/2362500000:ℝ) * t ^ 2 * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (96641/2362500000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 7)
    have ht3 : (0:ℝ) ≤ (330431/3543750000:ℝ) * t ^ 3 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (330431/3543750000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 6)
    have ht4 : (0:ℝ) ≤ (361681/2362500000:ℝ) * t ^ 4 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (361681/2362500000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 5)
    have ht5 : (0:ℝ) ≤ (424181/2362500000:ℝ) * t ^ 5 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (424181/2362500000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 4)
    have ht6 : (0:ℝ) ≤ (455431/3543750000:ℝ) * t ^ 6 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (455431/3543750000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 3)
    have ht7 : (0:ℝ) ≤ (127891/2362500000:ℝ) * t ^ 7 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (127891/2362500000:ℝ)) (pow_nonneg h0 7)) (pow_nonneg hone 2)
    have ht8 : (0:ℝ) ≤ (240157/18900000000:ℝ) * t ^ 8 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (240157/18900000000:ℝ)) (pow_nonneg h0 8)) (hone)
    have ht9 : (0:ℝ) ≤ (33/25000000:ℝ) * t ^ 9 := mul_nonneg (by norm_num : (0:ℝ) ≤ (33/25000000:ℝ)) (pow_nonneg h0 9)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u10_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)| ≤ (21/100000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (21/100000000:ℝ) - (t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) =(707737/3742200000000:ℝ) * (1 - t) ^ 10 + (707737/374220000000:ℝ) * t * (1 - t) ^ 9 + (3313/371250000:ℝ) * t ^ 2 * (1 - t) ^ 8 + (405431/15592500000:ℝ) * t ^ 3 * (1 - t) ^ 7 + (3113017/62370000000:ℝ) * t ^ 4 * (1 - t) ^ 6 + (3250517/51975000000:ℝ) * t ^ 5 * (1 - t) ^ 5 + (3113017/62370000000:ℝ) * t ^ 6 * (1 - t) ^ 4 + (405431/15592500000:ℝ) * t ^ 7 * (1 - t) ^ 3 + (3313/371250000:ℝ) * t ^ 8 * (1 - t) ^ 2 + (707737/374220000000:ℝ) * t ^ 9 * (1 - t) + (707737/3742200000000:ℝ) * t ^ 10 := by ring
  have e2 : (21/100000000:ℝ) + (t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) =(863987/3742200000000:ℝ) * (1 - t) ^ 10 + (863987/374220000000:ℝ) * t * (1 - t) ^ 9 + (29629/2970000000:ℝ) * t ^ 2 * (1 - t) ^ 8 + (380431/15592500000:ℝ) * t ^ 3 * (1 - t) ^ 7 + (2388017/62370000000:ℝ) * t ^ 4 * (1 - t) ^ 6 + (2250517/51975000000:ℝ) * t ^ 5 * (1 - t) ^ 5 + (2388017/62370000000:ℝ) * t ^ 6 * (1 - t) ^ 4 + (380431/15592500000:ℝ) * t ^ 7 * (1 - t) ^ 3 + (29629/2970000000:ℝ) * t ^ 8 * (1 - t) ^ 2 + (863987/374220000000:ℝ) * t ^ 9 * (1 - t) + (863987/3742200000000:ℝ) * t ^ 10 := by ring
  have p1 : (0:ℝ) ≤ (707737/3742200000000:ℝ) * (1 - t) ^ 10 + (707737/374220000000:ℝ) * t * (1 - t) ^ 9 + (3313/371250000:ℝ) * t ^ 2 * (1 - t) ^ 8 + (405431/15592500000:ℝ) * t ^ 3 * (1 - t) ^ 7 + (3113017/62370000000:ℝ) * t ^ 4 * (1 - t) ^ 6 + (3250517/51975000000:ℝ) * t ^ 5 * (1 - t) ^ 5 + (3113017/62370000000:ℝ) * t ^ 6 * (1 - t) ^ 4 + (405431/15592500000:ℝ) * t ^ 7 * (1 - t) ^ 3 + (3313/371250000:ℝ) * t ^ 8 * (1 - t) ^ 2 + (707737/374220000000:ℝ) * t ^ 9 * (1 - t) + (707737/3742200000000:ℝ) * t ^ 10 := by
    have ht0 : (0:ℝ) ≤ (707737/3742200000000:ℝ) * (1 - t) ^ 10 := mul_nonneg (by norm_num : (0:ℝ) ≤ (707737/3742200000000:ℝ)) (pow_nonneg hone 10)
    have ht1 : (0:ℝ) ≤ (707737/374220000000:ℝ) * t * (1 - t) ^ 9 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (707737/374220000000:ℝ)) (h0)) (pow_nonneg hone 9)
    have ht2 : (0:ℝ) ≤ (3313/371250000:ℝ) * t ^ 2 * (1 - t) ^ 8 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (3313/371250000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 8)
    have ht3 : (0:ℝ) ≤ (405431/15592500000:ℝ) * t ^ 3 * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (405431/15592500000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 7)
    have ht4 : (0:ℝ) ≤ (3113017/62370000000:ℝ) * t ^ 4 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (3113017/62370000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 6)
    have ht5 : (0:ℝ) ≤ (3250517/51975000000:ℝ) * t ^ 5 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (3250517/51975000000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 5)
    have ht6 : (0:ℝ) ≤ (3113017/62370000000:ℝ) * t ^ 6 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (3113017/62370000000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 4)
    have ht7 : (0:ℝ) ≤ (405431/15592500000:ℝ) * t ^ 7 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (405431/15592500000:ℝ)) (pow_nonneg h0 7)) (pow_nonneg hone 3)
    have ht8 : (0:ℝ) ≤ (3313/371250000:ℝ) * t ^ 8 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (3313/371250000:ℝ)) (pow_nonneg h0 8)) (pow_nonneg hone 2)
    have ht9 : (0:ℝ) ≤ (707737/374220000000:ℝ) * t ^ 9 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (707737/374220000000:ℝ)) (pow_nonneg h0 9)) (hone)
    have ht10 : (0:ℝ) ≤ (707737/3742200000000:ℝ) * t ^ 10 := mul_nonneg (by norm_num : (0:ℝ) ≤ (707737/3742200000000:ℝ)) (pow_nonneg h0 10)
    linarith
  have p2 : (0:ℝ) ≤ (863987/3742200000000:ℝ) * (1 - t) ^ 10 + (863987/374220000000:ℝ) * t * (1 - t) ^ 9 + (29629/2970000000:ℝ) * t ^ 2 * (1 - t) ^ 8 + (380431/15592500000:ℝ) * t ^ 3 * (1 - t) ^ 7 + (2388017/62370000000:ℝ) * t ^ 4 * (1 - t) ^ 6 + (2250517/51975000000:ℝ) * t ^ 5 * (1 - t) ^ 5 + (2388017/62370000000:ℝ) * t ^ 6 * (1 - t) ^ 4 + (380431/15592500000:ℝ) * t ^ 7 * (1 - t) ^ 3 + (29629/2970000000:ℝ) * t ^ 8 * (1 - t) ^ 2 + (863987/374220000000:ℝ) * t ^ 9 * (1 - t) + (863987/3742200000000:ℝ) * t ^ 10 := by
    have ht0 : (0:ℝ) ≤ (863987/3742200000000:ℝ) * (1 - t) ^ 10 := mul_nonneg (by norm_num : (0:ℝ) ≤ (863987/3742200000000:ℝ)) (pow_nonneg hone 10)
    have ht1 : (0:ℝ) ≤ (863987/374220000000:ℝ) * t * (1 - t) ^ 9 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (863987/374220000000:ℝ)) (h0)) (pow_nonneg hone 9)
    have ht2 : (0:ℝ) ≤ (29629/2970000000:ℝ) * t ^ 2 * (1 - t) ^ 8 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (29629/2970000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 8)
    have ht3 : (0:ℝ) ≤ (380431/15592500000:ℝ) * t ^ 3 * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (380431/15592500000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 7)
    have ht4 : (0:ℝ) ≤ (2388017/62370000000:ℝ) * t ^ 4 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2388017/62370000000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 6)
    have ht5 : (0:ℝ) ≤ (2250517/51975000000:ℝ) * t ^ 5 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2250517/51975000000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 5)
    have ht6 : (0:ℝ) ≤ (2388017/62370000000:ℝ) * t ^ 6 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2388017/62370000000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 4)
    have ht7 : (0:ℝ) ≤ (380431/15592500000:ℝ) * t ^ 7 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (380431/15592500000:ℝ)) (pow_nonneg h0 7)) (pow_nonneg hone 3)
    have ht8 : (0:ℝ) ≤ (29629/2970000000:ℝ) * t ^ 8 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (29629/2970000000:ℝ)) (pow_nonneg h0 8)) (pow_nonneg hone 2)
    have ht9 : (0:ℝ) ≤ (863987/374220000000:ℝ) * t ^ 9 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (863987/374220000000:ℝ)) (pow_nonneg h0 9)) (hone)
    have ht10 : (0:ℝ) ≤ (863987/3742200000000:ℝ) * t ^ 10 := mul_nonneg (by norm_num : (0:ℝ) ≤ (863987/3742200000000:ℝ)) (pow_nonneg h0 10)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u11_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160| ≤ (1/25000000:ℝ) := by
  have hone : (0:ℝ) ≤ 1 - t := by linarith
  have e1 : (1/25000000:ℝ) - (t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) =(1/25000000:ℝ) * (1 - t) ^ 11 + (1568443/3742200000000:ℝ) * t * (1 - t) ^ 10 + (745159/374220000000:ℝ) * t ^ 2 * (1 - t) ^ 9 + (180821/31185000000:ℝ) * t ^ 3 * (1 - t) ^ 8 + (13139/1113750000:ℝ) * t ^ 4 * (1 - t) ^ 7 + (1378247/77962500000:ℝ) * t ^ 5 * (1 - t) ^ 6 + (1503247/77962500000:ℝ) * t ^ 6 * (1 - t) ^ 5 + (2033/139218750:ℝ) * t ^ 7 * (1 - t) ^ 4 + (230821/31185000000:ℝ) * t ^ 8 * (1 - t) ^ 3 + (901409/374220000000:ℝ) * t ^ 9 * (1 - t) ^ 2 + (1724693/3742200000000:ℝ) * t ^ 10 * (1 - t) + (1/25000000:ℝ) * t ^ 11 := by ring
  have e2 : (1/25000000:ℝ) + (t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) =(1/25000000:ℝ) * (1 - t) ^ 11 + (1724693/3742200000000:ℝ) * t * (1 - t) ^ 10 + (901409/374220000000:ℝ) * t ^ 2 * (1 - t) ^ 9 + (230821/31185000000:ℝ) * t ^ 3 * (1 - t) ^ 8 + (2033/139218750:ℝ) * t ^ 4 * (1 - t) ^ 7 + (1503247/77962500000:ℝ) * t ^ 5 * (1 - t) ^ 6 + (1378247/77962500000:ℝ) * t ^ 6 * (1 - t) ^ 5 + (13139/1113750000:ℝ) * t ^ 7 * (1 - t) ^ 4 + (180821/31185000000:ℝ) * t ^ 8 * (1 - t) ^ 3 + (745159/374220000000:ℝ) * t ^ 9 * (1 - t) ^ 2 + (1568443/3742200000000:ℝ) * t ^ 10 * (1 - t) + (1/25000000:ℝ) * t ^ 11 := by ring
  have p1 : (0:ℝ) ≤ (1/25000000:ℝ) * (1 - t) ^ 11 + (1568443/3742200000000:ℝ) * t * (1 - t) ^ 10 + (745159/374220000000:ℝ) * t ^ 2 * (1 - t) ^ 9 + (180821/31185000000:ℝ) * t ^ 3 * (1 - t) ^ 8 + (13139/1113750000:ℝ) * t ^ 4 * (1 - t) ^ 7 + (1378247/77962500000:ℝ) * t ^ 5 * (1 - t) ^ 6 + (1503247/77962500000:ℝ) * t ^ 6 * (1 - t) ^ 5 + (2033/139218750:ℝ) * t ^ 7 * (1 - t) ^ 4 + (230821/31185000000:ℝ) * t ^ 8 * (1 - t) ^ 3 + (901409/374220000000:ℝ) * t ^ 9 * (1 - t) ^ 2 + (1724693/3742200000000:ℝ) * t ^ 10 * (1 - t) + (1/25000000:ℝ) * t ^ 11 := by
    have ht0 : (0:ℝ) ≤ (1/25000000:ℝ) * (1 - t) ^ 11 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1/25000000:ℝ)) (pow_nonneg hone 11)
    have ht1 : (0:ℝ) ≤ (1568443/3742200000000:ℝ) * t * (1 - t) ^ 10 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1568443/3742200000000:ℝ)) (h0)) (pow_nonneg hone 10)
    have ht2 : (0:ℝ) ≤ (745159/374220000000:ℝ) * t ^ 2 * (1 - t) ^ 9 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (745159/374220000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 9)
    have ht3 : (0:ℝ) ≤ (180821/31185000000:ℝ) * t ^ 3 * (1 - t) ^ 8 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (180821/31185000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 8)
    have ht4 : (0:ℝ) ≤ (13139/1113750000:ℝ) * t ^ 4 * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (13139/1113750000:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 7)
    have ht5 : (0:ℝ) ≤ (1378247/77962500000:ℝ) * t ^ 5 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1378247/77962500000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 6)
    have ht6 : (0:ℝ) ≤ (1503247/77962500000:ℝ) * t ^ 6 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1503247/77962500000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 5)
    have ht7 : (0:ℝ) ≤ (2033/139218750:ℝ) * t ^ 7 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2033/139218750:ℝ)) (pow_nonneg h0 7)) (pow_nonneg hone 4)
    have ht8 : (0:ℝ) ≤ (230821/31185000000:ℝ) * t ^ 8 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (230821/31185000000:ℝ)) (pow_nonneg h0 8)) (pow_nonneg hone 3)
    have ht9 : (0:ℝ) ≤ (901409/374220000000:ℝ) * t ^ 9 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (901409/374220000000:ℝ)) (pow_nonneg h0 9)) (pow_nonneg hone 2)
    have ht10 : (0:ℝ) ≤ (1724693/3742200000000:ℝ) * t ^ 10 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1724693/3742200000000:ℝ)) (pow_nonneg h0 10)) (hone)
    have ht11 : (0:ℝ) ≤ (1/25000000:ℝ) * t ^ 11 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1/25000000:ℝ)) (pow_nonneg h0 11)
    linarith
  have p2 : (0:ℝ) ≤ (1/25000000:ℝ) * (1 - t) ^ 11 + (1724693/3742200000000:ℝ) * t * (1 - t) ^ 10 + (901409/374220000000:ℝ) * t ^ 2 * (1 - t) ^ 9 + (230821/31185000000:ℝ) * t ^ 3 * (1 - t) ^ 8 + (2033/139218750:ℝ) * t ^ 4 * (1 - t) ^ 7 + (1503247/77962500000:ℝ) * t ^ 5 * (1 - t) ^ 6 + (1378247/77962500000:ℝ) * t ^ 6 * (1 - t) ^ 5 + (13139/1113750000:ℝ) * t ^ 7 * (1 - t) ^ 4 + (180821/31185000000:ℝ) * t ^ 8 * (1 - t) ^ 3 + (745159/374220000000:ℝ) * t ^ 9 * (1 - t) ^ 2 + (1568443/3742200000000:ℝ) * t ^ 10 * (1 - t) + (1/25000000:ℝ) * t ^ 11 := by
    have ht0 : (0:ℝ) ≤ (1/25000000:ℝ) * (1 - t) ^ 11 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1/25000000:ℝ)) (pow_nonneg hone 11)
    have ht1 : (0:ℝ) ≤ (1724693/3742200000000:ℝ) * t * (1 - t) ^ 10 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1724693/3742200000000:ℝ)) (h0)) (pow_nonneg hone 10)
    have ht2 : (0:ℝ) ≤ (901409/374220000000:ℝ) * t ^ 2 * (1 - t) ^ 9 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (901409/374220000000:ℝ)) (pow_nonneg h0 2)) (pow_nonneg hone 9)
    have ht3 : (0:ℝ) ≤ (230821/31185000000:ℝ) * t ^ 3 * (1 - t) ^ 8 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (230821/31185000000:ℝ)) (pow_nonneg h0 3)) (pow_nonneg hone 8)
    have ht4 : (0:ℝ) ≤ (2033/139218750:ℝ) * t ^ 4 * (1 - t) ^ 7 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (2033/139218750:ℝ)) (pow_nonneg h0 4)) (pow_nonneg hone 7)
    have ht5 : (0:ℝ) ≤ (1503247/77962500000:ℝ) * t ^ 5 * (1 - t) ^ 6 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1503247/77962500000:ℝ)) (pow_nonneg h0 5)) (pow_nonneg hone 6)
    have ht6 : (0:ℝ) ≤ (1378247/77962500000:ℝ) * t ^ 6 * (1 - t) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1378247/77962500000:ℝ)) (pow_nonneg h0 6)) (pow_nonneg hone 5)
    have ht7 : (0:ℝ) ≤ (13139/1113750000:ℝ) * t ^ 7 * (1 - t) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (13139/1113750000:ℝ)) (pow_nonneg h0 7)) (pow_nonneg hone 4)
    have ht8 : (0:ℝ) ≤ (180821/31185000000:ℝ) * t ^ 8 * (1 - t) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (180821/31185000000:ℝ)) (pow_nonneg h0 8)) (pow_nonneg hone 3)
    have ht9 : (0:ℝ) ≤ (745159/374220000000:ℝ) * t ^ 9 * (1 - t) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (745159/374220000000:ℝ)) (pow_nonneg h0 9)) (pow_nonneg hone 2)
    have ht10 : (0:ℝ) ≤ (1568443/3742200000000:ℝ) * t ^ 10 * (1 - t) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1568443/3742200000000:ℝ)) (pow_nonneg h0 10)) (hone)
    have ht11 : (0:ℝ) ≤ (1/25000000:ℝ) * t ^ 11 := mul_nonneg (by norm_num : (0:ℝ) ≤ (1/25000000:ℝ)) (pow_nonneg h0 11)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  rw [abs_le]
  constructor <;> linarith

private theorem abs_u12_le537 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)| ≤ ((28/100)/479001600:ℝ) := by
  set v : ℝ := (t - 1/2) ^ 2 with hv
  have hv0 : (0:ℝ) ≤ v := by positivity
  have hv1 : v ≤ 1/4 := by nlinarith
  have h4v0 : (0:ℝ) ≤ 4 * v := by linarith
  have h4v1 : (0:ℝ) ≤ 1 - 4 * v := by linarith
  have hB : (479001600:ℝ) * (t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) =(1/1:ℝ) * v ^ 6 + (-11/2:ℝ) * v ^ 5 + (231/16:ℝ) * v ^ 4 + (-341/16:ℝ) * v ^ 3 + (4191/256:ℝ) * v ^ 2 + (-2555/512:ℝ) * v + (1414477/5591040:ℝ) := by
    rw [hv]
    ring
  have e1 : (28/100:ℝ) - ((1/1:ℝ) * v ^ 6 + (-11/2:ℝ) * v ^ 5 + (231/16:ℝ) * v ^ 4 + (-341/16:ℝ) * v ^ 3 + (4191/256:ℝ) * v ^ 2 + (-2555/512:ℝ) * v + (1414477/5591040:ℝ)) =(755071/27955200:ℝ) * (1 - (4 * v)) ^ 6 + (410481/291200:ℝ) * (4 * v) * (1 - (4 * v)) ^ 5 + (1309177/232960:ℝ) * (4 * v) ^ 2 * (1 - (4 * v)) ^ 4 + (404303/43680:ℝ) * (4 * v) ^ 3 * (1 - (4 * v)) ^ 3 + (55941/7280:ℝ) * (4 * v) ^ 4 * (1 - (4 * v)) ^ 2 + (7277/2275:ℝ) * (4 * v) ^ 5 * (1 - (4 * v)) + (7277/13650:ℝ) * (4 * v) ^ 6 := by ring
  have e2 : (28/100:ℝ) + ((1/1:ℝ) * v ^ 6 + (-11/2:ℝ) * v ^ 5 + (231/16:ℝ) * v ^ 4 + (-341/16:ℝ) * v ^ 3 + (4191/256:ℝ) * v ^ 2 + (-2555/512:ℝ) * v + (1414477/5591040:ℝ)) =(14899841/27955200:ℝ) * (1 - (4 * v)) ^ 6 + (567951/291200:ℝ) * (4 * v) * (1 - (4 * v)) ^ 5 + (647687/232960:ℝ) * (4 * v) ^ 2 * (1 - (4 * v)) ^ 4 + (84913/43680:ℝ) * (4 * v) ^ 3 * (1 - (4 * v)) ^ 3 + (5211/7280:ℝ) * (4 * v) ^ 4 * (1 - (4 * v)) ^ 2 + (367/2275:ℝ) * (4 * v) ^ 5 * (1 - (4 * v)) + (367/13650:ℝ) * (4 * v) ^ 6 := by ring
  have p1 : (0:ℝ) ≤ (755071/27955200:ℝ) * (1 - (4 * v)) ^ 6 + (410481/291200:ℝ) * (4 * v) * (1 - (4 * v)) ^ 5 + (1309177/232960:ℝ) * (4 * v) ^ 2 * (1 - (4 * v)) ^ 4 + (404303/43680:ℝ) * (4 * v) ^ 3 * (1 - (4 * v)) ^ 3 + (55941/7280:ℝ) * (4 * v) ^ 4 * (1 - (4 * v)) ^ 2 + (7277/2275:ℝ) * (4 * v) ^ 5 * (1 - (4 * v)) + (7277/13650:ℝ) * (4 * v) ^ 6 := by
    have ht0 : (0:ℝ) ≤ (755071/27955200:ℝ) * (1 - (4 * v)) ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (755071/27955200:ℝ)) (pow_nonneg h4v1 6)
    have ht1 : (0:ℝ) ≤ (410481/291200:ℝ) * (4 * v) * (1 - (4 * v)) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (410481/291200:ℝ)) (h4v0)) (pow_nonneg h4v1 5)
    have ht2 : (0:ℝ) ≤ (1309177/232960:ℝ) * (4 * v) ^ 2 * (1 - (4 * v)) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1309177/232960:ℝ)) (pow_nonneg h4v0 2)) (pow_nonneg h4v1 4)
    have ht3 : (0:ℝ) ≤ (404303/43680:ℝ) * (4 * v) ^ 3 * (1 - (4 * v)) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (404303/43680:ℝ)) (pow_nonneg h4v0 3)) (pow_nonneg h4v1 3)
    have ht4 : (0:ℝ) ≤ (55941/7280:ℝ) * (4 * v) ^ 4 * (1 - (4 * v)) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (55941/7280:ℝ)) (pow_nonneg h4v0 4)) (pow_nonneg h4v1 2)
    have ht5 : (0:ℝ) ≤ (7277/2275:ℝ) * (4 * v) ^ 5 * (1 - (4 * v)) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (7277/2275:ℝ)) (pow_nonneg h4v0 5)) (h4v1)
    have ht6 : (0:ℝ) ≤ (7277/13650:ℝ) * (4 * v) ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (7277/13650:ℝ)) (pow_nonneg h4v0 6)
    linarith
  have p2 : (0:ℝ) ≤ (14899841/27955200:ℝ) * (1 - (4 * v)) ^ 6 + (567951/291200:ℝ) * (4 * v) * (1 - (4 * v)) ^ 5 + (647687/232960:ℝ) * (4 * v) ^ 2 * (1 - (4 * v)) ^ 4 + (84913/43680:ℝ) * (4 * v) ^ 3 * (1 - (4 * v)) ^ 3 + (5211/7280:ℝ) * (4 * v) ^ 4 * (1 - (4 * v)) ^ 2 + (367/2275:ℝ) * (4 * v) ^ 5 * (1 - (4 * v)) + (367/13650:ℝ) * (4 * v) ^ 6 := by
    have ht0 : (0:ℝ) ≤ (14899841/27955200:ℝ) * (1 - (4 * v)) ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (14899841/27955200:ℝ)) (pow_nonneg h4v1 6)
    have ht1 : (0:ℝ) ≤ (567951/291200:ℝ) * (4 * v) * (1 - (4 * v)) ^ 5 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (567951/291200:ℝ)) (h4v0)) (pow_nonneg h4v1 5)
    have ht2 : (0:ℝ) ≤ (647687/232960:ℝ) * (4 * v) ^ 2 * (1 - (4 * v)) ^ 4 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (647687/232960:ℝ)) (pow_nonneg h4v0 2)) (pow_nonneg h4v1 4)
    have ht3 : (0:ℝ) ≤ (84913/43680:ℝ) * (4 * v) ^ 3 * (1 - (4 * v)) ^ 3 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (84913/43680:ℝ)) (pow_nonneg h4v0 3)) (pow_nonneg h4v1 3)
    have ht4 : (0:ℝ) ≤ (5211/7280:ℝ) * (4 * v) ^ 4 * (1 - (4 * v)) ^ 2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (5211/7280:ℝ)) (pow_nonneg h4v0 4)) (pow_nonneg h4v1 2)
    have ht5 : (0:ℝ) ≤ (367/2275:ℝ) * (4 * v) ^ 5 * (1 - (4 * v)) := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (367/2275:ℝ)) (pow_nonneg h4v0 5)) (h4v1)
    have ht6 : (0:ℝ) ≤ (367/13650:ℝ) * (4 * v) ^ 6 := mul_nonneg (by norm_num : (0:ℝ) ≤ (367/13650:ℝ)) (pow_nonneg h4v0 6)
    linarith
  rw [← e1] at p1
  rw [← e2] at p2
  have hu : (479001600:ℝ) * (t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) ≤ 28/100 := by rw [hB]; linarith
  have hl : -(28/100:ℝ) ≤ (479001600:ℝ) * (t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) := by rw [hB]; linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

private theorem hasDerivAt_u3_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 / 6 - y ^ 2 / 4 + y / 12) (t ^ 2 / 2 - t / 2 + (1/12:ℝ)) t := by
  have h := (((hasDerivAt_pow 3 t).div_const 6).sub ((hasDerivAt_pow 2 t).div_const 4)).add ((hasDerivAt_id t).div_const 12)
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u4_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 4 / 24 - y ^ 3 / 12 + y ^ 2 / 24 - (1/720:ℝ)) (t ^ 3 / 6 - t ^ 2 / 4 + t / 12) t := by
  have h := ((((hasDerivAt_pow 4 t).div_const 24).sub ((hasDerivAt_pow 3 t).div_const 12)).add ((hasDerivAt_pow 2 t).div_const 24)).sub (hasDerivAt_const t ((1/720:ℝ)))
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u5_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 5 / 120 - y ^ 4 / 48 + y ^ 3 / 72 - y / 720) (t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) t := by
  have h := ((((hasDerivAt_pow 5 t).div_const 120).sub ((hasDerivAt_pow 4 t).div_const 48)).add ((hasDerivAt_pow 3 t).div_const 72)).sub ((hasDerivAt_id t).div_const 720)
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u6_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 6 / 720 - y ^ 5 / 240 + y ^ 4 / 288 - y ^ 2 / 1440 + (1/30240:ℝ)) (t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) t := by
  have h := (((((hasDerivAt_pow 6 t).div_const 720).sub ((hasDerivAt_pow 5 t).div_const 240)).add ((hasDerivAt_pow 4 t).div_const 288)).sub ((hasDerivAt_pow 2 t).div_const 1440)).add (hasDerivAt_const t ((1/30240:ℝ)))
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u7_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 7 / 5040 - y ^ 6 / 1440 + y ^ 5 / 1440 - y ^ 3 / 4320 + y / 30240) (t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) t := by
  have h := (((((hasDerivAt_pow 7 t).div_const 5040).sub ((hasDerivAt_pow 6 t).div_const 1440)).add ((hasDerivAt_pow 5 t).div_const 1440)).sub ((hasDerivAt_pow 3 t).div_const 4320)).add ((hasDerivAt_id t).div_const 30240)
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u8_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 8 / 40320 - y ^ 7 / 10080 + y ^ 6 / 8640 - y ^ 4 / 17280 + y ^ 2 / 60480 - (1/1209600:ℝ)) (t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) t := by
  have h := ((((((hasDerivAt_pow 8 t).div_const 40320).sub ((hasDerivAt_pow 7 t).div_const 10080)).add ((hasDerivAt_pow 6 t).div_const 8640)).sub ((hasDerivAt_pow 4 t).div_const 17280)).add ((hasDerivAt_pow 2 t).div_const 60480)).sub (hasDerivAt_const t ((1/1209600:ℝ)))
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u9_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 9 / 362880 - y ^ 8 / 80640 + y ^ 7 / 60480 - y ^ 5 / 86400 + y ^ 3 / 181440 - y / 1209600) (t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) t := by
  have h := ((((((hasDerivAt_pow 9 t).div_const 362880).sub ((hasDerivAt_pow 8 t).div_const 80640)).add ((hasDerivAt_pow 7 t).div_const 60480)).sub ((hasDerivAt_pow 5 t).div_const 86400)).add ((hasDerivAt_pow 3 t).div_const 181440)).sub ((hasDerivAt_id t).div_const 1209600)
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u10_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 10 / 3628800 - y ^ 9 / 725760 + y ^ 8 / 483840 - y ^ 6 / 518400 + y ^ 4 / 725760 - y ^ 2 / 2419200 + (1/47900160:ℝ)) (t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) t := by
  have h := (((((((hasDerivAt_pow 10 t).div_const 3628800).sub ((hasDerivAt_pow 9 t).div_const 725760)).add ((hasDerivAt_pow 8 t).div_const 483840)).sub ((hasDerivAt_pow 6 t).div_const 518400)).add ((hasDerivAt_pow 4 t).div_const 725760)).sub ((hasDerivAt_pow 2 t).div_const 2419200)).add (hasDerivAt_const t ((1/47900160:ℝ)))
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u11_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 11 / 39916800 - y ^ 10 / 7257600 + y ^ 9 / 4354560 - y ^ 7 / 3628800 + y ^ 5 / 3628800 - y ^ 3 / 7257600 + y / 47900160) (t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) t := by
  have h := (((((((hasDerivAt_pow 11 t).div_const 39916800).sub ((hasDerivAt_pow 10 t).div_const 7257600)).add ((hasDerivAt_pow 9 t).div_const 4354560)).sub ((hasDerivAt_pow 7 t).div_const 3628800)).add ((hasDerivAt_pow 5 t).div_const 3628800)).sub ((hasDerivAt_pow 3 t).div_const 7257600)).add ((hasDerivAt_id t).div_const 47900160)
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

private theorem hasDerivAt_u12_537 (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 12 / 479001600 - y ^ 11 / 79833600 + y ^ 10 / 43545600 - y ^ 8 / 29030400 + y ^ 6 / 21772800 - y ^ 4 / 29030400 + y ^ 2 / 95800320 - (691/1307674368000:ℝ)) (t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) t := by
  have h := ((((((((hasDerivAt_pow 12 t).div_const 479001600).sub ((hasDerivAt_pow 11 t).div_const 79833600)).add ((hasDerivAt_pow 10 t).div_const 43545600)).sub ((hasDerivAt_pow 8 t).div_const 29030400)).add ((hasDerivAt_pow 6 t).div_const 21772800)).sub ((hasDerivAt_pow 4 t).div_const 29030400)).add ((hasDerivAt_pow 2 t).div_const 95800320)).sub (hasDerivAt_const t ((691/1307674368000:ℝ)))
  convert h using 1 <;> (first | (funext y; dsimp only; ring) | (funext y; simp) | ring)

/-- The bracket `b₀ + b₁` of the second-order Euler–Maclaurin identity, bounded by `0.06859`. -/
private theorem norm_b_le537 {s : ℂ} (hsre : (1 / 2 : ℝ) ≤ s.re) (hsim : s.im = 50)
    (hsle : s.re ≤ 1) :
    ‖(-(10 : ℂ) ^ (1 - s)) / (1 - s) + (s * (1 / 12)) * (10 : ℂ) ^ (-(s + 1))‖ ≤ 0.06864 := by
  have hs1ne : (1 : ℂ) - s ≠ 0 := by
    intro h
    have h2 := congr_arg Complex.im h
    simp only [Complex.sub_im, Complex.one_im, Complex.zero_im] at h2
    rw [hsim] at h2
    norm_num at h2
  have hpow1 : (10 : ℂ) ^ (1 - s) = (10 : ℂ) ^ (-s) * 10 := by
    rw [show (1 - s : ℂ) = -s + 1 by ring,
      Complex.cpow_add (-s) 1 (by norm_num : (10 : ℂ) ≠ 0), Complex.cpow_one]
  have hpow2 : (10 : ℂ) ^ (-(s + 1)) = (10 : ℂ) ^ (-s) * (1 / 10) := by
    rw [show (-(s + 1) : ℂ) = -s + (-1) by ring,
      Complex.cpow_add (-s) (-1) (by norm_num : (10 : ℂ) ≠ 0), Complex.cpow_neg_one]
    norm_num
  have hsm1 : s - 1 ≠ 0 := by
    intro h
    apply hs1ne
    linear_combination -h
  have hsc : -(10 : ℂ) / (1 - s) + s / 120 = (1200 + s * (s - 1)) / (120 * (s - 1)) := by
    field_simp
    ring
  have hbr : (-(10 : ℂ) ^ (1 - s)) / (1 - s) + (s * (1 / 12)) * (10 : ℂ) ^ (-(s + 1))
      = (10 : ℂ) ^ (-s) * ((1200 + s * (s - 1)) / (120 * (s - 1))) := by
    have hb0 : -(10 : ℂ) ^ (1 - s) / (1 - s) = (10 : ℂ) ^ (-s) * (-(10 : ℂ) / (1 - s)) := by
      rw [hpow1]
      ring
    have hb1 : (s * (1 / 12)) * (10 : ℂ) ^ (-(s + 1)) = (10 : ℂ) ^ (-s) * (s / 120) := by
      rw [hpow2]
      ring
    rw [hb0, hb1, ← mul_add, hsc]
  have hpows : ‖(10 : ℂ) ^ (-s)‖ ≤ 0.3163 := by
    have h := norm_pow10_le537 (s := s) hsre 0
    simpa using h
  have hs1 : (50 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.sq_norm (s - 1)
    rw [Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hsim] at h
    nlinarith [norm_nonneg (s - 1), hsle]
  have hre : (1200 + s * (s - 1)).re = -1300 - (s.re - s.re ^ 2) := by
    have h2 : (s * (s - 1)).re = s.re * s.re - s.re - 2500 := by
      rw [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hsim]
      ring
    have h1 : ((1200 : ℂ)).re = 1200 := by norm_num
    rw [Complex.add_re, h1, h2]
    ring
  have him : (1200 + s * (s - 1)).im = 100 * s.re - 50 := by
    have h2 : (s * (s - 1)).im = 100 * s.re - 50 := by
      rw [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hsim]
      ring
    have h1 : ((1200 : ℂ)).im = 0 := by norm_num
    rw [Complex.add_im, h1, h2]
    ring
  have hnum : ‖1200 + s * (s - 1)‖ ≤ 1302 := by
    have h := Complex.sq_norm (1200 + s * (s - 1))
    rw [Complex.normSq_apply, hre, him] at h
    have ha0 : 0 ≤ s.re - s.re ^ 2 := by nlinarith [hsre, hsle]
    have ha1 : s.re - s.re ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (s.re - 1 / 2)]
    nlinarith [norm_nonneg (1200 + s * (s - 1))]
  rw [hbr, norm_mul, norm_div]
  have hden : ‖(120 : ℂ) * (s - 1)‖ = 120 * ‖s - 1‖ := by
    rw [norm_mul]
    norm_num
  rw [hden]
  have hfrac : ‖1200 + s * (s - 1)‖ / (120 * ‖s - 1‖) ≤ 1302 / (120 * 50) := by
    have hd : (0:ℝ) < 120 * ‖s - 1‖ := by
      have h1 : (0:ℝ) < ‖s - 1‖ := by linarith
      nlinarith
    rw [div_le_iff₀ hd]
    have h3 : (120:ℝ) * 50 ≤ 120 * ‖s - 1‖ := by nlinarith [hs1]
    have h4 : (0:ℝ) ≤ 1302 / (120 * 50) := by norm_num
    nlinarith [hnum, h3, h4]
  have hstep : ‖(10 : ℂ) ^ (-s)‖ * (‖1200 + s * (s - 1)‖ / (120 * ‖s - 1‖)) ≤
      0.3163 * (1302 / (120 * 50)) := by
    apply mul_le_mul hpows hfrac (by positivity)
    positivity
  calc ‖(10 : ℂ) ^ (-s)‖ * (‖1200 + s * (s - 1)‖ / (120 * ‖s - 1‖))
      ≤ 0.3163 * (1302 / (120 * 50)) := hstep
    _ ≤ 0.06864 := by norm_num

/-- Every factor `s + i` of the falling factorial, `Re s ∈ [0,1]`, `Im s = 50`. -/
private theorem norm_sadd_le537 {s : ℂ} (hsre0 : 0 ≤ s.re) (hsle : s.re ≤ 1) (hsim : s.im = 50)
    (i : ℕ) (r : ℝ) (hax : (1 + (i : ℝ)) ^ 2 + 2500 ≤ r ^ 2) (hr2 : 0 ≤ r) :
    ‖s + ((i : ℝ) : ℂ)‖ ≤ r := by
  have h := Complex.sq_norm (s + ((i : ℝ) : ℂ))
  rw [Complex.normSq_apply] at h
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at h
  rw [hsim] at h
  have hiR : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have h1 : s.re + (i : ℝ) ≤ 1 + (i : ℝ) := by linarith
  have h0 : 0 ≤ s.re + (i : ℝ) := by linarith
  have key : (s.re + (i : ℝ)) ^ 2 + 2500 ≤ r ^ 2 := by
    have : (s.re + (i : ℝ)) ^ 2 ≤ (1 + (i : ℝ)) ^ 2 := by nlinarith
    linarith
  nlinarith [norm_nonneg (s + ((i : ℝ) : ℂ))]


private theorem norm_prod3_le537 {s : ℂ} (hsre0 : 0 ≤ s.re) (hsle : s.re ≤ 1)
    (hsim : s.im = 50) :
    ‖s * (s + 1) * (s + 2)‖ ≤ 125401 := by
  have h0 : ‖s‖ ≤ 50.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 0 50.01 (by norm_num) (by norm_num)
    simpa using hh
  have h1 : ‖(s + 1)‖ ≤ 50.05 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 1 50.05 (by norm_num) (by norm_num)
    simpa using hh
  have h2 : ‖(s + 2)‖ ≤ 50.1 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 2 50.1 (by norm_num) (by norm_num)
    simpa using hh
  rw [norm_mul, norm_mul]
  refine le_trans (mul_le_mul (mul_le_mul (h0) h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _) (by norm_num)) ?_
  norm_num


private theorem norm_prod5_le537 {s : ℂ} (hsre0 : 0 ≤ s.re) (hsle : s.re ≤ 1)
    (hsim : s.im = 50) :
    ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4)‖ ≤ 316202463 := by
  have h0 : ‖s‖ ≤ 50.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 0 50.01 (by norm_num) (by norm_num)
    simpa using hh
  have h1 : ‖(s + 1)‖ ≤ 50.05 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 1 50.05 (by norm_num) (by norm_num)
    simpa using hh
  have h2 : ‖(s + 2)‖ ≤ 50.1 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 2 50.1 (by norm_num) (by norm_num)
    simpa using hh
  have h3 : ‖(s + 3)‖ ≤ 50.17 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 3 50.17 (by norm_num) (by norm_num)
    simpa using hh
  have h4 : ‖(s + 4)‖ ≤ 50.26 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 4 50.26 (by norm_num) (by norm_num)
    simpa using hh
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (h0) h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _) (by norm_num)) h4 (norm_nonneg _) (by norm_num)) ?_
  norm_num


private theorem norm_prod7_le537 {s : ℂ} (hsre0 : 0 ≤ s.re) (hsle : s.re ≤ 1)
    (hsim : s.im = 50) :
    ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)‖ ≤ 804319460336 := by
  have h0 : ‖s‖ ≤ 50.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 0 50.01 (by norm_num) (by norm_num)
    simpa using hh
  have h1 : ‖(s + 1)‖ ≤ 50.05 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 1 50.05 (by norm_num) (by norm_num)
    simpa using hh
  have h2 : ‖(s + 2)‖ ≤ 50.1 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 2 50.1 (by norm_num) (by norm_num)
    simpa using hh
  have h3 : ‖(s + 3)‖ ≤ 50.17 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 3 50.17 (by norm_num) (by norm_num)
    simpa using hh
  have h4 : ‖(s + 4)‖ ≤ 50.26 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 4 50.26 (by norm_num) (by norm_num)
    simpa using hh
  have h5 : ‖(s + 5)‖ ≤ 50.37 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 5 50.37 (by norm_num) (by norm_num)
    simpa using hh
  have h6 : ‖(s + 6)‖ ≤ 50.5 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 6 50.5 (by norm_num) (by norm_num)
    simpa using hh
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (h0) h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _) (by norm_num)) h4 (norm_nonneg _) (by norm_num)) h5 (norm_nonneg _) (by norm_num)) h6 (norm_nonneg _) (by norm_num)) ?_
  norm_num


private theorem norm_prod9_le537 {s : ℂ} (hsre0 : 0 ≤ s.re) (hsle : s.re ≤ 1)
    (hsim : s.im = 50) :
    ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)‖ ≤ 2070344833446484 := by
  have h0 : ‖s‖ ≤ 50.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 0 50.01 (by norm_num) (by norm_num)
    simpa using hh
  have h1 : ‖(s + 1)‖ ≤ 50.05 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 1 50.05 (by norm_num) (by norm_num)
    simpa using hh
  have h2 : ‖(s + 2)‖ ≤ 50.1 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 2 50.1 (by norm_num) (by norm_num)
    simpa using hh
  have h3 : ‖(s + 3)‖ ≤ 50.17 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 3 50.17 (by norm_num) (by norm_num)
    simpa using hh
  have h4 : ‖(s + 4)‖ ≤ 50.26 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 4 50.26 (by norm_num) (by norm_num)
    simpa using hh
  have h5 : ‖(s + 5)‖ ≤ 50.37 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 5 50.37 (by norm_num) (by norm_num)
    simpa using hh
  have h6 : ‖(s + 6)‖ ≤ 50.5 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 6 50.5 (by norm_num) (by norm_num)
    simpa using hh
  have h7 : ‖(s + 7)‖ ≤ 50.65 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 7 50.65 (by norm_num) (by norm_num)
    simpa using hh
  have h8 : ‖(s + 8)‖ ≤ 50.82 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 8 50.82 (by norm_num) (by norm_num)
    simpa using hh
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (h0) h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _) (by norm_num)) h4 (norm_nonneg _) (by norm_num)) h5 (norm_nonneg _) (by norm_num)) h6 (norm_nonneg _) (by norm_num)) h7 (norm_nonneg _) (by norm_num)) h8 (norm_nonneg _) (by norm_num)) ?_
  norm_num


private theorem norm_prod11_le537 {s : ℂ} (hsre0 : 0 ≤ s.re) (hsle : s.re ≤ 1)
    (hsim : s.im = 50) :
    ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)‖ ≤ 5409256611449265152 := by
  have h0 : ‖s‖ ≤ 50.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 0 50.01 (by norm_num) (by norm_num)
    simpa using hh
  have h1 : ‖(s + 1)‖ ≤ 50.05 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 1 50.05 (by norm_num) (by norm_num)
    simpa using hh
  have h2 : ‖(s + 2)‖ ≤ 50.1 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 2 50.1 (by norm_num) (by norm_num)
    simpa using hh
  have h3 : ‖(s + 3)‖ ≤ 50.17 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 3 50.17 (by norm_num) (by norm_num)
    simpa using hh
  have h4 : ‖(s + 4)‖ ≤ 50.26 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 4 50.26 (by norm_num) (by norm_num)
    simpa using hh
  have h5 : ‖(s + 5)‖ ≤ 50.37 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 5 50.37 (by norm_num) (by norm_num)
    simpa using hh
  have h6 : ‖(s + 6)‖ ≤ 50.5 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 6 50.5 (by norm_num) (by norm_num)
    simpa using hh
  have h7 : ‖(s + 7)‖ ≤ 50.65 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 7 50.65 (by norm_num) (by norm_num)
    simpa using hh
  have h8 : ‖(s + 8)‖ ≤ 50.82 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 8 50.82 (by norm_num) (by norm_num)
    simpa using hh
  have h9 : ‖(s + 9)‖ ≤ 51.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 9 51.01 (by norm_num) (by norm_num)
    simpa using hh
  have h10 : ‖(s + 10)‖ ≤ 51.22 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 10 51.22 (by norm_num) (by norm_num)
    simpa using hh
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (h0) h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _) (by norm_num)) h4 (norm_nonneg _) (by norm_num)) h5 (norm_nonneg _) (by norm_num)) h6 (norm_nonneg _) (by norm_num)) h7 (norm_nonneg _) (by norm_num)) h8 (norm_nonneg _) (by norm_num)) h9 (norm_nonneg _) (by norm_num)) h10 (norm_nonneg _) (by norm_num)) ?_
  norm_num


private theorem norm_prod12_le537 {s : ℂ} (hsre0 : 0 ≤ s.re) (hsle : s.re ≤ 1)
    (hsim : s.im = 50) :
    ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10) * (s + 11)‖ ≤ 278306252659064668160 := by
  have h0 : ‖s‖ ≤ 50.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 0 50.01 (by norm_num) (by norm_num)
    simpa using hh
  have h1 : ‖(s + 1)‖ ≤ 50.05 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 1 50.05 (by norm_num) (by norm_num)
    simpa using hh
  have h2 : ‖(s + 2)‖ ≤ 50.1 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 2 50.1 (by norm_num) (by norm_num)
    simpa using hh
  have h3 : ‖(s + 3)‖ ≤ 50.17 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 3 50.17 (by norm_num) (by norm_num)
    simpa using hh
  have h4 : ‖(s + 4)‖ ≤ 50.26 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 4 50.26 (by norm_num) (by norm_num)
    simpa using hh
  have h5 : ‖(s + 5)‖ ≤ 50.37 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 5 50.37 (by norm_num) (by norm_num)
    simpa using hh
  have h6 : ‖(s + 6)‖ ≤ 50.5 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 6 50.5 (by norm_num) (by norm_num)
    simpa using hh
  have h7 : ‖(s + 7)‖ ≤ 50.65 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 7 50.65 (by norm_num) (by norm_num)
    simpa using hh
  have h8 : ‖(s + 8)‖ ≤ 50.82 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 8 50.82 (by norm_num) (by norm_num)
    simpa using hh
  have h9 : ‖(s + 9)‖ ≤ 51.01 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 9 51.01 (by norm_num) (by norm_num)
    simpa using hh
  have h10 : ‖(s + 10)‖ ≤ 51.22 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 10 51.22 (by norm_num) (by norm_num)
    simpa using hh
  have h11 : ‖(s + 11)‖ ≤ 51.45 := by
    have hh := norm_sadd_le537 hsre0 hsle hsim 11 51.45 (by norm_num) (by norm_num)
    simpa using hh
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (h0) h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _) (by norm_num)) h4 (norm_nonneg _) (by norm_num)) h5 (norm_nonneg _) (by norm_num)) h6 (norm_nonneg _) (by norm_num)) h7 (norm_nonneg _) (by norm_num)) h8 (norm_nonneg _) (by norm_num)) h9 (norm_nonneg _) (by norm_num)) h10 (norm_nonneg _) (by norm_num)) h11 (norm_nonneg _) (by norm_num)) ?_
  norm_num


/-- The order-twelve remainder integral. -/
private theorem norm_I12_le537 {s : ℂ} (hσ : (1 / 2 : ℝ) ≤ s.re) :
    ‖∫ x in Set.Ioi (10 : ℝ), ((((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600
        + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400
        + t ^ 2 / 95800320 - (691 / 1307674368000 : ℝ)) (Int.fract x)) : ℝ) : ℂ) *
        (x : ℂ) ^ (-(s + 12))‖
      ≤ (28 / 100 : ℝ) / 479001600 * ((10 : ℝ) ^ (-s.re - 11) / (s.re + 11)) := by
  have hc : (0 : ℝ) ≤ (28 / 100 : ℝ) / 479001600 := by norm_num
  refine (norm_integral_le_integral_norm _).trans ?_
  have hni : IntegrableOn (fun x : ℝ => ((28 / 100 : ℝ) / 479001600) * x ^ (-s.re - 12))
      (Set.Ioi (10 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  refine (integral_mono_of_nonneg ?_ hni ?_).trans_eq ?_
  · filter_upwards with x
    positivity
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := by have h10 : (10:ℝ) < x := hx; linarith
    have hb : ‖((((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600
        - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320
        - (691 / 1307674368000 : ℝ)) (Int.fract x)) : ℝ) : ℂ)‖ ≤ (28 / 100 : ℝ) / 479001600 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_u12_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le
    rw [norm_mul]
    have hw : ‖(x : ℂ) ^ (-(s + 12))‖ = x ^ (-s.re - 12) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have e : (-(s + (12 : ℂ))).re = -s.re - 12 := by
        rw [Complex.neg_re, Complex.add_re]
        have h12 : ((12 : ℂ)).re = 12 := by norm_num
        rw [h12]
        ring
      rw [e]
    rw [hw]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx0.le _)
  · rw [integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -s.re - 12) (by linarith) (by norm_num)]
    have e : -((10 : ℝ) ^ (-s.re - 12 + 1)) / (-s.re - 12 + 1)
        = (10 : ℝ) ^ (-s.re - 11) / (s.re + 11) := by
      have a1 : -s.re - 12 + 1 = -s.re - 11 := by ring
      have a2 : -s.re - 11 = -(s.re + 11) := by ring
      rw [a1, a2, neg_div_neg_eq]
    rw [e]


set_option maxHeartbeats 20000000

/-- LEAF. Backlund p. 368, the k equal to two Euler summation remainder.
K is exactly zeta minus the finite sum H. Its modulus is below 0.281.
This is the remainder estimate from display 12, not a strip growth bound. -/
theorem boundaryK (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I) - boundaryH σ‖ ≤ 0.281 := by
  set s : ℂ := (σ : ℂ) + 50 * I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = 50 := by rw [hsdef]; simp
  have hσ1 : (1 / 2 : ℝ) ≤ s.re := by rw [hsre]; exact hσ.1
  have hσ2 : s.re ≤ 1 := by rw [hsre]; exact hσ.2
  have hσ0 : (0 : ℝ) ≤ s.re := by linarith
  have hspos : 0 < s.re := by linarith
  have hsne1 : s ≠ 1 := by
    intro h
    have h2 := congr_arg Complex.im h
    rw [hsim] at h2
    norm_num at h2
  set b : ℂ := (-(10 : ℂ) ^ (1 - s)) / (1 - s) + (s * (1 / 12)) * (10 : ℂ) ^ (-(s + 1)) with hb

  have e2 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 2 / 2 - t / 2 + (1/12:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))
      = -(((0 ^ 3 / 6 - 0 ^ 2 / 4 + 0 / 12 : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 2)) + (s + 2) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 3 / 6 - t ^ 2 / 4 + t / 12) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 3))) := by
    have hk : (1 : ℝ) < (s + (2 : ℂ)).re := by
      have e : (s + (2 : ℂ)).re = s.re + 2 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (3 : ℂ)).re := by
      have e : (s + (3 : ℂ)).re = s.re + 3 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 2) hk
      (fun t : ℝ => t ^ 2 / 2 - t / 2 + (1/12:ℝ)) (fun t : ℝ => t ^ 3 / 6 - t ^ 2 / 4 + t / 12)
      continuous_u2_fract537 continuous_u3_fract537
      hasDerivAt_u3_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 2 / 2 - t / 2 + (1/12:ℝ)) (83333334/100000000 : ℝ) (by norm_num)
        (k := (2 : ℂ)) hk continuous_u2_fract537
        (fun x => (abs_u2_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 3 / 6 - t ^ 2 / 4 + t / 12) (8018754/100000000 : ℝ) (by norm_num)
        (k := (3 : ℂ)) hk1 continuous_u3_fract537
        (fun x => (abs_u3_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e3 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 3 / 6 - t ^ 2 / 4 + t / 12) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 3)))
      = -(((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s + 3) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 4))) := by
    have hk : (1 : ℝ) < (s + (3 : ℂ)).re := by
      have e : (s + (3 : ℂ)).re = s.re + 3 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (4 : ℂ)).re := by
      have e : (s + (4 : ℂ)).re = s.re + 4 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 3) hk
      (fun t : ℝ => t ^ 3 / 6 - t ^ 2 / 4 + t / 12) (fun t : ℝ => t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ))
      continuous_u3_fract537 continuous_u4_fract537
      hasDerivAt_u4_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 3 / 6 - t ^ 2 / 4 + t / 12) (8018754/100000000 : ℝ) (by norm_num)
        (k := (3 : ℂ)) hk continuous_u3_fract537
        (fun x => (abs_u3_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) (1388889/100000000 : ℝ) (by norm_num)
        (k := (4 : ℂ)) hk1 continuous_u4_fract537
        (fun x => (abs_u4_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e4 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 4)))
      = -(((0 ^ 5 / 120 - 0 ^ 4 / 48 + 0 ^ 3 / 72 - 0 / 720 : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 4)) + (s + 4) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 5))) := by
    have hk : (1 : ℝ) < (s + (4 : ℂ)).re := by
      have e : (s + (4 : ℂ)).re = s.re + 4 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (5 : ℂ)).re := by
      have e : (s + (5 : ℂ)).re = s.re + 5 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 4) hk
      (fun t : ℝ => t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) (fun t : ℝ => t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720)
      continuous_u4_fract537 continuous_u5_fract537
      hasDerivAt_u5_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) (1388889/100000000 : ℝ) (by norm_num)
        (k := (4 : ℂ)) hk continuous_u4_fract537
        (fun x => (abs_u4_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) (203819/100000000 : ℝ) (by norm_num)
        (k := (5 : ℂ)) hk1 continuous_u5_fract537
        (fun x => (abs_u5_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e5 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 5)))
      = -(((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s + 5) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 6))) := by
    have hk : (1 : ℝ) < (s + (5 : ℂ)).re := by
      have e : (s + (5 : ℂ)).re = s.re + 5 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (6 : ℂ)).re := by
      have e : (s + (6 : ℂ)).re = s.re + 6 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 5) hk
      (fun t : ℝ => t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) (fun t : ℝ => t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ))
      continuous_u5_fract537 continuous_u6_fract537
      hasDerivAt_u6_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) (203819/100000000 : ℝ) (by norm_num)
        (k := (5 : ℂ)) hk continuous_u5_fract537
        (fun x => (abs_u5_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) (33069/100000000 : ℝ) (by norm_num)
        (k := (6 : ℂ)) hk1 continuous_u6_fract537
        (fun x => (abs_u6_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e6 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 6)))
      = -(((0 ^ 7 / 5040 - 0 ^ 6 / 1440 + 0 ^ 5 / 1440 - 0 ^ 3 / 4320 + 0 / 30240 : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 6)) + (s + 6) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 7))) := by
    have hk : (1 : ℝ) < (s + (6 : ℂ)).re := by
      have e : (s + (6 : ℂ)).re = s.re + 6 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (7 : ℂ)).re := by
      have e : (s + (7 : ℂ)).re = s.re + 7 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 6) hk
      (fun t : ℝ => t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) (fun t : ℝ => t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240)
      continuous_u6_fract537 continuous_u7_fract537
      hasDerivAt_u7_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) (33069/100000000 : ℝ) (by norm_num)
        (k := (6 : ℂ)) hk continuous_u6_fract537
        (fun x => (abs_u6_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) (5172/100000000 : ℝ) (by norm_num)
        (k := (7 : ℂ)) hk1 continuous_u7_fract537
        (fun x => (abs_u7_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e7 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 7)))
      = -(((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) + (s + 7) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 8))) := by
    have hk : (1 : ℝ) < (s + (7 : ℂ)).re := by
      have e : (s + (7 : ℂ)).re = s.re + 7 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (8 : ℂ)).re := by
      have e : (s + (8 : ℂ)).re = s.re + 8 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 7) hk
      (fun t : ℝ => t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) (fun t : ℝ => t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ))
      continuous_u7_fract537 continuous_u8_fract537
      hasDerivAt_u8_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) (5172/100000000 : ℝ) (by norm_num)
        (k := (7 : ℂ)) hk continuous_u7_fract537
        (fun x => (abs_u7_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) (827/100000000 : ℝ) (by norm_num)
        (k := (8 : ℂ)) hk1 continuous_u8_fract537
        (fun x => (abs_u8_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e8 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 8)))
      = -(((0 ^ 9 / 362880 - 0 ^ 8 / 80640 + 0 ^ 7 / 60480 - 0 ^ 5 / 86400 + 0 ^ 3 / 181440 - 0 / 1209600 : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 8)) + (s + 8) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 9))) := by
    have hk : (1 : ℝ) < (s + (8 : ℂ)).re := by
      have e : (s + (8 : ℂ)).re = s.re + 8 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (9 : ℂ)).re := by
      have e : (s + (9 : ℂ)).re = s.re + 9 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 8) hk
      (fun t : ℝ => t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) (fun t : ℝ => t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600)
      continuous_u8_fract537 continuous_u9_fract537
      hasDerivAt_u9_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) (827/100000000 : ℝ) (by norm_num)
        (k := (8 : ℂ)) hk continuous_u8_fract537
        (fun x => (abs_u8_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) (132/100000000 : ℝ) (by norm_num)
        (k := (9 : ℂ)) hk1 continuous_u9_fract537
        (fun x => (abs_u9_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e9 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 9)))
      = -(((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9)) + (s + 9) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 10))) := by
    have hk : (1 : ℝ) < (s + (9 : ℂ)).re := by
      have e : (s + (9 : ℂ)).re = s.re + 9 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (10 : ℂ)).re := by
      have e : (s + (10 : ℂ)).re = s.re + 10 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 9) hk
      (fun t : ℝ => t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) (fun t : ℝ => t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ))
      continuous_u9_fract537 continuous_u10_fract537
      hasDerivAt_u10_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) (132/100000000 : ℝ) (by norm_num)
        (k := (9 : ℂ)) hk continuous_u9_fract537
        (fun x => (abs_u9_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) (21/100000000 : ℝ) (by norm_num)
        (k := (10 : ℂ)) hk1 continuous_u10_fract537
        (fun x => (abs_u10_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e10 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 10)))
      = -(((0 ^ 11 / 39916800 - 0 ^ 10 / 7257600 + 0 ^ 9 / 4354560 - 0 ^ 7 / 3628800 + 0 ^ 5 / 3628800 - 0 ^ 3 / 7257600 + 0 / 47900160 : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 10)) + (s + 10) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 11))) := by
    have hk : (1 : ℝ) < (s + (10 : ℂ)).re := by
      have e : (s + (10 : ℂ)).re = s.re + 10 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (11 : ℂ)).re := by
      have e : (s + (11 : ℂ)).re = s.re + 11 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 10) hk
      (fun t : ℝ => t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) (fun t : ℝ => t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160)
      continuous_u10_fract537 continuous_u11_fract537
      hasDerivAt_u11_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) (21/100000000 : ℝ) (by norm_num)
        (k := (10 : ℂ)) hk continuous_u10_fract537
        (fun x => (abs_u10_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) (4/100000000 : ℝ) (by norm_num)
        (k := (11 : ℂ)) hk1 continuous_u11_fract537
        (fun x => (abs_u11_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have e11 : (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 11)))
      = -(((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 11)) + (s + 11) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12))) := by
    have hk : (1 : ℝ) < (s + (11 : ℂ)).re := by
      have e : (s + (11 : ℂ)).re = s.re + 11 := by simp
      rw [e]; linarith
    have hk1 : (1 : ℝ) < (s + (12 : ℂ)).re := by
      have e : (s + (12 : ℂ)).re = s.re + 12 := by simp
      rw [e]; linarith
    have h := ibp_Ioi_gen537 10 (by norm_num) (k := 11) hk
      (fun t : ℝ => t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) (fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ))
      continuous_u11_fract537 continuous_u12_fract537
      hasDerivAt_u12_537 ?_ ?_
    · exact h
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) (4/100000000 : ℝ) (by norm_num)
        (k := (11 : ℂ)) hk continuous_u11_fract537
        (fun x => (abs_u11_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))
    · exact integrable_fract_cpow537 10 (by norm_num) (fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (1/100000000 : ℝ) (by norm_num)
        (k := (12 : ℂ)) hk1 continuous_u12_fract537
        (fun x => (abs_u12_le537 (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x).le).trans (by norm_num))

  have hsum : (∑ n ∈ Finset.range (10 + 1), (1 : ℂ) / (n : ℂ) ^ s)
      = (∑ n ∈ Finset.Icc (1 : ℕ) 9, (1 : ℂ) / (n : ℂ) ^ s) + (10 : ℂ) ^ (-s) := by
    have hset : Finset.range (10 + 1) = insert 0 (insert 10 (Finset.Icc (1 : ℕ) 9)) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hspos
      simp at hspos
    have hzero : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ s = 0 := by
      have h0c : ((0 : ℕ) : ℂ) = 0 := by norm_num
      rw [h0c, Complex.zero_cpow hs0]
      simp
    rw [hzero, zero_add]
    have h10 : (1 : ℂ) / ((10 : ℕ) : ℂ) ^ s = (10 : ℂ) ^ (-s) := by
      rw [one_div]
      exact (Complex.cpow_neg ((10 : ℕ) : ℂ) s).symm
    rw [h10]
    ring
  have hHb : boundaryH σ = (∑ n ∈ Finset.Icc (1 : ℕ) 9, (1 : ℂ) / (n : ℂ) ^ s)
      + (1 / (2 * (10 : ℂ) ^ s)) := by
    simp only [boundaryH]
    rw [← hsdef]
  have hhalf : (1 / (2 * (10 : ℂ) ^ s)) = (10 : ℂ) ^ (-s) / 2 := by
    rw [one_div, mul_inv, ← Complex.cpow_neg (10 : ℂ) s]
    ring
  have hc2 : riemannZeta s - boundaryH σ = b - (s * (s + 1)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 2 / 2 - t / 2 + (1/12:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))) := by
    have hem := em_q_zeta537 (N := 10) (by norm_num) hspos hsne1
    rw [hsum] at hem
    rw [hHb, hhalf, hb]
    linear_combination hem

  have hc3 : riemannZeta s - boundaryH σ
      = b - (s * (s + 1) * (s + 2)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 3 / 6 - t ^ 2 / 4 + t / 12) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 3))) := by
    rw [hc2, e2] <;> try norm_num <;> try ring

  have hc4 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) - (s * (s + 1) * (s + 2) * (s + 3)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 4 / 24 - t ^ 3 / 12 + t ^ 2 / 24 - (1/720:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 4))) := by
    rw [hc3, e3] <;> try norm_num <;> try ring

  have hc5 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 5 / 120 - t ^ 4 / 48 + t ^ 3 / 72 - t / 720) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 5))) := by
    rw [hc4, e4] <;> try norm_num <;> try ring

  have hc6 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 6 / 720 - t ^ 5 / 240 + t ^ 4 / 288 - t ^ 2 / 1440 + (1/30240:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 6))) := by
    rw [hc5, e5] <;> try norm_num <;> try ring

  have hc7 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 7 / 5040 - t ^ 6 / 1440 + t ^ 5 / 1440 - t ^ 3 / 4320 + t / 30240) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 7))) := by
    rw [hc6, e6] <;> try norm_num <;> try ring

  have hc8 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 8 / 40320 - t ^ 7 / 10080 + t ^ 6 / 8640 - t ^ 4 / 17280 + t ^ 2 / 60480 - (1/1209600:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 8))) := by
    rw [hc7, e7] <;> try norm_num <;> try ring

  have hc9 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 9 / 362880 - t ^ 8 / 80640 + t ^ 7 / 60480 - t ^ 5 / 86400 + t ^ 3 / 181440 - t / 1209600) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 9))) := by
    rw [hc8, e8] <;> try norm_num <;> try ring

  have hc10 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 10 / 3628800 - t ^ 9 / 725760 + t ^ 8 / 483840 - t ^ 6 / 518400 + t ^ 4 / 725760 - t ^ 2 / 2419200 + (1/47900160:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 10))) := by
    rw [hc9, e9] <;> try norm_num <;> try ring

  have hc11 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 11 / 39916800 - t ^ 10 / 7257600 + t ^ 9 / 4354560 - t ^ 7 / 3628800 + t ^ 5 / 3628800 - t ^ 3 / 7257600 + t / 47900160) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 11))) := by
    rw [hc10, e10] <;> try norm_num <;> try ring

  have hc12 : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)) * (((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 11)) - (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10) * (s + 11)) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12))) := by
    rw [hc11, e11] <;> try norm_num <;> try ring

  have hK : riemannZeta s - boundaryH σ
      = b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)) * (((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 11)) - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10) * (s + 11) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12))) := hc12

  have hA2 : ‖(s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3))‖ ≤ 0.05509 := by
    have hP : ‖(s * (s + 1) * (s + 2))‖ ≤ 125401 := norm_prod3_le537 hσ0 hσ2 hsim
    have hp : ‖(10 : ℂ) ^ (-(s + 3))‖ ≤ 0.3163 / 1000 := by
      have h := norm_pow10_le537 (s := s) hσ1 3
      have h10 : (10 : ℝ) ^ (-((3 : ℕ) : ℝ)) = 1 / 1000 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        norm_num
      rw [h10] at h
      calc ‖(10 : ℂ) ^ (-(s + 3))‖ ≤ 0.3163 * (1 / 1000) := h
        _ = 0.3163 / 1000 := by norm_num
    calc ‖(s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3))‖
        = ‖(s * (s + 1) * (s + 2))‖ * (1 / 720) * ‖(10 : ℂ) ^ (-(s + 3))‖ := by
          rw [norm_mul, norm_mul]
          have hu : ‖(((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ)‖ = (1 / 720) := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            norm_num
          rw [hu] <;> try ring
      _ ≤ 125401 * (1 / 720) * (0.3163 / 1000) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP (by norm_num)) hp (norm_nonneg _) (by norm_num)
      _ ≤ 0.05509 := by norm_num

  have hA3 : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5))‖ ≤ 0.03308 := by
    have hP : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4))‖ ≤ 316202463 := norm_prod5_le537 hσ0 hσ2 hsim
    have hp : ‖(10 : ℂ) ^ (-(s + 5))‖ ≤ 0.3163 / 100000 := by
      have h := norm_pow10_le537 (s := s) hσ1 5
      have h10 : (10 : ℝ) ^ (-((5 : ℕ) : ℝ)) = 1 / 100000 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        norm_num
      rw [h10] at h
      calc ‖(10 : ℂ) ^ (-(s + 5))‖ ≤ 0.3163 * (1 / 100000) := h
        _ = 0.3163 / 100000 := by norm_num
    calc ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5))‖
        = ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4))‖ * (1 / 30240) * ‖(10 : ℂ) ^ (-(s + 5))‖ := by
          rw [norm_mul, norm_mul]
          have hu : ‖(((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ)‖ = (1 / 30240) := by
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by norm_num)]
            norm_num
          rw [hu] <;> try ring
      _ ≤ 316202463 * (1 / 30240) * (0.3163 / 100000) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP (by norm_num)) hp (norm_nonneg _) (by norm_num)
      _ ≤ 0.03308 := by norm_num

  have hA4 : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7))‖ ≤ 0.02104 := by
    have hP : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6))‖ ≤ 804319460336 := norm_prod7_le537 hσ0 hσ2 hsim
    have hp : ‖(10 : ℂ) ^ (-(s + 7))‖ ≤ 0.3163 / 10000000 := by
      have h := norm_pow10_le537 (s := s) hσ1 7
      have h10 : (10 : ℝ) ^ (-((7 : ℕ) : ℝ)) = 1 / 10000000 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        norm_num
      rw [h10] at h
      calc ‖(10 : ℂ) ^ (-(s + 7))‖ ≤ 0.3163 * (1 / 10000000) := h
        _ = 0.3163 / 10000000 := by norm_num
    calc ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7))‖
        = ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6))‖ * (1 / 1209600) * ‖(10 : ℂ) ^ (-(s + 7))‖ := by
          rw [norm_mul, norm_mul]
          have hu : ‖(((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ)‖ = (1 / 1209600) := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            norm_num
          rw [hu] <;> try ring
      _ ≤ 804319460336 * (1 / 1209600) * (0.3163 / 10000000) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP (by norm_num)) hp (norm_nonneg _) (by norm_num)
      _ ≤ 0.02104 := by norm_num

  have hA5 : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9))‖ ≤ 0.01368 := by
    have hP : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8))‖ ≤ 2070344833446484 := norm_prod9_le537 hσ0 hσ2 hsim
    have hp : ‖(10 : ℂ) ^ (-(s + 9))‖ ≤ 0.3163 / 1000000000 := by
      have h := norm_pow10_le537 (s := s) hσ1 9
      have h10 : (10 : ℝ) ^ (-((9 : ℕ) : ℝ)) = 1 / 1000000000 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        norm_num
      rw [h10] at h
      calc ‖(10 : ℂ) ^ (-(s + 9))‖ ≤ 0.3163 * (1 / 1000000000) := h
        _ = 0.3163 / 1000000000 := by norm_num
    calc ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9))‖
        = ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8))‖ * (1 / 47900160) * ‖(10 : ℂ) ^ (-(s + 9))‖ := by
          rw [norm_mul, norm_mul]
          have hu : ‖(((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ)‖ = (1 / 47900160) := by
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by norm_num)]
            norm_num
          rw [hu] <;> try ring
      _ ≤ 2070344833446484 * (1 / 47900160) * (0.3163 / 1000000000) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP (by norm_num)) hp (norm_nonneg _) (by norm_num)
      _ ≤ 0.01368 := by norm_num

  have hA6 : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)) * (((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 11))‖ ≤ 0.00905 := by
    have hP : ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10))‖ ≤ 5409256611449265152 := norm_prod11_le537 hσ0 hσ2 hsim
    have hp : ‖(10 : ℂ) ^ (-(s + 11))‖ ≤ 0.3163 / 100000000000 := by
      have h := norm_pow10_le537 (s := s) hσ1 11
      have h10 : (10 : ℝ) ^ (-((11 : ℕ) : ℝ)) = 1 / 100000000000 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        norm_num
      rw [h10] at h
      calc ‖(10 : ℂ) ^ (-(s + 11))‖ ≤ 0.3163 * (1 / 100000000000) := h
        _ = 0.3163 / 100000000000 := by norm_num
    calc ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)) * (((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 11))‖
        = ‖(s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10))‖ * (691 / 1307674368000) * ‖(10 : ℂ) ^ (-(s + 11))‖ := by
          rw [norm_mul, norm_mul]
          have hu : ‖(((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ)‖ = (691 / 1307674368000) := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            norm_num
          rw [hu] <;> try ring
      _ ≤ 5409256611449265152 * (691 / 1307674368000) * (0.3163 / 100000000000) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP (by norm_num)) hp (norm_nonneg _) (by norm_num)
      _ ≤ 0.00905 := by norm_num

  have hP12 : ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10) * (s + 11)‖ ≤ 278306252659064668160 := norm_prod12_le537 hσ0 hσ2 hsim
  have hI12 : ‖(∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12)))‖ ≤ (28 / 100 : ℝ) / 479001600 * ((10 : ℝ) ^ (-s.re - 11) / (s.re + 11)) :=
    norm_I12_le537 hσ1
  have hsplit2 : (10 : ℝ) ^ (-s.re - 11) = (10 : ℝ) ^ (-(11 : ℝ)) * (10 : ℝ) ^ (-s.re) := by
    rw [show (-s.re - 11 : ℝ) = -(11 : ℝ) + (-s.re) by ring, Real.rpow_add (by norm_num)]
  have h11 : (10 : ℝ) ^ (-(11 : ℝ)) = 1 / 100000000000 := by
    rw [Real.rpow_neg (by norm_num)]
    norm_num
  have hy : (10 : ℝ) ^ (-s.re - 11) / (s.re + 11) ≤ 0.3163 / 100000000000 / (23 / 2) := by
    rw [hsplit2, h11]
    have hA0 : (0 : ℝ) ≤ 1 / 100000000000 * (10 : ℝ) ^ (-s.re) := by positivity
    have hA1 : 1 / 100000000000 * (10 : ℝ) ^ (-s.re) ≤ 0.3163 / 100000000000 := by
      have hp := pow10_neg_re_le537 hσ1
      nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 10) (-s.re)]
    have hb1 : (23 / 2 : ℝ) ≤ s.re + 11 := by linarith
    have hstep1 : (1 / 100000000000 * (10 : ℝ) ^ (-s.re)) / (s.re + 11)
        ≤ (1 / 100000000000 * (10 : ℝ) ^ (-s.re)) / (23 / 2) := by
      apply div_le_div_of_nonneg_left hA0 (by norm_num) hb1
    have hstep2 : (1 / 100000000000 * (10 : ℝ) ^ (-s.re)) / (23 / 2)
        ≤ (0.3163 / 100000000000) / (23 / 2) := by
      apply div_le_div_of_nonneg_right hA1 (by norm_num)
    linarith
  have hrem : ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10) * (s + 11) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12)))‖ ≤ 0.04475 := by
    rw [norm_mul]
    have hI' : ‖(∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12)))‖ ≤ (28 / 100 : ℝ) / 479001600 * (0.3163 / 100000000000 / (23 / 2)) := by
      refine hI12.trans ?_
      apply mul_le_mul_of_nonneg_left hy (by norm_num)
    calc ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10) * (s + 11)‖ * ‖(∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12)))‖
        ≤ 278306252659064668160 * ((28 / 100 : ℝ) / 479001600 * (0.3163 / 100000000000 / (23 / 2))) := by
          apply mul_le_mul hP12 hI' (norm_nonneg _) (by norm_num)
      _ ≤ 0.04475 := by norm_num
  have hb01 : ‖b‖ ≤ 0.06864 := by
    rw [hb]
    exact norm_b_le537 (s := s) hσ1 hsim hσ2
  have h2 := norm_add_le (b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9))) ((s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)) * (((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 11)))
  have h3 := norm_add_le (b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7))) ((s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9)))
  have h4 := norm_add_le (b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5))) ((s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)))
  have h5 := norm_add_le (b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3))) ((s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)))
  have h6 := norm_add_le b ((s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)))
  have h7 := norm_sub_le (b + (s * (s + 1) * (s + 2)) * (((0 ^ 4 / 24 - 0 ^ 3 / 12 + 0 ^ 2 / 24 - (1/720:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 3)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (((0 ^ 6 / 720 - 0 ^ 5 / 240 + 0 ^ 4 / 288 - 0 ^ 2 / 1440 + (1/30240:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 5)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (((0 ^ 8 / 40320 - 0 ^ 7 / 10080 + 0 ^ 6 / 8640 - 0 ^ 4 / 17280 + 0 ^ 2 / 60480 - (1/1209600:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 7)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) * (((0 ^ 10 / 3628800 - 0 ^ 9 / 725760 + 0 ^ 8 / 483840 - 0 ^ 6 / 518400 + 0 ^ 4 / 725760 - 0 ^ 2 / 2419200 + (1/47900160:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 9)) + (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10)) * (((0 ^ 12 / 479001600 - 0 ^ 11 / 79833600 + 0 ^ 10 / 43545600 - 0 ^ 8 / 29030400 + 0 ^ 6 / 21772800 - 0 ^ 4 / 29030400 + 0 ^ 2 / 95800320 - (691/1307674368000:ℝ) : ℝ)) : ℂ) * (10 : ℂ) ^ (-(s + 11)))
    (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) * (s + 10) * (s + 11) * (∫ x in Set.Ioi (10 : ℝ), (((fun t : ℝ => t ^ 12 / 479001600 - t ^ 11 / 79833600 + t ^ 10 / 43545600 - t ^ 8 / 29030400 + t ^ 6 / 21772800 - t ^ 4 / 29030400 + t ^ 2 / 95800320 - (691/1307674368000:ℝ)) (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 12))))
  rw [hK]
  linarith [h2, h3, h4, h5, h6, h7, hb01, hA2, hA3, hA4, hA5, hA6, hrem]

/-- Backlund pp. 367 and 368, the explicit height-50 calculation.
CONDITIONAL ON the finite H enclosure and the Euler remainder bound. -/
theorem boundary_fifty (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 2.243 := by
  obtain ⟨hr, hi⟩ := boundaryH_components σ hσ
  have hh := norm_of_boundary_components (boundaryH σ) hr hi
  have hk := boundaryK σ hσ
  have h := norm_add_le (boundaryH σ)
    (riemannZeta ((σ : ℂ) + 50 * I) - boundaryH σ)
  rw [add_sub_cancel] at h
  linarith

/-- Backlund p. 368, a rational lower bound sufficient for display 73. -/
theorem three_lt_log_fifty : (3 : ℝ) < Real.log 50 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hp := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide : (3 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

/-- Backlund p. 367, display 73, its scalar threshold exceeds 2.243. -/
theorem boundary73_budget (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (2.243 : ℝ) ≤ 0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50 := by
  have hb : 1 ≤ (25 : ℝ) / π := by
    apply (one_le_div Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  have hp := Real.one_le_rpow hb (show 0 ≤ (1 - σ) / 2 by linarith [hσ.2])
  nlinarith [three_lt_log_fifty]

/-- Backlund display 73, the bottom edge before the strip principle.
CONDITIONAL ON the finite H enclosure and Euler remainder bound. -/
theorem boundary73 (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
      0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50 :=
  (boundary_fifty σ hσ).trans (boundary73_budget σ hσ)

/-- Norm bound for the `q`-kernel remainder integral. -/
private theorem norm_integral_q_le537 (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ x in Set.Ioi (N : ℝ),
        ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))‖
      ≤ (1 / 12) * (((N : ℝ)) ^ (-s.re - 1) / (s.re + 1)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsre : 0 < s.re := hs
  refine (norm_integral_le_integral_norm _).trans ?_
  have hni : IntegrableOn (fun x : ℝ => (1 / 12 : ℝ) * x ^ (-s.re - 2)) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNR).const_mul _
  refine (integral_mono_of_nonneg ?_ hni ?_).trans_eq ?_
  · filter_upwards with x
    positivity
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hNR.trans hx
    have hqx : ‖((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ)‖ ≤ 1 / 12 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_q_le537 x
    have hxw : ‖(x : ℂ) ^ (-(s + 2))‖ = x ^ (-s.re - 2) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.neg_re, Complex.add_re]
      norm_num
      ring
    rw [norm_mul, hxw]
    exact mul_le_mul_of_nonneg_right hqx (Real.rpow_nonneg hx0.le _)
  · rw [integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) hNR]
    have e : -((N : ℝ)) ^ (-s.re - 2 + 1) / (-s.re - 2 + 1)
        = ((N : ℝ)) ^ (-s.re - 1) / (s.re + 1) := by
      have a1 : -s.re - 2 + 1 = -s.re - 1 := by ring
      have a2 : -s.re - 1 = -(s.re + 1) := by ring
      rw [a1, a2, neg_div_neg_eq]
    rw [e]

/-- LEAF. Backlund p. 346, display 8, and p. 361, display 52.
This is the finite Euler norm estimate with its actual harmonic half endpoint.
The missing step is the complex periodic Bernoulli remainder representation
and its integral norm estimate. The harmonic comparison, periodic polynomial
bound, cutoff, root scalings and numerical savings are proved separately. -/
theorem euler8_bernoulli_bound (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ)
    (hσ : σ ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (harmonic (n - 1) : ℝ) + 1 / (2 * (n : ℝ)) + 1 / t +
        Real.sqrt (t ^ 2 + 9 / 4) / (12 * (n : ℝ) ^ 2) +
        Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / (24 * (n : ℝ) ^ 2) := by
  obtain ⟨hσ1, hσ2⟩ := hσ
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have hsne1 : s ≠ 1 := by
    intro h
    have h2 := congr_arg Complex.im h
    rw [hsim] at h2
    simp at h2
    linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hn0 : 0 < n := by omega
  -- the second-order Euler–Maclaurin identity, regrouped
  have hsplit : (∑ k ∈ Finset.range (n + 1), (1 : ℂ) / (k : ℂ) ^ s)
      = (∑ k ∈ Finset.range n, (1 : ℂ) / (k : ℂ) ^ s) + 1 / (n : ℂ) ^ s := by
    rw [Finset.sum_range_succ]
  have hneg : (1 : ℂ) / (n : ℂ) ^ s = (n : ℂ) ^ (-s) := by
    rw [one_div, Complex.cpow_neg]
  have hdiv : (-(n : ℂ) ^ (1 - s)) / (1 - s) = ((n : ℂ) ^ (1 - s)) / (s - 1) := by
    have h1 : (1 : ℂ) - s ≠ 0 := by
      intro h
      apply hsne1
      linear_combination -h
    field_simp
    ring
  have hmain : riemannZeta s = (∑ k ∈ Finset.range n, (1 : ℂ) / (k : ℂ) ^ s)
      + (n : ℂ) ^ (-s) / 2 + ((n : ℂ) ^ (1 - s)) / (s - 1)
      + s * (1 / 12) * (n : ℂ) ^ (-(s + 1))
      + -(s * (s + 1) * (∫ x in Set.Ioi (n : ℝ),
          ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2)))) := by
    rw [em_q_zeta537 n hn hspos hsne1, hsplit, hneg, hdiv]
    ring
  -- bound on the finite sum
  have hA : ‖∑ k ∈ Finset.range n, (1 : ℂ) / (k : ℂ) ^ s‖ ≤ (harmonic (n - 1) : ℝ) := by
    have hstep : ∀ k ∈ Finset.range n, ‖(1 : ℂ) / (k : ℂ) ^ s‖ ≤ ((k : ℝ))⁻¹ := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with h0 | hkpos
      · subst h0
        have hs0 : s ≠ 0 := by
          intro h
          rw [h] at hspos
          simp at hspos
        simp only [Nat.cast_zero, Complex.zero_cpow hs0, div_zero, norm_zero, inv_zero]
        exact le_refl 0
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
        rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hkpos, one_div, hsre]
        have hrp : (k : ℝ) ^ (1 : ℝ) ≤ (k : ℝ) ^ σ :=
          Real.rpow_le_rpow_of_exponent_le hk1 hσ1
        rw [Real.rpow_one] at hrp
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hk0 hrp
    refine (norm_sum_le_of_le (Finset.range n) hstep).trans_eq ?_
    have hset : Finset.range n = Finset.Icc 0 (n - 1) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    exact harmonic_eq_sum_Icc0 (n - 1)
  -- the half term
  have hB : ‖(n : ℂ) ^ (-s) / 2‖ ≤ 1 / (2 * (n : ℝ)) := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re, hsre,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hle : ((n : ℝ)) ^ (-σ) ≤ ((n : ℝ))⁻¹ := by
      calc ((n : ℝ)) ^ (-σ) ≤ ((n : ℝ)) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
        _ = ((n : ℝ))⁻¹ := Real.rpow_neg_one _
    have e : (1 : ℝ) / (2 * (n : ℝ)) = ((n : ℝ))⁻¹ / 2 := by
      rw [one_div, mul_comm (2 : ℝ) ((n : ℝ)), mul_inv, div_eq_mul_inv]
    rw [e]
    linarith
  -- the main term
  have hC : ‖((n : ℂ) ^ (1 - s)) / (s - 1)‖ ≤ 1 / t := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hn0, Complex.sub_re, Complex.one_re, hsre]
    have hnum : ((n : ℝ)) ^ (1 - σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
    have hst : t ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = t := by
        rw [Complex.sub_im, hsim, Complex.one_im, sub_zero]
      rw [him, abs_of_pos htpos] at h
      exact h
    have h1 : ((n : ℝ)) ^ (1 - σ) / ‖s - 1‖ ≤ 1 / ‖s - 1‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    have h2 : 1 / ‖s - 1‖ ≤ 1 / t := one_div_le_one_div_of_le htpos hst
    linarith
  -- the square-root of ‖s‖
  have hsq : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    have h := Complex.sq_norm s
    rw [Complex.normSq_apply] at h
    rw [h, hsre, hsim]
    ring
  have hsn : ‖s‖ ≤ Real.sqrt (t ^ 2 + 9 / 4) := by
    rw [show ‖s‖ = Real.sqrt (‖s‖ ^ 2) from (Real.sqrt_sq (norm_nonneg s)).symm]
    apply Real.sqrt_le_sqrt
    rw [hsq]
    nlinarith
  have hsq1 : ‖s + 1‖ ^ 2 = (σ + 1) ^ 2 + t ^ 2 := by
    have h := Complex.sq_norm (s + 1)
    rw [Complex.normSq_apply] at h
    have h1 : (s + 1).re = σ + 1 := by rw [Complex.add_re, hsre, Complex.one_re]
    have h2 : (s + 1).im = t := by rw [Complex.add_im, hsim, Complex.one_im, add_zero]
    rw [h, h1, h2]
    ring
  have hs1 : ‖s + 1‖ ≤ Real.sqrt (t ^ 2 + 25 / 4) := by
    rw [show ‖s + 1‖ = Real.sqrt (‖s + 1‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    apply Real.sqrt_le_sqrt
    rw [hsq1]
    nlinarith
  have hP : ∀ e : ℝ, e ≤ -2 → ((n : ℝ)) ^ e ≤ (((n : ℝ)) ^ 2)⁻¹ := by
    intro e he
    calc ((n : ℝ)) ^ e ≤ ((n : ℝ)) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnR he
      _ = (((n : ℝ)) ^ 2)⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_two]
  -- the 1/12 term
  have hD : ‖s * (1 / 12) * (n : ℂ) ^ (-(s + 1))‖ ≤
      Real.sqrt (t ^ 2 + 9 / 4) / (12 * (n : ℝ) ^ 2) := by
    have hn2 : ((n : ℝ)) ^ (-(σ + 1)) ≤ (((n : ℝ)) ^ 2)⁻¹ := hP _ (by linarith)
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re,
      Complex.add_re, Complex.one_re, hsre, show ‖(1 / 12 : ℂ)‖ = 1 / 12 by norm_num]
    have h1 : ‖s‖ * (1 / 12) ≤ Real.sqrt (t ^ 2 + 9 / 4) * (1 / 12) :=
      mul_le_mul_of_nonneg_right hsn (by norm_num)
    have h2 : ‖s‖ * (1 / 12) * ((n : ℝ)) ^ (-(σ + 1))
        ≤ Real.sqrt (t ^ 2 + 9 / 4) * (1 / 12) * (((n : ℝ)) ^ 2)⁻¹ :=
      mul_le_mul h1 hn2 (Real.rpow_nonneg (le_of_lt hnpos) _) (by positivity)
    refine h2.trans_eq ?_
    have hA : (((n : ℝ)) ^ 2) ≠ 0 := by positivity
    field_simp
  -- the remainder integral
  have hE : ‖-(s * (s + 1) * (∫ x in Set.Ioi (n : ℝ),
        ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))))‖
      ≤ Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / (24 * (n : ℝ) ^ 2) := by
    have hq := norm_integral_q_le537 n hn hspos
    rw [hsre] at hq
    have hqb : ‖∫ x in Set.Ioi (n : ℝ),
        ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))‖
        ≤ (1 / 24) * (((n : ℝ)) ^ 2)⁻¹ := by
      refine hq.trans ?_
      have hn2 : ((n : ℝ)) ^ (-σ - 1) ≤ (((n : ℝ)) ^ 2)⁻¹ := hP _ (by linarith)
      have hstep : ((n : ℝ)) ^ (-σ - 1) / (σ + 1) ≤ (1 / 2) * (((n : ℝ)) ^ 2)⁻¹ := by
        have h3 : (σ + 1)⁻¹ ≤ (2 : ℝ)⁻¹ := by
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le (by norm_num) (by linarith)
        calc ((n : ℝ)) ^ (-σ - 1) / (σ + 1)
            = ((n : ℝ)) ^ (-σ - 1) * (σ + 1)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ (((n : ℝ)) ^ 2)⁻¹ * (σ + 1)⁻¹ := by
              apply mul_le_mul_of_nonneg_right hn2 (by positivity)
          _ ≤ (((n : ℝ)) ^ 2)⁻¹ * (2 : ℝ)⁻¹ := by
              apply mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (1 / 2) * (((n : ℝ)) ^ 2)⁻¹ := by
              rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num]
              ring
      calc (1 / 12) * (((n : ℝ)) ^ (-σ - 1) / (σ + 1))
          ≤ (1 / 12) * ((1 / 2) * (((n : ℝ)) ^ 2)⁻¹) := by
            apply mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = (1 / 24) * (((n : ℝ)) ^ 2)⁻¹ := by ring
    rw [norm_neg, norm_mul, norm_mul]
    have h1 : ‖s‖ * ‖s + 1‖ ≤ Real.sqrt (t ^ 2 + 9 / 4) * Real.sqrt (t ^ 2 + 25 / 4) :=
      mul_le_mul hsn hs1 (norm_nonneg _) (by positivity)
    have h2 : ‖s‖ * ‖s + 1‖ * ‖∫ x in Set.Ioi (n : ℝ),
        ((Int.fract x ^ 2 / 2 - Int.fract x / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 2))‖
        ≤ Real.sqrt (t ^ 2 + 9 / 4) * Real.sqrt (t ^ 2 + 25 / 4) * ((1 / 24) * (((n : ℝ)) ^ 2)⁻¹) :=
      mul_le_mul h1 hqb (norm_nonneg _) (by positivity)
    refine h2.trans_eq ?_
    rw [Real.sqrt_mul (by positivity)]
    have hA : (((n : ℝ)) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hmain]
  refine (norm_add₅_le _ _ _ _ _).trans ?_
  linarith [hA, hB, hC, hD, hE]

/-- Backlund p. 361, the harmonic half-term is absorbed into log n plus C.
CONDITIONAL ON the finite complex Euler estimate with Bernoulli remainder. -/
theorem euler8_from_bernoulli (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ)
    (hσ : σ ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / t +
        Real.sqrt (t ^ 2 + 9 / 4) / (12 * (n : ℝ) ^ 2) +
        Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / (24 * (n : ℝ) ^ 2) := by
  have h := euler8_bernoulli_bound n hn σ t hσ ht
  have hh := harmonic_endpoint_bound n hn
  linarith

end LeanLab.RamareSaouter2003.Decomp537a

namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex MeasureTheory

/-- Backlund p. 346, display 8, and p. 361, display 52.
CONDITIONAL ON euler8_bernoulli_bound.
This is the finite Euler summation norm estimate before the cutoff is chosen.
The harmonic sum is bounded by log n plus the Euler constant as on p. 361.
For real part one through three halves the numerator norms are bounded by the
stated square roots. The second Bernoulli remainder identity is not imported.
No logarithmic height bound or circle envelope is assumed. -/
theorem euler8_truncation_bound (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ)
    (hσ : σ ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / t +
        Real.sqrt (t ^ 2 + 9 / 4) / (12 * (n : ℝ) ^ 2) +
        Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / (24 * (n : ℝ) ^ 2) := by
  exact euler8_from_bernoulli n hn σ t hσ ht

/-- Backlund pp. 361 and 362, display 54 on the compact right strip.
CONDITIONAL ON the finite Euler summation estimate. The cutoff choice,
root normalizations and complete scalar budget are proved. -/
theorem right54_from_euler8 (σ t : ℝ)
    (hσ : σ ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048 := by
  set n : ℕ := Nat.floor (t / 3) + 1
  obtain ⟨hn, hlo, hhi⟩ := euler_cutoff_bounds t ht
  have hn' : 1 ≤ n := hn
  have htpos : 0 < t := by linarith
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog := euler_cutoff_log t n ht hnpos hhi
  have hinv := euler_cutoff_inverse t n htpos hnpos hlo.le
  have ha := sqrt_height_scale t 9 htpos (by norm_num)
  have hb := sqrt_height_product t htpos
  have hterm1 : Real.sqrt (t ^ 2 + 9 / 4) / (12 * (n : ℝ) ^ 2) ≤
      3 / (4 * t) * Real.sqrt (1 + 9 / (4 * t ^ 2)) := by
    calc
      _ = Real.sqrt (t ^ 2 + 9 / 4) / 12 * (1 / (n : ℝ) ^ 2) := by ring
      _ ≤ Real.sqrt (t ^ 2 + 9 / 4) / 12 * (9 / t ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by
        rw [ha]
        field_simp [htpos.ne']
        <;> ring
  have hterm2 : Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / (24 * (n : ℝ) ^ 2) ≤
      (3 / 8) * Real.sqrt ((1 + 9 / (4 * t ^ 2)) * (1 + 25 / (4 * t ^ 2))) := by
    calc
      _ = Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / 24 * (1 / (n : ℝ) ^ 2) := by ring
      _ ≤ Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) / 24 * (9 / t ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by
        rw [hb]
        field_simp [htpos.ne']
        <;> ring
  have hz := euler8_truncation_bound n hn' σ t hσ ht
  have he := Table537.right54_error_budget t ht
  have hsum : 3 / t + 1 / t = (4 : ℝ) / t := by ring
  linarith

/-- Backlund p. 362, display 54 on the whole right half-plane.
CONDITIONAL ON the finite Euler estimate in the compact strip. Beyond three
halves the actual Dirichlet series and integral test give the bound three. -/
theorem backlund54_from_euler8 (σ t : ℝ) (hσ : 1 ≤ σ) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048 := by
  by_cases hhi : σ ≤ 3 / 2
  · exact right54_from_euler8 σ t ⟨hσ, hhi⟩ ht
  · exact (zeta_norm_le_three σ t (le_of_not_ge hhi)).trans (right54_log_room t ht)

end LeanLab.RamareSaouter2003.Decomp537a


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex MeasureTheory Circle419

/-- Backlund p. 362, display 54, including the printed saving.
CONDITIONAL ON the finite Euler summation estimate. The cutoff, scalar
budget and Dirichlet fallback are proved. Height fifty is included. -/
theorem backlund54 (σ t : ℝ) (hσ : 1 ≤ σ) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048 := by
  exact backlund54_from_euler8 σ t hσ ht

/-- Backlund display 54, its explicit height-50 specialization.
CONDITIONAL ON the Euler summation leaf. -/
theorem boundary54 (σ : ℝ) (hσ : 1 ≤ σ) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ Real.log 50 - 0.048 :=
  backlund54 σ 50 hσ (by norm_num)

/-- LEAF. Backlund pp. 363 to 368, displays 57 to 72 and the strip principle.
Given the actual right boundary and the certified height-50 half-edge,
the normalized Gamma and sine function yields display 56. The functional
symmetry, Gamma errors and growth condition are the remaining strip theory.
The finite bottom-edge calculation is supplied separately. -/
theorem strip56_of_boundary
    (h54 : ∀ σ t : ℝ, 1 ≤ σ → 50 ≤ t →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Real.log t - 0.048)
    (h50 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
        0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t := by
  sorry

/-- Backlund p. 363, display 56, with the bottom-edge data made explicit.
CONDITIONAL ON Euler summation, the H table, its remainder and strip theory. -/
theorem backlund56 (σ t : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t :=
  strip56_of_boundary backlund54 boundary73 σ t hσ ht

/-- Backlund display 56, the explicit corrected majorant at height 50.
CONDITIONAL ON the independent boundary and strip leaves. -/
theorem boundary56 (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
      (625 / 624 : ℝ) * (25 / π) ^ ((1 - σ) / 2) * Real.log 50 := by
  have h := backlund56 σ 50 hσ (by norm_num)
  have hb : (50 : ℝ) / (2 * π) = 25 / π := by ring
  norm_num [hb] at h ⊢
  exact h

/-- The functional equation at `s = t·I`, in norms, with the exact constants
`‖Γ (t I)‖² = π / (t sinh (π t))` and `‖cos (π t I / 2)‖ = cosh (π t / 2)`:
`‖ζ (t I)‖ · √(2 π / t) ≤ ‖ζ (1 + t I)‖`. -/
private theorem norm_zeta_I_mul_sqrt (t : ℝ) (ht : 0 < t) :
    ‖riemannZeta ((t : ℂ) * I)‖ * Real.sqrt (2 * π / t) ≤
      ‖riemannZeta (1 + (t : ℂ) * I)‖ := by
  have hsne : ∀ n : ℕ, ((t : ℂ) * I) ≠ -(n : ℂ) := by
    intro n h
    have h2 := congr_arg Complex.im h
    simp at h2
    linarith
  have hsne1 : ((t : ℂ) * I) ≠ 1 := by
    intro h
    have h2 := congr_arg Complex.im h
    simp at h2
    linarith
  have hfe := riemannZeta_one_sub (s := (t : ℂ) * I) hsne hsne1
  have hC : ‖Complex.cos (π * ((t : ℂ) * I) / 2)‖ = Real.cosh (π * t / 2) := by
    have he : π * ((t : ℂ) * I) / 2 = (((π * t / 2 : ℝ)) : ℂ) * I := by push_cast; ring
    rw [he, Complex.cos_mul_I, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
  have hG : ‖Complex.Gamma ((t : ℂ) * I)‖ ^ 2 = π / (t * Real.sinh (π * t)) := by
    have hne0 : ((t : ℂ) * I) ≠ 0 := by
      intro h
      have h2 := congr_arg Complex.im h
      simp at h2
      linarith
    have h1 : Complex.Gamma (1 + (t : ℂ) * I) =
        ((t : ℂ) * I) * Complex.Gamma ((t : ℂ) * I) := by
      rw [add_comm (1 : ℂ) ((t : ℂ) * I)]
      exact Complex.Gamma_add_one _ hne0
    have h2 := LeanLab.PNTPort.ZetaZeros.normSq_Gamma_one t (ne_of_gt ht)
    rw [h1, norm_mul, show ‖((t : ℂ) * I)‖ = t by
      rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht], mul_pow] at h2
    have hsh : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
    have hshne : Real.sinh (π * t) ≠ 0 := ne_of_gt hsh
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp at h2
    rw [eq_div_iff (by positivity : t * Real.sinh (π * t) ≠ 0)]
    rw [show Real.sinh (π * t) = Real.sinh (t * π) by rw [mul_comm]]
    linear_combination h2
  have hprod : ‖riemannZeta (1 - (t : ℂ) * I)‖
      = 2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (π * t / 2)
        * ‖riemannZeta ((t : ℂ) * I)‖ := by
    rw [hfe, norm_mul, norm_mul, norm_mul, norm_mul]
    have hbase : ‖(2 * (π : ℂ)) ^ (-((t : ℂ) * I))‖ = 1 := by
      rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      have hre : (-((t : ℂ) * I)).re = 0 := by simp
      rw [hre, Real.rpow_zero]
    rw [hbase, hC, show ‖(2 : ℂ)‖ = 2 by norm_num]
    ring
  have hconj : ‖riemannZeta (1 - (t : ℂ) * I)‖ = ‖riemannZeta (1 + (t : ℂ) * I)‖ := by
    have h : (1 : ℂ) - (t : ℂ) * I = starRingEnd ℂ (1 + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [h, riemannZeta_conj, Complex.norm_conj]
  have hch : Real.sinh (π * t) ≤ 2 * Real.cosh (π * t / 2) ^ 2 := by
    rw [Real.sinh_eq, Real.cosh_eq]
    have h1 : Real.exp (π * t / 2) * Real.exp (π * t / 2) = Real.exp (π * t) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(π * t / 2)) * Real.exp (-(π * t / 2)) = Real.exp (-(π * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [← h1, ← h2]
    have hx : (0:ℝ) < Real.exp (π * t / 2) := Real.exp_pos _
    have hy : (0:ℝ) < Real.exp (-(π * t / 2)) := Real.exp_pos _
    have hx1 : (1:ℝ) ≤ Real.exp (π * t / 2) := Real.one_le_exp (by positivity)
    nlinarith [hx, hy, hx1, mul_pos hx hy]
  have hbnd : Real.sqrt (2 * π / t) ≤
      2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (π * t / 2) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hshpos : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
    have hexp : (2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (π * t / 2)) ^ 2
        = 4 * (π / (t * Real.sinh (π * t))) * Real.cosh (π * t / 2) ^ 2 := by
      rw [mul_pow, mul_pow, hG]; ring
    rw [hexp]
    have hkey : 2 * π * Real.sinh (π * t) ≤ 2 * π * (2 * Real.cosh (π * t / 2) ^ 2) := by
      apply mul_le_mul_of_nonneg_left hch (by positivity)
    have htne : t ≠ 0 := ne_of_gt ht
    have hshne : Real.sinh (π * t) ≠ 0 := ne_of_gt hshpos
    field_simp
    nlinarith [hkey]
  calc ‖riemannZeta ((t : ℂ) * I)‖ * Real.sqrt (2 * π / t)
      ≤ ‖riemannZeta ((t : ℂ) * I)‖ *
          (2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (π * t / 2)) :=
        mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
    _ = ‖riemannZeta (1 + (t : ℂ) * I)‖ := by
        have e : ‖riemannZeta ((t : ℂ) * I)‖ *
              (2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (π * t / 2))
            = 2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (π * t / 2)
              * ‖riemannZeta ((t : ℂ) * I)‖ := by ring
        rw [e, ← hprod, hconj]

/-- The `σ = 0` edge of the reflection bound: the factor is `√(t/2π)`, with room for
`1 + 1/(2t²)`. This is the boundary case of `reflection76`. -/
private theorem norm_zeta_at_zero_re (t : ℝ) (ht : 50 ≤ t) :
    ‖riemannZeta ((t : ℂ) * I)‖ ≤
      (t / (2 * π)) ^ (1 / 2 : ℝ) * (1 + 1 / (2 * t ^ 2)) *
        ‖riemannZeta (1 + (t : ℂ) * I)‖ := by
  have htpos : 0 < t := by linarith
  have h := norm_zeta_I_mul_sqrt t htpos
  set r : ℝ := Real.sqrt (t / (2 * π)) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (2 * π / t) = r⁻¹ := by
    rw [hr, ← Real.sqrt_inv]
    congr 1
    field_simp
  rw [hsq] at h
  have h2 : ‖riemannZeta ((t : ℂ) * I)‖ ≤ ‖riemannZeta (1 + (t : ℂ) * I)‖ * r := by
    have hm := mul_le_mul_of_nonneg_right h hrpos.le
    rwa [mul_assoc, inv_mul_cancel₀ hrpos.ne', mul_one] at hm
  have hfac : r ≤ r * (1 + 1 / (2 * t ^ 2)) := by
    have hp : (1 : ℝ) ≤ 1 + 1 / (2 * t ^ 2) := by
      have h0 : (0 : ℝ) < 1 / (2 * t ^ 2) := by positivity
      linarith
    exact le_mul_of_one_le_right hrpos.le hp
  calc ‖riemannZeta ((t : ℂ) * I)‖ ≤ ‖riemannZeta (1 + (t : ℂ) * I)‖ * r := h2
    _ ≤ ‖riemannZeta (1 + (t : ℂ) * I)‖ * (r * (1 + 1 / (2 * t ^ 2))) :=
        mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
    _ = (t / (2 * π)) ^ (1 / 2 : ℝ) * (1 + 1 / (2 * t ^ 2)) *
          ‖riemannZeta (1 + (t : ℂ) * I)‖ := by
        rw [hr, Real.sqrt_eq_rpow]; ring

/-- The left edge of Backlund's display 56: `‖ζ (t I)‖ ≤ √(t/2π) log t` for `t ≥ 50`,
from the `σ = 0` reflection and display 54 (`backlund54`, proved above). -/
private theorem norm_zeta_at_zero_re_log (t : ℝ) (ht : 50 ≤ t) :
    ‖riemannZeta ((t : ℂ) * I)‖ ≤ (t / (2 * π)) ^ (1 / 2 : ℝ) * Real.log t := by
  have htpos : 0 < t := by linarith
  have h1 := norm_zeta_at_zero_re t ht
  have h2 := backlund54 1 t le_rfl ht
  have h3 : (1 + 1 / (2 * t ^ 2)) * (Real.log t - 0.048) ≤ Real.log t := by
    have hL : Real.log t ≤ t := by
      have := Real.log_le_sub_one_of_pos htpos
      linarith
    have hlt : Real.log t / (2 * t ^ 2) ≤ 0.048 := by
      have h4 : Real.log t / (2 * t ^ 2) ≤ t / (2 * t ^ 2) :=
        div_le_div_of_nonneg_right hL (by positivity)
      have he : t / (2 * t ^ 2) = 1 / (2 * t) := by
        field_simp
      rw [he] at h4
      have h5 : 1 / (2 * t) ≤ 1 / 100 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have key : (1 + 1 / (2 * t ^ 2)) * (Real.log t - 0.048)
        = Real.log t + (Real.log t / (2 * t ^ 2) - 0.048 - 0.048 / (2 * t ^ 2)) := by
      field_simp
      ring
    rw [key]
    have h7 : Real.log t / (2 * t ^ 2) - 0.048 ≤ 0 := by linarith
    have h8 : (0 : ℝ) < 0.048 / (2 * t ^ 2) := by positivity
    linarith
  calc ‖riemannZeta ((t : ℂ) * I)‖
      ≤ (t / (2 * π)) ^ (1 / 2 : ℝ) * (1 + 1 / (2 * t ^ 2)) *
          ‖riemannZeta (1 + (t : ℂ) * I)‖ := h1
    _ ≤ (t / (2 * π)) ^ (1 / 2 : ℝ) * (1 + 1 / (2 * t ^ 2)) *
          (Real.log t - 0.048) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ ≤ (t / (2 * π)) ^ (1 / 2 : ℝ) * Real.log t := by
        have hb : (0 : ℝ) ≤ (t / (2 * π)) ^ (1 / 2 : ℝ) := by positivity
        nlinarith [h3, hb]

/-- LEAF. Backlund p. 369, displays 75 and 76, functional equation multiplier.
This states only the norm comparison with the reflected right-strip point.
The saving 0.048 and its absorption are not part of this analytic leaf. -/
theorem reflection76 (σ t : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) 0) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * π)) ^ (1 / 2 - σ) * (1 + 1 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ := by
  sorry

/-- Backlund p. 369, the saving absorbs the functional-equation error. -/
theorem saving_absorbs (t : ℝ) (ht : 50 ≤ t) :
    (1 + 1 / (2 * t ^ 2)) * (Real.log t - 0.048) ≤ Real.log t := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < 2 * t ^ 2 := by positivity
  have hl := Real.log_le_sub_one_of_pos ht0
  have he : Real.log t - 0.048 ≤ 0.048 * (2 * t ^ 2) := by nlinarith
  have hdiv := (div_le_iff₀ hd).mpr he
  calc
    _ = Real.log t - 0.048 + (Real.log t - 0.048) / (2 * t ^ 2) := by ring
    _ ≤ Real.log t := by linarith

/-- Backlund p. 369, display 77, assembled from the reflected right-strip bound.
CONDITIONAL ON Euler summation and the functional-equation multiplier. -/
theorem backlund77 (σ t : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) 0) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * π)) ^ (1 / 2 - σ) * Real.log t := by
  have hz := backlund54 (1 - σ) t (by linarith [hσ.2]) ht
  have hp : 0 ≤ (t / (2 * π)) ^ (1 / 2 - σ) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ _ := reflection76 σ t hσ ht
    _ ≤ (t / (2 * π)) ^ (1 / 2 - σ) * (1 + 1 / (2 * t ^ 2)) *
        (Real.log t - 0.048) := mul_le_mul_of_nonneg_left hz (by positivity)
    _ = (t / (2 * π)) ^ (1 / 2 - σ) *
        ((1 + 1 / (2 * t ^ 2)) * (Real.log t - 0.048)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (saving_absorbs t ht) hp

/-- Backlund display 77, its explicit height-50 boundary.
CONDITIONAL ON Euler summation and the multiplier leaf. -/
theorem boundary77 (σ : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) 0) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
      (25 / π : ℝ) ^ (1 / 2 - σ) * Real.log 50 := by
  have h := backlund77 σ 50 hσ (by norm_num)
  have hb : (50 : ℝ) / (2 * π) = 25 / π := by ring
  simpa [hb] using h


/-- Backlund displays 54, 56 and 77 also bound negative heights by conjugation. -/
theorem norm_zeta_abs_height (σ t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ =
      ‖riemannZeta ((σ : ℂ) + |t| * I)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have hc : ((σ : ℂ) + |t| * I) = starRingEnd ℂ ((σ : ℂ) + t * I) := by
      simp [abs_of_neg (lt_of_not_ge ht), map_add, map_mul] <;> ring
    rw [hc, riemannZeta_conj, Complex.norm_conj]

/-- Rosser p. 224, the four arc ranges cover the whole circle. -/
theorem circle_real_range (φ : ℝ) :
    5 / 4 + 1.32 * Real.cos φ ∈ Set.Icc (-0.07 : ℝ) 2.57 := by
  constructor <;> nlinarith [Real.neg_one_le_cos φ, Real.cos_le_one φ]

/-- Rosser p. 224, the two circle ordinates stay within one radius of the center. -/
theorem circle_height_range (T φ : ℝ) (hT : 1400 ≤ T) :
    (|1.32 * Real.sin φ + T| ∈ Set.Icc (T - 1.32) (T + 1.32)) ∧
    (|1.32 * Real.sin φ - T| ∈ Set.Icc (T - 1.32) (T + 1.32)) := by
  have hsinlo := Real.neg_one_le_sin φ
  have hsinhi := Real.sin_le_one φ
  rw [abs_of_nonneg (show 0 ≤ 1.32 * Real.sin φ + T by nlinarith),
    abs_of_nonpos (show 1.32 * Real.sin φ - T ≤ 0 by nlinarith)]
  constructor <;> constructor <;> nlinarith

/-- Backlund display 56, monotonic enlargement of the critical-strip majorant. -/
theorem critical_majorant_enlarge (T t σ : ℝ) (hT : 1400 ≤ T)
    (ht : t ∈ Set.Icc (T - 1.32) (T + 1.32)) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    t ^ 2 / (t ^ 2 - 4) * (t / (2 * π)) ^ ((1 - σ) / 2) * Real.log t ≤
      (T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4) *
        ((T + 1.32) / (2 * π)) ^ ((1 - σ) / 2) * Real.log (T + 1.32) := by
  have ha : 50 ≤ T - 1.32 := by linarith
  have ht50 : 50 ≤ t := ha.trans ht.1
  have hdmin : 0 < (T - 1.32) ^ 2 - 4 := correction_pos (T - 1.32) ha
  have hcor := correction_antitone (T - 1.32) t ha ht.1
  have hpow : (t / (2 * π)) ^ ((1 - σ) / 2) ≤
      ((T + 1.32) / (2 * π)) ^ ((1 - σ) / 2) := by
    apply Real.rpow_le_rpow (by positivity)
    · exact div_le_div_of_nonneg_right ht.2 (by positivity)
    · linarith [hσ.2]
  have hlog : Real.log t ≤ Real.log (T + 1.32) :=
    Real.log_le_log (by linarith) ht.2
  exact mul_le_mul (mul_le_mul hcor hpow (by positivity) (by positivity)) hlog
    (Real.log_nonneg (by linarith)) (by positivity)

/-- Backlund display 77, monotonic enlargement of the short-left-strip majorant. -/
theorem left_majorant_enlarge (T t σ : ℝ) (hT : 1400 ≤ T)
    (ht : t ∈ Set.Icc (T - 1.32) (T + 1.32)) (hσ : σ ≤ 0) :
    (t / (2 * π)) ^ (1 / 2 - σ) * Real.log t ≤
      ((T + 1.32) / (2 * π)) ^ (1 / 2 - σ) * Real.log (T + 1.32) := by
  have ht50 : 50 ≤ t := by linarith [ht.1]
  apply mul_le_mul
  · apply Real.rpow_le_rpow (by positivity)
    · exact div_le_div_of_nonneg_right ht.2 (by positivity)
    · linarith
  · exact Real.log_le_log (by linarith) ht.2
  · exact Real.log_nonneg (by linarith)
  · positivity

/-- Rosser p. 224, the pointwise four-arc bound with the actual zeta function.
CONDITIONAL ON the independent Backlund boundary and analytic leaves. -/
theorem point_bound (T φ t : ℝ) (hT : 1400 ≤ T)
    (ht : |t| ∈ Set.Icc (T - 1.32) (T + 1.32)) :
    ‖riemannZeta (((5 / 4 + 1.32 * Real.cos φ : ℝ) : ℂ) + t * I)‖ ≤
      Real.exp (logEnvelope T φ) := by
  rw [norm_zeta_abs_height]
  set σ : ℝ := 5 / 4 + 1.32 * Real.cos φ with hσdef
  have hlow : 50 ≤ |t| := by linarith [ht.1]
  have hlogpos : 0 < Real.log (T + 1.32) := Real.log_pos (by linarith)
  have hbase : 0 < (T + 1.32) / (2 * π) := by positivity
  unfold logEnvelope
  change _ ≤ Real.exp (if 5 / 4 ≤ σ then
      Real.log (max 1 ‖riemannZeta ((max (5 / 4) σ : ℝ) : ℂ)‖)
    else if 1 ≤ σ then Real.log (Real.log (T + 1.32))
    else if 0 ≤ σ then
      Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) +
        (1 - σ) / 2 * Real.log ((T + 1.32) / (2 * π)) + Real.log (Real.log (T + 1.32))
    else (1 / 2 - σ) * Real.log ((T + 1.32) / (2 * π)) + Real.log (Real.log (T + 1.32)))
  split_ifs with hright hmid hcrit
  · rw [max_eq_right hright, Real.exp_log (by positivity)]
    simpa using far_right ((σ : ℂ) + |t| * I) (by simpa using hright)
  · rw [Real.exp_log hlogpos]
    have hz := backlund54 σ |t| hmid hlow
    have hl := Real.log_le_log (by linarith : 0 < |t|) ht.2
    linarith
  · have hcpos : 0 < (T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4) := by
      exact div_pos (by nlinarith) (correction_pos (T - 1.32) (by linarith))
    have hp : Real.exp ((1 - σ) / 2 * Real.log ((T + 1.32) / (2 * π))) =
        ((T + 1.32) / (2 * π)) ^ ((1 - σ) / 2) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hbase]
    rw [Real.exp_add, Real.exp_add, Real.exp_log hcpos, hp, Real.exp_log hlogpos]
    have hσ : σ ∈ Set.Icc (0 : ℝ) 1 := ⟨hcrit, le_of_not_ge hmid⟩
    exact (backlund56 σ |t| hσ hlow).trans (critical_majorant_enlarge T |t| σ hT ht hσ)
  · have hp : Real.exp ((1 / 2 - σ) * Real.log ((T + 1.32) / (2 * π))) =
        ((T + 1.32) / (2 * π)) ^ (1 / 2 - σ) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hbase]
    rw [Real.exp_add, hp, Real.exp_log hlogpos]
    have hrange := circle_real_range φ
    have hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) 0 := by
      change -1 / 2 ≤ σ ∧ σ ≤ 0
      constructor
      · dsimp [σ]; linarith [hrange.1]
      · exact le_of_not_ge hcrit
    exact (backlund77 σ |t| hσ hlow).trans (left_majorant_enlarge T |t| σ hT ht hσ.2)

/-- Rosser p. 224, the exact two shifted circle values from the four arcs.
CONDITIONAL ON the independent Backlund boundary and analytic leaves. -/
theorem circle_bound (T φ : ℝ) (hT : 1400 ≤ T) :
    ‖riemannZeta ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 + T * I)‖ ≤
      Real.exp (logEnvelope T φ) ∧
    ‖riemannZeta ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 - T * I)‖ ≤
      Real.exp (logEnvelope T φ) := by
  have hre : ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4).re =
      5 / 4 + 1.32 * Real.cos φ := by
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
    ring
  have him : ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4).im =
      1.32 * Real.sin φ := by
    simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]
  have hp : ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 + T * I) =
      (((5 / 4 + 1.32 * Real.cos φ : ℝ) : ℂ) + ((1.32 * Real.sin φ + T : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, sub_self, add_zero]
      exact hre
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add]
      exact congrArg (fun x : ℝ => x + T) him
  have hm : ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 - T * I) =
      (((5 / 4 + 1.32 * Real.cos φ : ℝ) : ℂ) + ((1.32 * Real.sin φ - T : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
        sub_self, add_zero]
      exact hre
    · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one,
        add_zero, zero_add]
      exact congrArg (fun x : ℝ => x - T) him
  rw [hp, hm]
  obtain ⟨htp, htm⟩ := circle_height_range T φ hT
  exact ⟨point_bound T φ _ hT htp, point_bound T φ _ hT htm⟩

end LeanLab.RamareSaouter2003.Decomp537a


namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex

/-- Backlund p. 366, an elementary logarithm bound for the vertical-edge budgets. -/
theorem log_height_le_tenth (t : ℝ) (ht : 50 ≤ t) : Real.log t ≤ t / 10 := by
  have htpos : 0 < t := by linarith
  have hlog50 : Real.log (50 : ℝ) = Real.log 2 + 2 * Real.log 5 := by
    rw [show (50 : ℝ) = 2 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h50 : Real.log (50 : ℝ) ≤ 4 := by
    linarith [Real.log_two_lt_d9, Table537.log_five_bounds.2]
  have h := Real.log_le_sub_one_of_pos (show 0 < t / 50 by positivity)
  rw [Real.log_div htpos.ne' (by norm_num : (50 : ℝ) ≠ 0)] at h
  linarith

/-- Backlund p. 366, displays 69 and 72, the vertical-edge scalar budget.
The extra factor with five covers the reflected edge as well. -/
theorem critical_vertical_budget (t : ℝ) (ht : 50 ≤ t) :
    (1 - 0.048 / Real.log t) * (1 + 4 / t ^ 2) * (1 + 5 / t ^ 2) ≤ 1 := by
  have htpos : 0 < t := by linarith
  have hd : 0 < t ^ 2 := by positivity
  set L : ℝ := Real.log t
  have hroom : (3 : ℝ) ≤ L - 0.048 := right54_log_room t ht
  have hL : 0 < L := by linarith
  have hLn : 0 ≤ L - 0.048 := by linarith
  have hlog : L ≤ t / 10 := log_height_le_tenth t ht
  have h20 : 20 / t ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hprod : (1 + 4 / t ^ 2) * (1 + 5 / t ^ 2) ≤ 1 + 10 / t ^ 2 := by
    calc
      _ = 1 + (9 + 20 / t ^ 2) / t ^ 2 := by ring
      _ ≤ _ := by
        have h := div_le_div_of_nonneg_right (by linarith : 9 + 20 / t ^ 2 ≤ 10) hd.le
        linarith
  have hgain : 10 * (L - 0.048) ≤ 0.048 * t ^ 2 := by nlinarith
  have hdiv : 10 * (L - 0.048) / t ^ 2 ≤ 0.048 := (div_le_iff₀ hd).mpr hgain
  have hbudget : (1 + 10 / t ^ 2) * (L - 0.048) ≤ L := by
    calc
      _ = L - 0.048 + 10 * (L - 0.048) / t ^ 2 := by ring
      _ ≤ _ := by linarith
  have hprodL := (mul_le_mul_of_nonneg_right hprod hLn).trans hbudget
  have heq : (1 - 0.048 / L) * (1 + 4 / t ^ 2) * (1 + 5 / t ^ 2) =
      ((1 + 4 / t ^ 2) * (1 + 5 / t ^ 2) * (L - 0.048)) / L := by
    field_simp [hL.ne', htpos.ne']
    <;> ring
  change (1 - 0.048 / L) * (1 + 4 / t ^ 2) * (1 + 5 / t ^ 2) ≤ 1
  rw [heq]
  exact (div_le_iff₀ hL).mpr (by simpa using hprodL)

/-- Backlund pp. 366 and 367, the explicit bottom-edge normalization for display 73. -/
theorem critical_bottom_budget :
    (0.9964 : ℝ) * (1 + 4 / (50 : ℝ) ^ 2) * (1 + 5 / (50 : ℝ) ^ 2) ≤ 1 := by norm_num

end LeanLab.RamareSaouter2003.Decomp537a



namespace LeanLab.RamareSaouter2003.Decomp537a
open Real Complex

/-- Backlund p. 361, display 52, the two elementary complex numerator norms. -/
theorem euler_numerator_norms (σ t : ℝ) (hσ : σ ∈ Set.Icc (1 : ℝ) (3 / 2)) :
    ‖(σ : ℂ) + t * I‖ ≤ Real.sqrt (t ^ 2 + 9 / 4) ∧
    ‖(σ : ℂ) + t * I + 1‖ ≤ Real.sqrt (t ^ 2 + 25 / 4) := by
  constructor
  · rw [Complex.norm_add_mul_I]
    apply Real.sqrt_le_sqrt
    nlinarith [hσ.1, hσ.2]
  · have he : (σ : ℂ) + t * I + 1 = (((σ + 1 : ℝ) : ℂ) + t * I) := by
      push_cast
      ring
    rw [he, Complex.norm_add_mul_I]
    apply Real.sqrt_le_sqrt
    nlinarith [hσ.1, hσ.2]

/-- Backlund p. 361, display 52, the elementary product numerator estimate. -/
theorem euler_product_norm (σ t : ℝ) (hσ : σ ∈ Set.Icc (1 : ℝ) (3 / 2)) :
    ‖((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)‖ ≤
      Real.sqrt ((t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4)) := by
  obtain ⟨h1, h2⟩ := euler_numerator_norms σ t hσ
  rw [norm_mul, Real.sqrt_mul (by positivity : 0 ≤ t ^ 2 + 9 / 4)]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg _)

end LeanLab.RamareSaouter2003.Decomp537a

namespace LeanLab.RamareSaouter2003.Decomp537a
open Real MeasureTheory
/-- Backlund p. 361, display 52, the exact real majorant integral. -/
theorem bernoulli_tail_integral (n : ℝ) (hn : 0 < n) :
    (∫ x : ℝ in Set.Ioi n, (1 / 6 : ℝ) * x ^ (-3 : ℝ)) = 1 / (12 * n ^ 2) := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hn]
  norm_num [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]
  ring
/-- Backlund p. 361, display 52, the pointwise real Bernoulli remainder majorant. -/
theorem bernoulli_tail_pointwise (σ x : ℝ) (hσ : 1 ≤ σ) (hx : 1 ≤ x) :
    |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| / x ^ (σ + 2) ≤
      (1 / 6 : ℝ) * x ^ (-3 : ℝ) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ x)]
  exact mul_le_mul (bernoulli_two_bound x)
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
    (Real.rpow_nonneg (by linarith) _) (by norm_num)

end LeanLab.RamareSaouter2003.Decomp537a
namespace LeanLab.RamareSaouter2003.Decomp537a
open Real
/-- Backlund p. 366, the two elementary rational comparisons before display 71. -/
theorem critical_ratio_budget (t : ℝ) (ht : 50 ≤ t) :
    1 - 5 / t ^ 2 ≤ (1 - 1 / t ^ 2) ^ 2 / (1 + 1 / t ^ 2) ^ 2 ∧
    (1 + 1 / t ^ 2) ^ 2 / (1 - 1 / t ^ 2) ^ 2 ≤ 1 + 5 / t ^ 2 := by
  set x : ℝ := 1 / t ^ 2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hpow : (2500 : ℝ) ≤ t ^ 2 := by nlinarith [ht]
  have hxu : x ≤ (1 / 2500 : ℝ) := by
    dsimp [x]
    exact one_div_le_one_div_of_le (by norm_num) hpow
  have hfive : 5 / t ^ 2 = 5 * x := by dsimp [x]; ring
  rw [hfive]
  change 1 - 5 * x ≤ (1 - x) ^ 2 / (1 + x) ^ 2 ∧
    (1 + x) ^ 2 / (1 - x) ^ 2 ≤ 1 + 5 * x
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 + x))).mpr
    nlinarith [pow_nonneg hx0 3]
  · apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - x))).mpr
    have hp : 0 ≤ x * (1 - 10 * x) := mul_nonneg hx0 (by linarith)
    nlinarith [pow_nonneg hx0 3]
end LeanLab.RamareSaouter2003.Decomp537a
#print axioms LeanLab.RamareSaouter2003.Decomp537a.zeta_norm_le_tsum_re
#print axioms LeanLab.RamareSaouter2003.Decomp537a.div_cpow_ofReal
#print axioms LeanLab.RamareSaouter2003.Decomp537a.zeta_ofReal_eq_tsum_rpow
#print axioms LeanLab.RamareSaouter2003.Decomp537a.zeta_abs_ofReal
#print axioms LeanLab.RamareSaouter2003.Decomp537a.far_right
#print axioms LeanLab.RamareSaouter2003.Decomp537a.correction_pos
#print axioms LeanLab.RamareSaouter2003.Decomp537a.correction_antitone
#print axioms LeanLab.RamareSaouter2003.Decomp537a.correction_at_fifty
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundaryH
#print axioms LeanLab.RamareSaouter2003.Table537.log_three_bounds
#print axioms LeanLab.RamareSaouter2003.Table537.log_five_bounds
#print axioms LeanLab.RamareSaouter2003.Table537.imaginary_two
#print axioms LeanLab.RamareSaouter2003.Table537.imaginary_three
#print axioms LeanLab.RamareSaouter2003.Table537.imaginary_five
#print axioms LeanLab.RamareSaouter2003.Table537.imaginaryPositiveAtHalf
#print axioms LeanLab.RamareSaouter2003.Table537.positive_table_exceeds_printed
#print axioms LeanLab.RamareSaouter2003.Table537.remainder12Budget
#print axioms LeanLab.RamareSaouter2003.Table537.boundary_factor_norm
#print axioms LeanLab.RamareSaouter2003.Table537.remainder12_floor
#print axioms LeanLab.RamareSaouter2003.Table537.remainder12_budget_exceeds_printed
#print axioms LeanLab.RamareSaouter2003.Table537.euler_constant_upper
#print axioms LeanLab.RamareSaouter2003.Table537.right54_error_budget
#print axioms LeanLab.RamareSaouter2003.Table537.right54_budget_at_fifty
#print axioms LeanLab.RamareSaouter2003.Table537.log_seven_bounds
#print axioms LeanLab.RamareSaouter2003.Table537.trig_enclosure
#print axioms LeanLab.RamareSaouter2003.Table537.phase_2
#print axioms LeanLab.RamareSaouter2003.Table537.phase_3
#print axioms LeanLab.RamareSaouter2003.Table537.phase_4
#print axioms LeanLab.RamareSaouter2003.Table537.phase_5
#print axioms LeanLab.RamareSaouter2003.Table537.phase_6
#print axioms LeanLab.RamareSaouter2003.Table537.phase_7
#print axioms LeanLab.RamareSaouter2003.Table537.phase_8
#print axioms LeanLab.RamareSaouter2003.Table537.phase_9
#print axioms LeanLab.RamareSaouter2003.Table537.phase_10
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary_term_re_im
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary_amplitude_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_2_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_3_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_4_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_5_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_6_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_7_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_8_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_9_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.term_10_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.finiteH_components
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundaryH_components
#print axioms LeanLab.RamareSaouter2003.Decomp537a.norm_of_boundary_components
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundaryK
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary_fifty
#print axioms LeanLab.RamareSaouter2003.Decomp537a.three_lt_log_fifty
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary73_budget
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary73
#print axioms LeanLab.RamareSaouter2003.Decomp537a.tsum_rpow_le_three
#print axioms LeanLab.RamareSaouter2003.Decomp537a.zeta_norm_le_three
#print axioms LeanLab.RamareSaouter2003.Decomp537a.right54_log_room
#print axioms LeanLab.RamareSaouter2003.Decomp537a.sqrt_height_scale
#print axioms LeanLab.RamareSaouter2003.Decomp537a.sqrt_height_product
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler_cutoff_bounds
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler_cutoff_log
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler_cutoff_inverse
#print axioms LeanLab.RamareSaouter2003.Decomp537a.log_trapezoid_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.harmonic_half_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.harmonic_endpoint_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.bernoulli_two_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler8_bernoulli_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler8_from_bernoulli
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler8_truncation_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.right54_from_euler8
#print axioms LeanLab.RamareSaouter2003.Decomp537a.backlund54_from_euler8
#print axioms LeanLab.RamareSaouter2003.Decomp537a.backlund54
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary54
#print axioms LeanLab.RamareSaouter2003.Decomp537a.strip56_of_boundary
#print axioms LeanLab.RamareSaouter2003.Decomp537a.backlund56
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary56
#print axioms LeanLab.RamareSaouter2003.Decomp537a.reflection76
#print axioms LeanLab.RamareSaouter2003.Decomp537a.saving_absorbs
#print axioms LeanLab.RamareSaouter2003.Decomp537a.backlund77
#print axioms LeanLab.RamareSaouter2003.Decomp537a.boundary77
#print axioms LeanLab.RamareSaouter2003.Decomp537a.norm_zeta_abs_height
#print axioms LeanLab.RamareSaouter2003.Decomp537a.circle_real_range
#print axioms LeanLab.RamareSaouter2003.Decomp537a.circle_height_range
#print axioms LeanLab.RamareSaouter2003.Decomp537a.critical_majorant_enlarge
#print axioms LeanLab.RamareSaouter2003.Decomp537a.left_majorant_enlarge
#print axioms LeanLab.RamareSaouter2003.Decomp537a.point_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.circle_bound
#print axioms LeanLab.RamareSaouter2003.Decomp537a.log_height_le_tenth
#print axioms LeanLab.RamareSaouter2003.Decomp537a.critical_vertical_budget
#print axioms LeanLab.RamareSaouter2003.Decomp537a.critical_bottom_budget
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler_numerator_norms
#print axioms LeanLab.RamareSaouter2003.Decomp537a.euler_product_norm
#print axioms LeanLab.RamareSaouter2003.Decomp537a.bernoulli_tail_integral
#print axioms LeanLab.RamareSaouter2003.Decomp537a.bernoulli_tail_pointwise
#print axioms LeanLab.RamareSaouter2003.Decomp537a.critical_ratio_budget
