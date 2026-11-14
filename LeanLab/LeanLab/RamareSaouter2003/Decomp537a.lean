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

/-- LEAF. Backlund p. 368, the k equal to two Euler summation remainder.
K is exactly zeta minus the finite sum H. Its modulus is below 0.281.
This is the remainder estimate from display 12, not a strip growth bound. -/
theorem boundaryK (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I) - boundaryH σ‖ ≤ 0.281 := by
  sorry

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
  sorry

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
