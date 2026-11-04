import LeanLab.RieselVaughan1983.Lemma6Theta
import LeanLab.Common.ThetaWindowDusart
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Chebyshev MeasureTheory Set

namespace LeanLab.RieselVaughan1983

namespace Task246

open Lemma6Theta

/-- The power error endpoint budget for the proof of Lemma 6 ii on page 57. -/
lemma power_error_budget {L : ℝ} (hL : 300 ≤ L) :
    140 * exp (9 * L / 10) ≤ (1 / 10000) * exp L / L := by
  have hL0 : 0 < L := by linarith
  have hm := sq_mul_exp_le (L0 := 30) (L := L / 10) (by norm_num) (by linarith)
  have he : (420000000 : ℝ) ≤ exp 30 := by
    have h := exp_nat_ge 30
    norm_num at h
    linarith
  have hq : 3 * L ≤ (L / 10) ^ 2 := by nlinarith
  have hE := exp_pos 30
  have heL : 1400000 * L ≤ exp (L / 10) := by
    nlinarith [mul_le_mul_of_nonneg_right hq hE.le,
      mul_le_mul_of_nonneg_right he hL0.le]
  have hsplit : exp L = exp (9 * L / 10) * exp (L / 10) := by
    rw [← exp_add]
    congr 1
    ring
  rw [le_div_iff₀ hL0, hsplit]
  nlinarith [mul_le_mul_of_nonneg_left heL (exp_pos (9 * L / 10)).le]

/-- CONDITIONAL ON the Schoenfeld psi error. The tail starts at exp 100.
Source: Riesel and Vaughan page 57, the integral step after equation 4.7. -/
lemma tail_upper_of_psi
    (hS : ∀ t : ℝ, 10 ^ 8 ≤ t → |psi t - t| ≤ t / (40 * log t))
    {x : ℝ} (hx : exp 100 ≤ x) :
    (∫ t in exp 100..x, θ t / (t * log t ^ 2)) ≤
      1.00025 * Gprim 2.1 x - 1.00025 * Gprim 2.1 (exp 100) := by
  have he : (10 ^ 8 : ℝ) ≤ exp 100 := by
    exact (by norm_num : (10 ^ 8 : ℝ) ≤ 200000000).trans
      (exp_20.trans (exp_le_exp.mpr (by norm_num)))
  have hy1 : 1 < exp (100 : ℝ) := by linarith
  refine intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    (g := fun t ↦ 1.00025 * Gprim 2.1 t) hx
    (fun t ht ↦ ((Gprim_continuousOn 2.1 hy1) t ht).const_smul (1.00025 : ℝ))
    (fun t ht ↦ ((hasDerivAt_Gprim 2.1 (by linarith [ht.1])).const_mul
      (1.00025 : ℝ)).hasDerivWithinAt)
    (theta_integrableOn x (by linarith) le_rfl) (fun t ht ↦ ?_)
  have ht0 : 0 < t := by linarith [ht.1]
  have hlog : 100 ≤ log t := by
    rw [← log_exp 100]
    exact log_le_log (exp_pos _) ht.1.le
  have hl0 : 0 < log t := by linarith
  have hpsi := hS t (by linarith [ht.1])
  have htheta : θ t ≤ 1.00025 * t := by
    have hsmall : t / (40 * log t) ≤ t / 4000 := by gcongr; linarith
    linarith [theta_le_psi t, le_abs_self (psi t - t)]
  have hd : Gprim' 2.1 t = 1 / log t ^ 2 +
      (0.1 * log t - 6.3) / log t ^ 4 := by
    unfold Gprim'
    field_simp
    ring
  have hpos : 0 ≤ (0.1 * log t - 6.3) / log t ^ 4 :=
    div_nonneg (by linarith) (by positivity)
  calc θ t / (t * log t ^ 2) ≤ 1.00025 * t / (t * log t ^ 2) := by gcongr
    _ = 1.00025 * (1 / log t ^ 2) := by field_simp
    _ ≤ 1.00025 * Gprim' 2.1 t := by rw [hd]; linarith

/-- CONDITIONAL ON the Schoenfeld psi error in the integral and the Dusart power error
at the endpoint. This proves the page 57 prime counting conclusion without a theta leaf. -/
theorem lemma6ii_of_psi_inputs
    (hS : ∀ t : ℝ, 10 ^ 8 ≤ t → |psi t - t| ≤ t / (40 * log t))
    (hP : ∀ L : ℝ, 300 ≤ L → |psi (exp L) - exp L| ≤ 140 * exp (9 * L / 10))
    (x : ℝ) (hx0 : 0 < x) (hx300 : 300 ≤ log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / log x + 10151 / 10000 * x / log x ^ 2 := by
  set L := log x with hL
  have hL0 : 0 < L := by linarith
  have hxe : x = exp L := (exp_log hx0).symm
  have he : (200000000 : ℝ) ≤ exp 100 := exp_20.trans (exp_le_exp.mpr (by norm_num))
  have h2y : (2 : ℝ) ≤ exp 100 := by linarith
  have hyx : exp 100 ≤ x := by rw [hxe]; exact exp_le_exp.mpr (by linarith)
  rw [pi_split h2y hyx]
  have hhead := head_le h2y
  have htail := tail_upper_of_psi hS hyx
  have hGy : 0 ≤ Gprim 2.1 (exp 100) := by unfold Gprim; rw [log_exp]; positivity
  have htheta : θ x ≤ x + (1 / 10000) * x / L := by
    have hp := hP L hx300
    have hb := power_error_budget hx300
    rw [← hxe] at hp hb
    linarith [theta_le_psi x, le_abs_self (psi x - x)]
  set B := x / L ^ 2 with hB
  set C := x / L ^ 3 with hC
  have hBpos : 0 < B := by positivity
  have hCB : C ≤ B / 300 := by
    rw [hC, hB, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ x * L ^ 2 * (L - 300) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hthetaL : θ x / L ≤ x / L + (1 / 10000) * B := by
    rw [div_le_iff₀ hL0]
    calc θ x ≤ x + (1 / 10000) * x / L := htheta
      _ = (x / L + (1 / 10000) * B) * L := by rw [hB]; field_simp
  have hGx : Gprim 2.1 x = B + 2.1 * C := by unfold Gprim; rw [← hL, hB, hC]; ring
  have hm := sq_mul_exp_le (L0 := 300) (L := L) (by norm_num) hx300
  have he200 : (2000000000 : ℝ) ≤ exp 200 := by
    have h := exp_nat_ge 30
    norm_num at h
    exact (by linarith : (2000000000 : ℝ) ≤ exp 30).trans
      (exp_le_exp.mpr (by norm_num))
  have hsplit : exp 300 = exp 100 * exp 200 := by rw [← exp_add]; norm_num
  have hheadB : exp 100 + 1 ≤ B / 10000 := by
    rw [hB, le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]
    rw [hsplit, ← hxe] at hm
    have hp := exp_pos 100
    have hL2 : 0 < L ^ 2 := by positivity
    have h1 : L ^ 2 * exp 100 * 2000000000 ≤ L ^ 2 * exp 100 * exp 200 := by gcongr
    have h2 : L ^ 2 * 1 ≤ L ^ 2 * exp 100 := by gcongr; linarith
    nlinarith
  rw [hGx] at htail
  rw [← hL]
  have hT : 10151 / 10000 * x / L ^ 2 = 10151 / 10000 * B := by rw [hB]; ring
  rw [hT]
  have hsharp : θ x / L + (∫ t in (2 : ℝ)..exp 100, θ t / (t * log t ^ 2)) +
      (∫ t in exp 100..x, θ t / (t * log t ^ 2)) < x / L + 1.008 * B := by
    linarith
  linarith

/-- Mathlib's prime power gap is small on the large range used on page 56. -/
lemma prime_power_error_budget {L : ℝ} (hL : 300 ≤ L) :
    2 * sqrt (exp L) * L ≤ (1 / 100000) * exp L / L := by
  have hL0 : 0 < L := by linarith
  have hm := sq_mul_exp_le (L0 := 150) (L := L / 2) (by norm_num) (by linarith)
  have he : (18000000000 : ℝ) ≤ exp 150 := by
    have h := exp_nat_ge 30
    norm_num at h
    exact (by linarith : (18000000000 : ℝ) ≤ exp 30).trans
      (exp_le_exp.mpr (by norm_num))
  have hpoly : 200000 * L ^ 2 ≤ exp (L / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg (L / 2))]
  rw [← exp_half, le_div_iff₀ hL0]
  have hsplit : exp L = exp (L / 2) * exp (L / 2) := by rw [← exp_add]; congr 1; ring
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hpoly (exp_pos (L / 2)).le]

/-- CONDITIONAL ON the pointwise Dusart psi power error.
This stronger large-range estimate also implies equation 4.3 on page 56. -/
lemma theta_error_of_power {x : ℝ} (hx0 : 0 < x) (hx : 300 ≤ log x)
    (hP : |psi x - x| ≤ 140 * exp (9 * log x / 10)) :
    |θ x - x| < (154 / 1000000) * x / log x := by
  have hx1 : 1 ≤ x := by
    apply (one_le_exp_iff.mpr (show 0 ≤ log x by linarith)).trans
    rw [exp_log hx0]
  have hgap := abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hp := power_error_budget hx
  have hb := prime_power_error_budget hx
  rw [exp_log hx0] at hp hb
  have htri : |θ x - x| ≤ |psi x - x| + |psi x - θ x| := by
    have h := abs_add_le (psi x - x) (θ x - psi x)
    rw [show psi x - x + (θ x - psi x) = θ x - x by ring,
      abs_sub_comm (θ x) (psi x)] at h
    exact h
  have hpos : 0 < x / log x := div_pos hx0 (by linarith)
  simp only [mul_div_assoc] at hP hp hb ⊢
  linarith

/-- CONDITIONAL ON the Dusart theta k = 1 input on the initial interval and the psi
power input above exp 300. This proves the lab's theta version of equation 4.4.
The printed equation 4.4 itself is a psi statement. -/
lemma theta_middle_of_inputs
    (hI : ∀ x : ℝ, 0 < x → 22 ≤ log x → log x < 300 →
      |θ x - x| < (1 / 1000) * x / log x)
    (hP : ∀ L : ℝ, 300 ≤ L → |psi (exp L) - exp L| ≤ 140 * exp (9 * L / 10))
    (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ log x) :
    |θ x - x| < (822 / 100000) * x / log x := by
  have hpos : 0 < x / log x := div_pos hx0 (by linarith)
  by_cases h300 : 300 ≤ log x
  · have hp := hP (log x) h300
    rw [exp_log hx0] at hp
    have h := theta_error_of_power hx0 h300 hp
    simp only [mul_div_assoc] at h ⊢
    linarith
  · have h := hI x hx0 hx (lt_of_not_ge h300)
    simp only [mul_div_assoc] at h ⊢
    linarith

/-- The normalized Dusart exponential error decreases once X is at least 5/2.
Auxiliary to the replacement proof of equation 4.3 on page 56. -/
lemma dusart_decay_le (a X : ℝ) (ha : (5 / 2 : ℝ) ≤ a) (hX : a ≤ X) :
    X ^ (5 / 2 : ℝ) * exp (-X) ≤ a ^ (5 / 2 : ℝ) * exp (-a) := by
  have ha0 : 0 < a := by linarith
  have hX0 : 0 < X := ha0.trans_le hX
  have hlog0 : 0 ≤ log X - log a := sub_nonneg.mpr (log_le_log ha0 hX)
  have hlog : log X - log a ≤ X / a - 1 := by
    simpa only [log_div hX0.ne' ha0.ne'] using
      log_le_sub_one_of_pos (div_pos hX0 ha0)
  have hm := mul_le_mul_of_nonneg_right hlog ha0.le
  simp only [sub_mul, div_mul_cancel₀ _ ha0.ne', one_mul] at hm
  have hp := mul_le_mul_of_nonneg_right ha hlog0
  rw [rpow_def_of_pos hX0, rpow_def_of_pos ha0, ← exp_add, ← exp_add]
  apply exp_le_exp.mpr
  linarith

/-- CONDITIONAL ON the pointwise Dusart exponential theta error, Prove2Me 8b054cf2.
The analytic input is valid from log x at least 70 times 5.69693.
The normalized error decreases and gives equation 4.3 on Riesel and Vaughan page 56. -/
theorem theta_error_of_dusart_exponential (x : ℝ) (hx0 : 0 < x) (hx : 3000 ≤ log x)
    (hD : |θ x - x| < x * sqrt (8 / Real.pi) *
      sqrt (sqrt (log x / (569693 / 100000 : ℝ))) *
      exp (-sqrt (log x / (569693 / 100000 : ℝ)))) :
    |θ x - x| < (154 / 1000000) * x / log x := by
  let R : ℝ := 569693 / 100000
  let X : ℝ := sqrt (log x / R)
  have hR : 0 < R := by norm_num [R]
  have hXnonneg : 0 ≤ X := sqrt_nonneg _
  have hXs : X ^ 2 = log x / R := sq_sqrt (by positivity)
  have hLX : log x = R * X ^ 2 := by rw [hXs]; field_simp
  have hX : 22 ≤ X := by
    have hRs : R * X ^ 2 = log x := hLX.symm
    norm_num [R] at hRs
    nlinarith
  have hX0 : 0 < X := by linarith
  have hc : sqrt (8 / Real.pi) ≤ 2 := by
    apply (sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.two_le_pi]
  have hpow : (22 : ℝ) ^ (5 / 2 : ℝ) ≤ 10648 := by
    calc (22 : ℝ) ^ (5 / 2 : ℝ) ≤ (22 : ℝ) ^ (3 : ℝ) :=
      rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 10648 := by norm_num
  have he : (3000000000 : ℝ) ≤ exp 22 := by
    have h := exp_nat_ge 22
    norm_num at h
    linarith
  have hend : (22 : ℝ) ^ (5 / 2 : ℝ) * exp (-22) ≤ 10648 / 3000000000 := by
    rw [exp_neg, ← div_eq_mul_inv]
    exact (div_le_div_of_nonneg_right hpow (exp_pos _).le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) he)
  have hdecay := (dusart_decay_le 22 X (by norm_num) hX).trans hend
  have hcoef : sqrt (8 / Real.pi) * R ≤ 12 := by
    calc sqrt (8 / Real.pi) * R ≤ 2 * R := mul_le_mul_of_nonneg_right hc hR.le
      _ ≤ 12 := by norm_num [R]
  have hratio : sqrt (8 / Real.pi) * R * (X ^ (5 / 2 : ℝ) * exp (-X)) <
      154 / 1000000 := by
    calc _ ≤ 12 * (X ^ (5 / 2 : ℝ) * exp (-X)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ 12 * (10648 / 3000000000) := mul_le_mul_of_nonneg_left hdecay (by norm_num)
      _ < _ := by norm_num
  have hpower : X ^ 2 * sqrt X = X ^ (5 / 2 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_natCast X 2, ← rpow_add hX0]
    norm_num
  have hid : (x * sqrt (8 / Real.pi) * sqrt X * exp (-X)) * log x =
      x * (sqrt (8 / Real.pi) * R * (X ^ (5 / 2 : ℝ) * exp (-X))) := by
    rw [hLX, ← hpower]
    ring
  apply (lt_div_iff₀ (by linarith : 0 < log x)).mpr
  have hm := mul_lt_mul_of_pos_left hratio hx0
  change |θ x - x| < x * sqrt (8 / Real.pi) * sqrt X * exp (-X) at hD
  have hd := mul_lt_mul_of_pos_right hD (by linarith : 0 < log x)
  rw [hid] at hd
  nlinarith

/-
Narrow elementary port from prove2me/formalpedia at 043f1deaf1ac9364d39e2c6f33604f0b7e7cc4ec.
Apache 2.0. PsiComparison and PowerQuarterPsi by abcdefg.
Sources: Definitions/Def_dusart_psi_433_20261014_PsiComparison.lean and
Solutions/Sol_ExplicitPNT_DusartTable1_Modules_PowerQuarterPsi.lean.
The analytic double average estimate remains an explicit hypothesis.
AI wrote and adapted the Lean code. Binary Goldbach is OPEN.
-/
namespace BoxTransfer

noncomputable def boxAverage (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..h, f (x + t)) / h

noncomputable def doubleBoxAverage (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  boxAverage (fun y => boxAverage f y h) x h

lemma boxAverage_mono (f : ℝ → ℝ) (hf : Monotone f) (h : ℝ) (hh : 0 < h) :
    Monotone (fun x => boxAverage f x h) := by
  intro x y hxy
  apply (div_le_div_iff_of_pos_right hh).2
  apply intervalIntegral.integral_mono_on hh.le
    ((hf.comp (monotone_const.add monotone_id)).intervalIntegrable)
    ((hf.comp (monotone_const.add monotone_id)).intervalIntegrable)
  intro t ht
  exact hf (by linarith)

lemma boxAverage_bounds (f : ℝ → ℝ) (hf : Monotone f) (x h : ℝ) (hh : 0 < h) :
    f x ≤ boxAverage f x h ∧ boxAverage f x h ≤ f (x + h) := by
  have hi : IntervalIntegrable (fun t : ℝ => f (x + t)) volume 0 h :=
    (hf.comp (monotone_const.add monotone_id)).intervalIntegrable
  have hl := intervalIntegral.integral_mono_on hh.le intervalIntegrable_const hi
    (fun t ht => hf (show x ≤ x + t by linarith [ht.1]))
  have hu := intervalIntegral.integral_mono_on hh.le hi intervalIntegrable_const
    (fun t ht => hf (show x + t ≤ x + h by linarith [ht.2]))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hl hu
  constructor
  · exact (le_div_iff₀ hh).2 (by simpa only [mul_comm] using hl)
  · exact (div_le_iff₀ hh).2 (by simpa only [mul_comm] using hu)

theorem doubleBoxAverage_bounds (f : ℝ → ℝ) (hf : Monotone f)
    (x h : ℝ) (hh : 0 < h) :
    f x ≤ doubleBoxAverage f x h ∧ doubleBoxAverage f x h ≤ f (x + 2 * h) := by
  have h₁ := boxAverage_bounds f hf x h hh
  have h₂ := boxAverage_bounds (fun y => boxAverage f y h)
    (boxAverage_mono f hf h hh) x h hh
  have h₃ := boxAverage_bounds f hf (x + h) h hh
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  simpa only [doubleBoxAverage, show x + h + h = x + 2 * h by ring] using
    h₂.2.trans h₃.2

theorem psi_between_double_averages (x h : ℝ) (hh : 0 < h) :
    doubleBoxAverage Chebyshev.psi (x - 2 * h) h ≤ Chebyshev.psi x ∧
      Chebyshev.psi x ≤ doubleBoxAverage Chebyshev.psi x h := by
  have hl := (doubleBoxAverage_bounds Chebyshev.psi Chebyshev.psi_mono
    (x - 2 * h) h hh).2
  have hu := (doubleBoxAverage_bounds Chebyshev.psi Chebyshev.psi_mono x h hh).1
  exact ⟨by simpa using hl, hu⟩

theorem psi_error_of_double_average_errors (x h E : ℝ) (hh : 0 < h)
    (hl : |doubleBoxAverage Chebyshev.psi (x - 2 * h) h - (x - h)| ≤ E)
    (hu : |doubleBoxAverage Chebyshev.psi x h - (x + h)| ≤ E) :
    |Chebyshev.psi x - x| ≤ E + h := by
  have hb := psi_between_double_averages x h hh
  have hll := (abs_le.mp hl).1
  have huu := (abs_le.mp hu).2
  apply abs_le.mpr
  constructor <;> linarith


lemma exp_ten_lower : (1024 : ℝ) ≤ Real.exp 10 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  exact hp

lemma inflated_exp_rpow (t r : ℝ) (hr : r ≤ 2) :
    ((11 / 10 : ℝ) * Real.exp t)^r ≤ (5 / 4 : ℝ) * Real.exp (t * r) := by
  rw [Real.mul_rpow (by norm_num) (Real.exp_pos t).le, ← Real.exp_mul]
  have hc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 11 / 10) hr
  norm_num at hc
  exact mul_le_mul_of_nonneg_right (hc.trans (by norm_num)) (Real.exp_pos _).le

theorem psi_power_of_average
    (hA : ∀ (a h z : ℝ), 1 ≤ a → 0 < h → a + 2 * h ≤ z → 4 ≤ z / h →
      |doubleBoxAverage psi a h - (a + h)| ≤
        2 + 192 * z ^ (9 / 8 : ℝ) / h ^ (1 / 4 : ℝ) +
          512 * z ^ (3 / 2 : ℝ) / h ^ 2)
    (t : ℝ) (ht : 300 ≤ t) :
    |Chebyshev.psi (Real.exp t) - Real.exp t| ≤ 140 * Real.exp (9 * t / 10) := by
  let x := Real.exp t
  let y := Real.exp (9 * t / 10)
  let h := 16 * y
  let z := (11 / 10 : ℝ) * x
  have hx0 : 0 < x := Real.exp_pos _
  have hy0 : 0 < y := Real.exp_pos _
  have hh : 0 < h := mul_pos (by norm_num) hy0
  have hd : (1024 : ℝ) ≤ Real.exp (t / 10) :=
    exp_ten_lower.trans (Real.exp_le_exp.mpr (by linarith))
  have hs : x = y * Real.exp (t / 10) := by
    dsimp [x, y]
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall : h ≤ x / 20 := by
    dsimp [h]
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left hd hy0.le]
  have hx2 : 2 ≤ x := by
    have he := exp_ten_lower.trans (Real.exp_le_exp.mpr (show 10 ≤ t by linarith))
    linarith
  have hy2 : 2 ≤ y := by
    have he := exp_ten_lower.trans (Real.exp_le_exp.mpr (show 10 ≤ 9 * t / 10 by linarith))
    exact (by linarith : (2 : ℝ) ≤ Real.exp (9 * t / 10))
  have hlow : 1 ≤ x - 2 * h := by linarith
  have hT : 4 ≤ z / h := (le_div_iff₀ hh).2 (by dsimp [z]; linarith)
  have hzlow : x - 2 * h + 2 * h ≤ z := by dsimp [z]; linarith
  have hzhigh : x + 2 * h ≤ z := by dsimp [z]; linarith
  have hroot : h^(1 / 4 : ℝ) = 2 * Real.exp (9 * t / 40) := by
    dsimp [h, y]
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    have h16 : (16 : ℝ)^(1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = (2 : ℝ)^4 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
      norm_num
    rw [h16]
    congr 2
    ring
  have hsq : h^2 = 256 * Real.exp (9 * t / 5) := by
    dsimp [h, y]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
    ring_nf
  have hzero : 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) ≤ 120 * y := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hh _)).2
    have hzpow := inflated_exp_rpow t (9 / 8) (by norm_num)
    change z^(9 / 8 : ℝ) ≤ (5 / 4 : ℝ) * Real.exp (t * (9 / 8)) at hzpow
    calc
      _ ≤ 192 * ((5 / 4 : ℝ) * Real.exp (t * (9 / 8))) :=
        mul_le_mul_of_nonneg_left hzpow (by norm_num)
      _ = 120 * y * h^(1 / 4 : ℝ) := by
        rw [hroot]
        dsimp [y]
        rw [show 120 * Real.exp (9 * t / 10) * (2 * Real.exp (9 * t / 40)) =
          240 * (Real.exp (9 * t / 10) * Real.exp (9 * t / 40)) by ring, ← Real.exp_add]
        rw [show 9 * t / 10 + 9 * t / 40 = t * (9 / 8) by ring]
        ring
  have hrest : 512 * z^(3 / 2 : ℝ) / h^2 ≤ y := by
    apply (div_le_iff₀ (sq_pos_of_pos hh)).2
    have hzpow := inflated_exp_rpow t (3 / 2) (by norm_num)
    change z^(3 / 2 : ℝ) ≤ (5 / 4 : ℝ) * Real.exp (t * (3 / 2)) at hzpow
    have he : (3 : ℝ) ≤ Real.exp (6 * t / 5) :=
      (by norm_num : (3 : ℝ) ≤ 1024).trans
        (exp_ten_lower.trans (Real.exp_le_exp.mpr (by linarith)))
    have hp := mul_le_mul_of_nonneg_left he (Real.exp_pos (t * (3 / 2))).le
    rw [← Real.exp_add] at hp
    have hprod : y * h^2 = 256 * Real.exp (t * (3 / 2) + 6 * t / 5) := by
      rw [hsq]
      dsimp [y]
      rw [show Real.exp (9 * t / 10) * (256 * Real.exp (9 * t / 5)) =
        256 * (Real.exp (9 * t / 10) * Real.exp (9 * t / 5)) by ring, ← Real.exp_add]
      congr 1
      ring
    rw [hprod]
    nlinarith [Real.exp_pos (t * (3 / 2))]
  have hbound : 2 + 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) +
      512 * z^(3 / 2 : ℝ) / h^2 ≤ 124 * y := by linarith
  have hl := (hA (x - 2 * h) h z hlow hh hzlow hT).trans hbound
  have hu := (hA x h z (by linarith) hh hzhigh hT).trans hbound
  have hcenter : x - 2 * h + h = x - h := by ring
  rw [hcenter] at hl
  have hp := psi_error_of_double_average_errors x h (124 * y) hh hl hu
  change |Chebyshev.psi x - x| ≤ 140 * y
  dsimp [h] at hp
  linarith


end BoxTransfer

/-- LEAF. The smoothed psi bound used by the power error proof.
Supporting variant for Dusart 2018 Table 1 and explicit formula estimates on pages 230 to 234.
Prove2Me PowerQuarterSmoothed, solution 9e2f241c. The analytic proof is not ported here. -/
theorem psi_double_average_quarter_leaf (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h) :
    |BoxTransfer.doubleBoxAverage psi a h - (a + h)| ≤
      2 + 192 * z ^ (9 / 8 : ℝ) / h ^ (1 / 4 : ℝ) +
        512 * z ^ (3 / 2 : ℝ) / h ^ 2 := by
  sorry


/-- LEAF. Schoenfeld 1976 Theorem 7, the psi input used by Tao 2012 Lemma 4.3.
The initial supplied Prove2Me 3fa7d8d1 export has a cyclic dependency graph.
The later accepted range proof uses finite RH through 65000 and is not ported here.
Riesel and Vaughan page 57 uses this type of psi upper input inside the integral. -/
theorem schoenfeld_psi_error_large_leaf (t : ℝ) (ht : 10 ^ 8 ≤ t) :
    |psi t - t| ≤ t / (40 * log t) := by
  sorry

/-- Dusart explicit psi power error, Prove2Me 6c28030e.
CONDITIONAL ON the smoothed psi estimate. Every unsmoothing and numerical step is proved.
Replacement endpoint input for Riesel and Vaughan page 57 equation 4.2. -/
theorem dusart_psi_power_error_leaf (L : ℝ) (hL : 300 ≤ L) :
    |psi (exp L) - exp L| ≤ 140 * exp (9 * L / 10) := by
  exact BoxTransfer.psi_power_of_average psi_double_average_quarter_leaf L hL

/-- LEAF. Dusart 2010 page 4 Theorem 5.2, k = 1 and eta = 0.001.
Restricted to the only remaining initial interval. The threshold 908994923 is below exp 22.
Source https://arxiv.org/abs/1002.0442v1. The printed Riesel and Vaughan equation 4.4 is for psi. -/
theorem dusart_theta_initial_leaf (x : ℝ) (hx0 : 0 < x) (hx22 : 22 ≤ log x)
    (hx300 : log x < 300) :
    |θ x - x| < (1 / 1000) * x / log x := by
  sorry

end Task246

/-- Page 56 equation 4.3. CONDITIONAL ON the shared psi power source leaf.
Statement repaired 2026-10-31 by the architect, run 20261031T2235Z-16111:
`hx0 : 0 < x` added. Without it the leaf was false at x = -exp 3000.
See `LeanLab.Common.FalseLeafAudit20261031`. Its sealed statement is retained. -/
theorem theta_bound_4_3 (x : ℝ) (hx0 : 0 < x) (hx : 3000 ≤ Real.log x) :
    |θ x - x| < 154 / 1000000 * x / Real.log x := by
  have hP := Task246.dusart_psi_power_error_leaf (log x) (by linarith)
  rw [exp_log hx0] at hP
  exact Task246.theta_error_of_power hx0 (by linarith) hP

/-- The lab theta version of page 56 equation 4.4. The printed equation is for psi.
CONDITIONAL ON the initial Dusart theta input and the shared psi power input.
Statement repaired 2026-10-31 by the architect, run 20261031T2235Z-16111:
`hx0 : 0 < x` added. Without it the leaf was false at x = -exp 22.
Its sealed statement is retained. -/
theorem theta_bound_4_4 (x : ℝ) (hx0 : 0 < x) (hx1 : 22 ≤ Real.log x) (hx2 : Real.log x ≤ 5000) :
    |θ x - x| < 822 / 100000 * x / Real.log x := by
  exact Task246.theta_middle_of_inputs Task246.dusart_theta_initial_leaf
    Task246.dusart_psi_power_error_leaf x hx0 hx1

/-- Page 57 combined theta bound. CONDITIONAL ON the two cited theta assemblies. -/
theorem theta_bound_combined (x : ℝ) (hx0: 0 < x) (hx : 22 ≤ Real.log x) :
    |θ x - x| < 822 / 100000 * x / Real.log x := by
  by_cases hx3000 : 3000 ≤ Real.log x
  · have h1 := theta_bound_4_3 x hx0 hx3000
    have h2 : (154 : ℝ) / 1000000 ≤ (822 : ℝ) / 100000 := by norm_num
    have h22 : (0 : ℝ) ≤ 22 := by norm_num
    have h3 : 0 ≤ x / Real.log x := div_nonneg hx0.le (h22.trans hx)
    calc |θ x - x| < 154 / 1000000 * x / Real.log x := h1
      _ = 154 / 1000000 * (x / Real.log x) := by ring
      _ ≤ 822 / 100000 * (x / Real.log x) := mul_le_mul_of_nonneg_right h2 h3
      _ = 822 / 100000 * x / Real.log x := by ring
  · push Not at hx3000
    have hx3000_le : Real.log x ≤ 5000 := hx3000.le.trans (by norm_num)
    exact theta_bound_4_4 x hx0 hx hx3000_le

/-- Page 57 integral bound for prime counting. CONDITIONAL ON the Schoenfeld psi input
inside the integral and the Dusart psi power input at the endpoint. -/
theorem lemma6ii_integral (x : ℝ) (hx0 : 0 < x) (hx300 : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  exact Task246.lemma6ii_of_psi_inputs Task246.schoenfeld_psi_error_large_leaf
    Task246.dusart_psi_power_error_leaf x hx0 hx300

/-- The exact Lemma 6 ii statement. CONDITIONAL ON the two shared psi source leaves. -/
theorem lemma6ii_decomposed : Lemma6ii := by
  intro x hx0 hx300
  exact lemma6ii_integral x hx0 hx300

end LeanLab.RieselVaughan1983
