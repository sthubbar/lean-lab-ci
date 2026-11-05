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

/-
Task206J: an additive block for `RieselVaughan1983/DecompJ206.lean`.

NOTHING above this line is changed: every declaration that existed before keeps its exact
statement, and the three `sorry` leaves of this file are untouched. What follows is proved on
top of the file's own imports only (no new import), as new lemmas in one new namespace.

What it contains, and why it is worth having next to the task246 route already in this file.

1. The page-57 argument for (4.2) driven by the *theta* form of page-56 (4.4) rather than by the
   psi inputs, which is the route the paper itself takes: `lemma6ii_of_theta_upper` needs only
   `theta t <= t + c t/log t`, and it does the partial summation (4.6), the split at e^22, the
   endpoint term, and the two interval estimates, with no numerical knowledge of pi.
2. How much the input may cost. Leaving the input constant symbolic gives
   `lemma6ii_of_theta_upper_const` (paper's split constants, c <= 0.00823), `..._le` (the paper's
   combined `I < 1.006818 x/log^2 x`, c <= 0.00825) and `..._sharp` (this file's sharp integral
   constants, c <= 0.00832, which is tight: c <= 0.0083234). So the target constant 1.0151 is
   within 3e-5 of what the page-57 argument can absorb, and a proof of the theta input at
   c = 0.00822 is needed exactly, not approximately.
3. The asymmetry of page 56: the psi entry gives the upper side at 0.00822 and the 1962 gap
   brings the lower side only to 0.00862, so an absolute-value theta bound at 0.00822 is
   strictly stronger than anything the paper proves for theta (`paper_constant_strictly_weaker`).
4. `0 < x` is necessary in the three original leaves, kernel checked: without it each fails at a
   negative argument, since `Real.log = log |x|` is even and theta vanishes below 1. This is the
   2026-10-31 repair, recorded as a theorem rather than a comment.

Sections are numbered as in `results/RieselVaughan1983-DecompJ206-wip.lean`, which also carries
the two transfer theorems that need `DecompJ246` and are therefore not repeated here.
AI wrote the Lean code. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983

open Real Chebyshev MeasureTheory Set

namespace Task206J

/-! ## 1. `hx0 : 0 < x` is necessary in all three leaves

`Real.log = log |x|` is even, so without `0 < x` the hypothesis `3000 <= log x` is also
satisfied at `x = -exp 3000`, where `theta x = 0` and every right-hand side is negative.
The lab docstrings record this as the 2026-10-31 repair; these are kernel checks of it.
-/

/-- Without `0 < x`, `theta_bound_4_3` fails at `x = -exp 3000`. -/
theorem theta_bound_4_3_drop_pos_false :
    ¬ ∀ x : ℝ, 3000 ≤ Real.log x →
      |θ x - x| < 154 / 1000000 * x / Real.log x := by
  intro h
  have hx : 3000 ≤ Real.log (-(Real.exp 3000)) := by
    rw [Real.log_neg_eq_log, Real.log_exp]
  have hbad := h (-(Real.exp 3000)) hx
  have hθ : θ (-(Real.exp 3000)) = 0 :=
    Chebyshev.theta_eq_zero_of_le_one (by have := Real.exp_pos 3000; linarith)
  have hlhs : |θ (-(Real.exp 3000)) - (-(Real.exp 3000))| = Real.exp 3000 := by
    rw [hθ]; simp
  rw [hlhs] at hbad
  have hlog : Real.log (-(Real.exp 3000)) = 3000 := by
    rw [Real.log_neg_eq_log, Real.log_exp]
  rw [hlog] at hbad
  have hneg : 154 / 1000000 * (-(Real.exp 3000)) / 3000 < 0 := by
    have := Real.exp_pos 3000
    exact div_neg_of_neg_of_pos (by nlinarith) (by norm_num)
  linarith

/-- Without `0 < x`, `theta_bound_4_4` fails at `x = -exp 22`. -/
theorem theta_bound_4_4_drop_pos_false :
    ¬ ∀ x : ℝ, 22 ≤ Real.log x → Real.log x ≤ 5000 →
      |θ x - x| < 822 / 100000 * x / Real.log x := by
  intro h
  have hx1 : 22 ≤ Real.log (-(Real.exp 22)) := by
    rw [Real.log_neg_eq_log, Real.log_exp]
  have hx2 : Real.log (-(Real.exp 22)) ≤ 5000 := by
    rw [Real.log_neg_eq_log, Real.log_exp]; norm_num
  have hbad := h (-(Real.exp 22)) hx1 hx2
  have hθ : θ (-(Real.exp 22)) = 0 :=
    Chebyshev.theta_eq_zero_of_le_one (by have := Real.exp_pos 22; linarith)
  have hlhs : |θ (-(Real.exp 22)) - (-(Real.exp 22))| = Real.exp 22 := by
    rw [hθ]; simp
  rw [hlhs] at hbad
  have hlog : Real.log (-(Real.exp 22)) = 22 := by
    rw [Real.log_neg_eq_log, Real.log_exp]
  rw [hlog] at hbad
  have hneg : 822 / 100000 * (-(Real.exp 22)) / 22 < 0 := by
    have := Real.exp_pos 22
    exact div_neg_of_neg_of_pos (by nlinarith) (by norm_num)
  linarith

/-- Without `0 < x`, `lemma6ii_integral` fails at `x = -exp 300`: the left side is
`pi 0 = 0` and the right side is negative. -/
theorem lemma6ii_drop_pos_false :
    ¬ ∀ x : ℝ, 300 ≤ Real.log x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x +
        10151 / 10000 * x / Real.log x ^ 2 := by
  intro h
  have hx : 300 ≤ Real.log (-(Real.exp 300)) := by
    rw [Real.log_neg_eq_log, Real.log_exp]
  have hbad := h (-(Real.exp 300)) hx
  have hfloor : ⌊(-(Real.exp 300) : ℝ)⌋₊ = 0 := by
    refine Nat.floor_eq_zero.2 ?_
    have := Real.exp_pos 300; linarith
  rw [hfloor] at hbad
  have hzero : (Nat.primeCounting 0 : ℝ) = 0 := by simp
  rw [hzero] at hbad
  have hlog : Real.log (-(Real.exp 300)) = 300 := by
    rw [Real.log_neg_eq_log, Real.log_exp]
  rw [hlog] at hbad
  have hE := Real.exp_pos 300
  have h1 : -(Real.exp 300) / 300 < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by norm_num)
  have h2 : 10151 / 10000 * (-(Real.exp 300)) / 300 ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by norm_num)
  linarith


/-! ## 2. Numeric log and exp facts -/

lemma exp22_gt_one : (1 : ℝ) < Real.exp 22 := by
  have h := Real.add_one_le_exp (22 : ℝ); linarith

lemma two_le_exp22 : (2 : ℝ) ≤ Real.exp 22 := by
  have h := Real.add_one_le_exp (22 : ℝ); linarith

lemma log_ge_22 {t : ℝ} (ht : Real.exp 22 ≤ t) : 22 ≤ Real.log t := by
  rw [← Real.log_exp (22 : ℝ)]
  exact Real.log_le_log (Real.exp_pos 22) ht

/-- `1/2 <= log 2`. -/
lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp (1 / 2) ^ 2 < 4 := by
    rw [h1]; linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

/-- `log 4 <= 2`. -/
lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.add_one_le_exp 1]
  linarith

/-- `exp 278` is huge, which is all that is needed of it. -/
lemma exp278_ge : (7200000000 : ℝ) ≤ Real.exp 278 := by
  have h : Real.exp 278 = Real.exp 1 ^ 278 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h3 : (2 : ℝ) ^ 278 ≤ Real.exp 1 ^ 278 := pow_le_pow_left₀ (by norm_num) h2 278
  have h40 : (7200000000 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
  calc (7200000000 : ℝ) ≤ (2 : ℝ) ^ 40 := h40
    _ ≤ (2 : ℝ) ^ 278 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ ≤ Real.exp 1 ^ 278 := h3
    _ = Real.exp 278 := h.symm

/-! ## 3. Derivatives of `t / log^k t` -/

lemma hd2 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 2)
    (1 / (Real.log t) ^ 2 - 2 / (Real.log t) ^ 3) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 2) (2 * (Real.log t) ^ 1 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 2
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 2 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

lemma hd3 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 3)
    (1 / (Real.log t) ^ 3 - 3 / (Real.log t) ^ 4) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 3) (3 * (Real.log t) ^ 2 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 3
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 3 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

lemma hd4 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 4)
    (1 / (Real.log t) ^ 4 - 4 / (Real.log t) ^ 5) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 4) (4 * (Real.log t) ^ 3 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 4
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 4 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

lemma hd5 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 5)
    (1 / (Real.log t) ^ 5 - 5 / (Real.log t) ^ 6) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 5) (5 * (Real.log t) ^ 4 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 5
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 5 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

/-! ## 4. Integrability of `1 / log^k t` -/

lemma ii_inv_log_pow (k : ℕ) {Y x : ℝ} (hY : 1 < Y) (hYx : Y ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ k) volume Y x := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hYx] at ht
  have htY : 1 < t := lt_of_lt_of_le hY ht.1
  have hne : Real.log t ≠ 0 := (Real.log_pos htY).ne'
  have hcont : ContinuousAt (fun s : ℝ => (Real.log s) ^ k) t :=
    (Real.continuousAt_log (by linarith : t ≠ 0)).pow k
  have hinv : ContinuousAt (fun s : ℝ => ((Real.log s) ^ k)⁻¹) t :=
    ContinuousAt.inv₀ hcont (pow_ne_zero k hne)
  simpa [one_div] using hinv.continuousWithinAt

/-! ## 5. The fundamental-theorem recurrence `A_k = x/log^k x - Y/log^k Y + k A_{k+1}` -/

lemma ftoc_expand (k : ℕ) {Y x : ℝ} (hY : 1 < Y) (hYx : Y ≤ x)
    (hd : ∀ t ∈ uIcc Y x, HasDerivAt (fun s : ℝ => s / (Real.log s) ^ k)
      (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1))) t) :
    ∫ t in Y..x, 1 / (Real.log t) ^ k
      = x / (Real.log x) ^ k - Y / (Real.log Y) ^ k
        + (k : ℝ) * ∫ t in Y..x, 1 / (Real.log t) ^ (k + 1) := by
  have hik := ii_inv_log_pow k hY hYx
  have hik1 := ii_inv_log_pow (k + 1) hY hYx
  have hcont : IntervalIntegrable
      (fun t : ℝ => 1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1)))
      volume Y x := hik.sub (hik1.const_mul (k : ℝ))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont
  rw [intervalIntegral.integral_sub hik (hik1.const_mul (k : ℝ)),
    intervalIntegral.integral_const_mul] at h
  linarith

/-! ## 6. The decaying bound `A_k <= x/(log^k x * (1 - k/22))` -/

lemma A_decay (k : ℕ) (hk22 : (k : ℝ) < 22) {Y x : ℝ}
    (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x)
    (hd : ∀ t ∈ uIcc Y x, HasDerivAt (fun s : ℝ => s / (Real.log s) ^ k)
      (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1))) t) :
    ∫ t in Y..x, 1 / (Real.log t) ^ k ≤ x / (Real.log x) ^ k / (1 - (k : ℝ) / 22) := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have hik := ii_inv_log_pow k hY hYx
  have hik1 := ii_inv_log_pow (k + 1) hY hYx
  have hcont : IntervalIntegrable
      (fun t : ℝ => 1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1)))
      volume Y x := hik.sub (hik1.const_mul (k : ℝ))
  have hftoc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont
  rw [intervalIntegral.integral_sub hik (hik1.const_mul (k : ℝ)),
    intervalIntegral.integral_const_mul] at hftoc
  -- pointwise comparison against `(1 - k/22) * 1/log^k t`
  have hcmp : ∫ t in Y..x, (1 - (k : ℝ) / 22) * (1 / (Real.log t) ^ k)
      ≤ ∫ t in Y..x,
          (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1))) := by
    refine intervalIntegral.integral_mono_on hYx (hik.const_mul _) hcont ?_
    intro t ht
    have htY : Real.exp 22 ≤ t := le_trans hYexp ht.1
    have hL22 : 22 ≤ Real.log t := log_ge_22 htY
    have hL : 0 < Real.log t := by linarith
    have hp : (0 : ℝ) ≤ 1 / (Real.log t) ^ k := by positivity
    have hkL : (k : ℝ) / Real.log t ≤ (k : ℝ) / 22 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hL22
    have key : (1 - (k : ℝ) / 22) ≤ 1 - (k : ℝ) / Real.log t := by linarith
    refine (mul_le_mul_of_nonneg_right key hp).trans_eq ?_
    rw [pow_succ]
    field_simp
  have hpos : 0 < 1 - (k : ℝ) / 22 := by
    have hle : (k : ℝ) / 22 < 1 := by
      rw [div_lt_one (by norm_num)]; exact hk22
    linarith
  have hsplit : ∫ t in Y..x,
        (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1)))
      = (∫ t in Y..x, 1 / (Real.log t) ^ k)
        - (k : ℝ) * ∫ t in Y..x, 1 / (Real.log t) ^ (k + 1) := by
    rw [intervalIntegral.integral_sub hik (hik1.const_mul (k : ℝ)),
      intervalIntegral.integral_const_mul]
  rw [hsplit, hftoc, intervalIntegral.integral_const_mul] at hcmp
  have hdrop : x / (Real.log x) ^ k - Y / (Real.log Y) ^ k ≤ x / (Real.log x) ^ k := by
    have : 0 ≤ Y / (Real.log Y) ^ k := by
      have hYpos : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
      positivity
    linarith
  rw [le_div_iff₀ hpos]
  linarith


/-! ## 7. The three expansions used on page 57 -/

lemma A2_expand {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / (Real.log x) ^ 2 + 2 * ∫ t in Y..x, 1 / (Real.log t) ^ 3 := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := ftoc_expand 2 hY hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd2 ht1
    convert hd using 1
    ring)
  have hpos : 0 ≤ Y / (Real.log Y) ^ 2 := by
    have hL : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
    positivity
  linarith

lemma A3_expand {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 3 + 3 * ∫ t in Y..x, 1 / (Real.log t) ^ 4 := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := ftoc_expand 3 hY hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd3 ht1
    convert hd using 1
    ring)
  have hpos : 0 ≤ Y / (Real.log Y) ^ 3 := by
    have hL : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
    positivity
  linarith

lemma A4_expand {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 4
      ≤ x / (Real.log x) ^ 4 + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5 := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := ftoc_expand 4 hY hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd4 ht1
    convert hd using 1
    ring)
  have hpos : 0 ≤ Y / (Real.log Y) ^ 4 := by
    have hL : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
    positivity
  linarith

/-- `A_2 <= x/log^2 x * (1 + 2/log x + 6/log^2 x + 528/(17 log^3 x))`. -/
lemma A2_bound {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)) := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have e2 := A2_expand hYexp hYx
  have e3 := A3_expand hYexp hYx
  have e4 := A4_expand hYexp hYx
  have e5 : ∫ t in Y..x, 1 / (Real.log t) ^ 5 ≤ 22 * x / (17 * (Real.log x) ^ 5) := by
    have h := A_decay 5 (by norm_num) hYexp hYx (fun t ht => by
      rw [uIcc_of_le hYx] at ht
      have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
      have hd := hd5 ht1
      convert hd using 1
      ring)
    refine h.trans_eq ?_
    field_simp
    ring
  have step1 : ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * ∫ t in Y..x, 1 / (Real.log t) ^ 4) := by linarith [e2, e3]
  have step2 : x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
        + 3 * ∫ t in Y..x, 1 / (Real.log t) ^ 4)
      ≤ x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * (x / Real.log x ^ 4 + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5)) := by
    linarith [e4]
  have step3 : x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
        + 3 * (x / Real.log x ^ 4 + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5))
      ≤ x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * (x / Real.log x ^ 4 + 4 * (22 * x / (17 * Real.log x ^ 5)))) := by
    linarith [e5]
  have s1 : ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4
        + 24 * (22 * x / (17 * Real.log x ^ 5)) := by
    have h4 : x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * (x / Real.log x ^ 4 + 4 * (22 * x / (17 * Real.log x ^ 5))))
        = x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4
          + 24 * (22 * x / (17 * Real.log x ^ 5)) := by ring
    linarith [step1, step2, step3, h4]
  have hrw : x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4
      + 24 * (22 * x / (17 * Real.log x ^ 5))
      = x / Real.log x ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)) := by
    have hL : Real.log x ≠ 0 := by
      have : 0 < Real.log x := by
        have h22 : Real.exp 22 ≤ x := le_trans hYexp hYx
        have := log_ge_22 h22; linarith
      linarith
    field_simp
    ring
  rw [hrw] at s1
  exact s1

/-- `A_3 <= 22 x/(19 log^3 x)`. -/
lemma A3_bound {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 3 ≤ 22 * x / (19 * (Real.log x) ^ 3) := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := A_decay 3 (by norm_num) hYexp hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd3 ht1
    convert hd using 1
    ring)
  refine h.trans_eq ?_
  field_simp
  ring

/-! ## 8. The two endpoint pieces -/

/-- The piece on `[2, exp 22]` costs at most `8 exp 22`, by Chebyshev's `theta t <= log 4 * t`
and `log t >= log 2 >= 1/2` there. -/
lemma head_le :
    ∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2) ≤ 8 * Real.exp 22 := by
  have h2Y : (2 : ℝ) ≤ Real.exp 22 := two_le_exp22
  have hintθ : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume 2 (Real.exp 22) := by
    rw [intervalIntegrable_iff, uIoc_of_le h2Y]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq (Real.exp 22)).mono_set
      Set.Ioc_subset_Icc_self
  have hmono : ∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2)
      ≤ ∫ t in (2 : ℝ)..Real.exp 22, (8 : ℝ) := by
    refine intervalIntegral.integral_mono_on h2Y hintθ (by simp) ?_
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : 0 < t := by linarith
    have hL2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hLhalf : (1 / 2 : ℝ) ≤ Real.log t := le_trans log_two_ge_half hL2
    have hsq : (1 / 4 : ℝ) ≤ (Real.log t) ^ 2 := by nlinarith
    have hθt : θ t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
    nlinarith [hθt, hsq, ht0, log_four_le_two]
  have hconst : ∫ t in (2 : ℝ)..Real.exp 22, (8 : ℝ) = 8 * (Real.exp 22 - 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hconst] at hmono
  nlinarith [hmono, h2Y, Real.exp_pos 22]

/-- The piece on `[exp 22, x]`, using `theta t <= t + 0.00822 t/log t`. -/
lemma tail_le {x : ℝ} (hYexp : Real.exp 22 ≤ x)
    (hint : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + 822 / 100000 * t / Real.log t) :
    ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ (∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 2)
        + 822 / 100000 * ∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 3 := by
  have hY : 1 < Real.exp 22 := exp22_gt_one
  have hpt : (∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2))
      ≤ ∫ t in Real.exp 22..x,
          (1 / (Real.log t) ^ 2 + 822 / 100000 * (1 / (Real.log t) ^ 3)) := by
    refine intervalIntegral.integral_mono_on hYexp hint ?_ ?_
    · -- integrability of the comparison function
      have h2 := ii_inv_log_pow 2 hY hYexp
      have h3 := ii_inv_log_pow 3 hY hYexp
      exact h2.add (h3.const_mul _)
    · intro t ht
      have htY : Real.exp 22 ≤ t := ht.1
      have hL22 : 22 ≤ Real.log t := log_ge_22 htY
      have hL : 0 < Real.log t := by linarith
      have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 22) htY
      have h1 := hθ t htY
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
      have hkey : (1 / Real.log t ^ 2 + 822 / 100000 * (1 / Real.log t ^ 3))
          * (t * Real.log t ^ 2) = t + 822 / 100000 * t / Real.log t := by
        field_simp
      rw [hkey]
      exact h1
  refine hpt.trans_eq ?_
  rw [intervalIntegral.integral_add (ii_inv_log_pow 2 hY hYexp)
    ((ii_inv_log_pow 3 hY hYexp).const_mul _), intervalIntegral.integral_const_mul]

/-! ## 9. The quantitative leftovers -/

/-- `(1 + s/300)^2 <= exp s` for `s >= 0`. -/
lemma one_add_sq_le_exp {s : ℝ} (hs : 0 ≤ s) : (1 + s / 300) ^ 2 ≤ Real.exp s := by
  have hsum : ∑ i ∈ Finset.range 3, s ^ i / (Nat.factorial i : ℝ) ≤ Real.exp s :=
    Real.sum_le_exp_of_nonneg hs 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hsum
  norm_num at hsum
  nlinarith [hs, sq_nonneg s]

/-- `exp 300 / 300^2 <= x / (log x)^2` for `log x >= 300`. -/
lemma exp300_div_sq_le {x L : ℝ} (hx0 : 0 < x) (hLx : L = Real.log x) (hL : 300 ≤ L) :
    Real.exp 300 / 300 ^ 2 ≤ x / L ^ 2 := by
  have hxexp : x = Real.exp L := by rw [hLx]; exact (Real.exp_log hx0).symm
  set s := L - 300 with hs
  have hs0 : 0 ≤ s := by linarith
  have hLs : L = 300 + s := by linarith
  rw [hxexp, hLs, Real.exp_add]
  have hkey := one_add_sq_le_exp hs0
  have hmain : (300 + s) ^ 2 ≤ 300 ^ 2 * Real.exp s := by
    have hsq : (300 + s) ^ 2 = 300 ^ 2 * (1 + s / 300) ^ 2 := by
      field_simp
    rw [hsq]
    nlinarith [hkey, sq_nonneg (1 + s / 300)]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 300 ^ 2), div_mul_eq_mul_div,
    le_div_iff₀ (by nlinarith : (0 : ℝ) < (300 + s) ^ 2)]
  nlinarith [hmain, Real.exp_pos 300]

/-- `exp 278 > 7.2e9`. -/
lemma exp278_gt : (7200000000 : ℝ) < Real.exp 278 := by
  have h : Real.exp 278 = Real.exp 1 ^ 278 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h40 : (7200000000 : ℝ) < (2 : ℝ) ^ 40 := by norm_num
  have h3 : (2 : ℝ) ^ 40 < (2 : ℝ) ^ 278 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have h4 : (2 : ℝ) ^ 278 ≤ Real.exp 1 ^ 278 := pow_le_pow_left₀ (by norm_num) h2 278
  calc (7200000000 : ℝ) < (2 : ℝ) ^ 40 := h40
    _ < (2 : ℝ) ^ 278 := h3
    _ ≤ Real.exp 1 ^ 278 := h4
    _ = Real.exp 278 := h.symm

/-- The `exp 22` endpoint term is negligible against `x / log^2 x`. -/
lemma eight_exp22_lt {x L : ℝ} (hx0 : 0 < x) (hLx : L = Real.log x) (hL : 300 ≤ L) :
    8 * Real.exp 22 < 1 / 10000 * (x / L ^ 2) := by
  have h1 := exp300_div_sq_le hx0 hLx hL
  have h300 : Real.exp 300 = Real.exp 22 * Real.exp 278 := by
    rw [← Real.exp_add]; norm_num
  have hbig : 8 * Real.exp 22 < 1 / 10000 * (Real.exp 300 / 300 ^ 2) := by
    rw [h300]
    have hp : (0 : ℝ) < Real.exp 22 := Real.exp_pos 22
    have h278 := exp278_gt
    rw [show (1 : ℝ) / 10000 * (Real.exp 22 * Real.exp 278 / 300 ^ 2)
        = Real.exp 22 * (Real.exp 278 / (10000 * 300 ^ 2)) by ring]
    have hle : (8 : ℝ) < Real.exp 278 / (10000 * 300 ^ 2) := by
      rw [lt_div_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  calc 8 * Real.exp 22 < 1 / 10000 * (Real.exp 300 / 300 ^ 2) := hbig
    _ ≤ 1 / 10000 * (x / L ^ 2) := by
        apply mul_le_mul_of_nonneg_left h1 (by norm_num)

/-- The constant chain `0.00822 + 1 + 2/L + 6/L^2 + 528/(17 L^3) + 0.00822 * 22/(19 L) <= 1.015`. -/
lemma const_sum_le {L : ℝ} (hL : 300 ≤ L) :
    822 / 100000 + 1 + 2 / L + 6 / L ^ 2 + 528 / (17 * L ^ 3)
      + 822 / 100000 * (22 / (19 * L)) ≤ 203 / 200 := by
  have h1 : 2 / L ≤ 2 / 300 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h2 : 6 / L ^ 2 ≤ 6 / 300 ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have h3 : 528 / (17 * L ^ 3) ≤ 528 / (17 * 300 ^ 3) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have h4 : 22 / (19 * L) ≤ 22 / (19 * 300) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have h5 : 822 / 100000 * (22 / (19 * L)) ≤ 822 / 100000 * (22 / (19 * 300)) := by
    have := mul_le_mul_of_nonneg_left h4 (show (0:ℝ) ≤ 822/100000 by norm_num)
    linarith
  nlinarith [h1, h2, h3, h5]


/-! ## 10. Lemma 6 (ii) from the single analytic input

Riesel-Vaughan page 57 obtains `pi x < x/log x + 1.0151 x/log^2 x` from the *upper* half of
their (4.4) (`psi t <= t + 0.00822 t/log t`) and the partial summation identity (4.6).
Below, that input is stated for `theta` (which follows from the `psi` form since `theta <= psi`),
and everything else is proved. -/

theorem lemma6ii_of_theta_upper
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + 822 / 100000 * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  have hlogpos : 0 < Real.log x := by linarith
  have hYexp : Real.exp 22 ≤ x := by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2x : (2 : ℝ) ≤ x := le_trans two_le_exp22 hYexp
  -- (4.6)
  have hid := Chebyshev.primeCounting_eq_theta_div_log_add_integral h2x
  -- integrability of the theta integrand on the two pieces
  have hint1 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume 2 (Real.exp 22) := by
    rw [intervalIntegrable_iff, uIoc_of_le two_le_exp22]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq (Real.exp 22)).mono_set
      Set.Ioc_subset_Icc_self
  have hint2 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x := by
    rw [intervalIntegrable_iff, uIoc_of_le hYexp]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (fun t ht => ⟨le_trans two_le_exp22 ht.1.le, ht.2⟩)
  have hsplit : ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)
      = (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
        + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  -- the three estimates
  have hhead := head_le
  have htail := tail_le hYexp hint2 hθ
  have hA2 := A2_bound (Y := Real.exp 22) le_rfl hYexp
  have hA3 := A3_bound (Y := Real.exp 22) le_rfl hYexp
  have hsmall := eight_exp22_lt hx0 rfl hL
  have hconst := const_sum_le hL
  -- theta at x
  have hthx : θ x / Real.log x
      ≤ x / Real.log x + 822 / 100000 * (x / Real.log x ^ 2) := by
    have h1 : θ x ≤ x + 822 / 100000 * x / Real.log x := hθ x hYexp
    have hid2 : x / Real.log x + 822 / 100000 * (x / Real.log x ^ 2)
        = (x + 822 / 100000 * x / Real.log x) / Real.log x := by
      field_simp
    rw [hid2]
    exact div_le_div_of_nonneg_right h1 hlogpos.le
  -- the `A_3` term in `B` form
  have hA3' : 822 / 100000 * ∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 3
      ≤ 822 / 100000 * ((x / Real.log x ^ 2) * (22 / (19 * Real.log x))) := by
    have hid3 : 22 * x / (19 * (Real.log x) ^ 3)
        = (x / Real.log x ^ 2) * (22 / (19 * Real.log x)) := by
      field_simp
    rw [← hid3]
    exact mul_le_mul_of_nonneg_left hA3 (by norm_num)
  -- the arithmetic
  have hBpos : 0 < x / Real.log x ^ 2 := div_pos hx0 (pow_pos hlogpos 2)
  have hkey : 822 / 100000 * (x / Real.log x ^ 2) + 8 * Real.exp 22
      + x / Real.log x ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
      + 822 / 100000 * ((x / Real.log x ^ 2) * (22 / (19 * Real.log x)))
      < 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h2 := mul_le_mul_of_nonneg_right hconst hBpos.le
    have hsum : (822 / 100000 + 1 + 2 / Real.log x + 6 / (Real.log x) ^ 2
        + 528 / (17 * (Real.log x) ^ 3) + 822 / 100000 * (22 / (19 * Real.log x)))
          * (x / Real.log x ^ 2)
        = 822 / 100000 * (x / Real.log x ^ 2)
          + x / Real.log x ^ 2 *
              (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
          + 822 / 100000 * ((x / Real.log x ^ 2) * (22 / (19 * Real.log x))) := by
      field_simp
      ring
    rw [hsum] at h2
    nlinarith [h2, hsmall.le, hBpos]
  -- assemble
  have htail' : ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ x / Real.log x ^ 2 *
            (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
        + 822 / 100000 * ((x / Real.log x ^ 2) * (22 / (19 * Real.log x))) := by
    have := htail
    linarith [hA2, hA3']
  rw [hid, hsplit]
  have e1 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      ≤ x / Real.log x + 822 / 100000 * (x / Real.log x ^ 2) + 8 * Real.exp 22 := by
    linarith [hthx, hhead]
  have e2 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ x / Real.log x + 822 / 100000 * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + (x / Real.log x ^ 2 * (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2
              + 528 / (17 * (Real.log x) ^ 3))
            + 822 / 100000 * ((x / Real.log x ^ 2) * (22 / (19 * Real.log x)))) := by
    linarith [e1, htail']
  have e3 : x / Real.log x + (822 / 100000 * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + x / Real.log x ^ 2 * (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2
              + 528 / (17 * (Real.log x) ^ 3))
        + 822 / 100000 * (x / Real.log x ^ 2 * (22 / (19 * Real.log x))))
      < x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h := add_lt_add_left hkey (x / Real.log x)
    linarith [h]
  have hgoal : x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2
      = x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by ring
  rw [hgoal]
  linarith [e2, e3]


/-! ## 11. The dependency map of the three leaves

Each leaf of `DecompJ206.lean`, related to the *named* cited input it needs. Nothing here
closes a leaf; these are hypothesis-level theorems, and they are axiom clean.

* leaf 1 (`theta_bound_4_3`) needs Rosser-Schoenfeld 1975 Theorem 2. The exact transfer is
  `Task202.theta_error_4_3_of_rs1975` in `RieselVaughan1983/DecompJ246.lean` (axiom clean on
  main), so it is not repeated here.
* leaf 2 (`theta_bound_4_4`) is two-sided. Its *upper* half is free from the page-56 `psi`
  entry (4.4), because `theta <= psi`. Its *lower* half is NOT: the paper's own route through
  (4.4) and the 1962 `psi - theta` gap reaches only `0.00862 = 0.00822 + 0.0003961`, which is
  strictly weaker than the leaf's `0.00822` at every admissible `x`.
* leaf 3 (`lemma6ii_integral`) follows from the two leaves above with no further analytic
  input: only their upper halves are used, through `lemma6ii_of_theta_upper`.
-/

/-- The upper half of leaf 2, from the `psi` form of (4.4) and `theta <= psi`. -/
theorem theta_bound_4_4_upper_of_psi (x : ℝ) (_hx0 : 0 < x) (_hx1 : 22 ≤ Real.log x)
    (_hx2 : Real.log x ≤ 5000) (hψ : |ψ x - x| ≤ 822 / 100000 * x / Real.log x) :
    θ x - x ≤ 822 / 100000 * x / Real.log x := by
  have h1 : ψ x - x ≤ 822 / 100000 * x / Real.log x := (abs_le.mp hψ).2
  have h2 : θ x ≤ ψ x := Chebyshev.theta_le_psi x
  linarith

/-- Page 56 equation (4.5): the paper's route to a `theta` *lower* bound runs through the
`psi` error and the 1962 gap, and pays the sum of the two constants, `0.00862`. -/
theorem theta_lower_4_5_of_psi_and_gap (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ Real.log x)
    (hψ : |ψ x - x| ≤ 822 / 100000 * x / Real.log x)
    (hgap : ψ x - θ x ≤ 3961 / 10000000 * x / Real.log x) :
    x - 862 / 100000 * x / Real.log x < θ x := by
  have hpos : 0 < x / Real.log x := div_pos hx0 (by linarith)
  have hle : x - 822 / 100000 * x / Real.log x ≤ ψ x := by
    have := (abs_le.mp hψ).1
    linarith
  have hmargin : (822 / 100000 : ℝ) * x / Real.log x +
      3961 / 10000000 * x / Real.log x < 862 / 100000 * x / Real.log x := by
    calc (822 / 100000 : ℝ) * x / Real.log x + 3961 / 10000000 * x / Real.log x
        = ((822 / 100000 : ℝ) + 3961 / 10000000) * (x / Real.log x) := by ring
      _ < (862 / 100000 : ℝ) * (x / Real.log x) :=
          mul_lt_mul_of_pos_right (by norm_num) hpos
      _ = 862 / 100000 * x / Real.log x := by ring
  linarith

/-- The shortfall, kernel checked: at every `x` with `x > 0` the paper's constant `0.00862` is
*strictly* bigger than the leaf-2 constant `0.00822`. This is why the route above cannot
produce leaf 2's lower half as it stands. -/
theorem paper_constant_strictly_weaker (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ Real.log x) :
    (822 / 100000 : ℝ) * x / Real.log x < 862 / 100000 * x / Real.log x := by
  have hpos : 0 < x / Real.log x := div_pos hx0 (by linarith)
  calc (822 / 100000 : ℝ) * x / Real.log x = (822 / 100000 : ℝ) * (x / Real.log x) := by ring
    _ < (862 / 100000 : ℝ) * (x / Real.log x) :=
        mul_lt_mul_of_pos_right (by norm_num) hpos
    _ = 862 / 100000 * x / Real.log x := by ring

/-- Lemma 6 (ii) from the paper's own (4.4), stated for `psi` exactly as page 56 uses it. -/
theorem lemma6ii_of_psi_upper
    (hψ : ∀ t : ℝ, Real.exp 22 ≤ t → ψ t ≤ t + 822 / 100000 * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 :=
  lemma6ii_of_theta_upper
    (fun t ht => (Chebyshev.theta_le_psi t).trans (hψ t ht)) x hx0 hL

/-- Leaf 3 from the *upper halves* of leaves 1 and 2. These one-sided forms are what the paper
supplies (page 56 quotes (4.3) and (4.4) and uses only `theta <= t + ...`), so this is the
sharpest statement of what `lemma6ii_integral` actually depends on. -/
theorem lemma6ii_of_upper_halves
    (h1 : ∀ t : ℝ, 0 < t → 3000 ≤ Real.log t → θ t - t < 154 / 1000000 * t / Real.log t)
    (h2 : ∀ t : ℝ, 0 < t → 22 ≤ Real.log t → Real.log t ≤ 5000 →
      θ t - t ≤ 822 / 100000 * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  refine lemma6ii_of_theta_upper (fun t ht => ?_) x hx0 hL
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 22) ht
  have hL22 : 22 ≤ Real.log t := log_ge_22 ht
  have hpos : 0 < t / Real.log t := div_pos ht0 (by linarith)
  by_cases h3000 : 3000 ≤ Real.log t
  · have h := h1 t ht0 h3000
    have hc : (154 : ℝ) / 1000000 ≤ 822 / 100000 := by norm_num
    have hmul : (154 : ℝ) / 1000000 * (t / Real.log t)
        ≤ 822 / 100000 * (t / Real.log t) := mul_le_mul_of_nonneg_right hc hpos.le
    have e1 : (154 : ℝ) / 1000000 * t / Real.log t
        = 154 / 1000000 * (t / Real.log t) := by ring
    have e2 : (822 : ℝ) / 100000 * t / Real.log t
        = 822 / 100000 * (t / Real.log t) := by ring
    rw [e1] at h
    rw [e2]
    linarith
  · push Not at h3000
    have h := h2 t ht0 hL22 (by linarith)
    have e2 : (822 : ℝ) / 100000 * t / Real.log t
        = 822 / 100000 * (t / Real.log t) := by ring
    rw [e2]
    rw [e2] at h
    linarith

/-- Leaf 3 needs no analytic input of its own: the two leaves above give it, and only their
*upper* halves are used. -/
theorem lemma6ii_of_leaf1_and_leaf2
    (h1 : ∀ t : ℝ, 0 < t → 3000 ≤ Real.log t →
      |θ t - t| < 154 / 1000000 * t / Real.log t)
    (h2 : ∀ t : ℝ, 0 < t → 22 ≤ Real.log t → Real.log t ≤ 5000 →
      |θ t - t| < 822 / 100000 * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  refine lemma6ii_of_theta_upper (fun t ht => ?_) x hx0 hL
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 22) ht
  have hL22 : 22 ≤ Real.log t := log_ge_22 ht
  have hpos : 0 < t / Real.log t := div_pos ht0 (by linarith)
  by_cases h3000 : 3000 ≤ Real.log t
  · have h := (abs_lt.1 (h1 t ht0 h3000)).2
    have hc : (154 : ℝ) / 1000000 ≤ 822 / 100000 := by norm_num
    have hmul : (154 : ℝ) / 1000000 * (t / Real.log t)
        ≤ 822 / 100000 * (t / Real.log t) := mul_le_mul_of_nonneg_right hc hpos.le
    have e1 : (154 : ℝ) / 1000000 * t / Real.log t
        = 154 / 1000000 * (t / Real.log t) := by ring
    have e2 : (822 : ℝ) / 100000 * t / Real.log t
        = 822 / 100000 * (t / Real.log t) := by ring
    rw [e1] at h
    rw [e2]
    linarith
  · push Not at h3000
    have h := (abs_lt.1 (h2 t ht0 hL22 (by linarith))).2
    have e2 : (822 : ℝ) / 100000 * t / Real.log t
        = 822 / 100000 * (t / Real.log t) := by ring
    rw [e2]
    have e1 : θ t - t = θ t - t := rfl
    linarith


/-! ## 13. The paper's own page-57 constants

Sections 2-10 proved Lemma 6(ii) from the single pointwise input with *synthesised* integral
constants (`1 + 2/L + 6/L^2 + 528/(17L^3)` and `22/(19L)`). Page 57 prints `1.006818` and
`0.003385`; both are proved here as upper bounds, so the chain below is the paper's, and the
leftover slack is the paper's as well (about `2.4 * 10^-5`, see
`lemma6ii_of_theta_upper_const`). -/

lemma exp278_gt_big : (72000000000 : ℝ) < Real.exp 278 := by
  have h : Real.exp 278 = Real.exp 1 ^ 278 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h40 : (72000000000 : ℝ) < (2 : ℝ) ^ 40 := by norm_num
  have h3 : (2 : ℝ) ^ 40 < (2 : ℝ) ^ 278 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have h4 : (2 : ℝ) ^ 278 ≤ Real.exp 1 ^ 278 := pow_le_pow_left₀ (by norm_num) h2 278
  calc (72000000000 : ℝ) < (2 : ℝ) ^ 40 := h40
    _ < (2 : ℝ) ^ 278 := h3
    _ ≤ Real.exp 1 ^ 278 := h4
    _ = Real.exp 278 := h.symm

/-- `A_5 <= 22 x/(17 log^5 x)`, the decaying end of the recurrence. -/
lemma A5_le {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 5 ≤ 22 * x / (17 * (Real.log x) ^ 5) := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := A_decay 5 (by norm_num) hYexp hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd5 ht1
    convert hd using 1
    ring)
  refine h.trans_eq ?_
  field_simp
  ring

/-- `A_3 <= x/log^2 x * (1/log x + 3/log^2 x + 264/(17 log^3 x))`, the sharper form needed to
reach the paper's `0.003385`. -/
lemma A3_sharp {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 * (1 / Real.log x + 3 / (Real.log x) ^ 2
          + 264 / (17 * (Real.log x) ^ 3)) := by
  have e3 := A3_expand hYexp hYx
  have e4 := A4_expand hYexp hYx
  have e5 := A5_le hYexp hYx
  have s1 : ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / Real.log x ^ 3 + 3 * (x / Real.log x ^ 4
          + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5) := by linarith [e3, e4]
  have s2 : ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / Real.log x ^ 3 + 3 * (x / Real.log x ^ 4
          + 4 * (22 * x / (17 * Real.log x ^ 5))) := by linarith [s1, e5]
  have hrw : x / Real.log x ^ 3 + 3 * (x / Real.log x ^ 4
        + 4 * (22 * x / (17 * Real.log x ^ 5)))
      = x / (Real.log x) ^ 2 * (1 / Real.log x + 3 / (Real.log x) ^ 2
          + 264 / (17 * (Real.log x) ^ 3)) := by
    have hL : Real.log x ≠ 0 := by
      have : 0 < Real.log x := by
        have h22 : Real.exp 22 ≤ x := le_trans hYexp hYx
        have := log_ge_22 h22; linarith
      linarith
    field_simp
    ring
  rw [hrw] at s2
  exact s2

/-- Page 57: `A_2 <= 1.006818 x/log^2 x` for `log x >= 300`. -/
lemma A2_le_paper {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x)
    (hL : 300 ≤ Real.log x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 2 ≤ 1006818 / 1000000 * (x / (Real.log x) ^ 2) := by
  have h := A2_bound hYexp hYx
  have hkey : 1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
      ≤ 1006818 / 1000000 := by
    have h1 : 2 / Real.log x ≤ 2 / 300 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have h2 : 6 / (Real.log x) ^ 2 ≤ 6 / 300 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3 : 528 / (17 * (Real.log x) ^ 3) ≤ 528 / (17 * 300 ^ 3) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    nlinarith [h1, h2, h3]
  have hB : 0 ≤ x / (Real.log x) ^ 2 := by
    have hpos : 0 < Real.log x := by linarith
    exact div_nonneg (by linarith [Real.exp_pos 22, hYexp, hYx]) (by positivity)
  calc ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)) := h
    _ ≤ x / (Real.log x) ^ 2 * (1006818 / 1000000) := mul_le_mul_of_nonneg_left hkey hB
    _ = 1006818 / 1000000 * (x / (Real.log x) ^ 2) := by ring

/-- Page 57: `A_3 <= 0.003385 x/log^2 x` for `log x >= 300`. -/
lemma A3_le_paper {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x)
    (hL : 300 ≤ Real.log x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 3 ≤ 3385 / 1000000 * (x / (Real.log x) ^ 2) := by
  have h := A3_sharp hYexp hYx
  have hkey : 1 / Real.log x + 3 / (Real.log x) ^ 2 + 264 / (17 * (Real.log x) ^ 3)
      ≤ 3385 / 1000000 := by
    have h1 : 1 / Real.log x ≤ 1 / 300 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have h2 : 3 / (Real.log x) ^ 2 ≤ 3 / 300 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3 : 264 / (17 * (Real.log x) ^ 3) ≤ 264 / (17 * 300 ^ 3) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    nlinarith [h1, h2, h3]
  have hB : 0 ≤ x / (Real.log x) ^ 2 := by
    have hpos : 0 < Real.log x := by linarith
    exact div_nonneg (by linarith [Real.exp_pos 22, hYexp, hYx]) (by positivity)
  calc ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 * (1 / Real.log x + 3 / (Real.log x) ^ 2
          + 264 / (17 * (Real.log x) ^ 3)) := h
    _ ≤ x / (Real.log x) ^ 2 * (3385 / 1000000) := mul_le_mul_of_nonneg_left hkey hB
    _ = 3385 / 1000000 * (x / (Real.log x) ^ 2) := by ring


/-- The endpoint term at the sharper allowance `10^-5`. -/
lemma eight_exp22_lt_1e5 {x L : ℝ} (hx0 : 0 < x) (hLx : L = Real.log x) (hL : 300 ≤ L) :
    8 * Real.exp 22 < 1 / 100000 * (x / L ^ 2) := by
  have h1 := exp300_div_sq_le hx0 hLx hL
  have h300 : Real.exp 300 = Real.exp 22 * Real.exp 278 := by
    rw [← Real.exp_add]; norm_num
  have hbig : 8 * Real.exp 22 < 1 / 100000 * (Real.exp 300 / 300 ^ 2) := by
    rw [h300]
    have hp : (0 : ℝ) < Real.exp 22 := Real.exp_pos 22
    have h278 := exp278_gt_big
    rw [show (1 : ℝ) / 100000 * (Real.exp 22 * Real.exp 278 / 300 ^ 2)
        = Real.exp 22 * (Real.exp 278 / (100000 * 300 ^ 2)) by ring]
    have hle : (8 : ℝ) < Real.exp 278 / (100000 * 300 ^ 2) := by
      rw [lt_div_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  calc 8 * Real.exp 22 < 1 / 100000 * (Real.exp 300 / 300 ^ 2) := hbig
    _ ≤ 1 / 100000 * (x / L ^ 2) := mul_le_mul_of_nonneg_left h1 (by norm_num)

/-- The whole page-57 budget, as a single constant inequality: with the paper's `1.006818` and
`0.003385` and an endpoint allowance of `10^-5`, an input constant `c` leaves the paper's
`1.0151` intact as long as `c` is at most `0.00823`. -/
lemma const_sum_param {c : ℝ} (_hc0 : 822 / 100000 ≤ c) (hc : c ≤ 823 / 100000) :
    c + 1 / 100000 + 1006818 / 1000000 + c * (3385 / 1000000) < 10151 / 10000 := by
  nlinarith

/-- `tail_le` with the error constant left symbolic. -/
lemma tail_le_const {x c : ℝ} (hYexp : Real.exp 22 ≤ x)
    (hint : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + c * t / Real.log t) :
    ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ (∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 2)
        + c * ∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 3 := by
  have hY : 1 < Real.exp 22 := exp22_gt_one
  have hpt : (∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2))
      ≤ ∫ t in Real.exp 22..x,
          (1 / (Real.log t) ^ 2 + c * (1 / (Real.log t) ^ 3)) := by
    refine intervalIntegral.integral_mono_on hYexp hint ?_ ?_
    · have h2 := ii_inv_log_pow 2 hY hYexp
      have h3 := ii_inv_log_pow 3 hY hYexp
      exact h2.add (h3.const_mul _)
    · intro t ht
      have htY : Real.exp 22 ≤ t := ht.1
      have hL22 : 22 ≤ Real.log t := log_ge_22 htY
      have hL : 0 < Real.log t := by linarith
      have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 22) htY
      have h1 := hθ t htY
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
      have hkey : (1 / Real.log t ^ 2 + c * (1 / Real.log t ^ 3))
          * (t * Real.log t ^ 2) = t + c * t / Real.log t := by
        field_simp
      rw [hkey]
      exact h1
  refine hpt.trans_eq ?_
  rw [intervalIntegral.integral_add (ii_inv_log_pow 2 hY hYexp)
    ((ii_inv_log_pow 3 hY hYexp).const_mul _), intervalIntegral.integral_const_mul]

/-- Lemma 6 (ii) from the pointwise input with the paper's own page-57 constants, and with the
input constant allowed to be anything in `[0.00822, 0.00823]`: the accumulated slack is then
`10151/10000 - 0.00823 - 10^-5 - 1.006818 - 0.00823 * 0.003385 = 1.4 * 10^-5`, so the target
constant `1.0151` is essentially tight against the input. -/
theorem lemma6ii_of_theta_upper_const (c : ℝ) (hc0 : 822 / 100000 ≤ c)
    (hc : c ≤ 823 / 100000)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + c * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  have hlogpos : 0 < Real.log x := by linarith
  have hcpos : (0 : ℝ) ≤ c := by linarith
  have hYexp : Real.exp 22 ≤ x := by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2x : (2 : ℝ) ≤ x := le_trans two_le_exp22 hYexp
  have hid := Chebyshev.primeCounting_eq_theta_div_log_add_integral h2x
  have hint1 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume 2 (Real.exp 22) := by
    rw [intervalIntegrable_iff, uIoc_of_le two_le_exp22]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq (Real.exp 22)).mono_set
      Set.Ioc_subset_Icc_self
  have hint2 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x := by
    rw [intervalIntegrable_iff, uIoc_of_le hYexp]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (fun t ht => ⟨le_trans two_le_exp22 ht.1.le, ht.2⟩)
  have hsplit : ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)
      = (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
        + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hhead := head_le
  have htail0 := tail_le_const hYexp hint2 hθ
  have hA2 := A2_le_paper (Y := Real.exp 22) le_rfl hYexp hL
  have hA3 := A3_le_paper (Y := Real.exp 22) le_rfl hYexp hL
  have hsmall := eight_exp22_lt_1e5 hx0 rfl hL
  have hconst := const_sum_param hc0 hc
  -- theta at x
  have hthx : θ x / Real.log x ≤ x / Real.log x + c * (x / Real.log x ^ 2) := by
    have h1 : θ x ≤ x + c * x / Real.log x := hθ x hYexp
    have hid2 : x / Real.log x + c * (x / Real.log x ^ 2)
        = (x + c * x / Real.log x) / Real.log x := by
      field_simp
    rw [hid2]
    exact div_le_div_of_nonneg_right h1 hlogpos.le
  -- the `A_3` term, scaled by `c`
  have hA3c : c * ∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 3
      ≤ c * (3385 / 1000000 * (x / Real.log x ^ 2)) :=
    mul_le_mul_of_nonneg_left hA3 hcpos
  have htail : ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ 1006818 / 1000000 * (x / Real.log x ^ 2)
        + c * (3385 / 1000000 * (x / Real.log x ^ 2)) := by
    have := htail0
    linarith [hA2, hA3c]
  -- the arithmetic
  have hBpos : 0 < x / Real.log x ^ 2 := div_pos hx0 (pow_pos hlogpos 2)
  have hkey : c * (x / Real.log x ^ 2) + 8 * Real.exp 22
      + 1006818 / 1000000 * (x / Real.log x ^ 2)
      + c * (3385 / 1000000 * (x / Real.log x ^ 2))
      < 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h2 := mul_lt_mul_of_pos_right hconst hBpos
    have hsum : (c + 1 / 100000 + 1006818 / 1000000 + c * (3385 / 1000000))
          * (x / Real.log x ^ 2)
        = c * (x / Real.log x ^ 2) + 1 / 100000 * (x / Real.log x ^ 2)
          + 1006818 / 1000000 * (x / Real.log x ^ 2)
          + c * (3385 / 1000000 * (x / Real.log x ^ 2)) := by
      field_simp
    rw [hsum] at h2
    nlinarith [h2, hsmall.le, hBpos]
  -- assemble
  rw [hid, hsplit]
  have e1 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22 := by
    linarith [hthx, hhead]
  have e2 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + (1006818 / 1000000 * (x / Real.log x ^ 2)
            + c * (3385 / 1000000 * (x / Real.log x ^ 2))) := by
    linarith [e1, htail]
  have e3 : x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + (1006818 / 1000000 * (x / Real.log x ^ 2)
            + c * (3385 / 1000000 * (x / Real.log x ^ 2)))
      < x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h := add_lt_add_left hkey (x / Real.log x)
    linarith [h]
  have hgoal : x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2
      = x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by ring
  rw [hgoal]
  linarith [e2, e3]

/-- The paper's own numbers: Lemma 6 (ii) from `theta t <= t + 0.00822 t/log t`. -/
theorem lemma6ii_of_theta_upper_paper
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + 822 / 100000 * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 :=
  lemma6ii_of_theta_upper_const (822 / 100000) le_rfl (by norm_num) hθ x hx0 hL


/-! ## 14. The paper's combined integral estimate `I < 1.006818 x/log^2 x`

Page 57 does not estimate `A_2` and `A_3` separately: it bounds
`I = int_y^x (1 + delta/log u) du/log^2 u` in one go by `1.006818 x/log^2 x`, with
`delta = 0.00822` already inside the constant. Section 13 estimated `A_2 <= 1.006818 B` and then
charged `delta A_3` on top, which spends about `2.8 * 10^-5` of the budget twice. Doing it the
paper's way leaves `6.2 * 10^-5` of slack instead of `3.4 * 10^-5`, so the input constant may go
up to `0.00825` instead of `0.00823`. -/

/-- Page 57's `I < 1.006818 x/log^2 x`, for every input constant `c <= 0.00822`. -/
lemma I_le_paper {Y x c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 825 / 100000)
    (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) (hL : 300 ≤ Real.log x) :
    (∫ t in Y..x, 1 / (Real.log t) ^ 2)
        + c * ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ 1006818 / 1000000 * (x / (Real.log x) ^ 2) := by
  have h2 := A2_bound hYexp hYx
  have h3 := A3_bound hYexp hYx
  have hB : 0 ≤ x / (Real.log x) ^ 2 :=
    div_nonneg (by linarith [Real.exp_pos 22, hYexp, hYx]) (by positivity)
  have hstep : (∫ t in Y..x, 1 / (Real.log t) ^ 2)
        + c * ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 *
            (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
        + c * (22 * x / (19 * (Real.log x) ^ 3)) := by
    have := mul_le_mul_of_nonneg_left h3 hc0
    linarith [h2, this]
  have he : x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
        + c * (22 * x / (19 * (Real.log x) ^ 3))
      = x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
            + c * (22 / (19 * Real.log x))) := by
    have hL0 : Real.log x ≠ 0 := by
      have : 0 < Real.log x := by linarith
      linarith
    field_simp
  have hk : 1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
        + c * (22 / (19 * Real.log x)) ≤ 1006818 / 1000000 := by
    have h1 : 2 / Real.log x ≤ 2 / 300 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have h2' : 6 / (Real.log x) ^ 2 ≤ 6 / 300 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3' : 528 / (17 * (Real.log x) ^ 3) ≤ 528 / (17 * 300 ^ 3) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h4 : 22 / (19 * Real.log x) ≤ 22 / (19 * 300) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h4' : c * (22 / (19 * Real.log x)) ≤ 825 / 100000 * (22 / (19 * 300)) :=
      mul_le_mul hc h4 (by positivity) (by norm_num)
    nlinarith [h1, h2', h3', h4']
  calc (∫ t in Y..x, 1 / (Real.log t) ^ 2)
        + c * ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 *
            (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
        + c * (22 * x / (19 * (Real.log x) ^ 3)) := hstep
    _ = x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
            + c * (22 / (19 * Real.log x))) := he
    _ ≤ x / (Real.log x) ^ 2 * (1006818 / 1000000) := mul_le_mul_of_nonneg_left hk hB
    _ = 1006818 / 1000000 * (x / (Real.log x) ^ 2) := by ring

/-- The budget with the paper's combined constant: input constants up to `0.00825` still leave
`1.0151` intact. (With the sharp integral constants of section 10 the ceiling is `0.00832`; the
paper's printed constants cost the difference.) -/
lemma budget_combined {c : ℝ} (hc : c ≤ 825 / 100000) :
    c + 1 / 100000 + 1006818 / 1000000 < 10151 / 10000 := by
  nlinarith

/-- Lemma 6 (ii) from `theta t <= t + c t/log t` for any `c <= 0.00825`, using the paper's
combined page-57 estimate. -/
theorem lemma6ii_of_theta_upper_le (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 825 / 100000)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + c * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  have hlogpos : 0 < Real.log x := by linarith
  have hYexp : Real.exp 22 ≤ x := by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2x : (2 : ℝ) ≤ x := le_trans two_le_exp22 hYexp
  have hid := Chebyshev.primeCounting_eq_theta_div_log_add_integral h2x
  have hint1 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume 2 (Real.exp 22) := by
    rw [intervalIntegrable_iff, uIoc_of_le two_le_exp22]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq (Real.exp 22)).mono_set
      Set.Ioc_subset_Icc_self
  have hint2 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x := by
    rw [intervalIntegrable_iff, uIoc_of_le hYexp]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (fun t ht => ⟨le_trans two_le_exp22 ht.1.le, ht.2⟩)
  have hsplit : ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)
      = (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
        + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hhead := head_le
  have htail := tail_le_const hYexp hint2 hθ
  have hI := I_le_paper (Y := Real.exp 22) hc0 hc le_rfl hYexp hL
  have hsmall := eight_exp22_lt_1e5 hx0 rfl hL
  have hbudget := budget_combined hc
  have hthx : θ x / Real.log x ≤ x / Real.log x + c * (x / Real.log x ^ 2) := by
    have h1 : θ x ≤ x + c * x / Real.log x := hθ x hYexp
    have hid2 : x / Real.log x + c * (x / Real.log x ^ 2)
        = (x + c * x / Real.log x) / Real.log x := by
      field_simp
    rw [hid2]
    exact div_le_div_of_nonneg_right h1 hlogpos.le
  have htail' : ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ 1006818 / 1000000 * (x / Real.log x ^ 2) := by
    have := htail
    linarith [hI]
  have hBpos : 0 < x / Real.log x ^ 2 := div_pos hx0 (pow_pos hlogpos 2)
  have hkey : c * (x / Real.log x ^ 2) + 8 * Real.exp 22
      + 1006818 / 1000000 * (x / Real.log x ^ 2)
      < 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h2 := mul_lt_mul_of_pos_right hbudget hBpos
    have hsum : (c + 1 / 100000 + 1006818 / 1000000) * (x / Real.log x ^ 2)
        = c * (x / Real.log x ^ 2) + 1 / 100000 * (x / Real.log x ^ 2)
          + 1006818 / 1000000 * (x / Real.log x ^ 2) := by
      field_simp
    rw [hsum] at h2
    nlinarith [h2, hsmall.le, hBpos]
  rw [hid, hsplit]
  have e1 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22 := by
    linarith [hthx, hhead]
  have e2 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + 1006818 / 1000000 * (x / Real.log x ^ 2) := by
    linarith [e1, htail']
  have e3 : x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + 1006818 / 1000000 * (x / Real.log x ^ 2)
      < x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h := add_lt_add_left hkey (x / Real.log x)
    linarith [h]
  have hgoal : x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2
      = x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by ring
  rw [hgoal]
  linarith [e2, e3]


/-! ## 15. The re-cut of leaf 2, and the sharp-constant chain as a theorem

Two things are left that are provable without a new analytic input.

1. What page 56 actually gives for `theta` is asymmetric: the upper side from the `psi` entry
   (constant `0.00822`) and the lower side from that entry plus the 1962 gap (constant
   `0.00862`). `theta_bound_4_4_faithful` states exactly that pair, which is the honest
   replacement for leaf 2: it is what (R2) plus the gap prove, and its upper half is exactly
   what leaf 3 consumes.
2. Section 10's *sharp* integral constants buy back the slack the paper's printed constants
   spend. `I_le_sharp` is the page-57 combined estimate with those constants, and the budget it
   leaves permits an input constant up to `0.00832`, which
   `lemma6ii_of_theta_upper_sharp` records as a theorem rather than as arithmetic. -/

/-- The asymmetric `theta` statement page 56 supports: upper side `0.00822` (from the `psi`
entry and `theta <= psi`), lower side `0.00862` (that entry plus the 1962 gap). This is the
recommended re-cut of leaf 2. -/
theorem theta_bound_4_4_faithful (x : ℝ) (hx0 : 0 < x) (hx1 : 22 ≤ Real.log x)
    (hx2 : Real.log x ≤ 5000)
    (hψ : |ψ x - x| ≤ 822 / 100000 * x / Real.log x)
    (hgap : ψ x - θ x ≤ 3961 / 10000000 * x / Real.log x) :
    (θ x - x ≤ 822 / 100000 * x / Real.log x) ∧
      (x - 862 / 100000 * x / Real.log x < θ x) :=
  ⟨theta_bound_4_4_upper_of_psi x hx0 hx1 hx2 hψ,
    theta_lower_4_5_of_psi_and_gap x hx0 hx1 hψ hgap⟩

/-- The page-57 combined integral estimate with section 10's sharp constants, for an arbitrary
nonnegative input constant. -/
lemma I_le_sharp {Y x c : ℝ} (hc0 : 0 ≤ c) (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    (∫ t in Y..x, 1 / (Real.log t) ^ 2)
        + c * ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
            + c * (22 / (19 * Real.log x))) := by
  have h2 := A2_bound hYexp hYx
  have h3 := A3_bound hYexp hYx
  have h3c := mul_le_mul_of_nonneg_left h3 hc0
  have hstep : (∫ t in Y..x, 1 / (Real.log t) ^ 2)
        + c * ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 *
            (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
        + c * (22 * x / (19 * (Real.log x) ^ 3)) := by
    linarith [h2, h3c]
  have he : x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
        + c * (22 * x / (19 * (Real.log x) ^ 3))
      = x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
            + c * (22 / (19 * Real.log x))) := by
    have hL0 : Real.log x ≠ 0 := by
      have : 0 < Real.log x := by
        have h22 : Real.exp 22 ≤ x := le_trans hYexp hYx
        have := log_ge_22 h22; linarith
      linarith
    field_simp
  linarith [hstep, he]

/-- The budget at the sharp constants of section 10, evaluated at `log x = 300`: an input
constant up to `0.00832` still fits under `1.0151`. -/
lemma const_budget_sharp {c : ℝ} (hc : c ≤ 832 / 100000) :
    c + 1 / 100000 + (1 + 2 / 300 + 6 / 300 ^ 2 + 528 / (17 * 300 ^ 3))
      + c * (22 / (19 * 300)) < 10151 / 10000 := by
  nlinarith

/-- Lemma 6 (ii) from `theta t <= t + c t/log t` for any `c <= 0.00832`, using the sharp
integral constants. This is the widest input a chain in this file admits: the true second-order
coefficient is `1.006734`, so even a zero input constant cannot beat `1.0151` by much. -/
theorem lemma6ii_of_theta_upper_sharp (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 832 / 100000)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + c * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  have hlogpos : 0 < Real.log x := by linarith
  have hYexp : Real.exp 22 ≤ x := by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2x : (2 : ℝ) ≤ x := le_trans two_le_exp22 hYexp
  have hid := Chebyshev.primeCounting_eq_theta_div_log_add_integral h2x
  have hint1 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume 2 (Real.exp 22) := by
    rw [intervalIntegrable_iff, uIoc_of_le two_le_exp22]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq (Real.exp 22)).mono_set
      Set.Ioc_subset_Icc_self
  have hint2 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x := by
    rw [intervalIntegrable_iff, uIoc_of_le hYexp]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (fun t ht => ⟨le_trans two_le_exp22 ht.1.le, ht.2⟩)
  have hsplit : ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)
      = (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
        + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hhead := head_le
  have htail := tail_le_const hYexp hint2 hθ
  have hI := I_le_sharp (Y := Real.exp 22) hc0 le_rfl hYexp
  have hsmall := eight_exp22_lt_1e5 hx0 rfl hL
  -- the budget at this `log x`
  have hbud : c + 1 / 100000
      + (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
      + c * (22 / (19 * Real.log x)) < 10151 / 10000 := by
    have h1 : 2 / Real.log x ≤ 2 / 300 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have h2' : 6 / (Real.log x) ^ 2 ≤ 6 / 300 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3' : 528 / (17 * (Real.log x) ^ 3) ≤ 528 / (17 * 300 ^ 3) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h4 : 22 / (19 * Real.log x) ≤ 22 / (19 * 300) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h4' : c * (22 / (19 * Real.log x)) ≤ c * (22 / (19 * 300)) :=
      mul_le_mul_of_nonneg_left h4 hc0
    nlinarith [const_budget_sharp hc, h1, h2', h3', h4']
  have hthx : θ x / Real.log x ≤ x / Real.log x + c * (x / Real.log x ^ 2) := by
    have h1 : θ x ≤ x + c * x / Real.log x := hθ x hYexp
    have hid2 : x / Real.log x + c * (x / Real.log x ^ 2)
        = (x + c * x / Real.log x) / Real.log x := by
      field_simp
    rw [hid2]
    exact div_le_div_of_nonneg_right h1 hlogpos.le
  have htail' : ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ x / Real.log x ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
            + c * (22 / (19 * Real.log x))) := by
    have := htail
    linarith [hI]
  have hBpos : 0 < x / Real.log x ^ 2 := div_pos hx0 (pow_pos hlogpos 2)
  have hkey : c * (x / Real.log x ^ 2) + 8 * Real.exp 22
      + x / Real.log x ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
            + c * (22 / (19 * Real.log x)))
      < 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h2 := mul_lt_mul_of_pos_right hbud hBpos
    have hsum : (c + 1 / 100000
          + (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3))
          + c * (22 / (19 * Real.log x))) * (x / Real.log x ^ 2)
        = c * (x / Real.log x ^ 2) + 1 / 100000 * (x / Real.log x ^ 2)
          + x / Real.log x ^ 2 *
              (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
                + c * (22 / (19 * Real.log x))) := by
      field_simp
      ring
    rw [hsum] at h2
    nlinarith [h2, hsmall.le, hBpos]
  rw [hid, hsplit]
  have e1 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22 := by
    linarith [hthx, hhead]
  have e2 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + x / Real.log x ^ 2 *
            (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
              + c * (22 / (19 * Real.log x))) := by
    linarith [e1, htail']
  have e3 : x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + x / Real.log x ^ 2 *
            (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
              + c * (22 / (19 * Real.log x)))
      < x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h := add_lt_add_left hkey (x / Real.log x)
    linarith [h]
  have hgoal : x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2
      = x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by ring
  rw [hgoal]
  linarith [e2, e3]


end Task206J

end LeanLab.RieselVaughan1983
