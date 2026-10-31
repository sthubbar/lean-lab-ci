/-
P0066, page 103, the first integral approximation in Lemma 11.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff

open Finset Real Nat MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals

open Vaughan1977Eq55 Vaughan1977Lemma12 Vaughan1977Lemma11Inputs
  Vaughan1977Lemma11Cutoff Vaughan1977Quadrature

def bad (x : ℝ) : Finset ℕ := (P1 x).filter (fun p => x - x ^ (9 / 13 : ℝ) < (p : ℝ))

def badError (x : ℝ) : ℝ := ∑ p ∈ bad x, Real.log p *
  ((piR (2 * x - p) - piR (x - p)) - (li2 (2 * x - p) - li2 (x - p)))

theorem li2_sub {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    li2 b - li2 a = ∫ u in a..b, 1 / Real.log u := by
  have h1 : IntervalIntegrable (fun u : ℝ => 1 / Real.log u) volume 2 a := by
    simpa using log_integrable 0 1 (by norm_num : (1 : ℝ) < 2) ha
  have h2 : IntervalIntegrable (fun u : ℝ => 1 / Real.log u) volume a b := by
    simpa using log_integrable 0 1 (by linarith : 1 < a) hab
  have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
  unfold li2
  linarith

theorem short_interval_error {x : ℝ} (hx : 6 ≤ x) {p : ℕ} (hp : p ∈ P1 x) :
    |(piR (2 * x - p) - piR (x - p)) - (li2 (2 * x - p) - li2 (x - p))| ≤ 4 * x := by
  have hx0 : 0 < x := by linarith
  have hpI := (Finset.mem_filter.mp hp).1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpx : (p : ℝ) ≤ x - 3 := by
    have h := Nat.floor_le (by linarith : 0 ≤ x - 3)
    have hc : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hpI).2
    linarith
  have ha : 3 ≤ x - p := by linarith
  have hab : x - p ≤ 2 * x - p := by linarith
  have hpi0 : 0 ≤ piR (2 * x - p) - piR (x - p) := by
    rw [← interval_card hab]
    exact Nat.cast_nonneg _
  have hpi : piR (2 * x - p) - piR (x - p) ≤ 3 * x := by
    have hc : Nat.primeCounting ⌊2 * x - p⌋₊ ≤ ⌊2 * x - p⌋₊ + 1 := Nat.count_le _
    have hcr : piR (2 * x - p) ≤ (⌊2 * x - p⌋₊ : ℝ) + 1 := by unfold piR; exact_mod_cast hc
    have hf := Nat.floor_le (by linarith : 0 ≤ 2 * x - p)
    have hpa : 0 ≤ piR (x - p) := Nat.cast_nonneg _
    linarith
  rw [li2_sub (by linarith) hab]
  have hi : IntervalIntegrable (fun u : ℝ => 1 / Real.log u) volume (x - p) (2 * x - p) := by
    simpa using log_integrable 0 1 (by linarith : 1 < x - p) hab
  have hli0 : 0 ≤ ∫ u in (x - p)..(2 * x - p), 1 / Real.log u := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    have hu1 : 1 < u := by linarith [hu.1]
    positivity [Real.log_pos hu1]
  have hli : (∫ u in (x - p)..(2 * x - p), 1 / Real.log u) ≤ x := by
    have hm := intervalIntegral.integral_mono_on hab hi
      (intervalIntegrable_const : IntervalIntegrable (fun _u : ℝ => (1 : ℝ)) volume (x - p) (2 * x - p))
      (fun u hu => by
        have hlog : 1 ≤ Real.log u := log_three_gt_one.le.trans
          (Real.log_le_log (by norm_num) (show (3 : ℝ) ≤ u by linarith [hu.1]))
        exact div_le_self (by norm_num : (0 : ℝ) ≤ 1) hlog)
    convert hm using 1 <;> simp <;> ring
  apply abs_le.mpr
  constructor <;> linarith

theorem bad_card_le {x : ℝ} (hx : 6 ≤ x) : (bad x).card ≤ (⌊x⌋₊ - ⌊x - x ^ (9 / 13 : ℝ)⌋₊) := by
  have hsub : bad x ⊆ Ioc ⌊x - x ^ (9 / 13 : ℝ)⌋₊ ⌊x⌋₊ := by
    intro p hp
    obtain ⟨hpP, hpbad⟩ := Finset.mem_filter.mp hp
    have hyx : x ^ (9 / 13 : ℝ) ≤ x := by
      calc
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) (by norm_num)
        _ = x := Real.rpow_one x
    have hpI := (Finset.mem_filter.mp hpP).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith)).mpr hpbad,
      (Finset.mem_Icc.mp hpI).2.trans (Nat.floor_le_floor (by linarith : x - 3 ≤ x))⟩
  simpa using Finset.card_le_card hsub

theorem bad_card_real {x : ℝ} (hx : 6 ≤ x) : ((bad x).card : ℝ) ≤ x ^ (9 / 13 : ℝ) + 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ x ^ (9 / 13 : ℝ) := Real.rpow_nonneg hx0 _
  have hfloor : ⌊x - x ^ (9 / 13 : ℝ)⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
  have hc : ((bad x).card : ℝ) ≤ ((⌊x⌋₊ - ⌊x - x ^ (9 / 13 : ℝ)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast bad_card_le hx
  rw [Nat.cast_sub hfloor] at hc
  have hupper := Nat.floor_le hx0
  have hlower := Nat.lt_floor_add_one (x - x ^ (9 / 13 : ℝ))
  linarith

theorem bad_log_sum {x : ℝ} (hx : 6 ≤ x) :
    ∑ p ∈ bad x, Real.log p ≤ (x ^ (9 / 13 : ℝ) + 1) * Real.log x := by
  have hL : 0 ≤ Real.log x := (Real.log_pos (by linarith : 1 < x)).le
  calc
    ∑ p ∈ bad x, Real.log p ≤ ∑ _p ∈ bad x, Real.log x := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hpI := Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hpx : (p : ℝ) ≤ x := by
        have hfloor := Nat.floor_le (by linarith : 0 ≤ x - 3)
        have hc : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hpI.2
        linarith
      exact Real.log_le_log hp0 hpx
    _ = ((bad x).card : ℝ) * Real.log x := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (bad_card_real hx) hL

theorem bad_error_le {x : ℝ} (hx : 6 ≤ x) :
    |badError x| ≤ 4 * x * ((x ^ (9 / 13 : ℝ) + 1) * Real.log x) := by
  have hsum := Finset.abs_sum_le_sum_abs (s := bad x)
    (f := fun p : ℕ => Real.log p *
      ((piR (2 * x - p) - piR (x - p)) - (li2 (2 * x - p) - li2 (x - p))))
  calc
    |badError x| ≤ ∑ p ∈ bad x, |Real.log p *
      ((piR (2 * x - p) - piR (x - p)) - (li2 (2 * x - p) - li2 (x - p)))| := hsum
    _ ≤ ∑ p ∈ bad x, Real.log p * (4 * x) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
      exact mul_le_mul_of_nonneg_left (short_interval_error hx (Finset.mem_filter.mp hp).1)
        (Real.log_natCast_nonneg p)
    _ = 4 * x * ∑ p ∈ bad x, Real.log p := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (bad_log_sum hx) (by linarith)

theorem log_cube_le_rpow {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    8000 * Real.log x ^ 3 ≤ x ^ (4 / 13 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  set L := Real.log x with hLdef
  have hL : 0 < L := by linarith
  have hc : 8000 * (13 : ℝ) ^ 14 * 87178291200 ≤ 4 ^ 14 * L ^ 11 := by
    calc
      _ ≤ (4 : ℝ) ^ 14 * 119 ^ 11 := by norm_num
      _ ≤ 4 ^ 14 * L ^ 11 := by gcongr
  have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hL.le 3)
  have hp : 8000 * L ^ 3 ≤ (4 * L / 13) ^ 14 / (Nat.factorial 14 : ℝ) := by
    norm_num [Nat.factorial]
    nlinarith
  have he := Real.pow_div_factorial_le_exp (4 * L / 13) (by positivity) 14
  have hpow : x ^ (4 / 13 : ℝ) = Real.exp (4 * L / 13) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    rw [hLdef]
    ring
  rw [hpow]
  exact hp.trans he

theorem bad_error_small {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    |badError x| ≤ 0.001 * (x ^ 2 / Real.log x ^ 2) := by
  have hx6 : 6 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  set y := x ^ (9 / 13 : ℝ) with hydef
  have hy1 : 1 ≤ y := (by linarith [cutoff_threshold hx] : (1 : ℝ) ≤ x ^ (9 / 13 : ℝ))
  have hy0 : 0 < y := by linarith
  have he : y * x ^ (4 / 13 : ℝ) = x := by
    rw [hydef, ← Real.rpow_add hx0]
    norm_num
  have hp := mul_le_mul_of_nonneg_left (log_cube_le_rpow hx) (show 0 ≤ x * y by positivity)
  have he2 : (x * y) * x ^ (4 / 13 : ℝ) = x ^ 2 := by rw [mul_assoc, he]; ring
  rw [he2] at hp
  have hbound : 8 * x * y * Real.log x ≤ 0.001 * (x ^ 2 / Real.log x ^ 2) := by
    rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hL)]
    nlinarith
  have hsmall : 4 * x * ((y + 1) * Real.log x) ≤ 8 * x * y * Real.log x := by
    have h := mul_le_mul_of_nonneg_left (show y + 1 ≤ 2 * y by linarith)
      (show 0 ≤ 4 * x * Real.log x by positivity)
    convert h using 1 <;> ring
  exact (bad_error_le hx6).trans (hsmall.trans hbound)

/-- The weighted logarithmic integral before the summation order is reversed on page 103. -/
def primeIntegral (x : ℝ) : ℝ := ∑ p ∈ P1 x,
  Real.log p * (li2 (2 * x - p) - li2 (x - p))

theorem error_split {x : ℝ} (hx : 6 ≤ x) :
    Psi x - primeIntegral x = goodError x + badError x := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (P1 x)
    (fun p => (p : ℝ) ≤ x - x ^ (9 / 13 : ℝ))
    (fun p => Real.log p * ((piR (2 * x - p) - piR (x - p)) - (li2 (2 * x - p) - li2 (x - p))))
  have he : Psi x - primeIntegral x = ∑ p ∈ P1 x,
      Real.log p * ((piR (2 * x - p) - piR (x - p)) - (li2 (2 * x - p) - li2 (x - p))) := by
    rw [psi_eq_pi x hx]
    unfold primeIntegral
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he]
  simpa [goodError, badError, good, bad, not_le] using hsplit.symm

/-- The first page 103 error budget, before the theta integral comparison. -/
theorem prime_interval_approximation (h215 : Eq215) (h216 : Eq216) {x : ℝ}
    (hx : 10 ^ 52 ≤ x) :
    |Psi x - primeIntegral x| < x ^ 2 / (12 * Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  set B := x ^ 2 / Real.log x ^ 2 with hBdef
  have hB : 0 < B := by positivity
  have hg : |goodError x| < 0.081 * B := by
    convert good_error_lt h216 h215 hx using 1 <;> rw [hBdef] <;> ring
  have hb : |badError x| ≤ 0.001 * B := bad_error_small hx
  have he : x ^ 2 / (12 * Real.log x ^ 2) = (1 / 12 : ℝ) * B := by rw [hBdef]; ring
  rw [error_split (by linarith : 6 ≤ x), he]
  have ht := abs_add_le (goodError x) (badError x)
  nlinarith

/-- The local integrals in the first page 103 display, with the first prime 2 excluded. -/
theorem primeIntegral_eq_local_integrals {x : ℝ} (hx : 6 ≤ x) :
    primeIntegral x = ∑ p ∈ P1 x, Real.log p *
      ∫ u in (x - p)..(2 * x - p), 1 / Real.log u := by
  unfold primeIntegral
  apply Finset.sum_congr rfl
  intro p hp
  have hpI := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  have hpx : (p : ℝ) ≤ x - 3 := by
    have hf := Nat.floor_le (by linarith : 0 ≤ x - 3)
    have hc : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast hpI.2
    linarith
  rw [li2_sub (by linarith) (by linarith)]

/-- The first integral error estimate in the paper, before the theta comparison. -/
theorem prime_interval_approximation_integral (h215 : Eq215) (h216 : Eq216) {x : ℝ}
    (hx : 10 ^ 52 ≤ x) :
    |Psi x - ∑ p ∈ P1 x, Real.log p *
      ∫ u in (x - p)..(2 * x - p), 1 / Real.log u| < x ^ 2 / (12 * Real.log x ^ 2) := by
  rw [← primeIntegral_eq_local_integrals (by linarith : 6 ≤ x)]
  exact prime_interval_approximation h215 h216 hx

/-- The logarithmic integral is differentiable above its normalization point. -/
theorem hasDerivAt_li2 {u : ℝ} (hu : 2 < u) : HasDerivAt li2 (1 / Real.log u) u := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 u := by
    simpa using log_integrable 0 1 (by norm_num : (1 : ℝ) < 2) hu.le
  have hm : Measurable (fun t : ℝ => 1 / Real.log t) := measurable_const.div Real.measurable_log
  have hc : ContinuousAt (fun t : ℝ => 1 / Real.log t) u :=
    continuousAt_const.div (Real.continuousAt_log (by linarith))
      (Real.log_pos (by linarith : 1 < u)).ne'
  exact intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurable.stronglyMeasurableAtFilter hc

/-- The smooth kernel needed for an Abel summation proof of the remaining theta comparison. -/
theorem hasDerivAt_kernel {x t : ℝ} (hx : 6 ≤ x) (ht : t ≤ x - 3) :
    HasDerivAt (fun s : ℝ => li2 (2 * x - s) - li2 (x - s))
      (1 / Real.log (x - t) - 1 / Real.log (2 * x - t)) t := by
  have h1 := (hasDerivAt_li2 (by linarith : 2 < 2 * x - t)).comp t
    ((hasDerivAt_const t (2 * x)).sub (hasDerivAt_id t))
  have h2 := (hasDerivAt_li2 (by linarith : 2 < x - t)).comp t
    ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  convert h1.sub h2 using 1
  · rfl
  · ring

example : li2 6 - li2 3 = ∫ u in (3 : ℝ)..6, 1 / Real.log u :=
  li2_sub (by norm_num) (by norm_num)

end LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.li2_sub
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.short_interval_error
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.bad_card_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.bad_card_real
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.bad_log_sum
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.bad_error_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.log_cube_le_rpow
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.bad_error_small
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.error_split
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.prime_interval_approximation
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.primeIntegral_eq_local_integrals
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.prime_interval_approximation_integral
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.hasDerivAt_li2
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.hasDerivAt_kernel
