/-
P0066, page 103, the cutoff y equal to x to the power 9/13 in Lemma 11.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Quadrature

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff

open Vaughan1977Eq55 Vaughan1977Lemma12 Vaughan1977Lemma11Inputs

theorem cutoff_threshold {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    (10 : ℝ) ^ 35 ≤ x ^ (9 / 13 : ℝ) := by
  have hx0 : 0 < x := by linarith
  apply (Real.le_rpow_iff_log_le (by positivity : (0 : ℝ) < 10 ^ 35) hx0).mpr
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 10 ^ 52) hx
  rw [Real.log_pow] at hlog ⊢
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  norm_num at hlog ⊢
  nlinarith

theorem error_ratio_le {x L t c k : ℝ} (hx : 0 < x) (hL : 0 < L) (hc : 0 < c)
    (hk : 0 ≤ k) (ht : t ≤ k * x) (hlog : c * L ≤ Real.log t) :
    t / (38 * Real.log t ^ 2) ≤ k * x / (38 * (c * L) ^ 2) := by
  have hcl : 0 < c * L := mul_pos hc hL
  have hlt : 0 < Real.log t := lt_of_lt_of_le hcl hlog
  calc
    t / (38 * Real.log t ^ 2) ≤ k * x / (38 * Real.log t ^ 2) :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (mul_nonneg hk hx.le) (by positivity)
      gcongr

/-- A uniform endpoint bound with room below the printed 1/12 budget. -/
theorem endpoint_error_le {x p : ℝ} (hx : 10 ^ 52 ≤ x) (hp0 : 0 ≤ p)
    (hp : p ≤ x - x ^ (9 / 13 : ℝ)) :
    (2 * x - p) / (38 * Real.log (2 * x - p) ^ 2) +
      (x - p) / (38 * Real.log (x - p) ^ 2) ≤ 0.08 * x / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < x ^ (9 / 13 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have ha0 : 0 < x - p := by linarith
  have hb0 : 0 < 2 * x - p := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  set L := Real.log x with hLdef
  have hL : 0 < L := by linarith
  have hbL : L ≤ Real.log (2 * x - p) := Real.log_le_log hx0 (by linarith)
  by_cases hpHalf : p ≤ x / 2
  · have haL : 0.99 * L ≤ Real.log (x - p) := by
      have he := Real.log_le_log (by positivity : 0 < x / 2) (show x / 2 ≤ x - p by linarith)
      rw [Real.log_div hx0.ne' (by norm_num)] at he
      have hl2 := Real.log_two_lt_d9
      linarith
    have hb := error_ratio_le hx0 hL (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 2) (show 2 * x - p ≤ 2 * x by linarith) (by simpa using hbL)
    have ha := error_ratio_le hx0 hL (by norm_num : (0 : ℝ) < 0.99)
      (by norm_num : (0 : ℝ) ≤ 1) (show x - p ≤ 1 * x by linarith) haL
    have he : 2 * x / (38 * (1 * L) ^ 2) + 1 * x / (38 * (0.99 * L) ^ 2) =
        (2 / 38 + 1 / (38 * 0.99 ^ 2)) * (x / L ^ 2) := by field_simp
    have hc : (2 / 38 + 1 / (38 * 0.99 ^ 2) : ℝ) ≤ 0.08 := by norm_num
    have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ x / L ^ 2 by positivity)
    rw [← he] at hm
    convert (add_le_add hb ha).trans hm using 1 <;> ring
  · have haL : (9 / 13 : ℝ) * L ≤ Real.log (x - p) := by
      have he := Real.log_le_log hy0 (show x ^ (9 / 13 : ℝ) ≤ x - p by linarith)
      rw [Real.log_rpow hx0] at he
      exact he
    have hb := error_ratio_le hx0 hL (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1.5) (show 2 * x - p ≤ 1.5 * x by linarith) (by simpa using hbL)
    have ha := error_ratio_le hx0 hL (by norm_num : (0 : ℝ) < 9 / 13)
      (by norm_num : (0 : ℝ) ≤ 0.5) (show x - p ≤ 0.5 * x by linarith) haL
    have he : 1.5 * x / (38 * (1 * L) ^ 2) + 0.5 * x / (38 * (9 / 13 * L) ^ 2) =
        (1.5 / 38 + 0.5 / (38 * (9 / 13) ^ 2)) * (x / L ^ 2) := by field_simp
    have hc : (1.5 / 38 + 0.5 / (38 * (9 / 13) ^ 2) : ℝ) ≤ 0.08 := by norm_num
    have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ x / L ^ 2 by positivity)
    rw [← he] at hm
    convert (add_le_add hb ha).trans hm using 1 <;> ring

def good (x : ℝ) : Finset ℕ := (P1 x).filter (fun p => (p : ℝ) ≤ x - x ^ (9 / 13 : ℝ))

def goodError (x : ℝ) : ℝ := ∑ p ∈ good x, Real.log p *
  ((piR (2 * x - p) - piR (x - p)) - (li2 (2 * x - p) - li2 (x - p)))

theorem good_error_le (h216 : Eq216) {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    |goodError x| ≤ 0.08 * x / Real.log x ^ 2 * Chebyshev.theta x := by
  have hx0 : 0 < x := by linarith
  have hg : ∀ p ∈ good x, (10 : ℝ) ^ 35 ≤ x - p := by
    intro p hp
    have hpg := (Finset.mem_filter.mp hp).2
    linarith [cutoff_threshold hx]
  have he := weighted_interval_error h216 (good x) (fun p => Real.log p)
    (fun p => x - p) (fun p => 2 * x - p) (fun p _ => Real.log_natCast_nonneg p)
    hg (fun p hp => by linarith [hg p hp])
  have hsum : ∑ p ∈ good x, Real.log p ≤ Chebyshev.theta x :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => Real.log_natCast_nonneg p)).trans (Vaughan1977Eq57.sum_logs_le_theta x)
  calc
    |goodError x| ≤ ∑ p ∈ good x, Real.log p *
      ((2 * x - p) / (38 * Real.log (2 * x - p) ^ 2) +
        (x - p) / (38 * Real.log (x - p) ^ 2)) := he
    _ ≤ ∑ p ∈ good x, Real.log p * (0.08 * x / Real.log x ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (endpoint_error_le hx (Nat.cast_nonneg p) (Finset.mem_filter.mp hp).2) (Real.log_natCast_nonneg p)
    _ = (∑ p ∈ good x, Real.log p) * (0.08 * x / Real.log x ^ 2) := by rw [Finset.sum_mul]
    _ ≤ Chebyshev.theta x * (0.08 * x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

theorem theta_relative (h215 : Eq215) {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    Chebyshev.theta x ≤ 1.001 * x := by
  have hx0 : 0 < x := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  have hL : 0 < Real.log x := by linarith
  have ht := thetaUpper_of_eq215 h215 x (by linarith)
  have hf : x / (40 * Real.log x) ≤ 0.001 * x := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hx0.le (show 0 ≤ Real.log x - 25 by linarith)]
  linarith

/-- The long interval endpoint errors fit strictly inside 0.081 of the normalized budget. -/
theorem good_error_lt (h216 : Eq216) (h215 : Eq215) {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    |goodError x| < 0.081 * x ^ 2 / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := good_error_le h216 hx
  have h2 := mul_le_mul_of_nonneg_left (theta_relative h215 hx)
    (show 0 ≤ 0.08 * x / Real.log x ^ 2 by positivity)
  have he : 0.08 * x / Real.log x ^ 2 * (1.001 * x) = 0.08008 * x ^ 2 / Real.log x ^ 2 := by ring
  rw [he] at h2
  have hB : 0 < x ^ 2 / Real.log x ^ 2 := by positivity
  have hs : 0.08008 * x ^ 2 / Real.log x ^ 2 < 0.081 * x ^ 2 / Real.log x ^ 2 := by
    have hm := mul_lt_mul_of_pos_right (show (0.08008 : ℝ) < 0.081 by norm_num) hB
    convert hm using 1 <;> ring
  exact lt_of_le_of_lt (h1.trans h2) hs

end LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff.cutoff_threshold
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff.error_ratio_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff.endpoint_error_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff.good_error_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff.theta_relative
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Cutoff.good_error_lt
