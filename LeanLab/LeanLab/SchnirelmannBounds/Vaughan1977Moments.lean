/-
P0066, pages 95 and 105, finite mass and moment inputs for equation 5.10.
Source: https://doi.org/10.1515/crll.1977.290.93
These inputs remain conditional until derived from the Euler products 2.6 and 2.7.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977DivisorTail
import LeanLab.SchnirelmannBounds.Vaughan1977LogWeights

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Moments

open Vaughan1977Eq55 Vaughan1977Eq56 Vaughan1977Eq57 Vaughan1977Lemma3
  Vaughan1977Lemma12 Vaughan1977LogWeights Vaughan1977DivisorTail

/-- The divisor weight f over phi. -/
def a (d : ℕ) : ℝ := f d / (d.totient : ℝ)

/-- Finite mass bound supplied by 2.6. This Prop is an unproved analytic input. -/
def MassBound (C : ℝ) : Prop := ∀ N : ℕ, ∑ d ∈ Icc 1 N, a d ≤ C

/-- Finite 3/8 moment bound supplied by 2.7 and 2.12. This Prop is an unproved input. -/
def MomentBound : Prop := ∀ N : ℕ, ∑ d ∈ Icc 1 N, (d : ℝ) ^ (3 / 8 : ℝ) * a d ≤ 14.46

/-- The theta upper bound used in 2.15. Only its upper half is needed here. -/
def ThetaUpper : Prop := ∀ x : ℝ, 678407 ≤ x →
  Chebyshev.theta x ≤ x + x / (40 * Real.log x)

theorem a_nonneg (d : ℕ) : 0 ≤ a d := div_nonneg (f_nonneg d) (Nat.cast_nonneg _)

theorem a_one : a 1 = 1 := by simp [a, f_one]

/-- Remove the unit term from a nonnegative finite mass bound. -/
theorem sum_le_sub_one {b : ℕ → ℝ} {N : ℕ} {C : ℝ} (hN : 1 ≤ N)
    (h0 : ∀ d, 0 ≤ b d) (h1 : b 1 = 1) (hC : ∑ d ∈ Icc 1 N, b d ≤ C)
    {s : Finset ℕ} (hs : s ⊆ Icc 2 N) : ∑ d ∈ s, b d ≤ C - 1 := by
  have hnot : 1 ∉ s := by intro h; have := Finset.mem_Icc.mp (hs h); omega
  have hsub : insert 1 s ⊆ Icc 1 N := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
    · have h := Finset.mem_Icc.mp (hs hd)
      exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hsum : ∑ d ∈ insert 1 s, b d ≤ ∑ d ∈ Icc 1 N, b d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => h0 d)
  rw [Finset.sum_insert hnot, h1] at hsum
  linarith

/-- The logarithmic form of the split at y equal to x to the power 1/3. -/
def small (x : ℝ) : Finset ℕ := (Icc 2 ⌊x⌋₊).filter (fun d => 3 * Real.log d ≤ Real.log x)

def large (x : ℝ) : Finset ℕ := (Icc 2 ⌊x⌋₊).filter (fun d => Real.log x < 3 * Real.log d)

theorem split_sum (x : ℝ) (b : ℕ → ℝ) :
    ∑ d ∈ Icc 2 ⌊x⌋₊, b d = ∑ d ∈ small x, b d + ∑ d ∈ large x, b d := by
  simpa [small, large, not_le] using
    (Finset.sum_filter_add_sum_filter_not (Icc 2 ⌊x⌋₊) (fun d => 3 * Real.log d ≤ Real.log x) b).symm

theorem small_iff_rpow {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 0 < d) :
    3 * Real.log d ≤ Real.log x ↔ (d : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← Real.log_le_log_iff hd0 (Real.rpow_pos_of_pos hx _), Real.log_rpow hx]
  constructor <;> intro h <;> linarith

/-- The mass and moment inputs imply a stronger coefficient than the printed 5.9. -/
theorem small_log_sum {C x : ℝ} (hx : 6 ≤ x) (hC : MassBound C) (hM : MomentBound) :
    ∑ d ∈ small x, a d / Real.log (x / d) ≤
      (C - 1) / Real.log x + 20.19 / Real.log x ^ 2 := by
  have hN : 1 ≤ ⌊x⌋₊ := by apply Nat.le_floor; norm_num; linarith
  have hs : small x ⊆ Icc 2 ⌊x⌋₊ := Finset.filter_subset _ _
  have hmass := sum_le_sub_one hN a_nonneg a_one (hC ⌊x⌋₊) hs
  have hm1 : ((1 : ℕ) : ℝ) ^ (3 / 8 : ℝ) * a 1 = 1 := by norm_num [a_one]
  have hmoment := sum_le_sub_one hN (fun d => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (a_nonneg d))
    hm1 (hM ⌊x⌋₊) hs
  have h := weighted_sum_bound (by linarith : 1 < x)
    (fun d hd => by have := (Finset.mem_Icc.mp (hs hd)).1; omega)
    (fun d hd => (Finset.mem_filter.mp hd).2) (fun d _ => a_nonneg d) hmass hmoment
  norm_num at h
  convert h using 1 <;> norm_num [small]

theorem large_power {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : d ∈ large x) :
    x ^ (1 / 8 : ℝ) ≤ (d : ℝ) ^ (3 / 8 : ℝ) := by
  have hd2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hd0, Real.exp_le_exp]
  have h := (Finset.mem_filter.mp hd).2
  linarith

theorem large_weight {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : d ∈ large x) :
    f d / d ≤ ((d : ℝ) ^ (3 / 8 : ℝ) * a d) / x ^ (1 / 8 : ℝ) := by
  have hd2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hdpos : 0 < d := by omega
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hdpos
  have hφd : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  calc
    f d / d ≤ a d := div_le_div_of_nonneg_left (f_nonneg d) hφ hφd
    _ ≤ _ := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hx _)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (large_power hx hd) (a_nonneg d)

/-- The large divisor range is controlled by the finite 3/8 moment. -/
theorem large_sum_bound {x : ℝ} (hx : 6 ≤ x) (hM : MomentBound) :
    ∑ d ∈ large x, f d * D x d ≤
      x * Chebyshev.theta x * (14.46 / x ^ (1 / 8 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hcoef : 0 ≤ x * Chebyshev.theta x := mul_nonneg hx0.le (Chebyshev.theta_nonneg x)
  have hs : large x ⊆ Icc 1 ⌊x⌋₊ := by
    intro d hd
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hm : ∑ d ∈ large x, (d : ℝ) ^ (3 / 8 : ℝ) * a d ≤ 14.46 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hs (fun d _ _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (a_nonneg d))).trans (hM ⌊x⌋₊)
  calc
    ∑ d ∈ large x, f d * D x d ≤
        ∑ d ∈ large x, x * Chebyshev.theta x *
          (((d : ℝ) ^ (3 / 8 : ℝ) * a d) / x ^ (1 / 8 : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      exact (f_mul_D_le hx (by omega)).trans
        (mul_le_mul_of_nonneg_left (large_weight hx0 hd) hcoef)
    _ = x * Chebyshev.theta x *
        ((∑ d ∈ large x, (d : ℝ) ^ (3 / 8 : ℝ) * a d) / x ^ (1 / 8 : ℝ)) := by
      rw [Finset.sum_div, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hm (Real.rpow_nonneg hx0.le _)) hcoef

theorem small_sum_bound {C x : ℝ} (hx : 6 ≤ x) (hBT : Lemma3Coprime)
    (hC : MassBound C) (hM : MomentBound) :
    ∑ d ∈ small x, f d * D x d ≤ 2 * x * Chebyshev.theta x *
      ((C - 1) / Real.log x + 20.19 / Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hs : ∀ d ∈ small x, 0 < d ∧ (d : ℝ) < x := by
    intro d hd
    have hd2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hdpos : 0 < d := by omega
    refine ⟨hdpos, ?_⟩
    by_contra h
    have hlog := Real.log_le_log hx0 (le_of_not_gt h)
    have hsmall := (Finset.mem_filter.mp hd).2
    linarith
  have h := eq57 hBT hx (small x) hs
  have he : (∑ d ∈ small x, 2 * x * Chebyshev.theta x * f d /
      ((d.totient : ℝ) * Real.log (x / d))) =
      2 * x * Chebyshev.theta x * (∑ d ∈ small x, a d / Real.log (x / d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    unfold a
    ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (small_log_sum hx hC hM)
    (by positivity [Chebyshev.theta_nonneg x]))

/-- A single positive Taylor term controls the tail at the paper's threshold. -/
theorem log_sq_le_rpow {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    15 * Real.log x ^ 2 ≤ x ^ (1 / 8 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hL : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  set L := Real.log x with hLdef
  have h10 : 15 * (8 : ℝ) ^ 12 * 479001600 ≤ L ^ 10 := by
    calc
      _ ≤ (119 : ℝ) ^ 10 := by norm_num
      _ ≤ L ^ 10 := by gcongr
  have hmul := mul_le_mul_of_nonneg_right h10 (sq_nonneg L)
  have hpoly : 15 * L ^ 2 ≤ (L / 8) ^ 12 / (Nat.factorial 12 : ℝ) := by
    norm_num [Nat.factorial]
    nlinarith
  have hexp := Real.pow_div_factorial_le_exp (L / 8) (by linarith : 0 ≤ L / 8) 12
  have he : x ^ (1 / 8 : ℝ) = Real.exp (L / 8) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    rw [hLdef]
    ring
  rw [he]
  exact hpoly.trans hexp

theorem tail_coefficient {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    14.46 / x ^ (1 / 8 : ℝ) ≤ 1 / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hx0 _) (sq_pos_of_pos hL)]
  have h := log_sq_le_rpow hx
  nlinarith [sq_nonneg (Real.log x)]

theorem mass_ge_one {C : ℝ} (hC : MassBound C) : 1 ≤ C := by
  have h := hC 1
  simpa [a_one] using h

/-- Equation 5.10, CONDITIONAL ON Brun Titchmarsh, theta, mass and moment bounds. -/
theorem eq510tail_of_moments {C : ℝ} (hCup : C ≤ 6.2130) (hBT : Lemma3Coprime)
    (hTheta : ThetaUpper) (hC : MassBound C) (hM : MomentBound) : Eq510tail C := by
  intro x hx
  have hx6 : 6 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  set L := Real.log x with hLdef
  have hL : 0 < L := by linarith
  have hC1 : 1 ≤ C := mass_ge_one hC
  have hθ0 : 0 ≤ Chebyshev.theta x := Chebyshev.theta_nonneg x
  have hs := small_sum_bound hx6 hBT hC hM
  have hl := large_sum_bound hx6 hM
  have ht := tail_coefficient hx
  have hsum : G x - Psi x ≤ x * Chebyshev.theta x * ((2 * C - 2) / L + 41.38 / L ^ 2) := by
    rw [tail_identity x hx6, split_sum]
    have hlarge : x * Chebyshev.theta x * (14.46 / x ^ (1 / 8 : ℝ)) ≤
        x * Chebyshev.theta x * (1 / L ^ 2) :=
      mul_le_mul_of_nonneg_left ht (mul_nonneg hx0.le hθ0)
    have he : 2 * x * Chebyshev.theta x * ((C - 1) / L + 20.19 / L ^ 2) +
        x * Chebyshev.theta x * (1 / L ^ 2) =
        x * Chebyshev.theta x * ((2 * C - 2) / L + 41.38 / L ^ 2) := by ring
    linarith
  have hB0 : 0 ≤ (2 * C - 2) / L + 41.38 / L ^ 2 :=
    add_nonneg (div_nonneg (by linarith) hL.le) (by positivity)
  have htheta := hTheta x (by linarith)
  have hθ : x * Chebyshev.theta x * ((2 * C - 2) / L + 41.38 / L ^ 2) ≤
      x * (x + x / (40 * L)) * ((2 * C - 2) / L + 41.38 / L ^ 2) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htheta hx0.le) hB0
  have hCL : (2 * C - 2) * L ≤ 10.426 * L :=
    mul_le_mul_of_nonneg_right (by linarith) hL.le
  have hnum : (40 * L + 1) * ((2 * C - 2) * L + 41.38) <
      40 * L * ((2 * C - 2) * L + 47) := by nlinarith
  have hbr : (1 + 1 / (40 * L)) * (2 * C - 2 + 41.38 / L) < 2 * C - 2 + 47 / L := by
    have e1 : (1 + 1 / (40 * L)) * (2 * C - 2 + 41.38 / L) =
        ((40 * L + 1) * ((2 * C - 2) * L + 41.38)) / (40 * L ^ 2) := by
      field_simp
    have e2 : 2 * C - 2 + 47 / L = (40 * L * ((2 * C - 2) * L + 47)) / (40 * L ^ 2) := by
      field_simp
    rw [e1, e2]
    exact div_lt_div_of_pos_right hnum (by positivity)
  have hfinal := mul_lt_mul_of_pos_left hbr (show 0 < x ^ 2 / L by positivity)
  have he : x * (x + x / (40 * L)) * ((2 * C - 2) / L + 41.38 / L ^ 2) =
      x ^ 2 / L * ((1 + 1 / (40 * L)) * (2 * C - 2 + 41.38 / L)) := by
    field_simp
  rw [← he] at hfinal
  exact lt_of_le_of_lt (hsum.trans hθ) hfinal

/-- The existing 27 prime route with 5.10 replaced by its four lower level inputs. -/
theorem statement27_of_moments {C : ℝ} (hClow : 6.2022 ≤ C) (hCup : C ≤ 6.2130)
    (hRS : LeanLab.RieselVaughan1983.RS33)
    (h8 : Vaughan1977Lemma10.Lemma8 LeanLab.ChenExplicit.twinC) (h11 : Lemma11)
    (hBT : Lemma3Coprime) (hTheta : ThetaUpper) (hC : MassBound C) (hM : MomentBound) :
    Vaughan1977.Statement27 :=
  statement27_of_L8_L11_510 hClow hCup hRS h8 h11
    (eq510tail_of_moments hCup hBT hTheta hC hM)

example : a 1 = 1 ∧ (1 : ℝ) ^ (3 / 8 : ℝ) * a 1 ≤ 14.46 := by
  norm_num [a_one]

example : 3 * Real.log (1 : ℕ) ≤ Real.log (8 : ℝ) ↔ (1 : ℝ) ≤ (8 : ℝ) ^ (1 / 3 : ℝ) := by
  simpa only [Nat.cast_one] using
    (small_iff_rpow (x := 8) (d := 1) (by norm_num) (by decide))

end LeanLab.SchnirelmannBounds.Vaughan1977Moments

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.a_nonneg
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.a_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.sum_le_sub_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.split_sum
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.small_iff_rpow
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.small_log_sum
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.large_power
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.large_weight
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.large_sum_bound
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.small_sum_bound
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.log_sq_le_rpow
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.tail_coefficient
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.mass_ge_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.eq510tail_of_moments
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Moments.statement27_of_moments
