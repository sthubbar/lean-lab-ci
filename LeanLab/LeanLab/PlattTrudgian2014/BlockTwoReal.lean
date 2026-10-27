/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 page 30 display 43 at h = 2.
Elementary hyperbolic inequalities prepare a two step block certificate.
-/
import LeanLab.PlattTrudgian2014.BlockCertificate

namespace LeanLab.PlattTrudgian2014

theorem convexOn_sinh_nonneg : ConvexOn ℝ (Set.Ici 0) Real.sinh := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := Real.cosh) (f'' := Real.sinh)
    (convex_Ici 0) Real.continuous_sinh.continuousOn
  · intro x hx
    exact (Real.hasDerivAt_sinh x).hasDerivWithinAt
  · intro x hx
    exact (Real.hasDerivAt_cosh x).hasDerivWithinAt
  · intro x hx
    apply Real.sinh_nonneg_iff.mpr
    exact (Set.mem_Ici.mp (interior_subset hx))

theorem sinh_scale_le {u a : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.sinh (a * u) ≤ a * Real.sinh u := by
  have hh := convexOn_sinh_nonneg.2 hu (le_refl (0 : ℝ)) ha (sub_nonneg.mpr ha1)
    (show a + (1 - a) = 1 by ring)
  simpa only [smul_eq_mul, mul_zero, add_zero, Real.sinh_zero] using hh

theorem cosh_half_identity (x : ℝ) : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
  have h1 := Real.cosh_two_mul (x / 2)
  have h2 := Real.cosh_sq_sub_sinh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h1
  linarith

theorem cosh_scale_quadratic {t a : ℝ} (ht : 0 ≤ t) (ha : |a| ≤ 1) :
    Real.cosh (t * a) ≤ 1 + (Real.cosh t - 1) * a ^ 2 := by
  have hs := sinh_scale_le (u := t / 2) (a := |a|) (by positivity) (abs_nonneg _) ha
  have hs0 : 0 ≤ Real.sinh (|a| * (t / 2)) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq := pow_le_pow_left₀ hs0 hs 2
  have he : Real.cosh (t * a) = Real.cosh (t * |a|) := by
    rw [← Real.cosh_abs (t * a), abs_mul, abs_of_nonneg ht]
  calc
    _ = 1 + 2 * Real.sinh (|a| * (t / 2)) ^ 2 := by
      rw [he, cosh_half_identity, show t * |a| / 2 = |a| * (t / 2) by ring]
    _ ≤ 1 + 2 * (|a| * Real.sinh (t / 2)) ^ 2 := by linarith
    _ = 1 + (Real.cosh t - 1) * a ^ 2 := by
      rw [cosh_half_identity t, mul_pow, sq_abs]
      ring

theorem paired_cosh_bound {t u a b : ℝ} (ht : 0 ≤ t) (hu : |u| ≤ 1)
    (hab : a ^ 2 + b ^ 2 ≤ 1) :
    Real.exp (t * u) * Real.cosh (t * a) + Real.exp (-(t * u)) * Real.cosh (t * b) ≤
      Real.exp t * Real.cosh t + Real.exp (-t) := by
  have ha : |a| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg b], by nlinarith [sq_nonneg b]⟩
  have hb : |b| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg a]⟩
  have hu' := abs_le.mp hu
  have hp : Real.exp (t * u) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
  have hq : Real.exp (-(t * u)) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
  have hc : Real.cosh (t * u) ≤ Real.cosh t := by
    apply Real.cosh_le_cosh.mpr
    simp only [abs_mul, abs_of_nonneg ht]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu ht
  have hsum : Real.exp (t * u) + Real.exp (-(t * u)) ≤ 2 * Real.cosh t := by
    rw [Real.cosh_eq] at hc
    linarith
  have hweight : Real.exp (t * u) * a ^ 2 + Real.exp (-(t * u)) * b ^ 2 ≤ Real.exp t := by
    calc
      _ ≤ Real.exp t * a ^ 2 + Real.exp t * b ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hp (sq_nonneg a))
          (mul_le_mul_of_nonneg_right hq (sq_nonneg b))
      _ = Real.exp t * (a ^ 2 + b ^ 2) := by ring
      _ ≤ Real.exp t * 1 := mul_le_mul_of_nonneg_left hab (Real.exp_nonneg _)
      _ = Real.exp t := mul_one _
  have hE : 0 ≤ Real.cosh t - 1 := sub_nonneg.mpr (Real.one_le_cosh t)
  calc
    _ ≤ Real.exp (t * u) * (1 + (Real.cosh t - 1) * a ^ 2) +
        Real.exp (-(t * u)) * (1 + (Real.cosh t - 1) * b ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (cosh_scale_quadratic ht ha) (Real.exp_nonneg _))
        (mul_le_mul_of_nonneg_left (cosh_scale_quadratic ht hb) (Real.exp_nonneg _))
    _ = Real.exp (t * u) + Real.exp (-(t * u)) +
        (Real.cosh t - 1) * (Real.exp (t * u) * a ^ 2 + Real.exp (-(t * u)) * b ^ 2) := by ring
    _ ≤ 2 * Real.cosh t + (Real.cosh t - 1) * Real.exp t :=
      add_le_add hsum (mul_le_mul_of_nonneg_left hweight hE)
    _ = Real.exp t * Real.cosh t + Real.exp (-t) := by rw [Real.cosh_eq]; ring

#print axioms convexOn_sinh_nonneg
#print axioms sinh_scale_le
#print axioms cosh_half_identity
#print axioms cosh_scale_quadratic

#print axioms paired_cosh_bound

end LeanLab.PlattTrudgian2014
