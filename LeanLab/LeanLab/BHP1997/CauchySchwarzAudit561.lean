/-
Audit of the leaf `leaf_section4Block_positive_large_cauchy_schwarz` of
`SPLIT_leaf_section4Block_mean_value_positive_large`.

The leaf states the Cauchy-Schwarz inequality `(∫ f)^2 ≤ (b - a) * ∫ f^2` for every
nonnegative `f`, with no integrability hypothesis. In Lean the integral of a function
that is not integrable is zero, so the leaf fails as written: `f t = |t| ^ (-1/2)` on
`[0, 1]` has integral `2`, and its square `1 / t` is not integrable, so the right side
is zero. This file proves that refutation and proves the inequality with the missing
hypotheses added. The paper's step is sound: there `f` is the norm of a finite Dirichlet
polynomial, which is continuous. No statement on main is changed.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_large

namespace LeanLab.BHP1997.CauchySchwarzAudit561

open MeasureTheory

/-- The statement of `leaf_section4Block_positive_large_cauchy_schwarz` is false as
written. Witness: `f t = |t| ^ (-1/2)`, `a = 0`, `b = 1`. The left side is `2 ^ 2 = 4`.
The square of `f` is `1 / t` on `(0, 1]`, which is not interval integrable, so the
integral on the right is zero by the junk value convention and the right side is `0`. -/
theorem leaf_section4Block_positive_large_cauchy_schwarz_false :
    ¬ (∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → (∀ t, 0 ≤ f t) →
      (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2) := by
  intro h
  have h1 : (∫ t in (0 : ℝ)..1, |t| ^ (-(1 / 2) : ℝ)) ^ 2 ≤
      (1 - 0) * ∫ t in (0 : ℝ)..1, (|t| ^ (-(1 / 2) : ℝ)) ^ 2 :=
    h (fun t => |t| ^ (-(1 / 2) : ℝ)) 0 1 zero_le_one
      (fun t => Real.rpow_nonneg (abs_nonneg t) _)
  have hI : ∫ t in (0 : ℝ)..1, |t| ^ (-(1 / 2) : ℝ) = 2 := by
    have e : ∫ t in (0 : ℝ)..1, |t| ^ (-(1 / 2) : ℝ) =
        ∫ t in (0 : ℝ)..1, t ^ (-(1 / 2) : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      simp only [abs_of_nonneg ht.1]
    rw [e, integral_rpow (Or.inl (by norm_num))]
    rw [Real.one_rpow, Real.zero_rpow (by norm_num)]
    norm_num
  have hJ : ∫ t in (0 : ℝ)..1, (|t| ^ (-(1 / 2) : ℝ)) ^ 2 = 0 := by
    apply intervalIntegral.integral_undef
    intro hint
    have h2 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 1 := by
      refine (intervalIntegrable_congr ?_).mp hint
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      show (|t| ^ (-(1 / 2) : ℝ)) ^ 2 = t⁻¹
      have e2 : (-(1 / 2) : ℝ) * ((2 : ℕ) : ℝ) = -1 := by norm_num
      rw [abs_of_pos ht.1, ← Real.rpow_natCast, ← Real.rpow_mul ht.1.le, e2,
        Real.rpow_neg_one]
    rw [intervalIntegrable_inv_iff] at h2
    rcases h2 with h2 | h2
    · norm_num at h2
    · exact h2 (by simp)
  rw [hI, hJ] at h1
  norm_num at h1

/-- Cauchy-Schwarz in the height with the hypotheses the leaf leaves out: `f` and its
square are interval integrable. Then the square of the integral is at most the length
of the range times the integral of the square. Proof: the integral of `(f - c)^2` is
nonnegative for the mean value `c`. Nonnegativity of `f` is not needed. -/
theorem cauchy_schwarz_of_intervalIntegrable (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf1 : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h
    simp
  have hd : 0 < b - a := by linarith
  have key : ∀ c : ℝ, 0 ≤ (∫ t in a..b, f t ^ 2) - 2 * c * (∫ t in a..b, f t) +
      c ^ 2 * (b - a) := by
    intro c
    have h0 : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
    have e : ∫ t in a..b, (f t - c) ^ 2 =
        (∫ t in a..b, f t ^ 2) - 2 * c * (∫ t in a..b, f t) + c ^ 2 * (b - a) := by
      have e1 : (fun t => (f t - c) ^ 2) = fun t => f t ^ 2 - 2 * c * f t + c ^ 2 := by
        funext t; ring
      rw [e1, intervalIntegral.integral_add (hf2.sub (hf1.const_mul _))
          intervalIntegrable_const,
        intervalIntegral.integral_sub hf2 (hf1.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    linarith
  have hk := key ((∫ t in a..b, f t) / (b - a))
  have e3 : (∫ t in a..b, f t ^ 2) -
      2 * ((∫ t in a..b, f t) / (b - a)) * (∫ t in a..b, f t) +
      ((∫ t in a..b, f t) / (b - a)) ^ 2 * (b - a) =
      (∫ t in a..b, f t ^ 2) - (∫ t in a..b, f t) ^ 2 / (b - a) := by
    field_simp
    ring
  rw [e3] at hk
  have h4 : (∫ t in a..b, f t) ^ 2 / (b - a) ≤ ∫ t in a..b, f t ^ 2 := by linarith
  rw [div_le_iff₀ hd] at h4
  linarith

/-- The same inequality for a continuous `f`, which is the case the split uses: the
norm of a finite Dirichlet polynomial is continuous in the height. -/
theorem cauchy_schwarz_of_continuous (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : Continuous f) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 :=
  cauchy_schwarz_of_intervalIntegrable f a b hab (hf.intervalIntegrable a b)
    ((hf.pow 2).intervalIntegrable a b)

end LeanLab.BHP1997.CauchySchwarzAudit561

set_option format.width 1000

#print axioms LeanLab.BHP1997.CauchySchwarzAudit561.leaf_section4Block_positive_large_cauchy_schwarz_false
#print axioms LeanLab.BHP1997.CauchySchwarzAudit561.cauchy_schwarz_of_intervalIntegrable
#print axioms LeanLab.BHP1997.CauchySchwarzAudit561.cauchy_schwarz_of_continuous
