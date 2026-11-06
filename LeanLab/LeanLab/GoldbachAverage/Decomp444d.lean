import LeanLab.GoldbachAverage.Decomp444b
import LeanLab.GoldbachAverage.Decomp444c
import LeanLab.GoldbachAverage.Decomp444e

/-!
BHMS, https://arxiv.org/abs/1704.06103v2 page 17 proof of Lemma 7.
The pointwise truncated explicit formula is separate from the elementary square integration.
Its source is Lemma 4 on page 7, proved there from Montgomery and Vaughan Theorem 12.5.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp444d
open MeasureTheory Complex
open Decomp287d

/-- LEAF. BHMS page 17 difference of Lemma 4 with cutoff T equal to x, at q one.
The constant term cancels. The low and high zero ranges partition the actual truncated sum.
This pointwise formula contains no square integration or zero count estimate. -/
theorem truncated_increment : ∃ C : ℝ, 0 ≤ C ∧ ∀ x h t : ℝ,
    2 ≤ x → 2 ≤ h → h ≤ x → t ∈ Set.Icc x (2 * x) →
      ‖((Chebyshev.psi (t + h) - Chebyshev.psi t - h : ℝ) : ℂ) +
        lowZeros x h t + highZeros x h t‖ ≤ C * Real.log x ^ 2 := by
  exact Decomp444e.truncated_increment_assembled

example : type_of% Decomp444e.truncated_increment_assembled = type_of% truncated_increment := rfl

/-- The exact explicit_variance_split target follows by squaring and integrating the pointwise formula.
CONDITIONAL ON truncated_increment. The two finite zero square integrals are genuine integrals. -/
theorem explicit_variance_split_assembled : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      (∫ t in x..(2 * x), (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
        K * ((∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) +
          (∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2) + x * Real.log x ^ 4) := by
  obtain ⟨C, hC, hT⟩ := truncated_increment
  refine ⟨3 * (C ^ 2 + 1), by positivity, ?_⟩
  intro x h hx hh hhx
  have hx0 : 0 ≤ x := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hfull := Decomp82.short_error_integrable (x := 2 * x) (by linarith) hh0
  have hi := hfull.mono_set (show Set.uIcc x (2 * x) ⊆ Set.uIcc 0 (2 * x) by
    rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x), Set.uIcc_of_le (by linarith : 0 ≤ 2 * x)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩)
  have hL := (Decomp444b.low_increment_average x h hx hh hhx).1
  have hH := (Decomp444c.high_difference_energy x h hx hh hhx).1
  have hpt (t : ℝ) (ht : t ∈ Set.Icc x (2 * x)) :
      (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2 ≤
        3 * (‖lowZeros x h t‖ ^ 2 + ‖highZeros x h t‖ ^ 2 + C ^ 2 * Real.log x ^ 4) := by
    let r : ℝ := Chebyshev.psi (t + h) - Chebyshev.psi t - h
    let l : ℂ := lowZeros x h t
    let u : ℂ := highZeros x h t
    have hn : |r| ≤ C * Real.log x ^ 2 + ‖l‖ + ‖u‖ := by
      have heq : (r : ℂ) = ((r : ℂ) + l + u) - l - u := by ring
      calc |r| = ‖(r : ℂ)‖ := by simp
        _ = ‖((r : ℂ) + l + u) - l - u‖ := congrArg norm heq
        _ ≤ ‖(r : ℂ) + l + u‖ + ‖l‖ + ‖u‖ := by
          have h1 := norm_sub_le ((r : ℂ) + l + u - l) u
          have h2 := norm_sub_le ((r : ℂ) + l + u) l
          linarith
        _ ≤ _ := by
          have hbound : ‖(r : ℂ) + l + u‖ ≤ C * Real.log x ^ 2 := hT x h t hx hh hhx ht
          linarith
    have hs := pow_le_pow_left₀ (abs_nonneg r) hn 2
    rw [sq_abs] at hs
    dsimp only [r, l, u] at *
    nlinarith [sq_nonneg (C * Real.log x ^ 2 - ‖lowZeros x h t‖),
      sq_nonneg (C * Real.log x ^ 2 - ‖highZeros x h t‖),
      sq_nonneg (‖lowZeros x h t‖ - ‖highZeros x h t‖)]
  have hb := intervalIntegral.integral_mono_on (μ := volume) (by linarith : x ≤ 2 * x) hi
    (((hL.add hH).add intervalIntegrable_const).const_mul 3) hpt
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hL.add hH) intervalIntegrable_const,
    intervalIntegral.integral_add hL hH, intervalIntegral.integral_const, smul_eq_mul] at hb
  have hLn : 0 ≤ ∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hHn : 0 ≤ ∫ t in x..(2 * x), ‖highZeros x h t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hR : 0 ≤ x * Real.log x ^ 4 := by positivity
  nlinarith [mul_nonneg (sq_nonneg C) (add_nonneg hLn hHn)]

example : type_of% Decomp287d.explicit_variance_split = type_of% explicit_variance_split_assembled := rfl

end LeanLab.GoldbachAverage.Decomp444d
