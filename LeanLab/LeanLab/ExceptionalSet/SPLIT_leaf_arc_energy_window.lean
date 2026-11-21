import LeanLab.ExceptionalSet.SPLIT_leaf_arc_energy
import LeanLab.ExceptionalSet.SPLIT_leaf_mean_square

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_arc_energy`: the even frequency window
alone, that is the squared coefficient energy of
`FX X (X ^ 2) ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X)` on the even integers `0 ≤ n ≤ X`, is
eventually at most `C · X^(3/2 + 2Θ + ε)`.

The window sum is handled one frequency at a time. At an even `n ≤ X` the coefficient of the
difference is the coefficient of `FX X (X ^ 2) ^ 2` minus the coefficient of the arc model; the
first is the smoothed count `r2 n · exp (−n / X)`, and subtracting and adding the smoothed
singular main term `exp (−n / X) · n · Sing n` splits it into the smoothed model error
`error n · exp (−n / X)` and the reconstruction residual `exp (−n / X) · n · Sing n` minus the
model coefficient. The square of a sum is at most twice the sum of the squares, the damping
`exp (−n / X) ∈ (0, 1]` only shrinks the error term, and the two resulting sums are bounded by the
two mean square estimates: the smoothed model error on the even window, and the reconstruction
residual of the truncated arc model against `exp (−n / X) · n · Sing n`, the latter with the
smaller power `5 / 2 + ε` which is below the target power because `1 ≤ 2 Θ`.

Four leaves, none of which gives the window bound alone:

* `leaf_window_coefficient_identity`, the coefficient of `FX X (X ^ 2) ^ 2` at an even `n ≤ X` is
  the smoothed count. This is an identity at one frequency, no hypothesis on `Θ`, and it is the
  rewriting step the per term estimate uses.
* `leaf_window_term_split`, the per frequency inequality: at an even `n ≤ X` the squared modulus of
  the coefficient of the difference is at most twice the squared smoothed model error plus twice
  the squared reconstruction residual. One inequality, one frequency, no constant to be found.
* `leaf_window_error_energy`, the mean square of the smoothed model error on the even window. This
  is the analytic input the reduction needs, and it is where the zero free hypothesis enters.
* `leaf_window_model_energy`, the reconstruction residual of the truncated arc model on the even
  window, with power `5 / 2 + ε`.

The assembly `leaf_arc_energy_window_split` takes `C = 2 Ce + 2 Cs` and `X₀` above both thresholds
and at least one, applies the per frequency inequality termwise, splits the sum, and uses the two
mean square estimates with `5 / 2 + ε ≤ 3 / 2 + 2 Θ + ε`.

Why the leaves are not degenerate. Each leaf carries the target's own numerical hypotheses
`1/2 ≤ Θ`, `Θ < 3/4`, `0 < ε` and `ε < 3/2 - 2 Θ`, so there are instances: `Θ = 1/2`, `ε = 1/4`,
and `3/2 - 2·(1/2) = 1/2 > 0`. The even window at `X = 4` is `{0, 2, 4}`, which is nonempty, so no
leaf sums over an empty set at that instance; at `X = 0` the window is `{0}` and the cutoff
`Nat.sqrt 0` is `0`, and the two threshold leaves carry their own `X₀`, whose honest value is at
least `4`. No division by `X`, by the cutoff or by `Nat.totient` appears in any statement, so Lean's
junk values for division play no role: the only division is `n / X` with `X ≥ 1`, and the only
power is at a nonnegative base. `error`, `Sing` and `r2` are total functions of a natural number,
so negative indices do not occur; the coefficient index is `(n : ℤ)` at `n : ℕ`. The identity leaf
is stated for `1 ≤ X` and `n ≤ X` only, which is exactly where `exp (−n / X)` is a genuine damping.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF: One frequency of the generating function: for `1 ≤ X` and `n ≤ X`, the `n`-th Fourier
coefficient of the square of the exponentially weighted prime generating function cut at `X ^ 2` is
the smoothed even count `r2 n · exp (−n / X)`, as a real number read in the complex coefficients.
This is the rewriting step of the per term estimate: an identity at a single frequency, with no
hypothesis on `Θ`, no constant and no asymptotic content, so it is strictly easier than the window
bound and gives nothing about a sum. Instance: `X = 4`, `n = 2`, where the coefficient is
`r2 2 · exp (−1/2)`. The two sums `r2` and `RΛ` have the same body, so the identification is
`rfl`. -/
theorem leaf_window_coefficient_identity (X : ℕ) (hX : 1 ≤ X) (n : ℕ) (hn : n ≤ X) :
    fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) (n : ℤ) =
      ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
  have hn2 : n ≤ X ^ 2 := hn.trans (Nat.le_self_pow two_ne_zero X)
  have h := fourierCoeff_FX_sq (X : ℝ) (X ^ 2) n hn2
  have hR : LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n = r2 n := rfl
  rw [hR] at h
  exact h

/-- LEAF: One frequency, split: at an even `n` in the window `0 ≤ n ≤ X` with `1 ≤ X`, the squared
modulus of the `n`-th coefficient of the difference between the squared generating function and the
arc model is at most twice the squared smoothed model error plus twice the squared reconstruction
residual. The step is adding and subtracting `exp (−n / X) · n · Sing n` and using that the square
of a sum of two moduli is at most twice the sum of the squares, with `exp (−n / X) ≤ 1` because
`n ≤ X`. One inequality at one frequency, no constant to be found, so strictly easier than the
window bound. Instance: `X = 4`, `n = 2`; the claim is not vacuous since `2` is even and `2 ≤ 4`. -/
theorem leaf_window_term_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) (X : ℕ) (hX : 1 ≤ X) (n : ℕ)
    (hn : n ∈ (range (X + 1)).filter Even) :
    ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
        (n : ℤ)‖ ^ 2 ≤
      2 * (error n) ^ 2 +
        2 * ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 := by
  classical
  have hnX : n ≤ X := by
    have := mem_range.mp (mem_filter.mp hn).1
    omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hFX : MemLp (fun t => FX (X : ℝ) (X ^ 2) t ^ 2) 2 haarAddCircle :=
    memLp_FX_sq (X : ℝ) (X ^ 2)
  have hW : MemLp (Vfun X (Nat.sqrt X) (Nat.sqrt X)) 2 haarAddCircle :=
    memLp_Vfun hX0 _ _
  have hneg : fourierCoeff (-(Vfun X (Nat.sqrt X) (Nat.sqrt X))) =
      -fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) := by
    ext m
    have h := fourierCoeff.const_smul (T := (1 : ℝ)) (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (-1) m
    simpa [neg_smul, one_smul] using h
  have hcoef : fourierCoeff
        (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) (n : ℤ) =
      ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) := by
    have hadd := fourierCoeff.add (T := (1 : ℝ))
      (f := fun t => FX X (X ^ 2) t ^ 2) (g := -(Vfun X (Nat.sqrt X) (Nat.sqrt X)))
      (hFX.integrable one_le_two) (hW.integrable one_le_two).neg
    have heq : (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) =
        (fun t => FX X (X ^ 2) t ^ 2) + (-(Vfun X (Nat.sqrt X) (Nat.sqrt X))) := by
      ext t
      simp [sub_eq_add_neg]
    rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply,
      leaf_window_coefficient_identity X hX n hnX]
    rfl
  rw [hcoef]
  have hexp1 : Real.exp (-(n : ℝ) / X) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    have hnn : (0 : ℝ) ≤ (n : ℝ) / X := div_nonneg (Nat.cast_nonneg n) hX0.le
    linarith
  have hexp0 : (0 : ℝ) < Real.exp (-(n : ℝ) / X) := Real.exp_pos _
  have hab : ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
      ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 ≤ (error n) ^ 2 := by
    have hid : ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) =
          ((error n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
      simp only [error]
      push_cast
      ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    have he2 : Real.exp (-(n : ℝ) / X) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (error n)]
  have hsplit : ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
      fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) =
      (((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)) +
      (((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ)) := by
    ring
  have hstep : ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
      fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ)‖ ^ 2 ≤
      2 * ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 +
      2 * ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ)‖ ^ 2 := by
    rw [hsplit]
    calc ‖(((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)) +
          (((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
            fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ))‖ ^ 2
        ≤ (‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ +
            ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
              fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ ≤ 2 * (‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 +
            ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
              fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ)‖ ^ 2) := add_sq_le
      _ = 2 * ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 +
            2 * ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
              fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ)‖ ^ 2 := by ring
  have hsymm : ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
      ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ =
      ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ)‖ := norm_sub_rev _ _
  rw [hsymm]
  nlinarith [hab, hstep]

/-- LEAF: the mean square of the smoothed model error on the even window. There are `C` and `X₀`
with `0 ≤ C` and, for every `X ≥ X₀`, the sum of `(error n) ^ 2` over the even `0 ≤ n ≤ X` is at
most `C · X^(3/2 + 2Θ + ε)`. This is the analytic input of the reduction, the one sum in which the
zero free hypothesis is used; it is a mean square of a single arithmetic error term, with no
generating function, no arc model and no Fourier coefficient in it, so it is strictly easier than
the window bound and does not imply it. Constant and threshold are free. Instance: `Θ = 1/2`,
`ε = 1/4`; at `X = 4` the summed set is `{0, 2, 4}`. -/
theorem leaf_window_error_energy (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2) ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨C, X₀, h⟩ :=
    LeanLab.ExceptionalSet.BG2026.Supply385.leaf_mean_square_split Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨max C 0, le_max_right _ _, X₀, ?_⟩
  intro X hX
  have hbound := h X hX
  have hpow : 0 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hmax : C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) ≤
      max C 0 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  linarith

/-- LEAF: The reconstruction residual of the truncated arc model on the even window: there are `C`
and `X₀` with `0 ≤ C` and, for every `X ≥ X₀`, the sum over the even `0 ≤ n ≤ X` of the squared
modulus of the `n`-th model coefficient minus `exp (−n / X) · n · Sing n` is at most
`C · X^(5/2 + ε)`. The power is the smaller one, `5 / 2 + ε`, and `1 ≤ 2 Θ` raises it to the target
power, so this estimate on its own is weaker than the window bound: it says nothing about the
generating function and it is stated at a lower exponent. Its constant and threshold are free.
Instance: `Θ = 1/2`, `ε = 1/4`; at `X = 4` the summed set is `{0, 2, 4}` and the cutoff is `2`. -/
theorem leaf_window_model_energy (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
          ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) ≤
        C * (X : ℝ) ^ (5 / 2 + ε) := by
  exact leaf_singular_energy ε hε

/-- Assembly of the window leaf from the per frequency split and the two mean square estimates.
The per frequency inequality is summed over the even window, the sum of the two pieces is split into
twice each sum, the two sums are bounded by their estimates, the model power `5 / 2 + ε` is raised
to `3 / 2 + 2 Θ + ε` using `1 ≤ 2 Θ`, and the constant is `2 Ce + 2 Cs` with the threshold above
both. Nothing else is used and no unproved step enters the assembly. -/
theorem leaf_arc_energy_window_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2) ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨Ce, hCe, Xe, hE⟩ := leaf_window_error_energy Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨Cs, hCs, Xs, hM⟩ := leaf_window_model_energy Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨2 * Ce + 2 * Cs, by positivity, max (max Xe Xs) 1 + 1, ?_⟩
  intro X hX
  have hXe : Xe ≤ X := by omega
  have hXs : Xs ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hpow : (X : ℝ) ^ (5 / 2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hXR (by linarith)
  have hsum : (∑ n ∈ (range (X + 1)).filter Even,
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
        (n : ℤ)‖ ^ 2) ≤
      2 * (∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2) +
        2 * (∑ n ∈ (range (X + 1)).filter Even,
          ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) := by
    have hsplit : (∑ n ∈ (range (X + 1)).filter Even,
        (2 * (error n) ^ 2 +
          2 * ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2)) =
        2 * (∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2) +
          2 * (∑ n ∈ (range (X + 1)).filter Even,
            ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    rw [← hsplit]
    exact sum_le_sum
      (fun n hn => leaf_window_term_split Θ hΘ1 hΘ2 hZF ε hε hsublinear X hX1 n hn)
  have h1 : (∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2) ≤
      Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := hE X hXe
  have h2 : (∑ n ∈ (range (X + 1)).filter Even,
      ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) ≤
      Cs * (X : ℝ) ^ (5 / 2 + ε) := hM X hXs
  have h2' : Cs * (X : ℝ) ^ (5 / 2 + ε) ≤ Cs * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    mul_le_mul_of_nonneg_left hpow hCs
  calc (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2)
      ≤ 2 * (Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) +
        2 * (Cs * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) := by linarith
    _ = (2 * Ce + 2 * Cs) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
