import LeanLab.HelfgottMajor.RealAxisKernel

/-!
# Nonvanishing of `L(σ, χ)` on the positive real axis for the modulus 13

What is proved: for every non principal Dirichlet character `χ` modulo 13 and every real `σ > 0`,
`L(σ, χ) ≠ 0`. The unit group modulo 13 is cyclic of order 12 with generator 2, so `χ` is
determined by `z = χ(2)`, a twelfth root of unity different from 1. In each of the five cases
`z = -1`, `z^2 + 1 = 0`, `z^2 + z + 1 = 0`, `z^2 - z + 1 = 0`, `z^4 - z^2 + 1 = 0` the real part
of `∑_{a < 13} χ(a) x^a` is an explicit real polynomial which factors as `x (1 - x)^k R(x)` with
`R` positive on the open unit interval, so the kernel criterion of `RealAxisKernel` applies with
the constant `c = 1` for all eleven characters. In the last case the coefficients involve the
real part `s` of `z`, with `s^2 = 3/4`, and only `-1 < s` is needed.

This is standard mathematics. AI wrote this Lean code. The binary Goldbach conjecture is open
and nothing here changes that.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

namespace ThirteenAux

open Finset

/-- A root of `z^2 + 1` has real part `0`. -/
private theorem re_of_i {z : ℂ} (h : z ^ 2 + 1 = 0) : z.re = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.zero_re,
    Complex.zero_im, pow_two, Complex.mul_re, Complex.mul_im] at h1 h2
  have h3 : z.re * z.im = 0 := by linear_combination h2 / 2
  rcases mul_eq_zero.mp h3 with h0 | h0
  · exact h0
  · rw [h0] at h1
    nlinarith [sq_nonneg z.re]

/-- A root of `z^2 + z + 1` has real part `-1/2`. -/
private theorem re_of_omega {z : ℂ} (h : z ^ 2 + z + 1 = 0) : z.re = -1 / 2 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.zero_re,
    Complex.zero_im, pow_two, Complex.mul_re, Complex.mul_im] at h1 h2
  have h3 : z.im * (2 * z.re + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h0 | h0
  · rw [h0] at h1
    nlinarith [sq_nonneg (2 * z.re + 1)]
  · linarith

/-- A root of `z^2 - z + 1` has real part `1/2`. -/
private theorem re_of_zeta {z : ℂ} (h : z ^ 2 - z + 1 = 0) : z.re = 1 / 2 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.zero_re, Complex.zero_im, pow_two, Complex.mul_re,
    Complex.mul_im] at h1 h2
  have h3 : z.im * (2 * z.re - 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h0 | h0
  · rw [h0] at h1
    nlinarith [sq_nonneg (2 * z.re - 1)]
  · linarith

/-- A root of `z^4 - z^2 + 1` has real part of square `3/4`, its square has real part `1/2` and
its cube has real part `0`. -/
private theorem re_of_twelfth {z : ℂ} (h : z ^ 4 - z ^ 2 + 1 = 0) :
    z.re ^ 2 = 3 / 4 ∧ (z ^ 2).re = 1 / 2 ∧ (z ^ 3).re = 0 := by
  have hw : (z ^ 2) ^ 2 - z ^ 2 + 1 = 0 := by linear_combination h
  have hwre := re_of_zeta hw
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hsqi : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]; ring
  have h1 := congrArg Complex.re hw
  rw [Complex.add_re, Complex.sub_re, pow_two (z ^ 2), Complex.mul_re, hsq, hsqi, Complex.one_re,
    Complex.zero_re] at h1
  have hb : z.im ^ 2 = z.re ^ 2 - 1 / 2 := by linarith
  have hq : (4 * z.re ^ 2 - 3) * (4 * z.re ^ 2 + 1) = 0 := by
    linear_combination (-4) * h1 + 4 * (z.im ^ 2 - z.re ^ 2 + 1 / 2 - 4 * z.re ^ 2) * hb
  have ha : z.re ^ 2 = 3 / 4 := by
    rcases mul_eq_zero.mp hq with h0 | h0
    · linarith
    · nlinarith [sq_nonneg z.re]
  refine ⟨ha, hwre, ?_⟩
  have e3 : z ^ 3 = z * (z * z) := by ring
  rw [e3, Complex.mul_re, Complex.mul_re, Complex.mul_im]
  linear_combination (-3 * z.re) * hb + (-2 * z.re) * ha

/-- The character sum over a full period vanishes for a non principal character. -/
private theorem sum_range_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ a ∈ range q, χ ((a : ℕ) : ZMod q) * (((1 : ℝ) : ℂ)) ^ a = 0 := by
  have h := LeanLab.HelfgottMajor.StripBound123.sum_range_shift (fun a => χ a) 0
  simp only [zero_add] at h
  have e : ∑ a ∈ range q, χ ((a : ℕ) : ZMod q) * (((1 : ℝ) : ℂ)) ^ a
      = ∑ a ∈ range q, χ ((a : ℕ) : ZMod q) :=
    Finset.sum_congr rfl (fun a _ => by simp)
  rw [e, h]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- For a twelfth root of unity `z ≠ 1` the real part of a real combination of the powers of
`z` is one of five explicit real combinations, the last one involving a real number `s` with
`s ^ 2 = 3 / 4`, namely the real part of `z`. -/
private theorem re_twelve (z : ℂ)
    (hz : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7 + z ^ 8 + z ^ 9 + z ^ 10
      + z ^ 11 = 0)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : ℝ) :
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))).re = y0 - y1 + y2 - y3 + y4 - y5 + y6 - y7 + y8 - y9 + y10 - y11 ∨
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))).re = y0 - y2 + y4 - y6 + y8 - y10 ∨
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))).re = (y0 - y2 + y3 - y5 + y6 - y8 + y9 - y11) + (-1 / 2) * (y1 - y2 + y4 - y5 + y7 - y8 + y10 - y11) ∨
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))).re = (y0 - y2 - y3 + y5 + y6 - y8 - y9 + y11) + (1 / 2) * (y1 + y2 - y4 - y5 + y7 + y8 - y10 - y11) ∨
    ∃ s : ℝ, s ^ 2 = 3 / 4 ∧
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))).re = (y0 - y4 - y6 + y10) + s * (y1 - y5 - y7 + y11) + (1 / 2) * (y2 + y4 - y8 - y10) := by
  have hr : ∀ (w : ℂ) (U V : ℝ), ((U : ℂ) + w * (V : ℂ)).re = U + w.re * V := by
    intro w U V
    simp
  have hf : (z + 1) * ((z ^ 2 + 1) * ((z ^ 2 + z + 1) * ((z ^ 2 - z + 1) * (z ^ 4 - z ^ 2 + 1))))
      = 0 := by linear_combination hz
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hz1 : z = -1 := by linear_combination h
    subst hz1
    have e : (1 : ℂ) * ((y0 : ℂ) + (-1) * (y1 : ℂ) + (-1) ^ 2 * (y2 : ℂ) + (-1) ^ 3 * (y3 : ℂ) + (-1) ^ 4 * (y4 : ℂ) + (-1) ^ 5 * (y5 : ℂ) + (-1) ^ 6 * (y6 : ℂ) + (-1) ^ 7 * (y7 : ℂ) + (-1) ^ 8 * (y8 : ℂ) + (-1) ^ 9 * (y9 : ℂ) + (-1) ^ 10 * (y10 : ℂ) + (-1) ^ 11 * (y11 : ℂ))
        = ((y0 - y1 + y2 - y3 + y4 - y5 + y6 - y7 + y8 - y9 + y10 - y11 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  rcases mul_eq_zero.mp h with h | h
  · right; left
    have hre := re_of_i h
    have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))
        = ((y0 - y2 + y4 - y6 + y8 - y10 : ℝ) : ℂ) + z * ((y1 - y3 + y5 - y7 + y9 - y11 : ℝ) : ℂ) := by
      push_cast
      linear_combination ((y2 : ℂ) * ((1) * z ^ 0) + (y3 : ℂ) * ((1) * z ^ 1) + (y4 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 2) + (y5 : ℂ) * ((-1) * z ^ 1 + (1) * z ^ 3) + (y6 : ℂ) * ((1) * z ^ 0 + (-1) * z ^ 2 + (1) * z ^ 4) + (y7 : ℂ) * ((1) * z ^ 1 + (-1) * z ^ 3 + (1) * z ^ 5) + (y8 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 2 + (-1) * z ^ 4 + (1) * z ^ 6) + (y9 : ℂ) * ((-1) * z ^ 1 + (1) * z ^ 3 + (-1) * z ^ 5 + (1) * z ^ 7) + (y10 : ℂ) * ((1) * z ^ 0 + (-1) * z ^ 2 + (1) * z ^ 4 + (-1) * z ^ 6 + (1) * z ^ 8) + (y11 : ℂ) * ((1) * z ^ 1 + (-1) * z ^ 3 + (1) * z ^ 5 + (-1) * z ^ 7 + (1) * z ^ 9)) * h
    rw [e, hr, hre]
    ring
  rcases mul_eq_zero.mp h with h | h
  · right; right; left
    have hre := re_of_omega h
    have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))
        = ((y0 - y2 + y3 - y5 + y6 - y8 + y9 - y11 : ℝ) : ℂ) + z * ((y1 - y2 + y4 - y5 + y7 - y8 + y10 - y11 : ℝ) : ℂ) := by
      push_cast
      linear_combination ((y2 : ℂ) * ((1) * z ^ 0) + (y3 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 1) + (y4 : ℂ) * ((-1) * z ^ 1 + (1) * z ^ 2) + (y5 : ℂ) * ((1) * z ^ 0 + (-1) * z ^ 2 + (1) * z ^ 3) + (y6 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 1 + (-1) * z ^ 3 + (1) * z ^ 4) + (y7 : ℂ) * ((-1) * z ^ 1 + (1) * z ^ 2 + (-1) * z ^ 4 + (1) * z ^ 5) + (y8 : ℂ) * ((1) * z ^ 0 + (-1) * z ^ 2 + (1) * z ^ 3 + (-1) * z ^ 5 + (1) * z ^ 6) + (y9 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 1 + (-1) * z ^ 3 + (1) * z ^ 4 + (-1) * z ^ 6 + (1) * z ^ 7) + (y10 : ℂ) * ((-1) * z ^ 1 + (1) * z ^ 2 + (-1) * z ^ 4 + (1) * z ^ 5 + (-1) * z ^ 7 + (1) * z ^ 8) + (y11 : ℂ) * ((1) * z ^ 0 + (-1) * z ^ 2 + (1) * z ^ 3 + (-1) * z ^ 5 + (1) * z ^ 6 + (-1) * z ^ 8 + (1) * z ^ 9)) * h
    rw [e, hr, hre]
  rcases mul_eq_zero.mp h with h | h
  · right; right; right; left
    have hre := re_of_zeta h
    have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))
        = ((y0 - y2 - y3 + y5 + y6 - y8 - y9 + y11 : ℝ) : ℂ) + z * ((y1 + y2 - y4 - y5 + y7 + y8 - y10 - y11 : ℝ) : ℂ) := by
      push_cast
      linear_combination ((y2 : ℂ) * ((1) * z ^ 0) + (y3 : ℂ) * ((1) * z ^ 0 + (1) * z ^ 1) + (y4 : ℂ) * ((1) * z ^ 1 + (1) * z ^ 2) + (y5 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 2 + (1) * z ^ 3) + (y6 : ℂ) * ((-1) * z ^ 0 + (-1) * z ^ 1 + (1) * z ^ 3 + (1) * z ^ 4) + (y7 : ℂ) * ((-1) * z ^ 1 + (-1) * z ^ 2 + (1) * z ^ 4 + (1) * z ^ 5) + (y8 : ℂ) * ((1) * z ^ 0 + (-1) * z ^ 2 + (-1) * z ^ 3 + (1) * z ^ 5 + (1) * z ^ 6) + (y9 : ℂ) * ((1) * z ^ 0 + (1) * z ^ 1 + (-1) * z ^ 3 + (-1) * z ^ 4 + (1) * z ^ 6 + (1) * z ^ 7) + (y10 : ℂ) * ((1) * z ^ 1 + (1) * z ^ 2 + (-1) * z ^ 4 + (-1) * z ^ 5 + (1) * z ^ 7 + (1) * z ^ 8) + (y11 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 2 + (1) * z ^ 3 + (-1) * z ^ 5 + (-1) * z ^ 6 + (1) * z ^ 8 + (1) * z ^ 9)) * h
    rw [e, hr, hre]
  · right; right; right; right
    obtain ⟨hs, h2, h3⟩ := re_of_twelfth h
    refine ⟨z.re, hs, ?_⟩
    have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ) + z ^ 8 * (y8 : ℂ) + z ^ 9 * (y9 : ℂ) + z ^ 10 * (y10 : ℂ) + z ^ 11 * (y11 : ℂ))
        = ((y0 - y4 - y6 + y10 : ℝ) : ℂ) + z * ((y1 - y5 - y7 + y11 : ℝ) : ℂ)
          + z ^ 2 * ((y2 + y4 - y8 - y10 : ℝ) : ℂ) + z ^ 3 * ((y3 + y5 - y9 - y11 : ℝ) : ℂ) := by
      push_cast
      linear_combination ((y4 : ℂ) * ((1) * z ^ 0) + (y5 : ℂ) * ((1) * z ^ 1) + (y6 : ℂ) * ((1) * z ^ 0 + (1) * z ^ 2) + (y7 : ℂ) * ((1) * z ^ 1 + (1) * z ^ 3) + (y8 : ℂ) * ((1) * z ^ 2 + (1) * z ^ 4) + (y9 : ℂ) * ((1) * z ^ 3 + (1) * z ^ 5) + (y10 : ℂ) * ((-1) * z ^ 0 + (1) * z ^ 4 + (1) * z ^ 6) + (y11 : ℂ) * ((-1) * z ^ 1 + (1) * z ^ 5 + (1) * z ^ 7)) * h
    rw [e, Complex.add_re, Complex.add_re, hr, Complex.re_mul_ofReal, Complex.re_mul_ofReal,
      h2, h3]
    ring

/-- The kernel polynomial modulo 13 in terms of the value of `χ` at the generator 2. -/
private theorem sum_13 (χ : DirichletCharacter ℂ 13) (x : ℝ) :
    ∑ a ∈ range 13, χ ((a : ℕ) : ZMod 13) * (x : ℂ) ^ a =
      ((x ^ 1 : ℝ) : ℂ) + χ (2 : ZMod 13) * ((x ^ 2 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 2 * ((x ^ 4 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 3 * ((x ^ 8 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 4 * ((x ^ 3 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 5 * ((x ^ 6 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 6 * ((x ^ 12 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 7 * ((x ^ 11 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 8 * ((x ^ 9 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 9 * ((x ^ 5 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 10 * ((x ^ 10 : ℝ) : ℂ)
      + χ (2 : ZMod 13) ^ 11 * ((x ^ 7 : ℝ) : ℂ) := by
  have h0 : χ ((0 : ℕ) : ZMod 13) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h1 : χ ((1 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 0 := by
    rw [show ((1 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 0 from by decide, map_pow]
  have h2 : χ ((2 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 1 := by
    rw [show ((2 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 1 from by decide, map_pow]
  have h3 : χ ((3 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 4 := by
    rw [show ((3 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 4 from by decide, map_pow]
  have h4 : χ ((4 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 2 := by
    rw [show ((4 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 2 from by decide, map_pow]
  have h5 : χ ((5 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 9 := by
    rw [show ((5 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 9 from by decide, map_pow]
  have h6 : χ ((6 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 5 := by
    rw [show ((6 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 5 from by decide, map_pow]
  have h7 : χ ((7 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 11 := by
    rw [show ((7 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 11 from by decide, map_pow]
  have h8 : χ ((8 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 3 := by
    rw [show ((8 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 3 from by decide, map_pow]
  have h9 : χ ((9 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 8 := by
    rw [show ((9 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 8 from by decide, map_pow]
  have h10 : χ ((10 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 10 := by
    rw [show ((10 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 10 from by decide, map_pow]
  have h11 : χ ((11 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 7 := by
    rw [show ((11 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 7 from by decide, map_pow]
  have h12 : χ ((12 : ℕ) : ZMod 13) = χ (2 : ZMod 13) ^ 6 := by
    rw [show ((12 : ℕ) : ZMod 13) = (2 : ZMod 13) ^ 6 from by decide, map_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  push_cast
  ring

/-- The value of a non principal character modulo 13 at the generator 2 is a twelfth root of
unity different from 1. -/
private theorem hz_13 (χ : DirichletCharacter ℂ 13) (hχ : χ ≠ 1) :
    1 + χ (2 : ZMod 13) + χ (2 : ZMod 13) ^ 2 + χ (2 : ZMod 13) ^ 3 + χ (2 : ZMod 13) ^ 4
      + χ (2 : ZMod 13) ^ 5 + χ (2 : ZMod 13) ^ 6 + χ (2 : ZMod 13) ^ 7 + χ (2 : ZMod 13) ^ 8
      + χ (2 : ZMod 13) ^ 9 + χ (2 : ZMod 13) ^ 10 + χ (2 : ZMod 13) ^ 11 = 0 := by
  have h := sum_13 χ 1
  rw [sum_range_eq_zero χ hχ] at h
  simp only [one_pow, Complex.ofReal_one, mul_one] at h
  linear_combination -h

end ThirteenAux

open ThirteenAux in
/-- PROVED. `L(σ, χ) ≠ 0` for every non principal character modulo 13 and every real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_mod_13 (χ : DirichletCharacter ℂ 13) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((1 : ℂ) * ∑ a ∈ Finset.range 13, χ ((a : ℕ) : ZMod 13) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    have h1 : 0 < 1 - x := by linarith
    rw [sum_13 χ x]
    rcases re_twelve (χ (2 : ZMod 13)) (hz_13 χ hχ) (x ^ 1) (x ^ 2) (x ^ 4) (x ^ 8) (x ^ 3) (x ^ 6) (x ^ 12) (x ^ 11) (x ^ 9) (x ^ 5) (x ^ 10) (x ^ 7)
      with h | h | h | h | ⟨s, hs, h⟩
    · rw [h]
      have hp : 0 < x * (1 - x) ^ 2 * (1 + x + 2 * x ^ 2 + 4 * x ^ 3 + 5 * x ^ 4 + 5 * x ^ 5
          + 4 * x ^ 6 + 2 * x ^ 7 + x ^ 8 + x ^ 9) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) * (1 + x + 2 * x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 + x ^ 7
          + 2 * x ^ 8 + x ^ 9 + x ^ 10) :=
        mul_pos (mul_pos hx h1) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) ^ 2 * (1 + (3/2) * x + (3/2) * x ^ 2 + x ^ 3 + (3/2) * x ^ 4
          + (3/2) * x ^ 5 + x ^ 6 + (3/2) * x ^ 7 + (3/2) * x ^ 8 + x ^ 9) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) ^ 2 * (1 + (5/2) * x + (7/2) * x ^ 2 + 4 * x ^ 3 + (7/2) * x ^ 4
          + (7/2) * x ^ 5 + 4 * x ^ 6 + (7/2) * x ^ 7 + (5/2) * x ^ 8 + x ^ 9) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hs1 : -1 < s := by nlinarith [sq_nonneg (s + 1)]
      have hx2 : x ^ 2 < 1 := pow_lt_one₀ hx.le hx1 (by norm_num)
      have hx8 : x ^ 8 < 1 := pow_lt_one₀ hx.le hx1 (by norm_num)
      have hA : 0 ≤ (1 + s) * (x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 6 + x ^ 7 + x ^ 8 + x ^ 9) :=
        mul_nonneg (by linarith) (by positivity)
      have hx5 : 0 < x ^ 5 := pow_pos hx 5
      have hx10 : 0 < x ^ 10 := pow_pos hx 10
      have hR : 0 < (1 + s) * (x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 6 + x ^ 7 + x ^ 8 + x ^ 9)
          + (1 - x ^ 2) / 2 + (1 - x ^ 8) / 2 + x ^ 5 + x ^ 10 := by linarith
      have hp := mul_pos (mul_pos hx h1) hR
      refine lt_of_lt_of_eq hp ?_
      ring
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ 1 (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key _ (by norm_num) (by norm_num)⟩ hσ

end LeanLab.HelfgottMajor.RealAxisKernel

#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_13
