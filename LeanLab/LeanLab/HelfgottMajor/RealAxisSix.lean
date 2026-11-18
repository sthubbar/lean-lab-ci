import LeanLab.HelfgottMajor.RealAxisKernel

/-!
# Nonvanishing of `L(σ, χ)` on the positive real axis for the moduli 7, 9 and 14

For every non principal Dirichlet character `χ` modulo 7, 9 or 14 and every real `σ > 0` we
prove `L(σ, χ) ≠ 0`. The unit groups are cyclic of order 6, so `χ` is determined by the value
`z` of `χ` at a generator, a sixth root of unity different from 1. In each of the three cases
`z = -1`, `z^2 + z + 1 = 0`, `z^2 - z + 1 = 0` the real part of `∑_{a < q} χ(a) x^a` is an
explicit rational polynomial which factors as `x (1 - x)^k R(x)` with `R` having nonnegative
coefficients, so the kernel criterion of `RealAxisKernel` applies with the constant `c = 1`.

This is standard mathematics. AI wrote this Lean code. The binary Goldbach conjecture is open
and nothing here changes that.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

namespace SixAux

open Finset

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

/-- For a sixth root of unity `z ≠ 1` the real part of a real combination of the powers of `z`
is one of three explicit real combinations. -/
private theorem re_six (z : ℂ) (hz : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 = 0)
    (y0 y1 y2 y3 y4 y5 : ℝ) :
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ)
        + z ^ 5 * (y5 : ℂ))).re = y0 - y1 + y2 - y3 + y4 - y5 ∨
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ)
        + z ^ 5 * (y5 : ℂ))).re = (y0 - y2 + y3 - y5) + (-1 / 2) * (y1 - y2 + y4 - y5) ∨
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ)
        + z ^ 5 * (y5 : ℂ))).re = (y0 - y2 - y3 + y5) + (1 / 2) * (y1 + y2 - y4 - y5) := by
  have hr : ∀ (w : ℂ) (U V : ℝ), ((U : ℂ) + w * (V : ℂ)).re = U + w.re * V := by
    intro w U V
    simp
  have hf : (z + 1) * ((z ^ 2 + z + 1) * (z ^ 2 - z + 1)) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hz1 : z = -1 := by linear_combination h
    subst hz1
    have e : (1 : ℂ) * ((y0 : ℂ) + (-1) * (y1 : ℂ) + (-1) ^ 2 * (y2 : ℂ) + (-1) ^ 3 * (y3 : ℂ)
        + (-1) ^ 4 * (y4 : ℂ) + (-1) ^ 5 * (y5 : ℂ))
        = ((y0 - y1 + y2 - y3 + y4 - y5 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  · rcases mul_eq_zero.mp h with h | h
    · right; left
      have hre := re_of_omega h
      have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ)
          + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ))
          = ((y0 - y2 + y3 - y5 : ℝ) : ℂ) + z * ((y1 - y2 + y4 - y5 : ℝ) : ℂ) := by
        push_cast
        linear_combination ((y2 : ℂ) + y3 * (z - 1) + y4 * (z * (z - 1))
          + y5 * (z ^ 3 - z ^ 2 + 1)) * h
      rw [e, hr, hre]
    · right; right
      have hre := re_of_zeta h
      have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ)
          + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ))
          = ((y0 - y2 - y3 + y5 : ℝ) : ℂ) + z * ((y1 + y2 - y4 - y5 : ℝ) : ℂ) := by
        push_cast
        linear_combination ((y2 : ℂ) + y3 * (z + 1) + y4 * (z * (z + 1))
          + y5 * (z ^ 3 + z ^ 2 - 1)) * h
      rw [e, hr, hre]

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

/-- The kernel polynomial modulo 7 in terms of the value of `χ` at the generator 3. -/
private theorem sum_7 (χ : DirichletCharacter ℂ 7) (x : ℝ) :
    ∑ a ∈ range 7, χ ((a : ℕ) : ZMod 7) * (x : ℂ) ^ a =
      ((x ^ 1 : ℝ) : ℂ) + χ (3 : ZMod 7) * ((x ^ 3 : ℝ) : ℂ)
      + χ (3 : ZMod 7) ^ 2 * ((x ^ 2 : ℝ) : ℂ)
      + χ (3 : ZMod 7) ^ 3 * ((x ^ 6 : ℝ) : ℂ)
      + χ (3 : ZMod 7) ^ 4 * ((x ^ 4 : ℝ) : ℂ)
      + χ (3 : ZMod 7) ^ 5 * ((x ^ 5 : ℝ) : ℂ) := by
  have h0 : χ ((0 : ℕ) : ZMod 7) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h1 : χ ((1 : ℕ) : ZMod 7) = χ (3 : ZMod 7) ^ 0 := by
    rw [show ((1 : ℕ) : ZMod 7) = (3 : ZMod 7) ^ 0 from by decide, map_pow]
  have h2 : χ ((2 : ℕ) : ZMod 7) = χ (3 : ZMod 7) ^ 2 := by
    rw [show ((2 : ℕ) : ZMod 7) = (3 : ZMod 7) ^ 2 from by decide, map_pow]
  have h3 : χ ((3 : ℕ) : ZMod 7) = χ (3 : ZMod 7) ^ 1 := by
    rw [show ((3 : ℕ) : ZMod 7) = (3 : ZMod 7) ^ 1 from by decide, map_pow]
  have h4 : χ ((4 : ℕ) : ZMod 7) = χ (3 : ZMod 7) ^ 4 := by
    rw [show ((4 : ℕ) : ZMod 7) = (3 : ZMod 7) ^ 4 from by decide, map_pow]
  have h5 : χ ((5 : ℕ) : ZMod 7) = χ (3 : ZMod 7) ^ 5 := by
    rw [show ((5 : ℕ) : ZMod 7) = (3 : ZMod 7) ^ 5 from by decide, map_pow]
  have h6 : χ ((6 : ℕ) : ZMod 7) = χ (3 : ZMod 7) ^ 3 := by
    rw [show ((6 : ℕ) : ZMod 7) = (3 : ZMod 7) ^ 3 from by decide, map_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6]
  push_cast
  ring

/-- The value of a non principal character modulo 7 at the generator 3 is a sixth root of
unity different from 1. -/
private theorem hz_7 (χ : DirichletCharacter ℂ 7) (hχ : χ ≠ 1) :
    1 + χ (3 : ZMod 7) + χ (3 : ZMod 7) ^ 2 + χ (3 : ZMod 7) ^ 3 + χ (3 : ZMod 7) ^ 4 + χ (3 : ZMod 7) ^ 5 = 0 := by
  have h := sum_7 χ 1
  rw [sum_range_eq_zero χ hχ] at h
  simp only [one_pow, Complex.ofReal_one, mul_one] at h
  linear_combination -h

end SixAux

open SixAux in
/-- PROVED. `L(σ, χ) ≠ 0` for every non principal character modulo 7 and every real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_mod_7 (χ : DirichletCharacter ℂ 7) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((1 : ℂ) * ∑ a ∈ Finset.range 7, χ ((a : ℕ) : ZMod 7) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    have h1 : 0 < 1 - x := by linarith
    rw [sum_7 χ x]
    rcases re_six (χ (3 : ZMod 7)) (hz_7 χ hχ) (x ^ 1) (x ^ 3) (x ^ 2) (x ^ 6) (x ^ 4) (x ^ 5) with h | h | h
    · rw [h]
      have hp : 0 < x * (1 - x) * (1 + 2 * x + x ^ 2 + 2 * x ^ 3 + x ^ 4) :=
        mul_pos (mul_pos hx h1) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) ^ 2 * (1 + (3/2) * x + (3/2) * x ^ 2 + x ^ 3) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) * (1 + (1/2) * x + x ^ 2 + (1/2) * x ^ 3 + x ^ 4) :=
        mul_pos (mul_pos hx h1) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ 1 (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key _ (by norm_num) (by norm_num)⟩ hσ

namespace SixAux

open Finset

/-- The kernel polynomial modulo 9 in terms of the value of `χ` at the generator 2. -/
private theorem sum_9 (χ : DirichletCharacter ℂ 9) (x : ℝ) :
    ∑ a ∈ range 9, χ ((a : ℕ) : ZMod 9) * (x : ℂ) ^ a =
      ((x ^ 1 : ℝ) : ℂ) + χ (2 : ZMod 9) * ((x ^ 2 : ℝ) : ℂ)
      + χ (2 : ZMod 9) ^ 2 * ((x ^ 4 : ℝ) : ℂ)
      + χ (2 : ZMod 9) ^ 3 * ((x ^ 8 : ℝ) : ℂ)
      + χ (2 : ZMod 9) ^ 4 * ((x ^ 7 : ℝ) : ℂ)
      + χ (2 : ZMod 9) ^ 5 * ((x ^ 5 : ℝ) : ℂ) := by
  have h0 : χ ((0 : ℕ) : ZMod 9) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h1 : χ ((1 : ℕ) : ZMod 9) = χ (2 : ZMod 9) ^ 0 := by
    rw [show ((1 : ℕ) : ZMod 9) = (2 : ZMod 9) ^ 0 from by decide, map_pow]
  have h2 : χ ((2 : ℕ) : ZMod 9) = χ (2 : ZMod 9) ^ 1 := by
    rw [show ((2 : ℕ) : ZMod 9) = (2 : ZMod 9) ^ 1 from by decide, map_pow]
  have h3 : χ ((3 : ℕ) : ZMod 9) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h4 : χ ((4 : ℕ) : ZMod 9) = χ (2 : ZMod 9) ^ 2 := by
    rw [show ((4 : ℕ) : ZMod 9) = (2 : ZMod 9) ^ 2 from by decide, map_pow]
  have h5 : χ ((5 : ℕ) : ZMod 9) = χ (2 : ZMod 9) ^ 5 := by
    rw [show ((5 : ℕ) : ZMod 9) = (2 : ZMod 9) ^ 5 from by decide, map_pow]
  have h6 : χ ((6 : ℕ) : ZMod 9) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h7 : χ ((7 : ℕ) : ZMod 9) = χ (2 : ZMod 9) ^ 4 := by
    rw [show ((7 : ℕ) : ZMod 9) = (2 : ZMod 9) ^ 4 from by decide, map_pow]
  have h8 : χ ((8 : ℕ) : ZMod 9) = χ (2 : ZMod 9) ^ 3 := by
    rw [show ((8 : ℕ) : ZMod 9) = (2 : ZMod 9) ^ 3 from by decide, map_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  push_cast
  ring

/-- The value of a non principal character modulo 9 at the generator 2 is a sixth root of
unity different from 1. -/
private theorem hz_9 (χ : DirichletCharacter ℂ 9) (hχ : χ ≠ 1) :
    1 + χ (2 : ZMod 9) + χ (2 : ZMod 9) ^ 2 + χ (2 : ZMod 9) ^ 3 + χ (2 : ZMod 9) ^ 4 + χ (2 : ZMod 9) ^ 5 = 0 := by
  have h := sum_9 χ 1
  rw [sum_range_eq_zero χ hχ] at h
  simp only [one_pow, Complex.ofReal_one, mul_one] at h
  linear_combination -h

end SixAux

open SixAux in
/-- PROVED. `L(σ, χ) ≠ 0` for every non principal character modulo 9 and every real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_mod_9 (χ : DirichletCharacter ℂ 9) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((1 : ℂ) * ∑ a ∈ Finset.range 9, χ ((a : ℕ) : ZMod 9) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    have h1 : 0 < 1 - x := by linarith
    rw [sum_9 χ x]
    rcases re_six (χ (2 : ZMod 9)) (hz_9 χ hχ) (x ^ 1) (x ^ 2) (x ^ 4) (x ^ 8) (x ^ 7) (x ^ 5) with h | h | h
    · rw [h]
      have hp : 0 < x * (1 - x) * (1 + x ^ 3 + x ^ 6) :=
        mul_pos (mul_pos hx h1) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) ^ 2 * (1 + (3/2) * x + 2 * x ^ 2 + 2 * x ^ 3 + (3/2) * x ^ 4 + x ^ 5) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) * (1 + (3/2) * x + (3/2) * x ^ 2 + x ^ 3 + (3/2) * x ^ 4 + (3/2) * x ^ 5 + x ^ 6) :=
        mul_pos (mul_pos hx h1) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ 1 (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key _ (by norm_num) (by norm_num)⟩ hσ

namespace SixAux

open Finset

/-- The kernel polynomial modulo 14 in terms of the value of `χ` at the generator 3. -/
private theorem sum_14 (χ : DirichletCharacter ℂ 14) (x : ℝ) :
    ∑ a ∈ range 14, χ ((a : ℕ) : ZMod 14) * (x : ℂ) ^ a =
      ((x ^ 1 : ℝ) : ℂ) + χ (3 : ZMod 14) * ((x ^ 3 : ℝ) : ℂ)
      + χ (3 : ZMod 14) ^ 2 * ((x ^ 9 : ℝ) : ℂ)
      + χ (3 : ZMod 14) ^ 3 * ((x ^ 13 : ℝ) : ℂ)
      + χ (3 : ZMod 14) ^ 4 * ((x ^ 11 : ℝ) : ℂ)
      + χ (3 : ZMod 14) ^ 5 * ((x ^ 5 : ℝ) : ℂ) := by
  have h0 : χ ((0 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h1 : χ ((1 : ℕ) : ZMod 14) = χ (3 : ZMod 14) ^ 0 := by
    rw [show ((1 : ℕ) : ZMod 14) = (3 : ZMod 14) ^ 0 from by decide, map_pow]
  have h2 : χ ((2 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h3 : χ ((3 : ℕ) : ZMod 14) = χ (3 : ZMod 14) ^ 1 := by
    rw [show ((3 : ℕ) : ZMod 14) = (3 : ZMod 14) ^ 1 from by decide, map_pow]
  have h4 : χ ((4 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h5 : χ ((5 : ℕ) : ZMod 14) = χ (3 : ZMod 14) ^ 5 := by
    rw [show ((5 : ℕ) : ZMod 14) = (3 : ZMod 14) ^ 5 from by decide, map_pow]
  have h6 : χ ((6 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h7 : χ ((7 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h8 : χ ((8 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h9 : χ ((9 : ℕ) : ZMod 14) = χ (3 : ZMod 14) ^ 2 := by
    rw [show ((9 : ℕ) : ZMod 14) = (3 : ZMod 14) ^ 2 from by decide, map_pow]
  have h10 : χ ((10 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h11 : χ ((11 : ℕ) : ZMod 14) = χ (3 : ZMod 14) ^ 4 := by
    rw [show ((11 : ℕ) : ZMod 14) = (3 : ZMod 14) ^ 4 from by decide, map_pow]
  have h12 : χ ((12 : ℕ) : ZMod 14) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h13 : χ ((13 : ℕ) : ZMod 14) = χ (3 : ZMod 14) ^ 3 := by
    rw [show ((13 : ℕ) : ZMod 14) = (3 : ZMod 14) ^ 3 from by decide, map_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  push_cast
  ring

/-- The value of a non principal character modulo 14 at the generator 3 is a sixth root of
unity different from 1. -/
private theorem hz_14 (χ : DirichletCharacter ℂ 14) (hχ : χ ≠ 1) :
    1 + χ (3 : ZMod 14) + χ (3 : ZMod 14) ^ 2 + χ (3 : ZMod 14) ^ 3 + χ (3 : ZMod 14) ^ 4 + χ (3 : ZMod 14) ^ 5 = 0 := by
  have h := sum_14 χ 1
  rw [sum_range_eq_zero χ hχ] at h
  simp only [one_pow, Complex.ofReal_one, mul_one] at h
  linear_combination -h

end SixAux

open SixAux in
/-- PROVED. `L(σ, χ) ≠ 0` for every non principal character modulo 14 and every real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_mod_14 (χ : DirichletCharacter ℂ 14) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((1 : ℂ) * ∑ a ∈ Finset.range 14, χ ((a : ℕ) : ZMod 14) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    have h1 : 0 < 1 - x := by linarith
    rw [sum_14 χ x]
    rcases re_six (χ (3 : ZMod 14)) (hz_14 χ hχ) (x ^ 1) (x ^ 3) (x ^ 9) (x ^ 13) (x ^ 11) (x ^ 5) with h | h | h
    · rw [h]
      have hp : 0 < x * (1 - x) ^ 3 * (1 + 3 * x + 5 * x ^ 2 + 7 * x ^ 3 + 8 * x ^ 4 + 8 * x ^ 5 + 7 * x ^ 6 + 5 * x ^ 7 + 3 * x ^ 8 + x ^ 9) :=
        mul_pos (mul_pos hx (pow_pos h1 3)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) ^ 2 * (1 + 2 * x + (5/2) * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 + 3 * x ^ 5 + 3 * x ^ 6 + 3 * x ^ 7 + (5/2) * x ^ 8 + 2 * x ^ 9 + x ^ 10) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h]
      have hp : 0 < x * (1 - x) * (1 + x + (3/2) * x ^ 2 + (3/2) * x ^ 3 + 2 * x ^ 4 + 2 * x ^ 5 + 2 * x ^ 6 + 2 * x ^ 7 + (3/2) * x ^ 8 + (3/2) * x ^ 9 + x ^ 10 + x ^ 11) :=
        mul_pos (mul_pos hx h1) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ 1 (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key _ (by norm_num) (by norm_num)⟩ hσ

end LeanLab.HelfgottMajor.RealAxisKernel

#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_7
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_9
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_14
