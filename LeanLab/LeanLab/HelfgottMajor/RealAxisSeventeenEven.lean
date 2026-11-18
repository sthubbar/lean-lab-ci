import LeanLab.HelfgottMajor.RealAxisKernel

/-!
# Nonvanishing of `L(σ, χ)` on the positive real axis for the even characters modulo 17

What is proved: for every non principal Dirichlet character `χ` modulo 17 with `χ(3)^8 = 1`,
that is for the seven even non principal characters, and every real `σ > 0`, `L(σ, χ) ≠ 0`.
The unit group modulo 17 is cyclic of order 16 with generator 3, so `χ` is determined by
`z = χ(3)`, here an eighth root of unity different from 1. In each of the three cases `z = -1`,
`z^2 + 1 = 0`, `z^4 + 1 = 0` the real part of `∑_{a < 17} χ(a) x^a` is an explicit real
polynomial which factors exactly as `x (1 - x)^2 R(x)` with `R` positive on the open unit
interval, so the kernel criterion of `RealAxisKernel` applies with the constant `c = 1` for all
seven characters. In the last case the coefficients involve the real part `s` of `z`, with
`s^2 = 1/2`, and only `-1 < s` is needed.

This is standard mathematics. AI wrote this Lean code. The binary Goldbach conjecture is open
and nothing here changes that.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

namespace SeventeenEvenAux

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

/-- A root of `z^4 + 1` has real part of square `1/2`, its square has real part `0` and its cube
has real part the negative of the real part of `z`. -/
private theorem re_of_eighth {z : ℂ} (h : z ^ 4 + 1 = 0) :
    z.re ^ 2 = 1 / 2 ∧ (z ^ 2).re = 0 ∧ (z ^ 3).re = -z.re := by
  have hw : (z ^ 2) ^ 2 + 1 = 0 := by linear_combination h
  have hwre := re_of_i hw
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hsqi : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]; ring
  have h1 := congrArg Complex.re hw
  rw [Complex.add_re, pow_two (z ^ 2), Complex.mul_re, hsq, hsqi, Complex.one_re,
    Complex.zero_re] at h1
  have hb : z.im ^ 2 = z.re ^ 2 := by rw [hsq] at hwre; linarith
  have hq : (2 * z.re ^ 2 - 1) * (2 * z.re ^ 2 + 1) = 0 := by
    linear_combination (-1) * h1 + (z.im ^ 2 - 5 * z.re ^ 2) * hb
  have ha : z.re ^ 2 = 1 / 2 := by
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

/-- For an eighth root of unity `z ≠ 1` the real part of a real combination of the powers of
`z` is one of three explicit real combinations, the last one involving a real number `s` with
`s ^ 2 = 1 / 2`, namely the real part of `z`. -/
private theorem re_eight (z : ℂ)
    (hz : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7 = 0)
    (y0 y1 y2 y3 y4 y5 y6 y7 : ℝ) :
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ))).re = y0 - y1 + y2 - y3 + y4 - y5 + y6 - y7 ∨
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ))).re = y0 - y2 + y4 - y6 ∨
    ∃ s : ℝ, s ^ 2 = 1 / 2 ∧
    ((1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ))).re = (y0 - y4) + s * (y1 - y3 - y5 + y7) := by
  have hr : ∀ (w : ℂ) (U V : ℝ), ((U : ℂ) + w * (V : ℂ)).re = U + w.re * V := by
    intro w U V
    simp
  have hf : (z + 1) * ((z ^ 2 + 1) * (z ^ 4 + 1)) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hz1 : z = -1 := by linear_combination h
    subst hz1
    have e : (1 : ℂ) * ((y0 : ℂ) + (-1) * (y1 : ℂ) + (-1) ^ 2 * (y2 : ℂ) + (-1) ^ 3 * (y3 : ℂ) + (-1) ^ 4 * (y4 : ℂ) + (-1) ^ 5 * (y5 : ℂ) + (-1) ^ 6 * (y6 : ℂ) + (-1) ^ 7 * (y7 : ℂ))
        = ((y0 - y1 + y2 - y3 + y4 - y5 + y6 - y7 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  rcases mul_eq_zero.mp h with h | h
  · right; left
    have hre := re_of_i h
    have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ))
        = ((y0 - y2 + y4 - y6 : ℝ) : ℂ) + z * ((y1 - y3 + y5 - y7 : ℝ) : ℂ) := by
      push_cast
      linear_combination ((y2 : ℂ) + (y3 : ℂ) * z + (y4 : ℂ) * (z ^ 2 - 1)
        + (y5 : ℂ) * (z * (z ^ 2 - 1)) + (y6 : ℂ) * (z ^ 4 - z ^ 2 + 1)
        + (y7 : ℂ) * (z * (z ^ 4 - z ^ 2 + 1))) * h
    rw [e, hr, hre]
    ring
  · right; right
    obtain ⟨hs, h2, h3⟩ := re_of_eighth h
    refine ⟨z.re, hs, ?_⟩
    have e : (1 : ℂ) * ((y0 : ℂ) + z * (y1 : ℂ) + z ^ 2 * (y2 : ℂ) + z ^ 3 * (y3 : ℂ) + z ^ 4 * (y4 : ℂ) + z ^ 5 * (y5 : ℂ) + z ^ 6 * (y6 : ℂ) + z ^ 7 * (y7 : ℂ))
        = ((y0 - y4 : ℝ) : ℂ) + z * ((y1 - y5 : ℝ) : ℂ)
          + z ^ 2 * ((y2 - y6 : ℝ) : ℂ) + z ^ 3 * ((y3 - y7 : ℝ) : ℂ) := by
      push_cast
      linear_combination ((y4 : ℂ) + (y5 : ℂ) * z + (y6 : ℂ) * z ^ 2 + (y7 : ℂ) * z ^ 3) * h
    rw [e, Complex.add_re, Complex.add_re, hr, Complex.re_mul_ofReal, Complex.re_mul_ofReal,
      h2, h3]
    ring

/-- The kernel polynomial modulo 17 for an even character, in terms of the value of `χ` at the
generator 3. -/
private theorem sum_17 (χ : DirichletCharacter ℂ 17) (h : χ (3 : ZMod 17) ^ 8 = 1) (x : ℝ) :
    ∑ a ∈ range 17, χ ((a : ℕ) : ZMod 17) * (x : ℂ) ^ a =
      ((x ^ 1 + x ^ 16 : ℝ) : ℂ) + χ (3 : ZMod 17) * ((x ^ 3 + x ^ 14 : ℝ) : ℂ)
      + χ (3 : ZMod 17) ^ 2 * ((x ^ 8 + x ^ 9 : ℝ) : ℂ)
      + χ (3 : ZMod 17) ^ 3 * ((x ^ 7 + x ^ 10 : ℝ) : ℂ)
      + χ (3 : ZMod 17) ^ 4 * ((x ^ 4 + x ^ 13 : ℝ) : ℂ)
      + χ (3 : ZMod 17) ^ 5 * ((x ^ 5 + x ^ 12 : ℝ) : ℂ)
      + χ (3 : ZMod 17) ^ 6 * ((x ^ 2 + x ^ 15 : ℝ) : ℂ)
      + χ (3 : ZMod 17) ^ 7 * ((x ^ 6 + x ^ 11 : ℝ) : ℂ) := by
  have h0 : χ ((0 : ℕ) : ZMod 17) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h1 : χ ((1 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 0 := by
    rw [show ((1 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 0 from by decide, map_pow]
  have h2 : χ ((2 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 14 := by
    rw [show ((2 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 14 from by decide, map_pow]
  have h3 : χ ((3 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 1 := by
    rw [show ((3 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 1 from by decide, map_pow]
  have h4 : χ ((4 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 12 := by
    rw [show ((4 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 12 from by decide, map_pow]
  have h5 : χ ((5 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 5 := by
    rw [show ((5 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 5 from by decide, map_pow]
  have h6 : χ ((6 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 15 := by
    rw [show ((6 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 15 from by decide, map_pow]
  have h7 : χ ((7 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 11 := by
    rw [show ((7 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 11 from by decide, map_pow]
  have h8 : χ ((8 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 10 := by
    rw [show ((8 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 10 from by decide, map_pow]
  have h9 : χ ((9 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 2 := by
    rw [show ((9 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 2 from by decide, map_pow]
  have h10 : χ ((10 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 3 := by
    rw [show ((10 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 3 from by decide, map_pow]
  have h11 : χ ((11 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 7 := by
    rw [show ((11 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 7 from by decide, map_pow]
  have h12 : χ ((12 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 13 := by
    rw [show ((12 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 13 from by decide, map_pow]
  have h13 : χ ((13 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 4 := by
    rw [show ((13 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 4 from by decide, map_pow]
  have h14 : χ ((14 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 9 := by
    rw [show ((14 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 9 from by decide, map_pow]
  have h15 : χ ((15 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 6 := by
    rw [show ((15 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 6 from by decide, map_pow]
  have h16 : χ ((16 : ℕ) : ZMod 17) = χ (3 : ZMod 17) ^ 8 := by
    rw [show ((16 : ℕ) : ZMod 17) = (3 : ZMod 17) ^ 8 from by decide, map_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  push_cast
  linear_combination (χ (3 : ZMod 17) ^ 6 * (x : ℂ) ^ 2 + χ (3 : ZMod 17) ^ 4 * (x : ℂ) ^ 4
    + χ (3 : ZMod 17) ^ 7 * (x : ℂ) ^ 6 + χ (3 : ZMod 17) ^ 3 * (x : ℂ) ^ 7
    + χ (3 : ZMod 17) ^ 2 * (x : ℂ) ^ 8 + χ (3 : ZMod 17) ^ 5 * (x : ℂ) ^ 12
    + χ (3 : ZMod 17) * (x : ℂ) ^ 14 + (x : ℂ) ^ 16) * h

/-- The value of a non principal even character modulo 17 at the generator 3 is an eighth root
of unity different from 1. -/
private theorem hz_17 (χ : DirichletCharacter ℂ 17) (hχ : χ ≠ 1)
    (h8 : χ (3 : ZMod 17) ^ 8 = 1) :
    1 + χ (3 : ZMod 17) + χ (3 : ZMod 17) ^ 2 + χ (3 : ZMod 17) ^ 3 + χ (3 : ZMod 17) ^ 4
      + χ (3 : ZMod 17) ^ 5 + χ (3 : ZMod 17) ^ 6 + χ (3 : ZMod 17) ^ 7 = 0 := by
  have h := sum_17 χ h8 1
  rw [sum_range_eq_zero χ hχ] at h
  simp only [one_pow, Complex.ofReal_add, Complex.ofReal_one] at h
  linear_combination -h / 2

end SeventeenEvenAux

open SeventeenEvenAux in
/-- PROVED. `L(σ, χ) ≠ 0` for every non principal even character modulo 17, that is with
`χ(3)^8 = 1`, and every real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_mod_17_even (χ : DirichletCharacter ℂ 17) (hχ : χ ≠ 1) (h : χ (3 : ZMod 17) ^ 8 = 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((1 : ℂ) * ∑ a ∈ Finset.range 17, χ ((a : ℕ) : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    have h1 : 0 < 1 - x := by linarith
    rw [sum_17 χ h x]
    rcases re_eight (χ (3 : ZMod 17)) (hz_17 χ hχ h) (x ^ 1 + x ^ 16) (x ^ 3 + x ^ 14)
      (x ^ 8 + x ^ 9) (x ^ 7 + x ^ 10) (x ^ 4 + x ^ 13) (x ^ 5 + x ^ 12) (x ^ 2 + x ^ 15)
      (x ^ 6 + x ^ 11) with h' | h' | ⟨s, hs, h'⟩
    · rw [h']
      have hp : 0 < x * (1 - x) ^ 2 * (1 + 3 * x + 4 * x ^ 2 + 6 * x ^ 3 + 7 * x ^ 4
          + 7 * x ^ 5 + 6 * x ^ 6 + 6 * x ^ 7 + 7 * x ^ 8 + 7 * x ^ 9 + 6 * x ^ 10 + 4 * x ^ 11
          + 3 * x ^ 12 + x ^ 13) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h']
      have hp : 0 < x * (1 - x) ^ 2 * (1 + x + x ^ 2 + 2 * x ^ 3 + 3 * x ^ 4 + 4 * x ^ 5
          + 5 * x ^ 6 + 5 * x ^ 7 + 4 * x ^ 8 + 3 * x ^ 9 + 2 * x ^ 10 + x ^ 11 + x ^ 12
          + x ^ 13) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by positivity)
      refine lt_of_lt_of_eq hp ?_
      ring
    · rw [h']
      have hs1 : -1 < s := by nlinarith [sq_nonneg (s + 1)]
      have hA : 0 ≤ (1 + s) * (x ^ 2 + 2 * x ^ 3 + 2 * x ^ 4 + 3 * x ^ 5 + 3 * x ^ 6
          + 3 * x ^ 7 + 3 * x ^ 8 + 2 * x ^ 9 + 2 * x ^ 10 + x ^ 11) :=
        mul_nonneg (by linarith) (by positivity)
      have hB : 0 < 1 + 2 * x + 2 * x ^ 2 + x ^ 3 + x ^ 4 + x ^ 9 + x ^ 10 + 2 * x ^ 11
          + 2 * x ^ 12 + x ^ 13 := by positivity
      have hp : 0 < x * (1 - x) ^ 2 * ((1 + 2 * x + 2 * x ^ 2 + x ^ 3 + x ^ 4 + x ^ 9 + x ^ 10
          + 2 * x ^ 11 + 2 * x ^ 12 + x ^ 13)
          + (1 + s) * (x ^ 2 + 2 * x ^ 3 + 2 * x ^ 4 + 3 * x ^ 5 + 3 * x ^ 6
          + 3 * x ^ 7 + 3 * x ^ 8 + 2 * x ^ 9 + 2 * x ^ 10 + x ^ 11)) :=
        mul_pos (mul_pos hx (pow_pos h1 2)) (by linarith)
      refine lt_of_lt_of_eq hp ?_
      ring
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ 1 (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_17_even
