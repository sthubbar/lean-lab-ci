import LeanLab.HelfgottMajor.RealAxisKernel

/-!
# Nonvanishing of `L(σ, χ)` on the positive real axis for the modulus 11

For every non principal Dirichlet character `χ` modulo 11 and every real `σ > 0` we prove
`L(σ, χ) ≠ 0`. The unit group is cyclic of order 10 with generator 2, so `χ` is determined by
`z = χ(2)`, a tenth root of unity different from 1. There are three cases: `z = -1`, `z` a root
of `z^4 + z^3 + z^2 + z + 1`, and `z` a root of `z^4 - z^3 + z^2 - z + 1`. In the last two cases
`a = Re z` is a root of `4 a^2 + 2 a - 1` or `4 a^2 - 2 a - 1`, every power of `z` is a real
combination of `1` and `z` with coefficients linear in `a`, and the real part of `c P(x)`, with
`P(x) = ∑_{a < 11} χ(a) x^a`, is `x (1 - x)^k R(x)` where `R` has nonnegative Bernstein
coefficients on the unit interval. The constant is `c = 1`, except for the root with
`a = (1 - sqrt 5)/4`, where `c = 4 - z`. Then the kernel criterion of `RealAxisKernel` applies.

This is standard mathematics. AI wrote this Lean code. The binary Goldbach conjecture is open
and nothing here changes that.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

namespace ElevenAux

open Finset

/-- Real part of a real combination of `1` and `w`. -/
private theorem re_aux (U V : ℝ) (w : ℂ) : ((U : ℂ) + (V : ℂ) * w).re = U + V * w.re := by
  simp

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

/-- The kernel polynomial modulo 11 in terms of the value of `χ` at the generator 2. -/
private theorem sum_11 (χ : DirichletCharacter ℂ 11) (x : ℝ) :
    ∑ a ∈ range 11, χ ((a : ℕ) : ZMod 11) * (x : ℂ) ^ a =
      χ (2 : ZMod 11) ^ 0 * (x : ℂ) ^ 1 + χ (2 : ZMod 11) ^ 1 * (x : ℂ) ^ 2 + χ (2 : ZMod 11) ^ 8 * (x : ℂ) ^ 3 + χ (2 : ZMod 11) ^ 2 * (x : ℂ) ^ 4 + χ (2 : ZMod 11) ^ 4 * (x : ℂ) ^ 5 + χ (2 : ZMod 11) ^ 9 * (x : ℂ) ^ 6 + χ (2 : ZMod 11) ^ 7 * (x : ℂ) ^ 7 + χ (2 : ZMod 11) ^ 3 * (x : ℂ) ^ 8 + χ (2 : ZMod 11) ^ 6 * (x : ℂ) ^ 9 + χ (2 : ZMod 11) ^ 5 * (x : ℂ) ^ 10 := by
  have h0 : χ ((0 : ℕ) : ZMod 11) = 0 :=
    MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; decide)
  have h1 : χ ((1 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 0 := by
    rw [show ((1 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 0 from by decide, map_pow]
  have h2 : χ ((2 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 1 := by
    rw [show ((2 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 1 from by decide, map_pow]
  have h3 : χ ((3 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 8 := by
    rw [show ((3 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 8 from by decide, map_pow]
  have h4 : χ ((4 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 2 := by
    rw [show ((4 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 2 from by decide, map_pow]
  have h5 : χ ((5 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 4 := by
    rw [show ((5 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 4 from by decide, map_pow]
  have h6 : χ ((6 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 9 := by
    rw [show ((6 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 9 from by decide, map_pow]
  have h7 : χ ((7 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 7 := by
    rw [show ((7 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 7 from by decide, map_pow]
  have h8 : χ ((8 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 3 := by
    rw [show ((8 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 3 from by decide, map_pow]
  have h9 : χ ((9 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 6 := by
    rw [show ((9 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 6 from by decide, map_pow]
  have h10 : χ ((10 : ℕ) : ZMod 11) = χ (2 : ZMod 11) ^ 5 := by
    rw [show ((10 : ℕ) : ZMod 11) = (2 : ZMod 11) ^ 5 from by decide, map_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

/-- The value of a non principal character modulo 11 at the generator 2 is a tenth root of
unity different from 1. -/
private theorem hz_11 (χ : DirichletCharacter ℂ 11) (hχ : χ ≠ 1) :
    1 + χ (2 : ZMod 11) + χ (2 : ZMod 11) ^ 2 + χ (2 : ZMod 11) ^ 3 + χ (2 : ZMod 11) ^ 4
      + χ (2 : ZMod 11) ^ 5 + χ (2 : ZMod 11) ^ 6 + χ (2 : ZMod 11) ^ 7 + χ (2 : ZMod 11) ^ 8
      + χ (2 : ZMod 11) ^ 9 = 0 := by
  have h := sum_11 χ 1
  rw [sum_range_eq_zero χ hχ] at h
  simp only [one_pow, Complex.ofReal_one, mul_one] at h
  linear_combination -h

/-- The case `z = -1`, the real character modulo 11. -/
private theorem keyReal (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    0 < ((1 : ℂ) * ((-1 : ℂ) ^ 0 * (x : ℂ) ^ 1 + (-1 : ℂ) ^ 1 * (x : ℂ) ^ 2 + (-1 : ℂ) ^ 8 * (x : ℂ) ^ 3 + (-1 : ℂ) ^ 2 * (x : ℂ) ^ 4 + (-1 : ℂ) ^ 4 * (x : ℂ) ^ 5 + (-1 : ℂ) ^ 9 * (x : ℂ) ^ 6 + (-1 : ℂ) ^ 7 * (x : ℂ) ^ 7 + (-1 : ℂ) ^ 3 * (x : ℂ) ^ 8 + (-1 : ℂ) ^ 6 * (x : ℂ) ^ 9 + (-1 : ℂ) ^ 5 * (x : ℂ) ^ 10)).re := by
  have h1x : 0 < 1 - x := by linarith
  have e : (1 : ℂ) * ((-1 : ℂ) ^ 0 * (x : ℂ) ^ 1 + (-1 : ℂ) ^ 1 * (x : ℂ) ^ 2 + (-1 : ℂ) ^ 8 * (x : ℂ) ^ 3 + (-1 : ℂ) ^ 2 * (x : ℂ) ^ 4 + (-1 : ℂ) ^ 4 * (x : ℂ) ^ 5 + (-1 : ℂ) ^ 9 * (x : ℂ) ^ 6 + (-1 : ℂ) ^ 7 * (x : ℂ) ^ 7 + (-1 : ℂ) ^ 3 * (x : ℂ) ^ 8 + (-1 : ℂ) ^ 6 * (x : ℂ) ^ 9 + (-1 : ℂ) ^ 5 * (x : ℂ) ^ 10)
      = ((x * (1 - x) * (1 + x ^ 2 + 2 * x ^ 3 + 3 * x ^ 4 + 2 * x ^ 5 + x ^ 6 + x ^ 8) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, Complex.ofReal_re]
  exact mul_pos (mul_pos hx h1x) (by positivity)

private theorem keyP5 (z : ℂ) (h : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0) :
    ∃ c : ℂ, ∀ x : ℝ, 0 < x → x < 1 → 0 < (c * (z ^ 0 * (x : ℂ) ^ 1 + z ^ 1 * (x : ℂ) ^ 2 + z ^ 8 * (x : ℂ) ^ 3 + z ^ 2 * (x : ℂ) ^ 4 + z ^ 4 * (x : ℂ) ^ 5 + z ^ 9 * (x : ℂ) ^ 6 + z ^ 7 * (x : ℂ) ^ 7 + z ^ 3 * (x : ℂ) ^ 8 + z ^ 6 * (x : ℂ) ^ 9 + z ^ 5 * (x : ℂ) ^ 10)).re := by
  have h10 : z ^ 10 = 1 := by linear_combination ((z - 1) * (z ^ 5 + 1)) * h
  have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h10 (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at h
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = z.re := ⟨_, rfl⟩
  have e1 : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have e2 : z + (starRingEnd ℂ) z = 2 * (a : ℂ) := by
    rw [Complex.add_conj, ← ha_def]
    norm_num
  have hz2 : z ^ 2 = 2 * (a : ℂ) * z - 1 := by linear_combination z * e2 - e1
  have haC : 4 * (a : ℂ) ^ 2 + 2 * (a : ℂ) - 1 = 0 := by
    have h' : z ^ 2 * (4 * (a : ℂ) ^ 2 + 2 * (a : ℂ) - 1) = 0 := by
      linear_combination h - (2 * (a : ℂ) * z + z ^ 2 + 1 * z + 1) * hz2
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (pow_ne_zero 2 hz0)
    · exact h''
  have ha : 4 * a ^ 2 + 2 * a - 1 = 0 := by exact_mod_cast haC
  have hp2 : z ^ 2 = ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * z + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by linear_combination hz2
  have hp3 : z ^ 3 = ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp2 + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * hz2 + (1 : ℂ) * z * haC
  have hp4 : z ^ 4 = ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp3 + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * hz2 + (-1 : ℂ) * z * haC
  have hp5 : z ^ 5 = ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp4 + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  have hp6 : z ^ 6 = ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp5 + ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  have hp7 : z ^ 7 = ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * z + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp6 + ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  have hp8 : z ^ 8 = ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp7 + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * hz2 + (1 : ℂ) * z * haC
  have hp9 : z ^ 9 = ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp8 + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * hz2 + (-1 : ℂ) * z * haC
  have hp10 : z ^ 10 = ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp9 + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  rcases le_total 0 a with hs | hs
  · have hlo : (30901/100000 : ℝ) < a := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ 4 * a + (80901/25000 : ℝ))]
    have hhi : a < (15451/50000 : ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ 4 * a + (40451/12500 : ℝ))]
    refine ⟨1, fun x hx hx1 => ?_⟩
    have h1x : 0 < 1 - x := by linarith
    have key : 1 * (z ^ 0 * (x : ℂ) ^ 1 + z ^ 1 * (x : ℂ) ^ 2 + z ^ 8 * (x : ℂ) ^ 3 + z ^ 2 * (x : ℂ) ^ 4 + z ^ 4 * (x : ℂ) ^ 5 + z ^ 9 * (x : ℂ) ^ 6 + z ^ 7 * (x : ℂ) ^ 7 + z ^ 3 * (x : ℂ) ^ 8 + z ^ 6 * (x : ℂ) ^ 9 + z ^ 5 * (x : ℂ) ^ 10) =
        ((((1 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 2 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 3 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 4 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 5 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 6 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 7 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 8 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 9 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) +
        ((((0 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 2 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 3 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 4 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 5 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 6 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 7 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 8 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 9 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) * z := by
      push_cast
      linear_combination ((1 : ℂ) * (x : ℂ) ^ 4) * hp2 + ((1 : ℂ) * (x : ℂ) ^ 8) * hp3 + ((1 : ℂ) * (x : ℂ) ^ 5) * hp4 + ((1 : ℂ) * (x : ℂ) ^ 10) * hp5 + ((1 : ℂ) * (x : ℂ) ^ 9) * hp6 + ((1 : ℂ) * (x : ℂ) ^ 7) * hp7 + ((1 : ℂ) * (x : ℂ) ^ 3) * hp8 + ((1 : ℂ) * (x : ℂ) ^ 6) * hp9
    rw [key, re_aux, ← ha_def]
    have c0 : 0 < ((1 : ℝ) + (0 : ℝ) * a) := by linarith
    have c1 : 0 ≤ ((9 : ℝ) + (1 : ℝ) * a) := by linarith
    have c2 : 0 ≤ ((71/2 : ℝ) + (7 : ℝ) * a) := by linarith
    have c3 : 0 ≤ ((80 : ℝ) + (20 : ℝ) * a) := by linarith
    have c4 : 0 ≤ ((225/2 : ℝ) + (30 : ℝ) * a) := by linarith
    have c5 : 0 ≤ ((101 : ℝ) + (26 : ℝ) * a) := by linarith
    have c6 : 0 ≤ ((56 : ℝ) + (14 : ℝ) * a) := by linarith
    have c7 : 0 ≤ ((16 : ℝ) + (4 : ℝ) * a) := by linarith
    have hS : 0 < ((1 : ℝ) + (0 : ℝ) * a) * x ^ 0 * (1 - x) ^ 7 + ((9 : ℝ) + (1 : ℝ) * a) * x ^ 1 * (1 - x) ^ 6 + ((71/2 : ℝ) + (7 : ℝ) * a) * x ^ 2 * (1 - x) ^ 5 + ((80 : ℝ) + (20 : ℝ) * a) * x ^ 3 * (1 - x) ^ 4 + ((225/2 : ℝ) + (30 : ℝ) * a) * x ^ 4 * (1 - x) ^ 3 + ((101 : ℝ) + (26 : ℝ) * a) * x ^ 5 * (1 - x) ^ 2 + ((56 : ℝ) + (14 : ℝ) * a) * x ^ 6 * (1 - x) ^ 1 + ((16 : ℝ) + (4 : ℝ) * a) * x ^ 7 * (1 - x) ^ 0 :=
      (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (mul_pos (mul_pos c0 (pow_pos hx 0)) (pow_pos h1x _))
      (mul_nonneg (mul_nonneg c1 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c2 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c3 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c4 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c5 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c6 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c7 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
    refine lt_of_lt_of_eq (mul_pos (mul_pos hx (pow_pos h1x 2)) hS) ?_
    linear_combination ((0 : ℝ) * x ^ 1 + (0 : ℝ) * x ^ 2 + (1/2 : ℝ) * x ^ 3 + (-1/2 : ℝ) * x ^ 4 + (0 : ℝ) * x ^ 5 + (0 : ℝ) * x ^ 6 + (-1/2 : ℝ) * x ^ 7 + (1/2 : ℝ) * x ^ 8 + (0 : ℝ) * x ^ 9 + (0 : ℝ) * x ^ 10) * ha
  · have hlo : (-40451/50000 : ℝ) < a := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ -(4 * a + (-15451/12500 : ℝ)))]
    have hhi : a < (-80901/100000 : ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ -(4 * a + (-30901/25000 : ℝ)))]
    refine ⟨1, fun x hx hx1 => ?_⟩
    have h1x : 0 < 1 - x := by linarith
    have key : 1 * (z ^ 0 * (x : ℂ) ^ 1 + z ^ 1 * (x : ℂ) ^ 2 + z ^ 8 * (x : ℂ) ^ 3 + z ^ 2 * (x : ℂ) ^ 4 + z ^ 4 * (x : ℂ) ^ 5 + z ^ 9 * (x : ℂ) ^ 6 + z ^ 7 * (x : ℂ) ^ 7 + z ^ 3 * (x : ℂ) ^ 8 + z ^ 6 * (x : ℂ) ^ 9 + z ^ 5 * (x : ℂ) ^ 10) =
        ((((1 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 2 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 3 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 4 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 5 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 6 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 7 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 8 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 9 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) +
        ((((0 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 2 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 3 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 4 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 5 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 6 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 7 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 8 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 9 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) * z := by
      push_cast
      linear_combination ((1 : ℂ) * (x : ℂ) ^ 4) * hp2 + ((1 : ℂ) * (x : ℂ) ^ 8) * hp3 + ((1 : ℂ) * (x : ℂ) ^ 5) * hp4 + ((1 : ℂ) * (x : ℂ) ^ 10) * hp5 + ((1 : ℂ) * (x : ℂ) ^ 9) * hp6 + ((1 : ℂ) * (x : ℂ) ^ 7) * hp7 + ((1 : ℂ) * (x : ℂ) ^ 3) * hp8 + ((1 : ℂ) * (x : ℂ) ^ 6) * hp9
    rw [key, re_aux, ← ha_def]
    have c0 : 0 < ((1 : ℝ) + (0 : ℝ) * a) := by linarith
    have c1 : 0 ≤ ((9 : ℝ) + (1 : ℝ) * a) := by linarith
    have c2 : 0 ≤ ((71/2 : ℝ) + (7 : ℝ) * a) := by linarith
    have c3 : 0 ≤ ((80 : ℝ) + (20 : ℝ) * a) := by linarith
    have c4 : 0 ≤ ((225/2 : ℝ) + (30 : ℝ) * a) := by linarith
    have c5 : 0 ≤ ((101 : ℝ) + (26 : ℝ) * a) := by linarith
    have c6 : 0 ≤ ((56 : ℝ) + (14 : ℝ) * a) := by linarith
    have c7 : 0 ≤ ((16 : ℝ) + (4 : ℝ) * a) := by linarith
    have hS : 0 < ((1 : ℝ) + (0 : ℝ) * a) * x ^ 0 * (1 - x) ^ 7 + ((9 : ℝ) + (1 : ℝ) * a) * x ^ 1 * (1 - x) ^ 6 + ((71/2 : ℝ) + (7 : ℝ) * a) * x ^ 2 * (1 - x) ^ 5 + ((80 : ℝ) + (20 : ℝ) * a) * x ^ 3 * (1 - x) ^ 4 + ((225/2 : ℝ) + (30 : ℝ) * a) * x ^ 4 * (1 - x) ^ 3 + ((101 : ℝ) + (26 : ℝ) * a) * x ^ 5 * (1 - x) ^ 2 + ((56 : ℝ) + (14 : ℝ) * a) * x ^ 6 * (1 - x) ^ 1 + ((16 : ℝ) + (4 : ℝ) * a) * x ^ 7 * (1 - x) ^ 0 :=
      (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (mul_pos (mul_pos c0 (pow_pos hx 0)) (pow_pos h1x _))
      (mul_nonneg (mul_nonneg c1 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c2 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c3 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c4 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c5 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c6 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c7 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
    refine lt_of_lt_of_eq (mul_pos (mul_pos hx (pow_pos h1x 2)) hS) ?_
    linear_combination ((0 : ℝ) * x ^ 1 + (0 : ℝ) * x ^ 2 + (1/2 : ℝ) * x ^ 3 + (-1/2 : ℝ) * x ^ 4 + (0 : ℝ) * x ^ 5 + (0 : ℝ) * x ^ 6 + (-1/2 : ℝ) * x ^ 7 + (1/2 : ℝ) * x ^ 8 + (0 : ℝ) * x ^ 9 + (0 : ℝ) * x ^ 10) * ha

private theorem keyP10 (z : ℂ) (h : z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0) :
    ∃ c : ℂ, ∀ x : ℝ, 0 < x → x < 1 → 0 < (c * (z ^ 0 * (x : ℂ) ^ 1 + z ^ 1 * (x : ℂ) ^ 2 + z ^ 8 * (x : ℂ) ^ 3 + z ^ 2 * (x : ℂ) ^ 4 + z ^ 4 * (x : ℂ) ^ 5 + z ^ 9 * (x : ℂ) ^ 6 + z ^ 7 * (x : ℂ) ^ 7 + z ^ 3 * (x : ℂ) ^ 8 + z ^ 6 * (x : ℂ) ^ 9 + z ^ 5 * (x : ℂ) ^ 10)).re := by
  have h10 : z ^ 10 = 1 := by linear_combination ((z + 1) * (z ^ 5 - 1)) * h
  have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h10 (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at h
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = z.re := ⟨_, rfl⟩
  have e1 : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have e2 : z + (starRingEnd ℂ) z = 2 * (a : ℂ) := by
    rw [Complex.add_conj, ← ha_def]
    norm_num
  have hz2 : z ^ 2 = 2 * (a : ℂ) * z - 1 := by linear_combination z * e2 - e1
  have haC : 4 * (a : ℂ) ^ 2 + -2 * (a : ℂ) - 1 = 0 := by
    have h' : z ^ 2 * (4 * (a : ℂ) ^ 2 + -2 * (a : ℂ) - 1) = 0 := by
      linear_combination h - (2 * (a : ℂ) * z + z ^ 2 + -1 * z + 1) * hz2
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (pow_ne_zero 2 hz0)
    · exact h''
  have ha : 4 * a ^ 2 + -2 * a - 1 = 0 := by exact_mod_cast haC
  have hp2 : z ^ 2 = ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * z + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by linear_combination hz2
  have hp3 : z ^ 3 = ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp2 + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * hz2 + (1 : ℂ) * z * haC
  have hp4 : z ^ 4 = ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp3 + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) * hz2 + (1 : ℂ) * z * haC
  have hp5 : z ^ 5 = ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp4 + ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  have hp6 : z ^ 6 = ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp5 + ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  have hp7 : z ^ 7 = ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * z + ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp6 + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  have hp8 : z ^ 8 = ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp7 + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * hz2 + (-1 : ℂ) * z * haC
  have hp9 : z ^ 9 = ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((0 : ℂ) + (2 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp8 + ((0 : ℂ) + (-2 : ℂ) * (a : ℂ)) * hz2 + (-1 : ℂ) * z * haC
  have hp10 : z ^ 10 = ((0 : ℂ) + (0 : ℂ) * (a : ℂ)) * z + ((1 : ℂ) + (0 : ℂ) * (a : ℂ)) := by
    linear_combination z * hp9 + ((-1 : ℂ) + (0 : ℂ) * (a : ℂ)) * hz2 + (0 : ℂ) * z * haC
  rcases le_total 0 a with hs | hs
  · have hlo : (80901/100000 : ℝ) < a := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ 4 * a + (30901/25000 : ℝ))]
    have hhi : a < (40451/50000 : ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ 4 * a + (15451/12500 : ℝ))]
    refine ⟨1, fun x hx hx1 => ?_⟩
    have h1x : 0 < 1 - x := by linarith
    have key : 1 * (z ^ 0 * (x : ℂ) ^ 1 + z ^ 1 * (x : ℂ) ^ 2 + z ^ 8 * (x : ℂ) ^ 3 + z ^ 2 * (x : ℂ) ^ 4 + z ^ 4 * (x : ℂ) ^ 5 + z ^ 9 * (x : ℂ) ^ 6 + z ^ 7 * (x : ℂ) ^ 7 + z ^ 3 * (x : ℂ) ^ 8 + z ^ 6 * (x : ℂ) ^ 9 + z ^ 5 * (x : ℂ) ^ 10) =
        ((((1 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 2 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 3 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 4 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 5 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 6 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 7 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 8 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 9 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) +
        ((((0 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 2 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 3 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 4 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 5 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 6 + ((0 : ℝ) + (-2 : ℝ) * a) * x ^ 7 + ((0 : ℝ) + (2 : ℝ) * a) * x ^ 8 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 9 + ((0 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) * z := by
      push_cast
      linear_combination ((1 : ℂ) * (x : ℂ) ^ 4) * hp2 + ((1 : ℂ) * (x : ℂ) ^ 8) * hp3 + ((1 : ℂ) * (x : ℂ) ^ 5) * hp4 + ((1 : ℂ) * (x : ℂ) ^ 10) * hp5 + ((1 : ℂ) * (x : ℂ) ^ 9) * hp6 + ((1 : ℂ) * (x : ℂ) ^ 7) * hp7 + ((1 : ℂ) * (x : ℂ) ^ 3) * hp8 + ((1 : ℂ) * (x : ℂ) ^ 6) * hp9
    rw [key, re_aux, ← ha_def]
    have c0 : 0 < ((1 : ℝ) + (0 : ℝ) * a) := by linarith
    have c1 : 0 ≤ ((9 : ℝ) + (1 : ℝ) * a) := by linarith
    have c2 : 0 ≤ ((71/2 : ℝ) + (9 : ℝ) * a) := by linarith
    have c3 : 0 ≤ ((80 : ℝ) + (36 : ℝ) * a) := by linarith
    have c4 : 0 ≤ ((225/2 : ℝ) + (82 : ℝ) * a) := by linarith
    have c5 : 0 ≤ ((101 : ℝ) + (116 : ℝ) * a) := by linarith
    have c6 : 0 ≤ ((57 : ℝ) + (104 : ℝ) * a) := by linarith
    have c7 : 0 ≤ ((20 : ℝ) + (56 : ℝ) * a) := by linarith
    have c8 : 0 ≤ ((5 : ℝ) + (14 : ℝ) * a) := by linarith
    have hS : 0 < ((1 : ℝ) + (0 : ℝ) * a) * x ^ 0 * (1 - x) ^ 8 + ((9 : ℝ) + (1 : ℝ) * a) * x ^ 1 * (1 - x) ^ 7 + ((71/2 : ℝ) + (9 : ℝ) * a) * x ^ 2 * (1 - x) ^ 6 + ((80 : ℝ) + (36 : ℝ) * a) * x ^ 3 * (1 - x) ^ 5 + ((225/2 : ℝ) + (82 : ℝ) * a) * x ^ 4 * (1 - x) ^ 4 + ((101 : ℝ) + (116 : ℝ) * a) * x ^ 5 * (1 - x) ^ 3 + ((57 : ℝ) + (104 : ℝ) * a) * x ^ 6 * (1 - x) ^ 2 + ((20 : ℝ) + (56 : ℝ) * a) * x ^ 7 * (1 - x) ^ 1 + ((5 : ℝ) + (14 : ℝ) * a) * x ^ 8 * (1 - x) ^ 0 :=
      (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (mul_pos (mul_pos c0 (pow_pos hx 0)) (pow_pos h1x _))
      (mul_nonneg (mul_nonneg c1 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c2 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c3 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c4 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c5 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c6 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c7 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c8 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
    refine lt_of_lt_of_eq (mul_pos (mul_pos hx (pow_pos h1x 1)) hS) ?_
    linear_combination ((0 : ℝ) * x ^ 1 + (0 : ℝ) * x ^ 2 + (1/2 : ℝ) * x ^ 3 + (-1/2 : ℝ) * x ^ 4 + (0 : ℝ) * x ^ 5 + (0 : ℝ) * x ^ 6 + (1/2 : ℝ) * x ^ 7 + (-1/2 : ℝ) * x ^ 8 + (0 : ℝ) * x ^ 9 + (0 : ℝ) * x ^ 10) * ha
  · have hlo : (-15451/50000 : ℝ) < a := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ -(4 * a + (-40451/12500 : ℝ)))]
    have hhi : a < (-30901/100000 : ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0:ℝ) ≤ -(4 * a + (-80901/25000 : ℝ)))]
    refine ⟨(4 - z), fun x hx hx1 => ?_⟩
    have h1x : 0 < 1 - x := by linarith
    have key : (4 - z) * (z ^ 0 * (x : ℂ) ^ 1 + z ^ 1 * (x : ℂ) ^ 2 + z ^ 8 * (x : ℂ) ^ 3 + z ^ 2 * (x : ℂ) ^ 4 + z ^ 4 * (x : ℂ) ^ 5 + z ^ 9 * (x : ℂ) ^ 6 + z ^ 7 * (x : ℂ) ^ 7 + z ^ 3 * (x : ℂ) ^ 8 + z ^ 6 * (x : ℂ) ^ 9 + z ^ 5 * (x : ℂ) ^ 10) =
        ((((4 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 2 + ((0 : ℝ) + (6 : ℝ) * a) * x ^ 3 + ((-4 : ℝ) + (2 : ℝ) * a) * x ^ 4 + ((1 : ℝ) + (-8 : ℝ) * a) * x ^ 5 + ((-1 : ℝ) + (8 : ℝ) * a) * x ^ 6 + ((4 : ℝ) + (-2 : ℝ) * a) * x ^ 7 + ((0 : ℝ) + (-6 : ℝ) * a) * x ^ 8 + ((-1 : ℝ) + (0 : ℝ) * a) * x ^ 9 + ((-4 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) +
        ((((-1 : ℝ) + (0 : ℝ) * a) * x ^ 1 + ((4 : ℝ) + (-2 : ℝ) * a) * x ^ 2 + ((1 : ℝ) + (-8 : ℝ) * a) * x ^ 3 + ((0 : ℝ) + (6 : ℝ) * a) * x ^ 4 + ((4 : ℝ) + (0 : ℝ) * a) * x ^ 5 + ((-4 : ℝ) + (0 : ℝ) * a) * x ^ 6 + ((0 : ℝ) + (-6 : ℝ) * a) * x ^ 7 + ((-1 : ℝ) + (8 : ℝ) * a) * x ^ 8 + ((-4 : ℝ) + (2 : ℝ) * a) * x ^ 9 + ((1 : ℝ) + (0 : ℝ) * a) * x ^ 10 : ℝ) : ℂ) * z := by
      push_cast
      linear_combination ((-1 : ℂ) * (x : ℂ) ^ 2 + (4 : ℂ) * (x : ℂ) ^ 4) * hp2 + ((-1 : ℂ) * (x : ℂ) ^ 4 + (4 : ℂ) * (x : ℂ) ^ 8) * hp3 + ((4 : ℂ) * (x : ℂ) ^ 5 + (-1 : ℂ) * (x : ℂ) ^ 8) * hp4 + ((-1 : ℂ) * (x : ℂ) ^ 5 + (4 : ℂ) * (x : ℂ) ^ 10) * hp5 + ((4 : ℂ) * (x : ℂ) ^ 9 + (-1 : ℂ) * (x : ℂ) ^ 10) * hp6 + ((4 : ℂ) * (x : ℂ) ^ 7 + (-1 : ℂ) * (x : ℂ) ^ 9) * hp7 + ((4 : ℂ) * (x : ℂ) ^ 3 + (-1 : ℂ) * (x : ℂ) ^ 7) * hp8 + ((-1 : ℂ) * (x : ℂ) ^ 3 + (4 : ℂ) * (x : ℂ) ^ 6) * hp9 + ((-1 : ℂ) * (x : ℂ) ^ 6) * hp10
    rw [key, re_aux, ← ha_def]
    have c0 : 0 < ((4 : ℝ) + (-1 : ℝ) * a) := by linarith
    have c1 : 0 ≤ ((73/2 : ℝ) + (-6 : ℝ) * a) := by linarith
    have c2 : 0 ≤ ((146 : ℝ) + (-9 : ℝ) * a) := by linarith
    have c3 : 0 ≤ ((667/2 : ℝ) + (26 : ℝ) * a) := by linarith
    have c4 : 0 ≤ ((476 : ℝ) + (131 : ℝ) * a) := by linarith
    have c5 : 0 ≤ ((871/2 : ℝ) + (248 : ℝ) * a) := by linarith
    have c6 : 0 ≤ ((505/2 : ℝ) + (260 : ℝ) * a) := by linarith
    have c7 : 0 ≤ ((92 : ℝ) + (152 : ℝ) * a) := by linarith
    have c8 : 0 ≤ ((23 : ℝ) + (38 : ℝ) * a) := by linarith
    have hS : 0 < ((4 : ℝ) + (-1 : ℝ) * a) * x ^ 0 * (1 - x) ^ 8 + ((73/2 : ℝ) + (-6 : ℝ) * a) * x ^ 1 * (1 - x) ^ 7 + ((146 : ℝ) + (-9 : ℝ) * a) * x ^ 2 * (1 - x) ^ 6 + ((667/2 : ℝ) + (26 : ℝ) * a) * x ^ 3 * (1 - x) ^ 5 + ((476 : ℝ) + (131 : ℝ) * a) * x ^ 4 * (1 - x) ^ 4 + ((871/2 : ℝ) + (248 : ℝ) * a) * x ^ 5 * (1 - x) ^ 3 + ((505/2 : ℝ) + (260 : ℝ) * a) * x ^ 6 * (1 - x) ^ 2 + ((92 : ℝ) + (152 : ℝ) * a) * x ^ 7 * (1 - x) ^ 1 + ((23 : ℝ) + (38 : ℝ) * a) * x ^ 8 * (1 - x) ^ 0 :=
      (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (mul_pos (mul_pos c0 (pow_pos hx 0)) (pow_pos h1x _))
      (mul_nonneg (mul_nonneg c1 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c2 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c3 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c4 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c5 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c6 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c7 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
      (mul_nonneg (mul_nonneg c8 (pow_nonneg hx.le _)) (pow_nonneg h1x.le _)))
    refine lt_of_lt_of_eq (mul_pos (mul_pos hx (pow_pos h1x 1)) hS) ?_
    linear_combination ((0 : ℝ) * x ^ 1 + (1/2 : ℝ) * x ^ 2 + (2 : ℝ) * x ^ 3 + (-3/2 : ℝ) * x ^ 4 + (0 : ℝ) * x ^ 5 + (0 : ℝ) * x ^ 6 + (3/2 : ℝ) * x ^ 7 + (-2 : ℝ) * x ^ 8 + (-1/2 : ℝ) * x ^ 9 + (0 : ℝ) * x ^ 10) * ha

/-- All three cases together: for a tenth root of unity `z ≠ 1` there is a constant `c` making
the real part of `c P(x)` positive on the open unit interval. -/
private theorem keyAll (z : ℂ)
    (hz : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7 + z ^ 8 + z ^ 9 = 0) :
    ∃ c : ℂ, ∀ x : ℝ, 0 < x → x < 1 → 0 < (c * (z ^ 0 * (x : ℂ) ^ 1 + z ^ 1 * (x : ℂ) ^ 2 + z ^ 8 * (x : ℂ) ^ 3 + z ^ 2 * (x : ℂ) ^ 4 + z ^ 4 * (x : ℂ) ^ 5 + z ^ 9 * (x : ℂ) ^ 6 + z ^ 7 * (x : ℂ) ^ 7 + z ^ 3 * (x : ℂ) ^ 8 + z ^ 6 * (x : ℂ) ^ 9 + z ^ 5 * (x : ℂ) ^ 10)).re := by
  have hf : (z + 1) * ((z ^ 4 + z ^ 3 + z ^ 2 + z + 1) * (z ^ 4 - z ^ 3 + z ^ 2 - z + 1)) = 0 := by
    linear_combination hz
  rcases mul_eq_zero.mp hf with h | h
  · have hz1 : z = -1 := by linear_combination h
    subst hz1
    exact ⟨1, keyReal⟩
  · rcases mul_eq_zero.mp h with h | h
    · exact keyP5 z h
    · exact keyP10 z h

end ElevenAux

open ElevenAux in
/-- PROVED. `L(σ, χ) ≠ 0` for every non principal character modulo 11 and every real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_mod_11 (χ : DirichletCharacter ℂ 11) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  obtain ⟨c, hc⟩ := keyAll (χ (2 : ZMod 11)) (hz_11 χ hχ)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < (c * ∑ a ∈ Finset.range 11, χ ((a : ℕ) : ZMod 11) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_11 χ x]
    exact hc x hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ c (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key _ (by norm_num) (by norm_num)⟩ hσ

end LeanLab.HelfgottMajor.RealAxisKernel

#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_11
