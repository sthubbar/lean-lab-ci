/-
Finite odd prime sixth moment for the complete period supply.
Source https://arxiv.org/abs/0801.0130 page 13 display 45 and page 15 first display.
This derives the local moment from the already proved quadratic Gauss evaluation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438m

namespace LeanLab.KumchevLiu2007.PrimeMoment447

open Real Complex Task438g
open scoped BigOperators
set_option maxHeartbeats 600000

/-- Page 15 first display through page 13 display 45, derived local identity.
The sixth moment depends only on the squared real part of the quadratic Gauss sum. -/
theorem sixth_moment_identity (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)‖ ^ 6) =
      ((p : ℝ) - 1) * (((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) *
        (gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))).re ^ 2) := by
  classical
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  let S := (Finset.univ : Finset (ZMod p)).erase 0
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = S := by
    ext a
    simp [S, isUnit_iff_ne_zero]
  have hG : ‖G‖ ^ 2 = (p : ℝ) := by
    simpa only [norm_pow] using quadratic_gauss_sq_norm p hp
  have hGre : G.re ^ 2 + G.im ^ 2 = (p : ℝ) := by
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← sq] using hG
  have hterm (a : ZMod p) (ha : a ∈ S) :
      ‖quadraticC p a * G - 1‖ ^ 6 =
      ((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) * G.re ^ 2 -
        (6 * ((p : ℝ) + 1) ^ 2 * G.re + 8 * G.re ^ 3) * (quadraticC p a).re := by
    have ha0 := Finset.ne_of_mem_erase ha
    have hs := quadraticC_sq p a ha0
    have hc : quadraticC p a = 1 ∨ quadraticC p a = -1 := sq_eq_one_iff.mp hs
    rcases hc with hc | hc
    · rw [hc, one_mul, Complex.one_re]
      have hn : ‖G - 1‖ ^ 2 = (p : ℝ) + 1 - 2 * G.re := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
        nlinarith [hGre]
      calc
        _ = (‖G - 1‖ ^ 2) ^ 3 := by ring
        _ = _ := by rw [hn]; ring
    · rw [hc, neg_one_mul, Complex.neg_re, Complex.one_re]
      have hn : ‖-G - 1‖ ^ 2 = (p : ℝ) + 1 + 2 * G.re := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
          Complex.one_re, Complex.one_im, sub_zero]
        nlinarith [hGre]
      calc
        _ = (‖-G - 1‖ ^ 2) ^ 3 := by ring
        _ = _ := by rw [hn]; ring
  have hsum : (∑ a ∈ S, (quadraticC p a).re) = 0 := by
    have hχ := MulChar.sum_eq_zero_of_ne_one (quadraticC_properties p hp).1
    have h0 : quadraticC p (0 : ZMod p) = 0 := by
      simp [quadraticC, MulChar.ringHomComp_apply]
    have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => quadraticC p a) (Finset.mem_univ 0)
    rw [h0, add_zero, hχ] at he
    have hr := congrArg Complex.re he
    simpa only [Complex.re_sum, Complex.zero_re, S] using hr
  rw [hset]
  calc
    _ = ∑ a ∈ S, ‖quadraticC p a * G - 1‖ ^ 6 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← hset, reduced_quadratic_sum p hp a (Finset.ne_of_mem_erase ha)]
    _ = ∑ a ∈ S, (((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) * G.re ^ 2 -
        (6 * ((p : ℝ) + 1) ^ 2 * G.re + 8 * G.re ^ 3) * (quadraticC p a).re) :=
      Finset.sum_congr rfl hterm
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero, Finset.sum_const]
      have hcard : (S.card : ℝ) = (p : ℝ) - 1 := by
        simp only [S, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
          Finset.card_univ, ZMod.card, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
      rw [nsmul_eq_mul, hcard]

/-- Page 15 first display, derived local sixth moment bound.
Discarding the imaginary square gives a polynomial upper bound. -/
theorem sixth_moment_polynomial (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)‖ ^ 6) ≤
      ((p : ℝ) - 1) * ((p : ℝ) ^ 3 + 15 * (p : ℝ) ^ 2 + 15 * (p : ℝ) + 1) := by
  rw [sixth_moment_identity p hp]
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  have hG : ‖G‖ ^ 2 = (p : ℝ) := by
    simpa only [norm_pow] using quadratic_gauss_sq_norm p hp
  have hGr : G.re ^ 2 ≤ (p : ℝ) := by
    nlinarith [Complex.sq_norm_sub_sq_re G, sq_nonneg G.im]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  calc
    _ ≤ ((p : ℝ) - 1) * (((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) * (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left hGr (by positivity)
    _ = _ := by ring

/-- Page 15 first display, derived numerical local factor comparison.
For x at least 3 the polynomial moment is below the chosen sixth power factor. -/
theorem local_moment_numerical (x : ℝ) (hx : 3 ≤ x) :
    (x - 1) * (x ^ 3 + 15 * x ^ 2 + 15 * x + 1) ≤
      (x - 1) ^ 6 / x ^ 2 * (1 + 6 / x) ^ 6 := by
  have hx0 : 0 < x := by linarith
  have ht : 0 ≤ x - 3 := by linarith
  have hpoly : x ^ 8 * (x ^ 3 + 15 * x ^ 2 + 15 * x + 1) ≤
      (x - 1) ^ 5 * (x + 6) ^ 6 := by
    apply sub_nonneg.mp
    convert (show 0 ≤ 16 * (x - 3) ^ 10 + 835 * (x - 3) ^ 9 +
      18034 * (x - 3) ^ 8 + 217001 * (x - 3) ^ 7 + 1621508 * (x - 3) ^ 6 +
      7866369 * (x - 3) ^ 5 + 25081650 * (x - 3) ^ 4 + 51989607 * (x - 3) ^ 3 +
      67295448 * (x - 3) ^ 2 + 49347468 * (x - 3) + 15641424 by positivity) using 1 <;> ring
  have he : (x - 1) ^ 6 / x ^ 2 * (1 + 6 / x) ^ 6 =
      (x - 1) ^ 6 * (x + 6) ^ 6 / x ^ 8 := by
    field_simp [ne_of_gt hx0]
    <;> ring
  rw [he, le_div_iff₀ (pow_pos hx0 8)]
  calc
    _ = (x - 1) * (x ^ 8 * (x ^ 3 + 15 * x ^ 2 + 15 * x + 1)) := by ring
    _ ≤ (x - 1) * ((x - 1) ^ 5 * (x + 6) ^ 6) :=
      mul_le_mul_of_nonneg_left hpoly (by linarith)
    _ = _ := by ring

/-- Page 15 first display, exact local sixth moment supply for Task447a.
It follows from the quadratic Gauss sum evaluation and finite character cancellation. -/
theorem odd_prime_sixth_moment (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)‖ ^ 6) ≤
      (Nat.totient p : ℝ) ^ 6 / (p : ℝ) ^ 2 * (1 + 6 / (p : ℝ)) ^ 6 := by
  have hp2 : p ≠ 2 := by omega
  have hb := (sixth_moment_polynomial p hp2).trans
    (local_moment_numerical (p : ℝ) (by exact_mod_cast hp))
  simpa only [Nat.totient_prime (Fact.out : p.Prime),
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] using hb

#print axioms sixth_moment_identity
#print axioms sixth_moment_polynomial
#print axioms local_moment_numerical
#print axioms odd_prime_sixth_moment

end LeanLab.KumchevLiu2007.PrimeMoment447
