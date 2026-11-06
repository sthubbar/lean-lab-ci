/-
Finite character Parseval identity for the remaining coefficient period estimate.
Source page 13 display 45 and page 15 first display.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438l
namespace LeanLab.KumchevLiu2007.Task438m
open Real Complex Task129b Task129c
open scoped BigOperators
set_option maxHeartbeats 400000
/-- Page 13 display 45 and page 15 first display. Finite Parseval identity
for the standard additive character. This supplies the exact Fourier norm
step needed to reduce the remaining period bound to a sixth Gauss moment. -/
theorem character_parseval (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    (∑ n : ZMod q, ‖∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n))‖ ^ 2) =
      (q : ℝ) * ∑ a : ZMod q, ‖b a‖ ^ 2 := by
  classical
  have hstar (z : ZMod q) : (starRingEnd ℂ) (ZMod.stdAddChar (N := q) z) =
      ZMod.stdAddChar (N := q) (-z) := by
    rw [AddChar.starComp_apply (by rw [ZMod.ringChar_zmod_n]; exact NeZero.pos q),
      AddChar.inv_apply]
  have he (a c n : ZMod q) :
      (b a * ZMod.stdAddChar (N := q) (-(a * n))) *
        (starRingEnd ℂ) (b c * ZMod.stdAddChar (N := q) (-(c * n))) =
      (b a * (starRingEnd ℂ) (b c)) * ZMod.stdAddChar (N := q) (n * (c - a)) := by
    rw [map_mul, hstar, neg_neg]
    have halg : n * (c - a) = -(a * n) + c * n := by ring
    rw [halg, AddChar.map_add_eq_mul]
    ring
  have hn (n : ZMod q) :
      ‖∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n))‖ ^ 2 =
      (∑ a : ZMod q, ∑ c : ZMod q,
        (b a * (starRingEnd ℂ) (b c)) * ZMod.stdAddChar (N := q) (n * (c - a))).re := by
    have h := congrArg Complex.re (Complex.mul_conj
      (∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n))))
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h
    rw [← h]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, he]
    rw [Finset.sum_comm]
  simp_rw [hn]
  rw [← Complex.re_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 1; arg 2; ext a; rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), sub_eq_zero]
  push_cast
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ZMod.card]
  simp only [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring
#print axioms character_parseval

/-- Page 13 display 45 and page 15 first display. The complete coefficient
mean square over residues is exactly q divided by the sixth power of the
totient times the sixth moment of the reduced quadratic sums. -/
theorem A3_period_square_identity (q : ℕ) [NeZero q] :
    (∑ n : ZMod q, ‖A3 n.val q‖ ^ 2) =
      (q : ℝ) / (Nat.totient q : ℝ) ^ 6 *
        ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ‖∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
            ZMod.stdAddChar (N := q) (a * x * x)‖ ^ 6 := by
  classical
  let F : ZMod q → ℂ := fun a =>
    ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * x * x)
  let b : ZMod q → ℂ := fun a =>
    (if IsUnit a then F a ^ 3 else 0) / (Nat.totient q : ℂ) ^ 3
  have ha (n : ZMod q) : A3 n.val q =
      ∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n)) := by
    rw [Task342h.A3_zmod_formula, ZMod.natCast_zmod_val, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hunit : IsUnit a <;> simp [b, F, hunit] <;> ring
  have hb (a : ZMod q) : ‖b a‖ ^ 2 =
      if IsUnit a then ‖F a‖ ^ 6 / (Nat.totient q : ℝ) ^ 6 else 0 := by
    by_cases hunit : IsUnit a
    · simp only [b, hunit, ite_true, norm_div, norm_pow, Complex.norm_natCast, div_pow, ← pow_mul]
    · simp [b, hunit]
  simp_rw [ha]
  rw [Task438m.character_parseval]
  simp_rw [hb]
  rw [← Finset.sum_filter]
  change (q : ℝ) * (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
    ‖F a‖ ^ 6 / (Nat.totient q : ℝ) ^ 6) = _
  rw [← Finset.sum_div]
  dsimp [F]
  ring

#print axioms A3_period_square_identity

end LeanLab.KumchevLiu2007.Task438m
