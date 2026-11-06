/-
Full period supply for the three-square diagonal mean square.
Source page 15 first display and Schwarz page 83 display 2.11.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438k

namespace LeanLab.KumchevLiu2007.Task438l

open Real Complex Task129b Task129c Task292a Task438g
open scoped BigOperators

/-- Page 15 first display, derived normalization. Multiply the complete
period square sum by the modulus to obtain a multiplicative local mass. -/
noncomputable def periodMass (q : ℕ) : ℝ :=
  (q : ℝ) * ∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2

/-- Page 13 display 45, finite residue bookkeeping for the period average. -/
theorem residue_sum_eq_range (q : ℕ) [NeZero q] (f : ℕ → ℝ) :
    (∑ n : ZMod q, f n.val) = ∑ n ∈ Finset.range q, f n := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => exact Fin.sum_univ_eq_sum_range f (q + 1)

/-- Page 15 first display, derived Chinese remainder step from
page 13 property i. -/
theorem periodMass_coprime_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    periodMass (a * b) = periodMass a * periodMass b := by
  classical
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero (a * b) := ⟨by positivity⟩
  have hval (q : ℕ) [NeZero q] (z : ZMod (a * b)) :
      A3 z.val q = A3 (ZMod.cast z : ZMod q).val q := by
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
    exact ((Task403a.A3_periodic q).map_mod_nat z.val).symm
  have hs : (∑ n : ZMod (a * b), ‖A3 n.val (a * b)‖ ^ 2) =
      (∑ n : ZMod a, ‖A3 n.val a‖ ^ 2) * (∑ n : ZMod b, ‖A3 n.val b‖ ^ 2) := by
    calc
      _ = ∑ z : ZMod (a * b),
          (fun w : ZMod a × ZMod b => ‖A3 w.1.val a‖ ^ 2 * ‖A3 w.2.val b‖ ^ 2)
            (ZMod.chineseRemainder hab z) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Task438e.A3_coprime_mul _ a b hab, norm_mul, mul_pow, hval a z, hval b z]
        have hc : ZMod.chineseRemainder hab z =
            ((ZMod.cast z : ZMod a), (ZMod.cast z : ZMod b)) := by
          calc
            _ = ZMod.chineseRemainder hab (z.val : ZMod (a * b)) := by
              rw [ZMod.natCast_zmod_val]
            _ = ((z.val : ZMod a), (z.val : ZMod b)) := by
              rw [map_natCast]
              rfl
            _ = _ := by simp only [ZMod.cast_eq_val]
        rw [hc]
      _ = ∑ w : ZMod a × ZMod b, ‖A3 w.1.val a‖ ^ 2 * ‖A3 w.2.val b‖ ^ 2 :=
        Equiv.sum_comp (ZMod.chineseRemainder hab).toEquiv
          (fun w : ZMod a × ZMod b => ‖A3 w.1.val a‖ ^ 2 * ‖A3 w.2.val b‖ ^ 2)
      _ = _ := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
  rw [residue_sum_eq_range (a * b) (fun n => ‖A3 n (a * b)‖ ^ 2),
    residue_sum_eq_range a (fun n => ‖A3 n a‖ ^ 2),
    residue_sum_eq_range b (fun n => ‖A3 n b‖ ^ 2)] at hs
  simp only [periodMass, Nat.cast_mul]
  rw [hs]
  ring

/-- Page 13 display 45. The normalized modulus one mass equals one. -/
theorem periodMass_one : periodMass 1 = 1 := by
  simp [periodMass, Task438d.A3_one]

/-- Page 13 property ii. Every vanishing coefficient gives zero mass. -/
theorem periodMass_prime_power_zero (p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    periodMass (p ^ k) = 0 := by
  simp [periodMass, Task438f.A3_prime_power_vanish _ p k hp hk]

/-- Page 13 property ii and page 15 first display. The three retained
powers of two have normalized mass at most 4096. -/
theorem periodMass_small_dyadic (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    periodMass (2 ^ k) ≤ 4096 := by
  have hq : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hsum : (∑ n ∈ Finset.range (2 ^ k), ‖A3 n (2 ^ k)‖ ^ 2) ≤
      ((2 ^ k : ℕ) : ℝ) * (64 / ((2 ^ k : ℕ) : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (2 ^ k), (64 / ((2 ^ k : ℕ) : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact pow_le_pow_left₀ (norm_nonneg _)
          (Task438d.A3_small_dyadic_bound n k hk hk3) 2
      _ = _ := by simp
  unfold periodMass
  calc
    _ ≤ ((2 ^ k : ℕ) : ℝ) *
        (((2 ^ k : ℕ) : ℝ) * (64 / ((2 ^ k : ℕ) : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hq.le
    _ = 4096 := by field_simp [ne_of_gt hq]; ring

/-- Page 13 display 45 and page 15 first display. Finite Parseval identity
for the standard additive character. -/
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
  rw [character_parseval]
  simp_rw [hb]
  rw [← Finset.sum_filter]
  change (q : ℝ) * (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
    ‖F a‖ ^ 6 / (Nat.totient q : ℝ) ^ 6) = _
  rw [← Finset.sum_div]
  dsimp [F]
  ring

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

/-- Page 15 first display, derived local sixth moment bound. -/
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

/-- Page 15 first display, derived numerical local factor comparison. -/
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

/-- Page 15 first display, exact local sixth moment supply. -/
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

/-- Page 15 first display. Parseval converts the local sixth moment
bound into the normalized odd prime mass bound. -/
theorem periodMass_odd_prime (p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    periodMass p ≤ (1 + 6 / (p : ℝ)) ^ 6 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht : (0 : ℝ) < Nat.totient p := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hi := A3_period_square_identity p
  rw [residue_sum_eq_range p (fun n => ‖A3 n p‖ ^ 2)] at hi
  have hm := odd_prime_sixth_moment p hodd
  unfold periodMass
  rw [hi]
  calc
    _ ≤ (p : ℝ) * ((p : ℝ) / (Nat.totient p : ℝ) ^ 6 *
      ((Nat.totient p : ℝ) ^ 6 / (p : ℝ) ^ 2 * (1 + 6 / (p : ℝ)) ^ 6)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (by positivity)) hp0.le
    _ = _ := by field_simp [ne_of_gt hp0, ne_of_gt ht]

/-- Page 15 first display. The normalized prime power estimate retains
all three even prime factors. -/
theorem periodMass_prime_power (p k : ℕ) (hp : p.Prime) :
    periodMass (p ^ k) ≤ localMajorant (p ^ k) ^ 6 := by
  by_cases hk : k = 0
  · subst k
    simp [periodMass_one, localMajorant]
  have hM : localMajorant (p ^ k) = 1 + 6 / (p : ℝ) := by
    simp [localMajorant, Nat.primeFactors_prime_pow hk hp]
  rw [hM]
  by_cases hp2 : p = 2
  · subst p
    by_cases hk3 : k ≤ 3
    · norm_num
      exact periodMass_small_dyadic k (by omega) hk3
    · rw [periodMass_prime_power_zero 2 k hp (Or.inr ⟨rfl, by omega⟩)]
      positivity
  · by_cases hk1 : k = 1
    · subst k
      simpa using periodMass_odd_prime p hp (by have := hp.two_le; omega)
    · rw [periodMass_prime_power_zero p k hp (Or.inl ⟨hp2, by omega⟩)]
      positivity

/-- Page 15 first display. The normalized mass is bounded by the sixth
power of the local prime product. -/
theorem periodMass_bound (q : ℕ) (hq : 0 < q) :
    periodMass q ≤ localMajorant q ^ 6 := by
  classical
  induction q using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hp => exact periodMass_prime_power p k hp
  | coprime a b ha hb hab ih_a ih_b =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hM : localMajorant (a * b) = localMajorant a * localMajorant b := by
      simp only [localMajorant, Nat.primeFactors_mul ha0 hb0,
        Finset.prod_union hab.disjoint_primeFactors]
    rw [periodMass_coprime_mul a b (by omega) (by omega) hab, hM, mul_pow]
    apply mul_le_mul (ih_a (by omega)) (ih_b (by omega))
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun n hn => sq_nonneg _))
    · positivity

/-- LEAF. Page 15 first display, using the character definition on page 13
and Schwarz page 83 display 2.11. This is only a complete period average
at one modulus. There is no interval, P, Q, x or y variable.
The even prime powers through 8 are included. -/
theorem complete_period_square :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q →
      (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) ≤
        K * (localMajorant q ^ 6 / (q : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [one_mul, le_div_iff₀ hq0]
  simpa only [periodMass, mul_comm] using periodMass_bound q hq

/-- Page 15 first display. A nonnegative periodic function summed over
an interval of length at least its period is bounded by six times the
length divided by the period times its complete period sum. -/
theorem nonnegative_periodic_interval (v : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic v q) (hv : ∀ n, 0 ≤ v n)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) (hqy : (q : ℝ) ≤ y) :
    (∑ n ∈ intervalNumbers x y, v n) ≤
      6 * y / (q : ℝ) * (∑ n ∈ Finset.range q, v n) := by
  classical
  let S := ∑ n ∈ Finset.range q, v n
  let μ := S / (q : ℝ)
  let g : ℕ → ℂ := fun n => ((v n - μ : ℝ) : ℂ)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n hn => hv n)
  have hμ : 0 ≤ μ := div_nonneg hS (by positivity)
  have hqμ : (q : ℝ) * μ = S := by dsimp [μ]; field_simp
  have hgper : Function.Periodic g q := by intro n; simp [g, hp n]
  have hgzero : (∑ n ∈ Finset.range q, g n) = 0 := by
    have he : (∑ n ∈ Finset.range q, g n) = ((S - (q : ℝ) * μ : ℝ) : ℂ) := by
      simp [g, S, Finset.sum_sub_distrib]
    rw [he, hqμ, sub_self, Complex.ofReal_zero]
  have hgperiod : (∑ n ∈ Finset.range q, ‖g n‖) ≤ 2 * S := by
    calc
      _ ≤ ∑ n ∈ Finset.range q, (v n + μ) := by
        apply Finset.sum_le_sum
        intro n hn
        calc
          _ = |v n - μ| := by
            change ‖((v n - μ : ℝ) : ℂ)‖ = _
            rw [Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |v n| + |μ| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (hv n), abs_of_nonneg hμ]
      _ = 2 * S := by simp [Finset.sum_add_distrib, ← hqμ, S]; ring
  have hi : ‖∑ n ∈ intervalNumbers x y, g n‖ ≤ 4 * S := by
    have h := periodic_zero_mean_interval g hq hgper hgzero
      (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    have h' : ‖∑ n ∈ intervalNumbers x y, g n‖ ≤ 2 * ∑ n ∈ Finset.range q, ‖g n‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using h
    exact h'.trans (by linarith)
  have hgsum : (∑ n ∈ intervalNumbers x y, g n) =
      (((∑ n ∈ intervalNumbers x y, v n) - ((intervalNumbers x y).card : ℝ) * μ : ℝ) : ℂ) := by
    simp [g, Finset.sum_sub_distrib]
  rw [hgsum, Complex.norm_real, Real.norm_eq_abs] at hi
  have hcard := Task271a.interval_card_le hx hy
  have hmain : ((intervalNumbers x y).card : ℝ) * μ ≤ 2 * y * μ :=
    mul_le_mul_of_nonneg_right hcard hμ
  have hSmain : S ≤ y * μ := by nlinarith
  have herr := le_abs_self ((∑ n ∈ intervalNumbers x y, v n) - ((intervalNumbers x y).card : ℝ) * μ)
  have hbound : (∑ n ∈ intervalNumbers x y, v n) ≤ 6 * y * μ := by nlinarith
  have heq : 6 * y * μ = 6 * y / (q : ℝ) * S := by dsimp [μ]; ring
  exact hbound.trans_eq heq

/-- Page 15 first display. Exact Task438b single modulus interval supply.
CONDITIONAL only on complete_period_square. -/
theorem coefficient_interval_square :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, ∀ q : ℕ,
      0 ≤ x → 1 ≤ y → 0 < q → (q : ℝ) ^ 3 ≤ y →
      (∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2) ≤
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := complete_period_square
  refine ⟨6 * K, by positivity, ?_⟩
  intro x y q hx hy hq hqy
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqle : (q : ℝ) ≤ y := by
    have hpos : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) + 1) := by positivity
    nlinarith
  have hper : Function.Periodic (fun n => ‖A3 n q‖ ^ 2) q := by
    intro n
    change ‖A3 (n + q) q‖ ^ 2 = ‖A3 n q‖ ^ 2
    have he : A3 (n + q) q = A3 n q := Task403a.A3_periodic q n
    rw [he]
  calc
    _ ≤ 6 * y / (q : ℝ) * (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) :=
      nonnegative_periodic_interval _ q hq hper (fun n => sq_nonneg _) x y hx hy hqle
    _ ≤ 6 * y / (q : ℝ) * (K * (localMajorant q ^ 6 / (q : ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q hq) (by positivity)
    _ = (6 * K) * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by ring

#print axioms complete_period_square
#print axioms nonnegative_periodic_interval
#print axioms coefficient_interval_square

end LeanLab.KumchevLiu2007.Task438l
