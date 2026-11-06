/-
Odd prime coefficient estimate from quadratic characters.
Source page 14 before display 47 and Schwarz page 83 display 2.11.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438f

namespace LeanLab.KumchevLiu2007.Task438g

open Real Complex U1534 Task129c
open scoped BigOperators

/-- Page 14 Legendre symbol notation. The quadratic character with complex values. -/
noncomputable def quadraticC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- Page 14 before display 47. This complex character is nontrivial and quadratic
at every odd prime. -/
theorem quadraticC_properties (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    quadraticC p ≠ 1 ∧ (quadraticC p).IsQuadratic := by
  constructor
  · intro he
    apply quadraticChar_ne_one (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp)
    exact (MulChar.ringHomComp_eq_one_iff Int.cast_injective).mp he
  · exact (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- Page 14 before display 47. Quadratic root counting changes the full
quadratic phase sum into its Gauss sum at every nonzero frequency. -/
theorem full_quadratic_sum (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) :
    (∑ x : ZMod p, ZMod.stdAddChar (N := p) (a * x ^ 2)) =
      quadraticC p a * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) := by
  classical
  have hroot (y : ZMod p) :
      ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℂ) =
        quadraticC p y + 1 := by
    have h := quadraticChar_card_sqrts (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp) y
    have hc := congrArg (fun z : ℤ => (z : ℂ)) h
    simpa [quadraticC, MulChar.ringHomComp_apply, Set.toFinset_ofPred, Int.cast_add] using hc
  have hf : (∑ x : ZMod p, ZMod.stdAddChar (N := p) (a * x ^ 2)) =
      ∑ y : ZMod p, (quadraticC p y + 1) * ZMod.stdAddChar (N := p) (a * y) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2)]
    apply Finset.sum_congr rfl
    intro y hy
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y),
          ZMod.stdAddChar (N := p) (a * y) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = _ := by simp [hroot]
  rw [hf]
  simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
  have hs : (∑ y : ZMod p, ZMod.stdAddChar (N := p) (a * y)) = 0 := by
    simpa only [mul_comm, ite_eq_right ha, Nat.cast_zero] using
      (AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) a (ZMod.isPrimitive_stdAddChar p))
  rw [hs, add_zero]
  have hg := gaussSum_mulShift_eq (quadraticC p) (ZMod.stdAddChar (N := p)) (Units.mk0 a ha)
  rw [(quadraticC_properties p hp).2.inv] at hg
  exact hg

/-- Page 2 display 8 and page 14 before display 47. Removing the zero residue
subtracts one from the full quadratic Gauss sum. -/
theorem reduced_quadratic_sum (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) :
    (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ZMod.stdAddChar (N := p) (a * x * x)) =
      quadraticC p a * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) - 1 := by
  classical
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = Finset.univ.erase 0 := by
    ext x
    simp [isUnit_iff_ne_zero]
  rw [hset]
  have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
    (fun x => ZMod.stdAddChar (N := p) (a * x * x)) (Finset.mem_univ 0)
  simp only [mul_zero, AddChar.map_zero_eq_one] at h
  have hf := full_quadratic_sum p hp a ha
  simp only [sq, ← mul_assoc] at hf
  rw [hf] at h
  exact eq_sub_of_add_eq h

/-- Page 14 before display 47. The square of the quadratic Gauss sum is
p times the quadratic character at minus one. -/
theorem quadratic_gauss_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) ^ 2 =
      quadraticC p (-1) * (p : ℂ) := by
  simpa using gaussSum_sq (quadraticC_properties p hp).1
    (quadraticC_properties p hp).2 (ZMod.isPrimitive_stdAddChar p)

/-- Page 14 Legendre notation. A nonzero quadratic character value has square one. -/
theorem quadraticC_sq (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    quadraticC p a ^ 2 = 1 := by
  have h := quadraticChar_sq_one (F := ZMod p) ha
  change (((quadraticChar (ZMod p)) a : ℤ) : ℂ) ^ 2 = 1
  exact_mod_cast h

/-- Page 14 Legendre notation. Every complex quadratic character value has norm at most one. -/
theorem quadraticC_norm_le (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    ‖quadraticC p a‖ ≤ 1 := by
  by_cases ha : a = 0
  · subst a
    simp [quadraticC, MulChar.ringHomComp_apply]
  · have hs := congrArg norm (quadraticC_sq p a ha)
    rw [norm_pow, norm_one] at hs
    nlinarith [norm_nonneg (quadraticC p a)]

/-- Page 14 before display 47. The Gauss sum twisted by b equals the quadratic
character at b times the original Gauss sum, including the zero twist. -/
theorem quadratic_gauss_shift (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (b : ZMod p) :
    gaussSum (quadraticC p) ((ZMod.stdAddChar (N := p)).mulShift b) =
      quadraticC p b * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) := by
  by_cases hb : b = 0
  · subst b
    have hz : (ZMod.stdAddChar (N := p)).mulShift 0 = 1 := by ext x; simp
    rw [hz, gaussSum_one_right (quadraticC_properties p hp).1]
    simp [quadraticC, MulChar.ringHomComp_apply]
  · have h := gaussSum_mulShift_eq (quadraticC p) (ZMod.stdAddChar (N := p)) (Units.mk0 b hb)
    simpa only [(quadraticC_properties p hp).2.inv, Units.val_mk0] using h

/-- Page 14 before display 47. The squared quadratic Gauss sum has norm p. -/
theorem quadratic_gauss_sq_norm (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ‖gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) ^ 2‖ = (p : ℝ) := by
  rw [quadratic_gauss_sq p hp, norm_mul, Complex.norm_natCast]
  have hs := congrArg norm (quadraticC_sq p (-1) (by simp))
  rw [norm_pow, norm_one] at hs
  have h1 : ‖quadraticC p (-1)‖ = 1 := by nlinarith [norm_nonneg (quadraticC p (-1))]
  rw [h1, one_mul]

/-- Page 14 before display 47. Cubing the reduced quadratic Gauss sum leaves
one twisted Gauss sum and one Ramanujan sum. This is a finite algebra identity. -/
theorem A3_odd_prime_formula (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    A3 n p =
      (((gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) ^ 3 +
        3 * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) *
          (quadraticC p (-(n : ZMod p)) * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) -
        (3 * (gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) ^ 2 + 1) *
          (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1)) / ((p : ℂ) - 1) ^ 3 := by
  classical
  let S : Finset (ZMod p) := Finset.univ.erase 0
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = S := by
    ext x
    simp [S, isUnit_iff_ne_zero]
  have hterm (a : ZMod p) (ha : a ∈ S) :
      (quadraticC p a * G - 1) ^ 3 * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p))) =
        (G ^ 3 + 3 * G) * (quadraticC p a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) -
          (3 * G ^ 2 + 1) * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p))) := by
    have hs := quadraticC_sq p a (Finset.ne_of_mem_erase ha)
    have ht : quadraticC p a ^ 3 = quadraticC p a := by rw [pow_succ, hs, one_mul]
    ring_nf
    rw [hs, ht]
    ring
  have hT : (∑ a ∈ S, quadraticC p a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      quadraticC p (-(n : ZMod p)) * G := by
    have h0 : quadraticC p (0 : ZMod p) = 0 := by
      simp [quadraticC, MulChar.ringHomComp_apply]
    have ht := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => quadraticC p a * ZMod.stdAddChar (N := p) (a * (-(n : ZMod p))))
      (Finset.mem_univ 0)
    simp only [h0, zero_mul, add_zero] at ht
    have he : (∑ a : ZMod p, quadraticC p a * ZMod.stdAddChar (N := p) (a * (-(n : ZMod p)))) =
        gaussSum (quadraticC p) ((ZMod.stdAddChar (N := p)).mulShift (-(n : ZMod p))) := by
      simp only [gaussSum, AddChar.mulShift_apply, mul_comm]
    simpa only [S, ← mul_neg, he, quadratic_gauss_shift p hp, G] using ht
  have hR : (∑ a ∈ S, ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1 := by
    have ht := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => ZMod.stdAddChar (N := p) (a * (-(n : ZMod p)))) (Finset.mem_univ 0)
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p))
      (-(n : ZMod p)) (ZMod.isPrimitive_stdAddChar p)
    simp only [zero_mul, AddChar.map_zero_eq_one] at ht
    rw [hs] at ht
    by_cases hn : (n : ZMod p) = 0 <;> simp [hn, S] at ht ⊢ <;> linear_combination ht
  rw [Task342h.A3_zmod_formula, Nat.totient_prime (Fact.out : p.Prime), hset]
  have hpp : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [Nat.cast_sub hpp, Nat.cast_one]
  have hsum : (∑ a ∈ S,
      (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)) ^ 3 *
        ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      (G ^ 3 + 3 * G) * (quadraticC p (-(n : ZMod p)) * G) -
        (3 * G ^ 2 + 1) * (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1) := by
    calc
      _ = ∑ a ∈ S, ((G ^ 3 + 3 * G) *
          (quadraticC p a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) -
          (3 * G ^ 2 + 1) * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [reduced_quadratic_sum p hp a (Finset.ne_of_mem_erase ha)]
        exact hterm a ha
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hT, hR]
  rw [hset] at hsum
  rw [hsum]
  dsimp [G]
  ring

/-- Page 14 before display 47. The explicit Gauss expression yields a uniform
odd prime bound with constant 8. This uses no prime counting input. -/
theorem A3_odd_prime_bound (n p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    ‖A3 n p‖ ≤ 8 / (p : ℝ) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by positivity
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hodd
  have hp2 : p ≠ 2 := by omega
  by_cases hpIs3 : p = 3
  · subst p
    have hb := Task403d.A3_norm_le_totient n 3
    norm_num [Nat.totient_prime] at hb ⊢
    linarith
  have hp5 : (5 : ℝ) ≤ p := by
    have h4 : p ≠ 4 := by intro he; subst p; norm_num at hp
    exact_mod_cast (show 5 ≤ p by omega)
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  have hG : ‖G ^ 2‖ = (p : ℝ) := quadratic_gauss_sq_norm p hp2
  have hthree : ‖3 * G ^ 2 + 1‖ ≤ 3 * (p : ℝ) + 1 := by
    calc
      _ ≤ ‖(3 : ℂ) * G ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, hG]; norm_num
  have hden : ‖((p : ℂ) - 1) ^ 3‖ = ((p : ℝ) - 1) ^ 3 := by
    rw [norm_pow]
    congr 1
    rw [← Complex.ofReal_natCast p, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [A3_odd_prime_formula p hp2 n, norm_div, hden]
  change ‖(G ^ 3 + 3 * G) * (quadraticC p (-(n : ZMod p)) * G) -
    (3 * G ^ 2 + 1) * (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1)‖ /
      ((p : ℝ) - 1) ^ 3 ≤ _
  by_cases hn : (n : ZMod p) = 0
  · have hz : quadraticC p (0 : ZMod p) = 0 := by
      simp [quadraticC, MulChar.ringHomComp_apply]
    simp only [hn, neg_zero, hz, zero_mul, mul_zero, zero_sub, norm_neg, ite_true]
    have hpnorm : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
      rw [← Complex.ofReal_natCast p, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [norm_mul, hpnorm]
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (p : ℝ) - 1) 3)).mpr
    have hnumer : ‖3 * G ^ 2 + 1‖ * ((p : ℝ) - 1) ≤
        (3 * (p : ℝ) + 1) * ((p : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hthree (by linarith)
    have hnum : ((3 : ℝ) * p + 1) * ((p : ℝ) - 1) ≤
        8 / (p : ℝ) * ((p : ℝ) - 1) ^ 3 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp0).mpr
      have hpos : 0 ≤ ((p : ℝ) - 3) * (5 * (p : ℝ) - 2) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hpos (by linarith : 0 ≤ (p : ℝ) - 1)]
    exact hnumer.trans hnum
  · rw [ite_eq_right hn]
    have heq : (G ^ 3 + 3 * G) * (quadraticC p (-(n : ZMod p)) * G) -
        (3 * G ^ 2 + 1) * (-1) =
          quadraticC p (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3) + (3 * G ^ 2 + 1) := by ring
    rw [heq]
    have hnumer : ‖quadraticC p (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3) + (3 * G ^ 2 + 1)‖ ≤
        (p : ℝ) ^ 2 + 6 * (p : ℝ) + 1 := by
      have hplus : ‖G ^ 2 + 3‖ ≤ (p : ℝ) + 3 := by
        calc _ ≤ ‖G ^ 2‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
             _ = _ := by rw [hG]; norm_num
      calc
        _ ≤ ‖quadraticC p (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3)‖ + ‖3 * G ^ 2 + 1‖ := norm_add_le _ _
        _ ≤ (p : ℝ) * ((p : ℝ) + 3) + (3 * (p : ℝ) + 1) := by
          apply add_le_add _ hthree
          rw [norm_mul, norm_mul, hG]
          have hχ := quadraticC_norm_le p (-(n : ZMod p))
          exact mul_le_mul (mul_le_of_le_one_left hp0.le hχ) hplus
            (norm_nonneg _) hp0.le
        _ = _ := by ring
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (p : ℝ) - 1) 3)).mpr
    apply hnumer.trans
    have hpos : 0 ≤ ((p : ℝ) - 5) * (7 * (p : ℝ) ^ 2 + 5 * (p : ℝ) + 48) :=
      mul_nonneg (by linarith) (by positivity)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hp0).mpr
    nlinarith

#print axioms quadraticC_properties
#print axioms full_quadratic_sum
#print axioms reduced_quadratic_sum
#print axioms quadratic_gauss_sq
#print axioms quadraticC_sq
#print axioms quadraticC_norm_le
#print axioms quadratic_gauss_shift
#print axioms quadratic_gauss_sq_norm
#print axioms A3_odd_prime_formula
#print axioms A3_odd_prime_bound

end LeanLab.KumchevLiu2007.Task438g
