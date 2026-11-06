/-
Local moment decomposition for the complete period mean square.
Source https://arxiv.org/abs/0801.0130 page 15 first display.
Schwarz Part II page 83 displays 2.11 and 2.14 give the local setting.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.PrimeMoment447

namespace LeanLab.KumchevLiu2007.Task447a

open Real Complex Task129c Task292a
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

/-- LEAF. Page 15 first display, derived Chinese remainder step from
page 13 property i. Schwarz Part II page 83 Lemma 2.4 cites the written
Chinese remainder proof in Part I page 28 Lemma 2.5.
Only two coprime complete periods occur. There is no bound here. -/
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

/-- LEAF. Page 15 first display, derived odd prime sixth moment input
using the quadratic sums of page 2 display 8 and page 13 display 45.
Schwarz Part II page 82 display 2.6 supplies the quadratic sum setting.
This is a finite local estimate at one odd prime, with no composite modulus
or interval. The factor 1 plus 6 over p matches localMajorant. -/
theorem odd_prime_sixth_moment (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)‖ ^ 6) ≤
      (Nat.totient p : ℝ) ^ 6 / (p : ℝ) ^ 2 * (1 + 6 / (p : ℝ)) ^ 6 := by
  exact PrimeMoment447.odd_prime_sixth_moment p hp

/-- Page 13 display 45. The normalized modulus one mass equals one. -/
theorem periodMass_one : periodMass 1 = 1 := by
  simp [periodMass, Task438d.A3_one]

/-- Page 13 property ii. Every vanishing coefficient gives zero mass. -/
theorem periodMass_prime_power_zero (p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    periodMass (p ^ k) = 0 := by
  simp [periodMass, Task438f.A3_prime_power_vanish _ p k hp hk]

/-- Page 13 property ii and page 15 first display. The three retained
powers of two have normalized mass at most 4096. This is a coarse bound. -/
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

/-- Page 15 first display. Parseval converts the local sixth moment
bound into the normalized odd prime mass bound. The odd prime moment input has a clean proof. -/
theorem periodMass_odd_prime (p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    periodMass p ≤ (1 + 6 / (p : ℝ)) ^ 6 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht : (0 : ℝ) < Nat.totient p := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hi := Task438m.A3_period_square_identity p
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
all three even prime factors. The odd prime moment input has a clean proof. -/
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
power of the local prime product. Both local inputs have clean proofs. -/
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

/-- Page 15 first display. Exact Task438l.complete_period_square target,
assembled from strictly local estimates. No sorry occurs in the assembly.
Both local inputs have clean proofs. -/
theorem complete_period_square :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q →
      (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) ≤
        K * (localMajorant q ^ 6 / (q : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [one_mul, le_div_iff₀ hq0]
  simpa only [periodMass, mul_comm] using periodMass_bound q hq

#print axioms residue_sum_eq_range
#print axioms periodMass_coprime_mul
#print axioms odd_prime_sixth_moment
#print axioms periodMass_one
#print axioms periodMass_prime_power_zero
#print axioms periodMass_small_dyadic
#print axioms periodMass_odd_prime
#print axioms periodMass_prime_power
#print axioms periodMass_bound
#print axioms complete_period_square

end LeanLab.KumchevLiu2007.Task447a
