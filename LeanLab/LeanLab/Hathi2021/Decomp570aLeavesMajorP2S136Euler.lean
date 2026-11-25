/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Third split, burst-20261122 S136, of the leaf `singularSeries_eulerProduct` of
Decomp570aLeavesMajorP2, page 193 definition of the singular series S of n for one
prime and two prime squares, S of n equal to the sum over q of A of n and q.
The Euler product is assembled as `singularSeries_eulerProduct_of_leaves` from four
properties of the coefficient A of n and q, the standard steps behind the page 193
product formula: multiplicativity in q, vanishing on higher prime powers, absolute
convergence, and reality at primes. The conversion itself is Mathlib's Euler product
`EulerProduct.eulerProduct_hasProd` for summable multiplicative functions.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570aLeavesMajorP2

open Finset

namespace LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136Euler

open Decomp570a Decomp319a

/-- Page 193, coefficient A of n and q at the excluded denominator zero: the residue
set is empty, so A of n and 0 is zero. -/
theorem singularCoefficient_zero (r : ℤ) : singularCoefficient r 0 = 0 := by
  simp [singularCoefficient]

/-- The character e at an integer is one. -/
theorem e_intCast (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  have : (2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- Page 193, coefficient A of n and q at q equal to one: the only reduced residue
is a equal to one and every character value is one, so A of n and 1 is one. -/
theorem singularCoefficient_one (r : ℤ) : singularCoefficient r 1 = 1 := by
  have hs : (Finset.Icc 1 1).filter (fun a => Nat.Coprime a 1) = {1} := by decide
  have h1 : ∀ d : ℕ, residueSum 1 1 d = 1 := by
    intro d
    unfold residueSum
    rw [hs, Finset.sum_singleton]
    have := e_intCast 1
    simpa using this
  unfold singularCoefficient
  rw [hs, Finset.sum_singleton, h1, h1]
  have := e_intCast (-r)
  simp only [Nat.totient_one, Nat.cast_one, one_pow, div_one, one_mul, Nat.cast_one]
  convert this using 2
  push_cast; ring

/-! CRT section, S136 round 2, moved from Decomp570aLeavesMajorP2S136bMul so that
the leaf below is proved in place. -/
namespace CRT

/-- e is one periodic, local copy for the CRT section. -/
theorem e_int_add (k : ℤ) (x : ℝ) : e ((k : ℝ) + x) = e x := by
  rw [e_add, e_intCast, one_mul]

/-- Representative in Icc 1 Q of the class of x modulo Q. -/
def rep (Q x : ℕ) : ℕ := if x % Q = 0 then Q else x % Q

/-- rep Q x is congruent to x modulo Q. -/
theorem rep_modEq (Q x : ℕ) : rep Q x ≡ x [MOD Q] := by
  unfold rep
  split_ifs with h
  · show Q % Q = x % Q; rw [h, Nat.mod_self]
  · exact Nat.mod_modEq x Q

/-- rep Q x depends only on x modulo Q. -/
theorem rep_congr {Q x y : ℕ} (h : x ≡ y [MOD Q]) : rep Q x = rep Q y := by
  unfold rep; unfold Nat.ModEq at h; rw [h]

/-- rep Q x lies in Icc 1 Q. -/
theorem rep_mem {Q : ℕ} (hQ : 0 < Q) (x : ℕ) : rep Q x ∈ Icc 1 Q := by
  unfold rep
  rw [mem_Icc]
  split_ifs with h
  · omega
  · exact ⟨by omega, (Nat.mod_lt x hQ).le⟩

/-- rep Q x is x on Icc 1 Q. -/
theorem rep_self {Q x : ℕ} (hx : x ∈ Icc 1 Q) : rep Q x = x := by
  rw [mem_Icc] at hx
  unfold rep
  rcases Nat.lt_or_ge x Q with h | h
  · rw [Nat.mod_eq_of_lt h, ite_eq_right_iff.mpr (by omega)]
  · have : x = Q := by omega
    subst this; simp

/-- rep Q x is prime to Q iff x is. -/
theorem rep_coprime {Q x : ℕ} : Nat.Coprime (rep Q x) Q ↔ Nat.Coprime x Q := by
  unfold Nat.Coprime; rw [(rep_modEq Q x).gcd_eq]

/-- e of a x over Q depends only on x modulo Q. -/
theorem e_modEq {Q x y : ℕ} (hQ : 0 < Q) (a : ℕ) (h : x ≡ y [MOD Q]) :
    e ((a : ℝ) * x / Q) = e ((a : ℝ) * y / Q) := by
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd.mp h)
  have hQ' : (Q : ℝ) ≠ 0 := by positivity
  have hy : (y : ℝ) = x + Q * t := by
    have : ((y : ℤ) : ℝ) = ((x : ℤ) : ℝ) + (Q : ℤ) * t := by
      rw [← Int.cast_mul, ← Int.cast_add]; congr 1; omega
    simpa using this
  have : (a : ℝ) * y / Q = (((a : ℤ) * t : ℤ) : ℝ) + (a : ℝ) * x / Q := by
    rw [hy]; push_cast; field_simp; ring
  rw [this, e_int_add]

/-- Hu page 193, the sum C of q q', a1 q' plus a2 q and d factors as
C of q, a1 and d times C of q', a2 and d for coprime q and q', by the Chinese remainder
theorem on the reduced residues m modulo q q'.
Proved S136 round 2, formerly a MEDIUM leaf, via m to the pair m mod q, m mod q'.
P0101 page 193 definition of C of q, a and d, standard CRT factorization. -/
theorem residueSum_crt {q q' : ℕ} (h : Nat.Coprime q q') (a1 a2 d : ℕ) :
    residueSum (q * q') (a1 * q' + a2 * q) d = residueSum q a1 d * residueSum q' a2 d := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [residueSum]
  rcases Nat.eq_zero_or_pos q' with rfl | hq'
  · simp [residueSum]
  unfold residueSum
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hterm : ∀ m : ℕ, e (((a1 * q' + a2 * q : ℕ) : ℝ) * (m : ℝ) ^ d / ((q * q' : ℕ) : ℝ)) =
      e ((a1 : ℝ) * ((rep q m ^ d : ℕ) : ℝ) / q) * e ((a2 : ℝ) * ((rep q' m ^ d : ℕ) : ℝ) / q') := by
    intro m
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hq0' : (q' : ℝ) ≠ 0 := by positivity
    have : ((a1 * q' + a2 * q : ℕ) : ℝ) * (m : ℝ) ^ d / ((q * q' : ℕ) : ℝ) =
        (a1 : ℝ) * ((m ^ d : ℕ) : ℝ) / q + (a2 : ℝ) * ((m ^ d : ℕ) : ℝ) / q' := by
      push_cast; field_simp
    rw [this, e_add]
    congr 1
    · exact e_modEq hq a1 ((rep_modEq q m).pow d).symm
    · exact e_modEq hq' a2 ((rep_modEq q' m).pow d).symm
  simp_rw [hterm]
  apply Finset.sum_nbij' (fun m => (rep q m, rep q' m))
    (fun p => rep (q * q') (Nat.chineseRemainder h p.1 p.2).1)
  · intro m hm
    simp only [mem_filter, mem_product] at hm ⊢
    rw [Nat.coprime_mul_iff_right] at hm
    exact ⟨⟨rep_mem hq m, rep_coprime.mpr hm.2.1⟩, ⟨rep_mem hq' m, rep_coprime.mpr hm.2.2⟩⟩
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    have h3 := (Nat.chineseRemainder h p.1 p.2).2
    refine ⟨rep_mem (by positivity) _, ?_⟩
    rw [rep_coprime, Nat.coprime_mul_iff_right]
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq h3.1, Nat.ModEq.gcd_eq h3.2]
    exact ⟨hp.1.2, hp.2.2⟩
  · intro m hm
    simp only [mem_filter] at hm
    conv_rhs => rw [← rep_self hm.1]
    apply rep_congr
    rw [← Nat.modEq_and_modEq_iff_modEq_mul h]
    have h3 := (Nat.chineseRemainder h (rep q m) (rep q' m)).2
    exact ⟨h3.1.trans (rep_modEq q m), h3.2.trans (rep_modEq q' m)⟩
  · intro p hp
    simp only [mem_filter, mem_product] at hp
    have h3 := (Nat.chineseRemainder h p.1 p.2).2
    have h4 := rep_modEq (q * q') (Nat.chineseRemainder h p.1 p.2).1
    rw [← Nat.modEq_and_modEq_iff_modEq_mul h] at h4
    ext
    · show rep q _ = p.1
      rw [rep_congr (h4.1.trans h3.1), rep_self hp.1.1]
    · show rep q' _ = p.2
      rw [rep_congr (h4.2.trans h3.2), rep_self hp.2.1]
  · intro m _
    push_cast
    rfl

/-- A function of period Q is determined by the residue modulo Q. -/
theorem periodic_mod {Q : ℕ} (f : ℕ → ℂ) (hf : ∀ a, f (a + Q) = f a) (x : ℕ) :
    f x = f (x % Q) := by
  have key : ∀ k y, f (y + Q * k) = f y := by
    intro k; induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [Nat.mul_succ, ← add_assoc, hf, ih]
  conv_lhs => rw [← Nat.mod_add_div x Q]
  exact key _ _

/-- A function of period Q takes equal values at congruent arguments. -/
theorem periodic_congr {Q : ℕ} (f : ℕ → ℂ) (hf : ∀ a, f (a + Q) = f a) {x y : ℕ}
    (h : x ≡ y [MOD Q]) : f x = f y := by
  rw [periodic_mod f hf x, periodic_mod f hf y]; exact congrArg f h

/-- Euler inverse: q' times q' to the totient of q minus one is one modulo q. -/
theorem inv_modEq {q q' : ℕ} (h : Nat.Coprime q q') :
    q' * q' ^ (Nat.totient q - 1) ≡ 1 [MOD q] := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp at h; subst h; simp
  rw [← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.mpr hq)]
  exact Nat.ModEq.pow_totient h.symm

/-- x q' plus y q is congruent to x q' modulo q. -/
theorem lin_modEq (x y q q' : ℕ) : x * q' + y * q ≡ x * q' [MOD q] := by
  unfold Nat.ModEq; exact Nat.add_mul_mod_self_right _ _ _

/-- Hu page 193, a sum over the reduced residues a modulo q q' of a
function of period q q' equals the double sum over reduced a1 modulo q and a2 modulo q' at
a1 q' plus a2 q, for coprime q and q'.
Proved S136 round 2, formerly a MEDIUM leaf, inverse via Euler's theorem.
P0101 page 193 definition of A of n and q, standard CRT reindexing. -/
theorem reduced_sum_crt {q q' : ℕ} (h : Nat.Coprime q q') (hq : 0 < q) (hq' : 0 < q')
    (f : ℕ → ℂ) (hf : ∀ a, f (a + q * q') = f a) :
    ∑ a ∈ (Icc 1 (q * q')).filter (fun a => Nat.Coprime a (q * q')), f a =
      ∑ a1 ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ a2 ∈ (Icc 1 q').filter (fun a => Nat.Coprime a q'), f (a1 * q' + a2 * q) := by
  rw [← Finset.sum_product']
  set u := q' ^ (Nat.totient q - 1) with hu
  set u' := q ^ (Nat.totient q' - 1) with hu'
  have hinv : q' * u ≡ 1 [MOD q] := inv_modEq h
  have hinv' : q * u' ≡ 1 [MOD q'] := inv_modEq h.symm
  have hQ : 0 < q * q' := by positivity
  -- the reconstruction congruence
  have recon : ∀ a, rep q (a * u) * q' + rep q' (a * u') * q ≡ a [MOD q * q'] := by
    intro a
    rw [← Nat.modEq_and_modEq_iff_modEq_mul h]
    constructor
    · refine (lin_modEq _ _ q q').trans ?_
      have := ((rep_modEq q (a * u)).mul_right q').trans
        (show a * u * q' ≡ a * 1 [MOD q] by
          rw [mul_assoc, mul_comm u q']; exact Nat.ModEq.mul_left a hinv)
      simpa using this
    · rw [add_comm]
      refine (lin_modEq _ _ q' q).trans ?_
      have := ((rep_modEq q' (a * u')).mul_right q).trans
        (show a * u' * q ≡ a * 1 [MOD q'] by
          rw [mul_assoc, mul_comm u' q]; exact Nat.ModEq.mul_left a hinv')
      simpa using this
  apply Finset.sum_nbij' (fun a => (rep q (a * u), rep q' (a * u')))
    (fun p => rep (q * q') (p.1 * q' + p.2 * q))
  · intro a ha
    simp only [mem_filter, mem_product] at ha ⊢
    rw [Nat.coprime_mul_iff_right] at ha
    refine ⟨⟨rep_mem hq _, rep_coprime.mpr ((Nat.coprime_mul_iff_left.mpr ⟨ha.2.1, (Nat.Coprime.pow_left _ h.symm)⟩))⟩,
      ⟨rep_mem hq' _, rep_coprime.mpr ((Nat.coprime_mul_iff_left.mpr ⟨ha.2.2, (Nat.Coprime.pow_left _ h)⟩))⟩⟩
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    refine ⟨rep_mem hQ _, ?_⟩
    rw [rep_coprime, Nat.coprime_mul_iff_right]
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq (lin_modEq p.1 p.2 q q'), add_comm,
      Nat.ModEq.gcd_eq (lin_modEq p.2 p.1 q' q)]
    exact ⟨(Nat.coprime_mul_iff_left.mpr ⟨hp.1.2, h.symm⟩), (Nat.coprime_mul_iff_left.mpr ⟨hp.2.2, h⟩)⟩
  · intro a ha
    simp only [mem_filter] at ha
    conv_rhs => rw [← rep_self ha.1]
    exact rep_congr (recon a)
  · intro p hp
    simp only [mem_filter, mem_product] at hp
    have h4 := rep_modEq (q * q') (p.1 * q' + p.2 * q)
    rw [← Nat.modEq_and_modEq_iff_modEq_mul h] at h4
    ext
    · show rep q _ = p.1
      rw [← rep_self hp.1.1]
      apply rep_congr
      have := ((h4.1.trans (lin_modEq p.1 p.2 q q')).mul_right u).trans
        (show p.1 * q' * u ≡ p.1 * 1 [MOD q] by
          rw [mul_assoc]; exact Nat.ModEq.mul_left _ hinv)
      simpa [rep_self hp.1.1] using this
    · show rep q' _ = p.2
      rw [← rep_self hp.2.1]
      apply rep_congr
      have := ((h4.2.trans (by rw [add_comm]; exact lin_modEq p.2 p.1 q' q)).mul_right u').trans
        (show p.2 * q * u' ≡ p.2 * 1 [MOD q'] by
          rw [mul_assoc]; exact Nat.ModEq.mul_left _ hinv')
      simpa [rep_self hp.2.1] using this
  · intro a ha
    exact (periodic_congr f hf (recon a)).symm

/-- C of Q, a and d is periodic in a with period Q. -/
theorem residueSum_add_period (Q a d : ℕ) : residueSum Q (a + Q) d = residueSum Q a d := by
  unfold residueSum
  apply Finset.sum_congr rfl
  intro m hm
  have hQ : (Q : ℝ) ≠ 0 := by
    have := (Finset.mem_filter.mp hm).1
    rw [Finset.mem_Icc] at this
    have : 0 < Q := by omega
    positivity
  have : ((a + Q : ℕ) : ℝ) * (m : ℝ) ^ d / Q = (((m ^ d : ℕ) : ℤ) : ℝ) + (a : ℝ) * (m : ℝ) ^ d / Q := by
    push_cast; field_simp; ring
  rw [this, e_int_add]

/-- The multiplicativity statement, proved here for use in place below. -/
theorem mul_aux (r : ℤ) {q q' : ℕ} (h : Nat.Coprime q q') :
    singularCoefficient r (q * q') = singularCoefficient r q * singularCoefficient r q' := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [singularCoefficient_zero]
  rcases Nat.eq_zero_or_pos q' with rfl | hq'
  · simp [singularCoefficient_zero]
  unfold singularCoefficient
  rw [Nat.totient_mul h]
  push_cast
  rw [mul_pow, div_mul_div_comm, Finset.sum_mul_sum]
  congr 1
  rw [reduced_sum_crt h hq hq' (fun a => residueSum (q * q') a 1 * residueSum (q * q') a 2 ^ 2 *
      e (-(a : ℝ) * r / ((q : ℝ) * q')))]
  · apply Finset.sum_congr rfl
    intro a1 _
    apply Finset.sum_congr rfl
    intro a2 _
    rw [residueSum_crt h, residueSum_crt h]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hq0' : (q' : ℝ) ≠ 0 := by positivity
    have : -((a1 * q' + a2 * q : ℕ) : ℝ) * r / ((q : ℝ) * q') =
        -(a1 : ℝ) * r / q + -(a2 : ℝ) * r / q' := by
      push_cast; field_simp; ring
    rw [this, e_add]
    ring
  · intro a
    rw [residueSum_add_period, residueSum_add_period]
    congr 1
    have hQ : ((q : ℝ) * q') ≠ 0 := by positivity
    have : -((a + q * q' : ℕ) : ℝ) * r / ((q : ℝ) * q') = ((-r : ℤ) : ℝ) + -(a : ℝ) * r / ((q : ℝ) * q') := by
      push_cast; field_simp; ring
    rw [this, e_int_add]

end CRT

/-- Hu page 193, multiplicativity of the coefficient A of n and q in q: for
coprime q and q', A of n and q q' equals A of n and q times A of n and q'. By the
Chinese remainder theorem the reduced residues modulo q q' split as pairs, the sums
C of q, a and d split into twisted products, and the totient is multiplicative.
Proved S136 round 2 in the CRT section above, formerly a HARD leaf.
P0101 page 193 definition of A of n and q, standard multiplicativity. -/
theorem singularCoefficient_mul (r : ℤ) {q q' : ℕ} (h : Nat.Coprime q q') :
    singularCoefficient r (q * q') = singularCoefficient r q * singularCoefficient r q' :=
  CRT.mul_aux r h

/-- The character e at b m over M is the m th power of e at b over M. -/
theorem e_eq_pow (b M m : ℕ) : e ((b : ℝ) * m / M) = e ((b : ℝ) / M) ^ m := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

/-- e of b over M is not one when M does not divide b. -/
theorem e_ne_one_of (b M : ℕ) (hM : 0 < M) (hb : ¬ M ∣ b) : e ((b : ℝ) / M) ≠ 1 := by
  unfold e
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (((b : ℝ) / M : ℝ) : ℂ) = (n : ℂ) := by
    have : (2 * (Real.pi : ℂ) * Complex.I) * (((b : ℝ) / M : ℝ) : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by rw [hn]; ring
    exact mul_left_cancel₀ hpi this
  have h3 : ((b : ℝ) / M) = (n : ℝ) := by exact_mod_cast h2
  have hMr : (M : ℝ) ≠ 0 := by positivity
  have h4 : (b : ℝ) = n * M := by field_simp at h3; linarith
  have h5 : (b : ℤ) = n * M := by exact_mod_cast h4
  apply hb
  have : (M : ℤ) ∣ (b : ℤ) := ⟨n, by rw [h5]; ring⟩
  exact_mod_cast this

/-- The complete sum of e of b m over M over m from 1 to M vanishes when M does not divide b. -/
theorem geom_Icc_zero (b M : ℕ) (hM : 0 < M) (hb : ¬ M ∣ b) :
    ∑ m ∈ Icc 1 M, e ((b : ℝ) * m / M) = 0 := by
  have hz := e_ne_one_of b M hM hb
  have hzM : e ((b : ℝ) / M) ^ M = 1 := by
    rw [← e_eq_pow]
    have : ((b : ℝ) * (M : ℕ) / M) = ((b : ℤ) : ℝ) := by
      field_simp; push_cast; ring
    rw [this]
    unfold e
    have : (2 * (Real.pi : ℂ) * Complex.I * (((b:ℤ) : ℝ) : ℂ)) = (b : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  simp_rw [e_eq_pow]
  have : Icc 1 M = Ico 1 (M + 1) := rfl
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, pow_add, pow_one, ← Finset.mul_sum]
  rw [geom_sum_eq hz, hzM]
  simp

/-- Page 193. The Ramanujan sum C of p to the k, a and 1 vanishes for k at least two and a prime to p. -/
theorem residueSum_prime_pow_one {p k a : ℕ} (hp : p.Prime) (hk : 2 ≤ k)
    (ha : Nat.Coprime a (p ^ k)) : residueSum (p ^ k) a 1 = 0 := by
  have hpos : 0 < p := hp.pos
  have hpa : ¬ p ∣ a := by
    intro h
    have : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) ha
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm this) h)
  unfold residueSum
  simp only [pow_one]
  have hfilt : (Icc 1 (p ^ k)).filter (fun m => Nat.Coprime m (p ^ k)) =
      (Icc 1 (p ^ k)).filter (fun m => ¬ p ∣ m) := by
    apply Finset.filter_congr
    intro m _
    rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]
  rw [hfilt]
  have htot := geom_Icc_zero a (p ^ k) (by positivity) (by
    intro h; exact hpa ((dvd_pow_self p (by omega)).trans h))
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 (p ^ k)) (fun m => p ∣ m)] at htot
  have himg : (Icc 1 (p ^ k)).filter (fun m => p ∣ m) =
      (Icc 1 (p ^ (k - 1))).image (fun j => p * j) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    have hk' : p ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with h | h
        · subst h; omega
        · exact h
      · rw [hk'] at h2; exact Nat.le_of_mul_le_mul_left h2 hpos
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right p j⟩
      · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      · rw [hk']; exact Nat.mul_le_mul_left p h2
  have hsub : ∑ m ∈ (Icc 1 (p ^ k)).filter (fun m => p ∣ m), e ((a : ℝ) * m / (p ^ k : ℕ)) = 0 := by
    rw [himg, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hpos h)]
    have := geom_Icc_zero a (p ^ (k - 1)) (by positivity) (by
      intro h; exact hpa ((dvd_pow_self p (by omega)).trans h))
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hk' : (p : ℝ) ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    push_cast
    rw [hk']
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hsub, zero_add] at htot
  push_cast at htot ⊢
  exact htot

/-- Hu page 193, A of n and p to the k vanishes for k at least two: the linear
sum C of p to the k, a and 1 with a prime to p is the Ramanujan sum, which is zero for
higher prime powers. Proved S136, formerly a MEDIUM leaf.
P0101 page 193 definition of A of n and q, Ramanujan sum at prime powers. -/
theorem singularCoefficient_prime_pow (r : ℤ) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    singularCoefficient r (p ^ k) = 0 := by
  unfold singularCoefficient
  rw [Finset.sum_eq_zero, zero_div]
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [residueSum_prime_pow_one hp hk ha.2]
  simp

/-- LEAF: Hu page 193, absolute convergence of the singular series: for fixed n the
sum over q of the absolute value of A of n and q converges, since A of n and p is
at most a constant over p squared for p not dividing n, by the Gauss sum bound for C
of p, a and 2 and the Ramanujan sum value of C of p, a and 1.
Class HARD. P0101 page 193 definition of S of n, absolute convergence. -/
theorem singularCoefficient_summable_norm (r : ℤ) :
    Summable (fun q : ℕ => ‖singularCoefficient r q‖) := by
  sorry

/-- The conjugate of e of x is e of minus x. -/
theorem e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

/-- e is one periodic: e of k plus x is e of x for integer k. -/
theorem e_int_add (k : ℤ) (x : ℝ) : e ((k : ℝ) + x) = e x := by
  rw [e_add, e_intCast, one_mul]

/-- Page 193. The conjugate of C of q, a and d is C of q, q minus a and d. -/
theorem residueSum_conj {q a d : ℕ} (ha : a ≤ q) :
    (starRingEnd ℂ) (residueSum q a d) = residueSum q (q - a) d := by
  unfold residueSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [e_conj]
  have hq : (q : ℝ) ≠ 0 := by
    have := (Finset.mem_filter.mp hm).1
    rw [Finset.mem_Icc] at this
    have : 0 < q := by omega
    positivity
  have : ((q - a : ℕ) : ℝ) * (m : ℝ) ^ d / q = (((m ^ d : ℕ) : ℤ) : ℝ) + (-((a : ℝ) * (m : ℝ) ^ d / q)) := by
    rw [Nat.cast_sub ha]
    push_cast
    field_simp
    ring
  rw [this, e_int_add]

/-- Page 193. A of n and q is self conjugate for q at least two, by a to q minus a. -/
theorem singularCoefficient_conj (r : ℤ) {q : ℕ} (hq : 2 ≤ q) :
    (starRingEnd ℂ) (singularCoefficient r q) = singularCoefficient r q := by
  unfold singularCoefficient
  rw [map_div₀, map_pow, map_natCast, map_sum]
  congr 1
  apply Finset.sum_nbij' (fun a => q - a) (fun a => q - a)
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    rw [Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    have hne : a ≠ q := by
      rintro rfl; rw [Nat.coprime_self] at h3; omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.coprime_self_sub_left (by omega)]
    exact h3
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    rw [Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    have hne : a ≠ q := by
      rintro rfl; rw [Nat.coprime_self] at h3; omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.coprime_self_sub_left (by omega)]
    exact h3
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    omega
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    have haq : a ≤ q := ha.1.2
    rw [map_mul, map_mul, map_pow, residueSum_conj haq, residueSum_conj haq, e_conj]
    congr 1
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have : -((q - a : ℕ) : ℝ) * (r : ℝ) / q = ((-r : ℤ) : ℝ) + (-(-(a : ℝ) * r / q)) := by
      rw [Nat.cast_sub haq]; push_cast; field_simp; ring
    rw [this, e_int_add]

/-- Hu page 193, A of n and p is real for prime p: replacing a by minus a
conjugates every term, and minus a runs over the reduced residues modulo p again.
Proved S136, formerly a MEDIUM leaf. P0101 page 193 definition of A of n and q, symmetry a to minus a. -/
theorem singularCoefficient_prime_im (r : ℤ) (p : Nat.Primes) :
    (singularCoefficient r (p : ℕ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (singularCoefficient_conj r p.prop.two_le)

/-- Page 193. The local Euler factor: the sum over e of A of n and p to the e is
one plus A of n and p. -/
theorem localSum_eq (r : ℤ) (p : Nat.Primes) :
    ∑' k : ℕ, singularCoefficient r ((p : ℕ) ^ k) = 1 + singularCoefficient r (p : ℕ) := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, singularCoefficient_one]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    exact singularCoefficient_prime_pow r p.prop hk

/-- Hu page 193. The leaf `singularSeries_eulerProduct` of Decomp570aLeavesMajorP2,
with its exact statement, from the four coefficient leaves and Mathlib's Euler
product for summable multiplicative functions. -/
theorem singularSeries_eulerProduct_of_leaves (r : ℤ) :
    singularSeries r = ∏' p : Nat.Primes, (1 + (singularCoefficient r (p : ℕ)).re) := by
  set A := singularCoefficient r with hAdef
  have hsum := singularCoefficient_summable_norm r
  have H : HasProd (fun p : Nat.Primes => ∑' k : ℕ, A ((p : ℕ) ^ k)) (∑' n, A n) :=
    EulerProduct.eulerProduct_hasProd (singularCoefficient_one r)
      (fun h => singularCoefficient_mul r h) hsum (singularCoefficient_zero r)
  have hfac : (fun p : Nat.Primes => ∑' k : ℕ, A ((p : ℕ) ^ k)) =
      fun p : Nat.Primes => (((1 + (A (p : ℕ)).re : ℝ)) : ℂ) := by
    funext p
    rw [localSum_eq r p]
    apply Complex.ext
    · simp [hAdef]
    · simp [singularCoefficient_prime_im r p]
  rw [hfac] at H
  have Hre : HasProd (fun p : Nat.Primes => (1 + (A (p : ℕ)).re)) (∑' n, A n).re := by
    have := (Complex.continuous_re.tendsto _).comp H
    unfold HasProd
    convert this using 1
    funext s
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hshift : ∑' n, A n = ∑' q : ℕ, A (q + 1) := by
    rw [hsum.of_norm.tsum_eq_zero_add, singularCoefficient_zero r, zero_add]
  rw [Hre.tprod_eq]
  unfold singularSeries
  rw [hshift]

end LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136Euler
