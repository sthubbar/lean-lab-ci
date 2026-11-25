/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Split, burst-20261122 S136 round 2, of the leaf `singularCoefficient_mul` of
Decomp570aLeavesMajorP2S136Euler, page 193 definition of the coefficient A of n and q.
Multiplicativity is proved as `singularCoefficient_mul_of_leaves` from two Chinese
remainder theorem lemmas, both proved in round 2: the twisted product formula for the sums C of q, a and d, and the
reindexing of reduced residues modulo q q' by pairs a1 q' plus a2 q.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136Euler

open Finset

namespace LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136bMul

open Decomp570a Decomp319a LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136Euler

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

/-- Hu page 193. The leaf `singularCoefficient_mul` of Decomp570aLeavesMajorP2S136Euler, with
its exact statement, from the two CRT lemmas. PROVED S136 round 2. -/
theorem singularCoefficient_mul_of_leaves (r : ℤ) {q q' : ℕ} (h : Nat.Coprime q q') :
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

end LeanLab.Hathi2021.Decomp570aLeavesMajorP2S136bMul
