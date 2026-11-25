/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Second split, burst-20261122 S123, of the leaf `singularSeries_nonneg` of
Decomp570aLeavesMajor, page 193 definition of the singular series S of n.
The leaf is assembled as `singularSeries_nonneg_of_leaves` from the Euler product
of S of n and the nonnegativity of each local factor.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570aLeavesMajor

namespace LeanLab.Hathi2021.Decomp570aLeavesMajorP2

open Decomp570a

/-- LEAF: Hu page 193, the Euler product of the singular series S of n for one prime
and two prime squares: the coefficient A of n and q is real, multiplicative in q,
vanishes on higher prime powers, and the series is absolutely convergent, so S of n
is the product over primes p of one plus the real part of A of n and p.
Class HARD. P0101 page 193 definition of S of n, standard Euler product. -/
theorem singularSeries_eulerProduct (r : ℤ) :
    singularSeries r = ∏' p : Nat.Primes, (1 + (singularCoefficient r (p : ℕ)).re) := by
  sorry

section LocalFactor
open Decomp319a

/-! Helpers for `localFactor_nonneg`, Hu page 193: orthogonality of e of a k over p
and the expansion of the local coefficient as a triple exponential sum. -/

lemma lf_filter_coprime_eq_Ico {P : ℕ} (hp : P.Prime) :
    (Finset.Icc 1 P).filter (fun m => Nat.Coprime m P) = Finset.Ico 1 P := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, hc⟩
    refine ⟨h1, lt_of_le_of_ne h2 fun h => ?_⟩
    subst h
    exact hp.one_lt.ne' (by simpa [Nat.Coprime] using hc)
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.le⟩, (Nat.coprime_of_lt_prime (by omega) h2 hp).symm⟩

lemma lf_e_pow (a : ℕ) (t : ℝ) : e ((a : ℝ) * t) = e t ^ a := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma lf_e_int (m : ℤ) : e (m : ℝ) = 1 := by
  unfold e
  rw [← Complex.exp_int_mul_two_pi_mul_I m]
  congr 1
  push_cast
  ring

lemma lf_e_int0 : e 0 = 1 := by simp [e]

lemma lf_orth (P : ℕ) (hP : 0 < P) (k : ℤ) :
    ∑ a ∈ Finset.range P, e ((a : ℝ) * k / P) = if (P : ℤ) ∣ k then (P : ℂ) else 0 := by
  have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have h1 : ∀ a : ℕ, e ((a : ℝ) * k / P) = e ((k : ℝ) / P) ^ a := by
    intro a
    rw [← lf_e_pow]
    ring_nf
  simp_rw [h1]
  have hzP : e ((k : ℝ) / P) ^ P = 1 := by
    rw [← lf_e_pow]
    rw [show (P : ℝ) * ((k : ℝ) / P) = (k : ℝ) by field_simp]
    exact lf_e_int k
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [show ((((P : ℤ) * m : ℤ)) : ℝ) / P = (m : ℝ) by push_cast; field_simp]
    simp [lf_e_int]
  · have hz : e ((k : ℝ) / P) ≠ 1 := by
      intro hz
      unfold e at hz
      rw [Complex.exp_eq_one_iff] at hz
      obtain ⟨n, hn⟩ := hz
      apply h
      refine ⟨n, ?_⟩
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
      have : ((k : ℝ) / P : ℝ) = ((n : ℂ)) := by
        apply mul_left_cancel₀ hpi
        rw [hn]; ring
      push_cast at this
      field_simp at this
      exact_mod_cast this
    rw [geom_sum_eq hz, hzP]
    simp

lemma lf_expand (P a : ℕ) (r : ℤ) :
    residueSum P a 1 * residueSum P a 2 ^ 2 * e (-(a : ℝ) * r / P) =
      ∑ x ∈ (Finset.Icc 1 P).filter (fun m => Nat.Coprime m P),
        ∑ y ∈ (Finset.Icc 1 P).filter (fun m => Nat.Coprime m P),
          ∑ z ∈ (Finset.Icc 1 P).filter (fun m => Nat.Coprime m P),
            e ((a : ℝ) * (((z : ℤ) + (y : ℤ) ^ 2 + (x : ℤ) ^ 2 - r : ℤ) : ℝ) / P) := by
  unfold residueSum
  rw [sq]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  simp only [e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end LocalFactor

/-- LEAF: Hu page 193, each local factor one plus A of n and p is nonnegative, since
it is p times the normalized count of solutions modulo p of the local congruence
x plus y squared plus z squared equal to n with x, y, z prime to p.
Class MEDIUM. P0101 page 193 definition of S of n, local densities. -/
theorem localFactor_nonneg (r : ℤ) (p : Nat.Primes) :
    0 ≤ 1 + (singularCoefficient r (p : ℕ)).re := by
  set P : ℕ := (p : ℕ) with hPdef
  have hp : P.Prime := p.2
  have hP0 : 0 < P := hp.pos
  have hS := lf_filter_coprime_eq_Ico hp
  set k : ℕ → ℕ → ℕ → ℤ := fun x y z => (z : ℤ) + (y : ℤ) ^ 2 + (x : ℤ) ^ 2 - r with hk
  set F : ℕ → ℂ := fun a => ∑ x ∈ Finset.Ico 1 P, ∑ y ∈ Finset.Ico 1 P, ∑ z ∈ Finset.Ico 1 P,
      Decomp319a.e ((a : ℝ) * ((k x y z : ℤ) : ℝ) / P) with hF
  set t : ℝ := ∑ x ∈ Finset.Ico 1 P, ∑ y ∈ Finset.Ico 1 P, ∑ z ∈ Finset.Ico 1 P,
      (if (P : ℤ) ∣ k x y z then (P : ℝ) else 0) with ht
  have ht0 : 0 ≤ t := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      Finset.sum_nonneg fun z _ => ?_
    split_ifs <;> positivity
  have htot : ∑ a ∈ Finset.range P, F a = (t : ℂ) := by
    rw [hF, ht]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [lf_orth P hP0]
    split_ifs <;> simp
  set c : ℂ := (((P - 1 : ℕ) : ℂ)) ^ 3 with hc
  have hF0 : F 0 = c := by
    rw [hF, hc]
    simp [lf_e_int0]
    ring
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : P - 1 ≠ 0 := by have := hp.two_le; omega
    exact pow_ne_zero _ (by exact_mod_cast this)
  have hsplit : ∑ a ∈ Finset.range P, F a = F 0 + ∑ a ∈ Finset.Ico 1 P, F a := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hP0]
  have hA : singularCoefficient r P = (∑ a ∈ Finset.Ico 1 P, F a) / c := by
    unfold singularCoefficient
    rw [hS, Nat.totient_prime hp, hc]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [lf_expand, hS]
  have hfin : 1 + singularCoefficient r P = ((t / ((P - 1 : ℕ) : ℝ) ^ 3 : ℝ) : ℂ) := by
    rw [hA]
    have h2 : ∑ a ∈ Finset.Ico 1 P, F a = (t : ℂ) - c := by
      rw [← htot, hsplit, hF0]; ring
    have hne : (((P - 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by
      have : P - 1 ≠ 0 := by have := hp.two_le; omega
      exact_mod_cast this
    rw [h2, hc]
    push_cast
    rw [show (((P - 1 : ℕ) : ℂ)) = (((P - 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    field_simp
    ring
  have hre : 1 + (singularCoefficient r P).re = (1 + singularCoefficient r P).re := by simp
  rw [hre, hfin, Complex.ofReal_re]
  positivity

/-- Hu page 193. The leaf `singularSeries_nonneg` of Decomp570aLeavesMajor, with its
exact statement, from the Euler product and the local factor bound. -/
theorem singularSeries_nonneg_of_leaves (r : ℤ) : 0 ≤ singularSeries r := by
  rw [singularSeries_eulerProduct r]
  exact tprod_nonneg fun p => localFactor_nonneg r p

end LeanLab.Hathi2021.Decomp570aLeavesMajorP2

#print axioms LeanLab.Hathi2021.Decomp570aLeavesMajorP2.singularSeries_nonneg_of_leaves
#print axioms LeanLab.Hathi2021.Decomp570aLeavesMajorP2.localFactor_nonneg
