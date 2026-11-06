/-
Split of the exceptional prime mass estimate used by the binary Goldbach circle
method. The sealed target exceptional_prime_mass357 stays untouched in
Decomp357c; this file states the smaller steps it is assembled from and proves
the target from them under the same hypotheses.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357c

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology BigOperators

/-- LEAF. Step 1 of the exceptional set analysis: the rational arc cover and its
weight. For one absolute positive threshold, every point of the exceptional set
lies on a short arc around a rational written in lowest terms, whose denominator
is at most N to the one seventh and whose half width is the reciprocal of that
denominator times N to the one seventh. The covering rationals carry total
reciprocal weight that gains the power saving one twentieth over the trivial
weight N to the one seventh of all rationals of that size. This is the covering
and counting input only: it carries no integral and no hypothesis. -/
theorem exceptional_cover357 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∃ F : Finset (ℕ × ℤ),
        (∀ p ∈ F, 1 ≤ p.1) ∧
        (∀ p ∈ F, ¬ ((p.1 : ℤ) ∣ p.2)) ∧
        (∀ p ∈ F, (p.1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
        (∀ α ∈ exceptionalArcs280 N η, ∃ p ∈ F,
          |α - (p.2 : ℝ) / (p.1 : ℝ)| ≤
            1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))) ∧
        (∑ p ∈ F, 1 / (p.1 : ℝ)) ≤ (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) := by
  sorry

/-- LEAF. Step 2 of the exceptional set analysis: the mass of the primes on one
short arc. At a rational with denominator one at most q not dividing the
numerator, the square mean of the damped prime series over the arc of half width
the reciprocal of q times N to the one seventh is at most a constant times N
divided by both q and N to the one seventh, with a fixed power of the logarithm
of N. This is one arc only, not the whole exceptional set, and it excludes the
principal arcs where the mean is of size N. -/
theorem local_prime_mass357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ a : ℤ, ¬ ((q : ℤ) ∣ a) →
          (∫ α in Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
              ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
            ‖primeFourier111 N α‖ ^ 2) ≤
          B * (N : ℝ) / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13 := by
  sorry

/-- LEAF. Step 3 of the exceptional set analysis: the finite cover sum. The square
mean of the prime series over a set contained in the union of finitely many closed
arcs is at most the sum over those arcs of the square mean on the arc, so a
per-arc estimate turns into an estimate for the whole exceptional set with the
reciprocal denominators factored out. This is subadditivity of the integral over a
finite cover; it contains no arithmetic and no hypothesis. -/
theorem cover_mass_summation357 (N : ℕ) (η : ℝ) (F : Finset (ℕ × ℤ)) (B : ℝ)
    (hB : 0 ≤ B)
    (hq : ∀ p ∈ F, 1 ≤ p.1)
    (hcover : exceptionalArcs280 N η ⊆
      ⋃ p ∈ F, Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
        ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))))
    (harc : ∀ p ∈ F,
      (∫ α in Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
          ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
        ‖primeFourier111 N α‖ ^ 2) ≤
      B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13) :
    (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
      B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
        (∑ p ∈ F, 1 / (p.1 : ℝ)) := by
  sorry

/-- LEAF. Step 4 of the exceptional set analysis: the logarithm is absorbed by the
saving. Beyond some point a fixed power of the logarithm of N is at most N to the
one fortieth, which is what the cover weight leaves free. This is one elementary
numeric inequality about the real logarithm and a real power. -/
theorem log_power_absorption357 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      Real.log (N : ℝ) ^ 13 ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
  sorry

/-- The target assembled from the four leaves above. -/
theorem exceptional_prime_mass357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
          C * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
  obtain ⟨η, hη0, hη1, Nc, hcov⟩ := exceptional_cover357
  obtain ⟨B, hB0, NB, hmass⟩ := local_prime_mass357 hG
  obtain ⟨NL, hlog⟩ := log_power_absorption357
  refine ⟨η, hη0, hη1, B, hB0, max Nc (max NB NL), ?_⟩
  intro N hN
  have hNc : Nc < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNB : NB < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNL : NL < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos_nat : 0 < N := lt_of_le_of_lt (Nat.zero_le NL) hNL
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : 1 ≤ N := hNpos_nat
    exact_mod_cast h
  obtain ⟨F, hq, hred, hqle, hcovF, hweight⟩ := hcov N hNc
  have hsub : exceptionalArcs280 N η ⊆
      ⋃ p ∈ F, Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
        ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))) := by
    intro α hα
    obtain ⟨p, hpF, hp⟩ := hcovF α hα
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨p, hpF, ?_⟩
    simp only [Set.mem_Icc]
    have h1 := (abs_le.mp hp).1
    have h2 := (abs_le.mp hp).2
    constructor <;> linarith
  have harc : ∀ p ∈ F,
      (∫ α in Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
        ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
          ‖primeFourier111 N α‖ ^ 2) ≤
        B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13 := by
    intro p hp
    exact hmass N hNB p.1 (hq p hp) (hqle p hp) p.2 (hred p hp)
  have hsum := cover_mass_summation357 N η F B hB0.le hq hsub harc
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hcoef : 0 ≤ B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 :=
    mul_nonneg (mul_nonneg hB0.le (Real.rpow_nonneg hNpos.le _)) (pow_nonneg hlogN 13)
  have hkey1 : (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) =
      (N : ℝ) ^ (1 - (1 / 20 : ℝ)) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hkey2 : (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ) =
      (N : ℝ) ^ (1 - (1 / 40 : ℝ)) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  calc
    (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2)
        ≤ B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
            (∑ p ∈ F, 1 / (p.1 : ℝ)) := hsum
    _ ≤ B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
          (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left hweight hcoef
    _ = B * (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * Real.log (N : ℝ) ^ 13 := by
      rw [show B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
            (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) =
          B * ((N : ℝ) ^ (1 - (1 / 7 : ℝ)) * (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ)) *
            Real.log (N : ℝ) ^ 13 from by ring,
        hkey1]
    _ ≤ B * (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ) :=
      mul_le_mul_of_nonneg_left (hlog N hNL)
        (mul_nonneg hB0.le (Real.rpow_nonneg hNpos.le _))
    _ = B * (N : ℝ) ^ (1 - (1 / 40 : ℝ)) := by
      rw [show B * (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ) =
          B * ((N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ)) from by ring,
        hkey2]
    _ ≤ B * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hB0.le
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

end LeanLab.Linnik1951
