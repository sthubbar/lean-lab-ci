/-
DEAD SPLIT. Unit U-1622, 2026-11-06. Do not work on any leaf in this file.
Reason: the conclusion of local_prime_mass357 is false. At q equal to 2 and a equal to 1 the
arc about 1/2 carries mass above N over log cubed N, far above the allowed bound.
Audit1622.not_leafLocalMass states this, build pending at the return of U-1622. Equation 9.1 of P0093 is used
only for q above Q equal to N to one tenth, and this leaf dropped that condition.
Live route: doubled_system_mass376 in Decomp376c, and its re-cut in SPLIT1622_exceptional.
Statements below are unchanged. This file is not on the route of linnik1951_decomposed412.
-/
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

/-- The measure theory core: for a nonnegative continuous `f`, the mass over a set covered by
finitely many closed arcs is at most the sum of the masses of the arcs. -/
private theorem cover_sum_bound_wip (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    (s : Set ℝ) (hs : MeasurableSet s) (hsb : s ⊆ Set.Icc 0 1)
    (F : Finset (ℕ × ℤ)) (lo hi : ℕ × ℤ → ℝ)
    (hsub : s ⊆ ⋃ p ∈ F, Set.Icc (lo p) (hi p)) :
    (∫ x in s, f x) ≤ ∑ p ∈ F, ∫ x in Set.Icc (lo p) (hi p), f x := by
  have hpoint : ∀ x : ℝ, s.indicator f x ≤ ∑ p ∈ F, (Set.Icc (lo p) (hi p)).indicator f x := by
    intro x
    by_cases hx : x ∈ s
    · have hex : ∃ p ∈ F, x ∈ Set.Icc (lo p) (hi p) := by
        simpa only [Set.mem_iUnion, exists_prop] using hsub hx
      obtain ⟨p, hpF, hpI⟩ := hex
      have hnonneg : ∀ q ∈ F, 0 ≤ (Set.Icc (lo q) (hi q)).indicator f x := by
        intro q _
        by_cases h : x ∈ Set.Icc (lo q) (hi q)
        · rw [Set.indicator_of_mem h]; exact hfn x
        · rw [Set.indicator_of_notMem h]
      have hsingle := Finset.single_le_sum
        (f := fun q => (Set.Icc (lo q) (hi q)).indicator f x) hnonneg hpF
      rw [Set.indicator_of_mem hpI] at hsingle
      rw [Set.indicator_of_mem hx]
      exact hsingle
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun q _ => by
        by_cases h : x ∈ Set.Icc (lo q) (hi q)
        · rw [Set.indicator_of_mem h]; exact hfn x
        · rw [Set.indicator_of_notMem h])
  have hIntS : Integrable (s.indicator f) := by
    rw [integrable_indicator_iff hs]
    exact hf.integrableOn_Icc.mono_set hsb
  have hIntP : ∀ p ∈ F, Integrable ((Set.Icc (lo p) (hi p)).indicator f) := by
    intro p _
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hf.integrableOn_Icc
  have hIntSum : Integrable (fun x => ∑ p ∈ F, (Set.Icc (lo p) (hi p)).indicator f x) :=
    integrable_finsetSum F hIntP
  have hmono := integral_mono hIntS hIntSum hpoint
  rw [integral_indicator hs, integral_finset_sum F hIntP] at hmono
  refine hmono.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun p _ => integral_indicator measurableSet_Icc)

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
  by_cases hN1 : 1 ≤ N
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h0 : (0 : ℝ) < (N : ℕ) := by exact_mod_cast (by omega : 0 < N)
      exact_mod_cast h0
    have hcont : Continuous (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2) :=
      (continuous_prime_fourier111 N hN1).norm.pow 2
    have hbound := cover_sum_bound_wip (fun α => ‖primeFourier111 N α‖ ^ 2) hcont
      (fun α => by positivity) (exceptionalArcs280 N η)
      (measurable_exceptional357 N hN1 η) (fun α hα => hα.1) F
      (fun p => (p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
      (fun p => (p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
      hcover
    have hsum : (∑ p ∈ F,
        ∫ α in Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
          ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
          ‖primeFourier111 N α‖ ^ 2) ≤
        ∑ p ∈ F, B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) *
          Real.log (N : ℝ) ^ 13 :=
      Finset.sum_le_sum (fun p hp => harc p hp)
    have halg : (∑ p ∈ F, B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) *
        Real.log (N : ℝ) ^ 13) =
        B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
          (∑ p ∈ F, 1 / (p.1 : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hq1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hq p hp
      have hppos : (0 : ℝ) < (p.1 : ℝ) := by linarith
      have hτpos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
      have hsubr : (N : ℝ) ^ (1 - (1 / 7 : ℝ)) = (N : ℝ) / ((N : ℝ) ^ (1 / 7 : ℝ)) := by
        rw [Real.rpow_sub hNpos, Real.rpow_one]
      rw [hsubr]
      field_simp
      try ring
    exact hbound.trans (hsum.trans (le_of_eq halg))
  · -- the degenerate case N = 0
    have hN0 : N = 0 := by omega
    subst hN0
    have hexp1 : ∀ m : ℕ,
        Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) = 1 := by
      intro m
      have hden : (-(((2 ^ (m + 1) : ℕ) : ℝ))) / ((0 : ℕ) : ℝ) = 0 := by simp
      rw [hden, Real.exp_zero]
    have hzero : ∀ α : ℝ, powerFourier111 0 α = 0 := by
      intro α
      have hnot : ¬ Summable (fun m : ℕ =>
          (Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
        intro h
        have h2 : Tendsto (fun m : ℕ =>
            ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖)
            atTop (𝓝 0) := by
          simpa using h.tendsto_atTop_zero.norm
        have hterm : ∀ m : ℕ,
            ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖ = 1 := by
          intro m
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hexp1 m]
          simp
        have h3 : Tendsto (fun m : ℕ =>
            ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖)
            atTop (𝓝 1) := by
          have hconst : (fun m : ℕ =>
              ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖) =
              fun _ => (1 : ℝ) := funext hterm
          rw [hconst]
          exact tendsto_const_nhds
        have h01 := tendsto_nhds_unique h2 h3
        norm_num at h01
      unfold powerFourier111
      exact tsum_eq_zero_of_not_summable hnot
    have hempty : exceptionalArcs280 0 η = ∅ := by
      have hsub0 : exceptionalArcs280 0 η ⊆ ∅ := by
        intro α hα
        have h2 := hα.2.2
        rw [hzero 0, hzero α, norm_zero, mul_zero] at h2
        exact absurd h2 (lt_irrefl 0)
      exact Set.Subset.antisymm hsub0 (Set.empty_subset _)
    have hrhs : B * ((0 : ℕ) : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log ((0 : ℕ) : ℝ) ^ 13 *
        (∑ p ∈ F, 1 / (p.1 : ℝ)) = 0 := by
      norm_num [Real.zero_rpow, Real.log_zero]
    rw [hempty, hrhs]
    simp

/-- LEAF. Step 4 of the exceptional set analysis: the logarithm is absorbed by the
saving. Beyond some point a fixed power of the logarithm of N is at most N to the
one fortieth, which is what the cover weight leaves free. This is one elementary
numeric inequality about the real logarithm and a real power. -/
theorem log_power_absorption357 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      Real.log (N : ℝ) ^ 13 ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
  refine ⟨560 ^ 7280, ?_⟩
  intro N hN
  have hNge : 560 ^ 7280 ≤ N := le_of_lt hN
  have hpos : 0 < 560 ^ 7280 := by positivity
  have hN1n : 1 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1n
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : Real.log (N : ℝ) ≤ 560 * (N : ℝ) ^ (1 / 560 : ℝ) := by
    have h := Real.log_le_rpow_div (x := (N : ℝ)) (ε := (1 / 560 : ℝ)) hNpos.le
      (by norm_num)
    rwa [show (N : ℝ) ^ (1 / 560 : ℝ) / (1 / 560 : ℝ) = 560 * (N : ℝ) ^ (1 / 560 : ℝ) by
      field_simp] at h
  have hlog0 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have h13 : Real.log (N : ℝ) ^ 13 ≤ (560 * (N : ℝ) ^ (1 / 560 : ℝ)) ^ 13 :=
    pow_le_pow_left₀ hlog0 hlog 13
  have hexp : (560 * (N : ℝ) ^ (1 / 560 : ℝ)) ^ 13 =
      (560 : ℝ) ^ 13 * (N : ℝ) ^ (13 / 560 : ℝ) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 560 : ℝ)) 13,
      ← Real.rpow_mul (le_of_lt hNpos),
      show ((1 / 560 : ℝ) * ((13 : ℕ) : ℝ)) = (13 / 560 : ℝ) by norm_num]
  have hNbig : (560 : ℝ) ^ 13 ≤ (N : ℝ) ^ (1 / 560 : ℝ) := by
    have h7280 : (560 : ℝ) ^ 7280 ≤ (N : ℝ) := by
      calc (560 : ℝ) ^ 7280 = ((560 ^ 7280 : ℕ) : ℝ) := by push_cast; norm_num
        _ ≤ (N : ℝ) := by exact_mod_cast hNge
    calc (560 : ℝ) ^ 13 = ((560 : ℝ) ^ 7280) ^ (1 / 560 : ℝ) := by
          rw [← Real.rpow_natCast (560 : ℝ) 7280,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 560),
            show (((7280 : ℕ) : ℝ) * (1 / 560 : ℝ)) = ((13 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
      _ ≤ (N : ℝ) ^ (1 / 560 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) h7280 (by norm_num)
  calc Real.log (N : ℝ) ^ 13 ≤ (560 * (N : ℝ) ^ (1 / 560 : ℝ)) ^ 13 := h13
    _ = (560 : ℝ) ^ 13 * (N : ℝ) ^ (13 / 560 : ℝ) := hexp
    _ ≤ (N : ℝ) ^ (1 / 560 : ℝ) * (N : ℝ) ^ (13 / 560 : ℝ) :=
        mul_le_mul_of_nonneg_right hNbig (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (1 / 40 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num

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
