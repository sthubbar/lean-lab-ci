/-
Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4, pages 194 and 195.
Unchanged declaration prefix moved from Decomp570b for independent supply.
The minor prime square estimate remains open here.
The other parent leaves stay in Decomp570b.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp570a
import LeanLab.Hathi2021.Decomp577a

open Finset Real MeasureTheory Filter Topology
open LeanLab.Hathi2021.Decomp319a

namespace LeanLab.Hathi2021.Decomp570b

/-- Pages 194 and 195. The absolute product before the factor G. -/
noncomputable def baseNorm (n₁ n₂ : ℕ) (α : ℝ × ℝ) : ℝ :=
  ‖S n₁ n₁ α.1‖ * ‖T n₁ n₁ α.1‖ ^ 2 *
    ‖S n₁ n₂ α.2‖ * ‖T n₁ n₂ α.2‖ ^ 2

/-- Page 194. One of the two minor coordinate strips inside the unit square
and the exceptional set. The Boolean true selects the first coordinate. -/
noncomputable def minorStrip (n₁ n₂ : ℕ) (first : Bool) : Set (ℝ × ℝ) :=
  (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩ exceptional n₁ ∩
    {α | if first then α.1 ∉ majorOne n₁ n₁ else α.2 ∉ majorOne n₁ n₂}

/-- Pages 194 to 196. The absolute mass of one minor coordinate strip,
without the power 82 factor of G. -/
noncomputable def stripMass (n₁ n₂ : ℕ) (first : Bool) : ℝ :=
  ∫ α in minorStrip n₁ n₂ first, baseNorm n₁ n₂ α

/-- Page 195. The prime linear second moment. -/
noncomputable def primeSecondMoment (n₁ n : ℕ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, ‖S n₁ n x‖ ^ 2

/-- Page 195. The prime square fourth moment. -/
noncomputable def primeSquareFourthMoment (n₁ n : ℕ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, ‖T n₁ n x‖ ^ 4

/-- Page 195. A translated one dimensional large G slice. -/
noncomputable def exceptionalSlice (n₁ : ℕ) (t : ℝ) : Set ℝ :=
  Set.Icc 0 1 ∩ {x | (PairLinnik.lam : ℝ) * L n₁ ≤ ‖G n₁ (x + t)‖}

/-- LEAF. Hu page 195, Hu and Liu reference 2 Lemma 2.5.
This is the pointwise prime square estimate on a minor arc.
The common logarithmic cutoff is retained. -/
theorem minor_prime_square_sup (C ε : ℝ) (hC : 1 < C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ → (n₁ : ℝ) ≤ C * n → ∀ x : ℝ,
      x ∉ majorOne n₁ n → ‖T n₁ n x‖ ≤ K * (n : ℝ) ^ (7 / 16 + ε : ℝ) := by
  sorry

/-- Private helper: conjugation inverts the additive character. -/
private lemma e_conj (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- Private helper: the squared modulus of `S` as a double sum of characters. -/
private lemma S_mul_conj (n₁ n : ℕ) (x : ℝ) :
    S n₁ n x * (starRingEnd ℂ) (S n₁ n x) =
      ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)),
        ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧ cutoff n₁ n < (q : ℝ)),
          ((Real.log p * Real.log q : ℝ) : ℂ) * e ((↑((p : ℤ) - (q : ℤ)) : ℝ) * x) := by
  unfold S
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  have hconj : (starRingEnd ℂ) ((Real.log q : ℂ) * e (↑q * x)) =
      (Real.log q : ℂ) * e (-(↑q * x)) := by
    rw [map_mul, e_conj, Complex.conj_ofReal]
  rw [hconj]
  have harg : (↑p * x) + -(↑q * x) = (↑((p : ℤ) - (q : ℤ)) : ℝ) * x := by
    push_cast
    ring
  calc (Real.log p : ℂ) * e (↑p * x) * ((Real.log q : ℂ) * e (-(↑q * x)))
      = ((Real.log p * Real.log q : ℝ) : ℂ) * (e (↑p * x) * e (-(↑q * x))) := by
        push_cast
        ring
    _ = ((Real.log p * Real.log q : ℝ) : ℂ) * e ((↑p * x) + -(↑q * x)) := by rw [← e_add]
    _ = ((Real.log p * Real.log q : ℝ) : ℂ) * e ((↑((p : ℤ) - (q : ℤ)) : ℝ) * x) := by
        rw [harg]

/-- Private helper: a finite character sum integrates to its zero mode. -/
private lemma integral_e_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℂ) (m : ι → ℤ) :
    (∫ x in Set.Icc (0 : ℝ) 1, ∑ i ∈ s, w i * e ((m i : ℝ) * x)) =
      ∑ i ∈ s, if m i = 0 then w i else 0 := by
  classical
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, setIntegral_e_int]
    split_ifs <;> simp
  · intro i _
    have hc : Continuous (fun x : ℝ => w i * e ((m i : ℝ) * x)) := by
      unfold e
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc

/-- Private helper: the restricted prime weight sum is bounded by the Chebyshev theta. -/
private lemma sum_log_le_theta (n₁ n : ℕ) :
    (∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)),
      Real.log p) ≤ Chebyshev.theta (n : ℝ) := by
  classical
  have hsub : (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)) ⊆
      (range (n + 1)).filter (fun p : ℕ => p.Prime) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hnn : ∀ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime), 0 ≤ Real.log p := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
    exact Real.log_nonneg (by linarith)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnn p hp)).trans ?_
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range]

/-- LEAF. Hu page 195, the well known prime linear mean square estimate.
This input involves neither G nor either two dimensional arc. -/
theorem prime_second_moment_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ →
      primeSecondMoment n₁ n ≤ K * (n : ℝ) * Real.log n := by
  classical
  refine ⟨Real.log 4, Real.log_nonneg (by norm_num), 4, ?_⟩
  intro n₁ n hn hn1
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  set P := (range (n + 1)).filter (fun p : ℕ => p.Prime ∧ cutoff n₁ n < (p : ℝ)) with hP
  have hval : primeSecondMoment n₁ n = ∑ p ∈ P, (Real.log p) ^ 2 := by
    unfold primeSecondMoment
    have hS : Continuous fun x : ℝ => S n₁ n x := by
      unfold S e
      fun_prop
    have hcont : Continuous fun x : ℝ => S n₁ n x * (starRingEnd ℂ) (S n₁ n x) :=
      hS.mul (continuous_star.comp hS)
    have hint : IntegrableOn (fun x : ℝ => S n₁ n x * (starRingEnd ℂ) (S n₁ n x))
        (Set.Icc (0 : ℝ) 1) :=
      hcont.continuousOn.integrableOn_compact isCompact_Icc
    have hre2 : (∫ x in Set.Icc (0 : ℝ) 1,
          (S n₁ n x * (starRingEnd ℂ) (S n₁ n x)).re) =
        (∫ x in Set.Icc (0 : ℝ) 1, S n₁ n x * (starRingEnd ℂ) (S n₁ n x)).re := by
      simpa using integral_re hint
    have hre : (∫ x in Set.Icc (0 : ℝ) 1, ‖S n₁ n x‖ ^ 2) =
        (∫ x in Set.Icc (0 : ℝ) 1, S n₁ n x * (starRingEnd ℂ) (S n₁ n x)).re := by
      rw [← hre2]
      refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hcomplex : (∫ x in Set.Icc (0 : ℝ) 1, S n₁ n x * (starRingEnd ℂ) (S n₁ n x)) =
        ∑ p ∈ P, (((Real.log p) ^ 2 : ℝ) : ℂ) := by
      simp_rw [S_mul_conj]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun p hp => ?_
        rw [integral_e_finset_sum, Finset.sum_eq_single p]
        · rw [if_pos (by simp)]
          push_cast
          ring
        · intro q hq hne
          refine if_neg ?_
          intro h
          exact hne (by omega)
        · intro hp'
          exact absurd hp hp'
      · intro p _
        have hc : Continuous fun x : ℝ =>
            ∑ q ∈ P, ((Real.log p * Real.log q : ℝ) : ℂ) *
              e ((↑((p : ℤ) - (q : ℤ)) : ℝ) * x) := by
          refine continuous_finsetSum _ fun q _ => ?_
          unfold e
          fun_prop
        exact hc.continuousOn.integrableOn_compact isCompact_Icc
    rw [hre, hcomplex]
    have hfin : (∑ p ∈ P, (((Real.log p) ^ 2 : ℝ) : ℂ)).re = ∑ p ∈ P, (Real.log p) ^ 2 := by
      rw [← Complex.ofReal_sum (s := P) (f := fun p : ℕ => (Real.log p) ^ 2)]
      exact Complex.ofReal_re _
    exact hfin
  rw [hval]
  have hPsub : P ⊆ (range (n + 1)).filter (fun p : ℕ => p.Prime) := by
    intro p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hmem : ∀ p ∈ P, p ≤ n := by
    intro p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    omega
  have hlogpos : ∀ p ∈ P, 0 ≤ Real.log p := by
    intro p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1.two_le
    exact Real.log_nonneg (by linarith)
  have hlogle : ∀ p ∈ P, Real.log p ≤ Real.log n := by
    intro p hp
    have hle : p ≤ n := hmem p hp
    rw [hP] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1.two_le
    exact Real.log_le_log (by linarith) (by exact_mod_cast hle)
  calc ∑ p ∈ P, (Real.log p) ^ 2 = ∑ p ∈ P, Real.log p * Real.log p :=
        Finset.sum_congr rfl fun p _ => pow_two _
    _ ≤ ∑ p ∈ P, Real.log n * Real.log p :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hlogle p hp) (hlogpos p hp)
    _ = Real.log n * ∑ p ∈ P, Real.log p := by rw [Finset.mul_sum]
    _ ≤ Real.log n * Chebyshev.theta (n : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hlogn.le
        rw [hP]
        exact sum_log_le_theta n₁ n
    _ ≤ Real.log n * (Real.log 4 * (n : ℝ)) := by
        have h := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (by positivity)
        nlinarith [hlogn.le]
    _ = Real.log 4 * (n : ℝ) * Real.log n := by ring

end LeanLab.Hathi2021.Decomp570b
