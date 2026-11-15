/-
MMS https://arxiv.org/abs/1610.02017v2 page 11 bottom Buchstab display.
Separate primes from composite rough numbers before the mean evaluation.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp571a

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory

/-- The normalized weighted prime term in the first Buchstab step.
MMS page 11 bottom display, prime number theorem contribution. -/
noncomputable def primeMean (x : ℝ) : ℝ :=
  Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
    Task379.referenceWeight x n * ρ n) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The composite part of the rough indicator.
MMS page 11 bottom display, first Buchstab step with primes removed.
The finite extension retains n one. Only n above one occur asymptotically. -/
noncomputable def compositeRough (n : ℕ) (y : ℝ) : ℝ :=
  if n.Prime then 0 else Task361.roughIndicator n y

/-- The normalized weighted composite rough term.
MMS page 11 bottom Buchstab display. -/
noncomputable def compositeMean (x : ℝ) : ℝ :=
  Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
    Task379.referenceWeight x n * compositeRough n (x ^ (1 / 4 : ℝ))) /
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The rough indicator is exactly the threshold test on the least prime factor.
Derived arithmetic form of the Buchstab identity used on MMS page 11.
The exclusion of one is essential. -/
theorem roughIndicator_minFac {n : ℕ} (hn : n ≠ 1) (y : ℝ) :
    Task361.roughIndicator n y = if y ≤ (n.minFac : ℝ) then 1 else 0 := by
  classical
  unfold Task361.roughIndicator
  congr 1
  apply propext
  constructor
  · intro h
    by_contra hy
    exact h n.minFac (Nat.minFac_prime hn) (lt_of_not_ge hy) (Nat.minFac_dvd n)
  · intro h p hp hpy hd
    have hm : (n.minFac : ℝ) ≤ p := by
      exact_mod_cast Nat.minFac_le_of_dvd hp.two_le hd
    linarith

/-- The composite term is a single least prime factor bucket.
Derived finite Buchstab partition for MMS page 11 bottom display. -/
theorem compositeRough_bucket {n : ℕ} (hn : n ≠ 1) (y : ℝ) :
    compositeRough n y =
      if ¬n.Prime ∧ y ≤ (n.minFac : ℝ) then 1 else 0 := by
  classical
  unfold compositeRough
  rw [roughIndicator_minFac hn]
  split_ifs <;> simp_all

/-- The cofactor after removing the least prime factor remains rough at that prime.
Derived arithmetic Buchstab step for MMS page 11 bottom display. -/
theorem minFac_cofactor_rough (n : ℕ) :
    Task361.roughIndicator (n / n.minFac) n.minFac = 1 := by
  classical
  unfold Task361.roughIndicator
  apply if_pos
  intro q hq hlt hd
  have hqn : q ∣ n := hd.trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd n))
  have hle : (n.minFac : ℝ) ≤ q := by
    exact_mod_cast Nat.minFac_le_of_dvd hq.two_le hqn
  linarith

/-- Composite rough numbers partition by their unique least prime factor.
Derived finite Buchstab identity for MMS page 11 bottom display.
Each bucket retains the actual rough cofactor at its least prime. -/
theorem compositeRough_buchstab {n : ℕ} (hn : 2 ≤ n) (y : ℝ) :
    compositeRough n y = ∑ p ∈ range (n + 1),
      if ¬n.Prime ∧ p = n.minFac ∧ y ≤ (p : ℝ) then
        Task361.roughIndicator (n / p) p else 0 := by
  classical
  rw [sum_eq_single n.minFac]
  · rw [minFac_cofactor_rough, compositeRough_bucket (by omega)]
    simp
  · intro p hp hne
    exact if_neg (fun h => hne h.2.1)
  · intro hnot
    exact False.elim (hnot (mem_range.mpr (Nat.lt_succ_of_le (Nat.minFac_le (by omega)))))

/-- Prime and composite parts partition the rough indicator above the cutoff.
Derived first Buchstab step for MMS page 11 bottom display. -/
theorem roughIndicator_split {n : ℕ} {y : ℝ} (hy : y ≤ n) :
    Task361.roughIndicator n y = ρ n + compositeRough n y := by
  classical
  by_cases hp : n.Prime
  · simp [compositeRough, ρ, hp, Task361.roughIndicator_prime hp hy]
  · simp [compositeRough, ρ, hp]

/-- Every reference interval integer lies above the fourth root cutoff.
Derived endpoint check for MMS page 11. -/
theorem reference_cutoff {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : n ∈ ints x (x + Task379.referenceLength x)) : x ^ (1 / 4 : ℝ) ≤ n := by
  have hxn : x ≤ n :=
    (Nat.le_ceil x).trans (by exact_mod_cast (mem_Icc.mp hn).1)
  exact (Real.rpow_le_self_of_one_le hx (by norm_num)).trans hxn

/-- The normalized first rough mean splits exactly into primes and composites.
MMS page 11 bottom display, before either analytic limit is used. -/
theorem weighted_rough_split {x : ℝ} (hx : 1 ≤ x) :
    Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
        primeMean x + compositeMean x := by
  have hs : (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) =
      (∑ n ∈ ints x (x + Task379.referenceLength x), Task379.referenceWeight x n * ρ n) +
      ∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * compositeRough n (x ^ (1 / 4 : ℝ)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [roughIndicator_split (reference_cutoff hx hn), mul_add]
  rw [hs]
  unfold primeMean compositeMean
  ring

/-- LEAF. The weighted prime contribution has normalized limit one.
MMS page 11 bottom display, the prime number theorem in the reference interval.
This is only the prime term and contains no composite rough numbers. -/
theorem primeMean_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |primeMean x - 1| ≤ δ := by
  sorry

/-- LEAF. The composite least prime factor buckets give the Buchstab integral.
MMS page 11 bottom display, Buchstab identity and prime number theorem,
with the prime term removed. The substitution u equals log x over log p
minus one gives the integral from one to three. This contains no prime term
and no ordered triple correction from equation 5.1. -/
theorem compositeMean_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - (∫ t in (1 : ℝ)..3, Task571.buchstabModel t)| ≤ δ := by
  sorry

/-- The Buchstab recursion identifies the sum of the two limiting coefficients.
MMS page 11 bottom display and the finite model recursion. -/
theorem rough_coefficient_identity :
    1 + (∫ t in (1 : ℝ)..3, Task571.buchstabModel t) =
      4 * Task571.buchstabModel 4 := by
  rw [Task571.buchstabModel_recursion (by norm_num) (by norm_num)]
  norm_num
  ring

/-- The exact first rough mean limit follows from its prime and composite pieces.
MMS page 11 first term of the bottom display.
CONDITIONAL ON primeMean_limit and compositeMean_limit.
This is the exact statement of the sealed roughReferenceMean_limit after unfolding. -/
theorem roughReferenceMean_limit_supply :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
        (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) -
          4 * Task571.buchstabModel 4| ≤ δ := by
  intro δ hδ
  obtain ⟨Xp, hp⟩ := primeMean_limit (δ / 2) (by linarith)
  obtain ⟨Xc, hc⟩ := compositeMean_limit (δ / 2) (by linarith)
  refine ⟨max 1 (max Xp Xc), fun x hx => ?_⟩
  rw [weighted_rough_split ((le_max_left _ _).trans hx), ← rough_coefficient_identity]
  have hp' := hp x ((le_max_left Xp Xc).trans ((le_max_right _ _).trans hx))
  have hc' := hc x ((le_max_right Xp Xc).trans ((le_max_right _ _).trans hx))
  have he : primeMean x + compositeMean x -
      (1 + ∫ t in (1 : ℝ)..3, Task571.buchstabModel t) =
      (primeMean x - 1) +
        (compositeMean x - ∫ t in (1 : ℝ)..3, Task571.buchstabModel t) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end LeanLab.Ternary.MMS.Task581
