/-
# R-0034, T3 MOONSHOT: majorant subtraction with Selberg's Λ² weights on both variables

Unit U-1311, PC run 20261021T0103Z-19411. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

The route: with 1_P ≤ ν, ν a Selberg Λ² majorant of level z on both variables, the identity
xy = xv + uy - uv + (u - x)(v - y) gives, for every N,
  r(N) ≥ 2 Σ_p ν(N - p) - Σ_{a+b=N} ν(a) ν(b).
The two sums on the right are sieve objects, computable from distribution of primes in
progressions, the input zero density estimates supply. Binary Goldbach at N would follow
whenever the right side is positive. In the sieve main term model the two sums are κM and κ²M,
κ the mass ratio of ν to the primes, and the bound is κ(2 - κ)M, positive only when κ < 2;
Selberg's parity example forces κ ≥ 2 for any majorant built from level below N.

PROVED here, unconditional:
* `pair_ineq`: x ≤ u, y ≤ v ⟹ x v + u y - u v ≤ x y.  Plain math: (u - x)(v - y) ≥ 0.
* `majorant_sub`: the summed form over any finite set of a.
* `goldbach_of_majorant_pos`: if the majorant lower bound with f = g = 1_P is positive, N is a
  sum of two primes.
* `parity_limit`: for κ ≥ 2 and M ≥ 0, 2κM - κ²M ≤ 0, the barrier in the main term model.
* `window_pos`: for 0 < κ < 2 and M > 0 the main term bound is positive.
* `vacuity_ten`, `vacuity_const`: concrete instances where every hypothesis holds.
-/
import LeanLab.Common.Goldbach

namespace LeanLab.R0034

open Finset

/-- Indicator of the primes as a real function. -/
noncomputable def primeInd (n : ℕ) : ℝ := if n.Prime then 1 else 0

lemma primeInd_nonneg (n : ℕ) : 0 ≤ primeInd n := by
  unfold primeInd; split_ifs <;> norm_num

lemma primeInd_le_one (n : ℕ) : primeInd n ≤ 1 := by
  unfold primeInd; split_ifs <;> norm_num

/-- The pointwise majorant inequality, from `(u - x)(v - y) ≥ 0`. -/
theorem pair_ineq (x y u v : ℝ) (hx : x ≤ u) (hy : y ≤ v) :
    x * v + u * y - u * v ≤ x * y := by
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)]

/-- Summed majorant subtraction over any finite set of first variables `a`, second `N - a`. -/
theorem majorant_sub (s : Finset ℕ) (N : ℕ) (f g u v : ℕ → ℝ)
    (hf : ∀ a ∈ s, f a ≤ u a) (hg : ∀ a ∈ s, g (N - a) ≤ v (N - a)) :
    ∑ a ∈ s, (f a * v (N - a) + u a * g (N - a) - u a * v (N - a)) ≤
      ∑ a ∈ s, f a * g (N - a) :=
  Finset.sum_le_sum fun a ha => pair_ineq _ _ _ _ (hf a ha) (hg a ha)

/-- If the majorant lower bound for the prime pair count of `N` is positive, `N` is a sum of
two primes. `s ⊆ range (N + 1)` keeps `a ≤ N`. -/
theorem goldbach_of_majorant_pos (N : ℕ) (s : Finset ℕ) (hs : s ⊆ range (N + 1))
    (u v : ℕ → ℝ) (hu : ∀ a ∈ s, primeInd a ≤ u a)
    (hv : ∀ a ∈ s, primeInd (N - a) ≤ v (N - a))
    (hpos : 0 < ∑ a ∈ s,
      (primeInd a * v (N - a) + u a * primeInd (N - a) - u a * v (N - a))) :
    IsGoldbachSum N := by
  have hsum : 0 < ∑ a ∈ s, primeInd a * primeInd (N - a) :=
    lt_of_lt_of_le hpos (majorant_sub s N _ _ u v hu hv)
  by_contra hno
  have hle : ∑ a ∈ s, primeInd a * primeInd (N - a) ≤ 0 := by
    apply Finset.sum_nonpos
    intro a ha
    have haN : a ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hs ha))
    unfold primeInd
    by_cases hp : a.Prime
    · by_cases hq : (N - a).Prime
      · exact absurd ⟨a, N - a, hp, hq, by omega⟩ hno
      · simp [hq]
    · simp [hp]
  linarith

/-- The parity limit in the main term model: sums `κM` and `κ²M` give a bound `≤ 0` once
`κ ≥ 2`. -/
theorem parity_limit (κ M : ℝ) (hκ : 2 ≤ κ) (hM : 0 ≤ M) :
    2 * (κ * M) - κ ^ 2 * M ≤ 0 := by
  have h1 : 0 ≤ κ - 2 := by linarith
  have h2 : 0 ≤ κ * M := mul_nonneg (by linarith) hM
  nlinarith [mul_nonneg h1 h2]

/-- Below the parity threshold the main term bound would be positive. -/
theorem window_pos (κ M : ℝ) (hκ0 : 0 < κ) (hκ2 : κ < 2) (hM : 0 < M) :
    0 < 2 * (κ * M) - κ ^ 2 * M := by
  have : 2 * (κ * M) - κ ^ 2 * M = κ * (2 - κ) * M := by ring
  rw [this]
  exact mul_pos (mul_pos hκ0 (by linarith)) hM

/-- Vacuity test 1: the hypotheses of `majorant_sub` hold for the primes against the constant
majorant `1`, at `N = 10`, so the inequality is a genuine statement there. -/
theorem vacuity_const :
    ∑ a ∈ range 11, (primeInd a * 1 + 1 * primeInd (10 - a) - 1 * 1) ≤
      ∑ a ∈ range 11, primeInd a * primeInd (10 - a) :=
  majorant_sub (range 11) 10 primeInd primeInd (fun _ => 1) (fun _ => 1)
    (fun a _ => primeInd_le_one a) (fun a _ => primeInd_le_one (10 - a))

/-- Vacuity test 2: with the exact majorant `u = v = 1_P` the bound is positive at `N = 10`,
the pairs 3 + 7, 5 + 5, 7 + 3, and `goldbach_of_majorant_pos` fires. -/
theorem vacuity_ten : IsGoldbachSum 10 := by
  apply goldbach_of_majorant_pos 10 (range 11) subset_rfl primeInd primeInd
    (fun a _ => le_rfl) (fun a _ => le_rfl)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, primeInd]
  norm_num

end LeanLab.R0034

#print axioms LeanLab.R0034.pair_ineq
#print axioms LeanLab.R0034.majorant_sub
#print axioms LeanLab.R0034.goldbach_of_majorant_pos
#print axioms LeanLab.R0034.parity_limit
#print axioms LeanLab.R0034.window_pos
#print axioms LeanLab.R0034.vacuity_const
#print axioms LeanLab.R0034.vacuity_ten
