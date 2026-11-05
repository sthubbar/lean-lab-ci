import LeanLab.ChenDoubleSieve.Decomp363e

/-!
The finite Euler product part of the dimension condition in Wu 2004.
Removing the primes dividing N can only improve the interval product bound.
This supplies no linear sieve theorem or mean value theorem.
Source: https://arxiv.org/pdf/0705.1652, page 5 equation 2.3 and page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363

/-- The local density V at an arbitrary sifting level, as on page 5. -/
def localDensity (N : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ Wu41.PS N 0 z, (1 - 1 / ((p : ℝ) - 1))

/-- Local densities are positive on every finite level for even N. -/
theorem localDensity_pos {N : ℕ} (hEven : Even N) (z : ℝ) :
    0 < localDensity N z := by
  apply Finset.prod_pos
  intro p hp
  have hs := Wu41.mem_PS.mp hp
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hs.2.2.2) hEven.two_dvd
  have hpgt : (2 : ℝ) < p := by
    exact_mod_cast (lt_of_le_of_ne hs.1.two_le (Ne.symm hp2))
  have hi : 1 / ((p : ℝ) - 1) < 1 :=
    (div_lt_one (by linarith)).2 (by linarith)
  linarith

/-- Split the local density exactly at an intermediate cutoff. -/
theorem localDensity_split (N : ℕ) {w z : ℝ} (hw : 0 ≤ w) (hwz : w ≤ z) :
    localDensity N z = localDensity N w *
      ∏ p ∈ Wu41.PS N w z, (1 - 1 / ((p : ℝ) - 1)) := by
  have hset : Wu41.PS N 0 z = Wu41.PS N 0 w ∪ Wu41.PS N w z := by
    ext p
    simp only [Finset.mem_union, Wu41.mem_PS]
    constructor
    · rintro ⟨hp, hp0, hpz, hcop⟩
      by_cases hpw : (p : ℝ) < w
      · exact Or.inl ⟨hp, hp0, hpw, hcop⟩
      · exact Or.inr ⟨hp, le_of_not_gt hpw, hpz, hcop⟩
    · rintro (⟨hp, hp0, hpw, hcop⟩ | ⟨hp, hpw, hpz, hcop⟩)
      · exact ⟨hp, hp0, hpw.trans_le hwz, hcop⟩
      · exact ⟨hp, hw.trans hpw, hpz, hcop⟩
  have hdis : Disjoint (Wu41.PS N 0 w) (Wu41.PS N w z) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpw := (Wu41.mem_PS.mp hp).2.2.1
    have hqw := (Wu41.mem_PS.mp hq).2.1
    linarith
  unfold localDensity
  rw [hset, Finset.prod_union hdis]

/-- The density ratio is the product of inverse factors in the intervening interval. -/
theorem localDensity_ratio {N : ℕ} (hEven : Even N) {w z : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) :
    localDensity N w / localDensity N z =
      ∏ p ∈ Wu41.PS N w z, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  rw [localDensity_split N hw hwz, Finset.prod_inv_distrib,
    div_mul_eq_div_div, div_self (localDensity_pos hEven w).ne', one_div]

/-- Above three the local density ratio is bounded by the same interval product
with no prime divisors of N removed. This is the uniform exclusion step in 2.3. -/
theorem localDensity_ratio_le {N : ℕ} (hEven : Even N) {w z : ℝ}
    (hw : 3 ≤ w) (hwz : w ≤ z) :
    localDensity N w / localDensity N z ≤
      ∏ p ∈ Wu41.PS 1 w z, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  rw [localDensity_ratio hEven (by linarith) hwz]
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    obtain ⟨hp, hpw, hpz, _⟩ := Wu41.mem_PS.mp hp
    exact Wu41.mem_PS.mpr ⟨hp, hpw, hpz, by simp⟩
  · intro p hp
    have hpw := (Wu41.mem_PS.mp hp).2.1
    have hpgt : (2 : ℝ) < p := by linarith
    have hi : 1 / ((p : ℝ) - 1) < 1 :=
      (div_lt_one (by linarith)).2 (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · intro p hp _
    have hpw := (Wu41.mem_PS.mp hp).2.1
    have hpgt : (2 : ℝ) < p := by linarith
    have hi : 1 / ((p : ℝ) - 1) < 1 :=
      (div_lt_one (by linarith)).2 (by linarith)
    have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) :=
      div_nonneg zero_le_one (by linarith)
    exact (one_le_inv₀ (by linarith)).2 (by linarith)

/-- A nontrivial exclusion instance: N equal six removes the prime three
from the interval, so the two density ratios are four thirds and eight thirds. -/
theorem localDensity_instance :
    localDensity 6 3 / localDensity 6 6 = 4 / 3 ∧
      (∏ p ∈ Wu41.PS 1 3 6, (1 - 1 / ((p : ℝ) - 1))⁻¹) = 8 / 3 := by
  norm_num [localDensity, Wu41.PS, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

end LeanLab.ChenDoubleSieve.Task363
