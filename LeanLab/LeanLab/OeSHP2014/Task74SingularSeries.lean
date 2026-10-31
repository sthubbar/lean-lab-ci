import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The elementary singleton case of equation 2.3 on page 2045.
The odd prime product is written with division in place of a negative power.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

abbrev OddPrime := {p : ℕ // p.Prime ∧ p ≠ 2}

/-- Number of occupied residue classes for integer shifts. -/
def residueCount (h : Finset ℤ) (p : ℕ) : ℕ :=
  (h.image fun z => z % (p : ℤ)).card

/-- The singular series of equation 2.3, as a total infinite product. -/
noncomputable def singularSeries (h : Finset ℤ) : ℝ :=
  2 ^ (h.card - 1) * ∏' p : OddPrime,
    (1 - (residueCount h p.val : ℝ) / p.val) / (1 - 1 / (p.val : ℝ)) ^ h.card

/-- A singleton has singular series one, the first entry of Table 6. -/
theorem singularSeries_singleton (a : ℤ) : singularSeries {a} = 1 := by
  unfold singularSeries residueCount
  simp only [Finset.card_singleton, Finset.image_singleton, Nat.sub_self, pow_zero,
    one_mul, Nat.cast_one, pow_one]
  have hf : ∀ p : OddPrime, (1 - 1 / (p.val : ℝ)) / (1 - 1 / (p.val : ℝ)) = 1 := by
    intro p
    have hp : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.1.two_le
    have hpos : 0 < 1 - 1 / (p.val : ℝ) := by
      have hp0 : (0 : ℝ) < p.val := by linarith
      rw [sub_pos, div_lt_one hp0]
      linarith
    exact div_self (ne_of_gt hpos)
  simp only [hf, tprod_one]

/-- The coefficient sum in equation 2.4 for an arbitrary finite pool of shifts. -/
noncomputable def coefficientC (s : Finset ℤ) (p : ℤ) (k : ℕ) : ℝ :=
  ∑ t ∈ s.powerset.filter (fun t => p ∈ t ∧ t.card = k), singularSeries t

/-- The size one coefficient is exactly one whenever the distinguished shift is present. -/
theorem coefficientC_one (s : Finset ℤ) (p : ℤ) (hp : p ∈ s) : coefficientC s p 1 = 1 := by
  have he : s.powerset.filter (fun t => p ∈ t ∧ t.card = 1) = {{p}} := by
    ext t
    constructor
    · intro ht
      have ht' := Finset.mem_filter.mp ht
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp ht'.2.2
      subst t
      have hpq : p = q := Finset.mem_singleton.mp ht'.2.1
      subst q
      simp
    · intro ht
      have ht' : t = {p} := Finset.mem_singleton.mp ht
      subst t
      simp [hp]
  unfold coefficientC
  rw [he, Finset.sum_singleton, singularSeries_singleton]

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.singularSeries_singleton

#print axioms LeanLab.OeSHP2014.Task74.coefficientC_one
