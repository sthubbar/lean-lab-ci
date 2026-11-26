import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_lower_half

/-!
Units S2-18 and S2-19 of burst-20261124, agent S2G6, the Lean half of the refutation.

The note `notes/burst-20261124/HelfgottMajor-S2-18-19-near-cells-false.md`, on branch
claude/HelfgottMajor-S2-18-19-near-cells-false, gives numerical counterexamples to the leaves
`leaf_low_mass_lower_half_near_low` and `leaf_low_mass_lower_half_near_high` of
`SPLIT_leaf_moment_low_mass_lower_half.lean`: a zero of `L χ` on the critical line for q = 19
at height 0.018956 and for q = 13 at height 0.883960, with `‖gaussianMellin 0 ρ‖ ^ 2` at least
4.61 and 0.83, above the bound `Sec45.nTwo / 8 = 0.1108`.

This file proves, with no `sorry`, that one zero in a near cell of multiplicity at least one
and squared Mellin norm above `Sec45.nTwo / 8` refutes that near cell leaf for that `q`, `χ`
and `δ`.  The theorems are CONDITIONAL ON the three numerical inputs, a zero of `L χ` in the
cell, its order at least one, and the size of the Mellin norm; a kernel checked disproof
still needs a certified zero and a certified lower bound on `|Γ(ρ / 2)|`, neither of which is
in the lab.  No new definition.
-/

namespace LeanLab.HelfgottMajor.S2G6NearCell
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- On a finite index set a sum of an indicator of nonnegative terms is at least the term of
any member of the set. -/
private theorem le_tsum_indicator {α : Type*} [Fintype α] (s : Set α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (a : α) (ha : a ∈ s) : f a ≤ ∑' x, s.indicator f x := by
  classical
  rw [tsum_fintype]
  have hfa : s.indicator f a = f a := Set.indicator_of_mem ha f
  rw [← hfa]
  exact Finset.single_le_sum (f := fun x => s.indicator f x)
    (fun x _ => Set.indicator_nonneg (fun y _ => hf y) x) (Finset.mem_univ a)

/-- The weighted squared Mellin mass of a set `s` of zeros in the window is at least the
weight of any one of its zeros of order at least one. -/
private theorem single_zero_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (s : Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1})
    (ρ0 : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1}) (hs : ρ0 ∈ s)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0.val) :
    ‖gaussianMellin δ ρ0.val‖ ^ 2 ≤
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator s
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := (DecompJ1153.leaf_moment_window_finite q χ 1).fintype
  have hle := le_tsum_indicator s
    (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2)
    (fun x => by positivity) ρ0 hs
  have h1 : (1 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0.val : ℝ) := by
    exact_mod_cast hord
  have hn : 0 ≤ ‖gaussianMellin δ ρ0.val‖ ^ 2 := by positivity
  have hmul : ‖gaussianMellin δ ρ0.val‖ ^ 2 ≤
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0.val : ℝ) *
        ‖gaussianMellin δ ρ0.val‖ ^ 2 := by nlinarith
  exact le_trans hmul hle

/-- Near low cell, S2-19: a zero `ρ0` of `L χ` with `1/4 < re ρ0 ≤ 1/2`, `|im ρ0| ≤ 1/2`, of
order at least one and with `Sec45.nTwo / 8 < ‖gaussianMellin δ ρ0‖ ^ 2`, makes the left side
of `leaf_low_mass_lower_half_near_low` exceed its bound, for this `q`, `χ`, `δ`. -/
theorem near_low_refuted_of_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (ρ0 : ℂ) (hz : DirichletCharacter.LFunction χ ρ0 = 0) (hre1 : ρ0.re < 1)
    (hlo : 1 / 4 < ρ0.re) (hhi : ρ0.re ≤ 1 / 2) (him : |ρ0.im| ≤ 1 / 2)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0)
    (hbig : Sec45.nTwo / 8 < ‖gaussianMellin δ ρ0‖ ^ 2) :
    Sec45.nTwo / 8 <
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩
          {ρ | |ρ.val.im| ≤ 1 / 2})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  have h0 : 0 < ρ0.re := lt_trans (by norm_num) hlo
  have hb : |ρ0.im| ≤ 1 := le_trans him (by norm_num)
  have hle := single_zero_le q χ δ
    (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩ {ρ | |ρ.val.im| ≤ 1 / 2})
    ⟨ρ0, hz, h0, hre1, hb⟩ ⟨⟨hhi, hlo⟩, him⟩ hord
  exact lt_of_lt_of_le hbig hle

/-- Near high cell, S2-18: a zero `ρ0` of `L χ` with `1/4 < re ρ0 ≤ 1/2`,
`1/2 < |im ρ0| ≤ 1`, of order at least one and with
`Sec45.nTwo / 8 < ‖gaussianMellin δ ρ0‖ ^ 2`, makes the left side of
`leaf_low_mass_lower_half_near_high` exceed its bound, for this `q`, `χ`, `δ`. -/
theorem near_high_refuted_of_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (ρ0 : ℂ) (hz : DirichletCharacter.LFunction χ ρ0 = 0) (hre1 : ρ0.re < 1)
    (hlo : 1 / 4 < ρ0.re) (hhi : ρ0.re ≤ 1 / 2) (him : 1 / 2 < |ρ0.im|)
    (him1 : |ρ0.im| ≤ 1)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0)
    (hbig : Sec45.nTwo / 8 < ‖gaussianMellin δ ρ0‖ ^ 2) :
    Sec45.nTwo / 8 <
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩
          {ρ | 1 / 2 < |ρ.val.im|})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  have h0 : 0 < ρ0.re := lt_trans (by norm_num) hlo
  have hle := single_zero_le q χ δ
    (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩ {ρ | 1 / 2 < |ρ.val.im|})
    ⟨ρ0, hz, h0, hre1, him1⟩ ⟨⟨hhi, hlo⟩, him⟩ hord
  exact lt_of_lt_of_le hbig hle

end LeanLab.HelfgottMajor.S2G6NearCell

#print axioms LeanLab.HelfgottMajor.S2G6NearCell.near_low_refuted_of_zero
#print axioms LeanLab.HelfgottMajor.S2G6NearCell.near_high_refuted_of_zero
