import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_le

/-!
KEEP GOING after unit S2-19 of burst-20261124, agent S2G6: the Lean half of the refutation of
the two parents of the near low cell, `leaf_moment_low_mass_lower_half` of
`SPLIT_leaf_moment_low_mass_le.lean` and `leaf_moment_low_mass_le` of
`SPLIT_leaf_moment_full_mass_plancherel.lean`, both reported FALSE numerically by CLOUD S95 of
burst-20261122 with the zero `1/2 + 0.018956 i` of an order 18 character mod 19, whose squared
Mellin norm at `δ = 0` is 4.64, above `Sec45.nTwo = 0.886` and `Sec45.nTwo / 2`.

The two theorems below prove, with no `sorry`, that one zero in the relevant region of order
at least one and with squared Mellin norm above the bound makes the left side exceed the bound.
They are CONDITIONAL ON those numerical inputs; a kernel checked disproof still needs a
certified zero and a lower bound on `|Γ(ρ / 2)|`.  No new definition.
-/

namespace LeanLab.HelfgottMajor.S2G6LowMass
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

/-- The weighted squared Mellin mass of a set `s` of zeros in the window of height `T` is at
least the squared Mellin norm of any one of its zeros of order at least one. -/
private theorem single_zero_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (s : Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T})
    (ρ0 : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T}) (hs : ρ0 ∈ s)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0.val) :
    ‖gaussianMellin δ ρ0.val‖ ^ 2 ≤
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator s
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := (DecompJ1153.leaf_moment_window_finite q χ T).fintype
  have hle := le_tsum_indicator s
    (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2)
    (fun x => by positivity) ρ0 hs
  have h1 : (1 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0.val : ℝ) := by
    exact_mod_cast hord
  have hn : 0 ≤ ‖gaussianMellin δ ρ0.val‖ ^ 2 := by positivity
  have hmul : ‖gaussianMellin δ ρ0.val‖ ^ 2 ≤
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0.val : ℝ) *
        ‖gaussianMellin δ ρ0.val‖ ^ 2 := by nlinarith
  exact le_trans hmul hle

/-- Parent `leaf_moment_low_mass_lower_half`: a zero `ρ0` of `L χ` with
`0 < re ρ0 ≤ 1/2`, `|im ρ0| ≤ 1`, of order at least one and with
`Sec45.nTwo / 2 < ‖gaussianMellin δ ρ0‖ ^ 2`, makes the left side exceed `Sec45.nTwo / 2`. -/
theorem lower_half_refuted_of_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (ρ0 : ℂ) (hz : DirichletCharacter.LFunction χ ρ0 = 0) (h0 : 0 < ρ0.re)
    (hhi : ρ0.re ≤ 1 / 2) (him : |ρ0.im| ≤ 1)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0)
    (hbig : Sec45.nTwo / 2 < ‖gaussianMellin δ ρ0‖ ^ 2) :
    Sec45.nTwo / 2 <
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  have hre1 : ρ0.re < 1 := lt_of_le_of_lt hhi (by norm_num)
  have hle := single_zero_le q χ δ 1 {ρ | ρ.val.re ≤ 1 / 2} ⟨ρ0, hz, h0, hre1, him⟩ hhi hord
  exact lt_of_lt_of_le hbig hle

/-- Grandparent `leaf_moment_low_mass_le`: a zero `ρ0` of `L χ` in the strip with
`|im ρ0| ≤ 1` and `|im ρ0| ≤ T`, of order at least one and with
`Sec45.nTwo < ‖gaussianMellin δ ρ0‖ ^ 2`, makes the left side exceed `Sec45.nTwo`. -/
theorem low_mass_le_refuted_of_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (ρ0 : ℂ) (hz : DirichletCharacter.LFunction χ ρ0 = 0) (h0 : 0 < ρ0.re)
    (hre1 : ρ0.re < 1) (him : |ρ0.im| ≤ 1) (hT : |ρ0.im| ≤ T)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ0)
    (hbig : Sec45.nTwo < ‖gaussianMellin δ ρ0‖ ^ 2) :
    Sec45.nTwo <
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  have hle := single_zero_le q χ δ T {ρ | |ρ.val.im| ≤ 1} ⟨ρ0, hz, h0, hre1, hT⟩ him hord
  exact lt_of_lt_of_le hbig hle

end LeanLab.HelfgottMajor.S2G6LowMass

#print axioms LeanLab.HelfgottMajor.S2G6LowMass.lower_half_refuted_of_zero
#print axioms LeanLab.HelfgottMajor.S2G6LowMass.low_mass_le_refuted_of_zero
