import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_lower_half

/-!
Conditional refutation of `leaf_moment_low_mass_lower_half` and of the two near cells of its
split `SPLIT_leaf_moment_low_mass_lower_half.lean`.

The leaf asks for a bound by `Sec45.nTwo / 2`, about `0.443`, uniform in the conductor.  A single
zero `ρ` of `L χ` with `re ρ ≤ 1/2`, `|im ρ| ≤ 1` and Mellin mass above `0.443` already breaks it.
Numerically, AI computed with mpmath 1.4.1: for `q = 163` and `χ` the Legendre symbol modulo
`163`, `L χ` vanishes at `ρ = 1/2 + 0.2029013375 i`, residual `|L χ ρ|` below `1e-22`, and with
`δ = 0` one has `gaussianMellin 0 ρ = 2 ^ (ρ/2 - 1) * Γ (ρ/2)`, whose squared norm is `3.9416`,
confirmed by direct quadrature.  That beats `Sec45.nTwo / 2 = 0.4431` and the near low cell
budget `Sec45.nTwo / 8 = 0.1108`.  For `q = 43` the zero `1/2 + 0.8364 i` has squared mass
`0.9990`, which beats the near high cell budget `0.1108`.  The paper bound, P0014 page 39 and
display 4.30, grows like `log q`, so a uniform constant is not what the book proves.

The theorems below are the honest Lean part: the leaf statement is refuted by any such zero,
given finiteness of the index set and a positive multiplicity.  They use no `sorry`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122W5LowerHalfFalse
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.DecompJ1153 Decomp269a Decomp269b

/-- A single index with indicator mass above the bound refutes a bound on the finite indicator
sum of a nonnegative family. -/
private theorem tsum_ind_gt {ι : Type*} [Finite ι] (s : Set ι) (f : ι → ℝ)
    (hnn : ∀ i, 0 ≤ f i) (i₀ : ι) (hi : i₀ ∈ s) (B : ℝ) (hB : B < f i₀) :
    ¬ (∑' i, Set.indicator s f i) ≤ B := by
  classical
  let _ := Fintype.ofFinite ι
  rw [tsum_fintype]
  intro h
  have h1 : Set.indicator s f i₀ ≤ ∑ i, Set.indicator s f i :=
    Finset.single_le_sum (f := fun i => Set.indicator s f i)
      (fun i _ => Set.indicator_nonneg (fun j _ => hnn j) i) (Finset.mem_univ i₀)
  rw [Set.indicator_of_mem hi] at h1
  linarith

/-- Conditional refutation of the lower half leaf: a zero `ρ` with `re ρ ≤ 1/2`, `|im ρ| ≤ 1`,
positive multiplicity and squared Mellin mass above `Sec45.nTwo / 2` contradicts it, once the
index set of zeros in the unit band is finite.  The instance `q = 163`, `δ = 0`,
`ρ = 1/2 + 0.2029 i` meets all hypotheses numerically. -/
theorem not_lower_half_of_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hfin : Finite {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1})
    (ρ : ℂ) (hz : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re) (hhalf : ρ.re ≤ 1 / 2)
    (him : |ρ.im| ≤ 1) (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    (hG : Sec45.nTwo / 2 < ‖gaussianMellin δ ρ‖ ^ 2) :
    ¬ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 2 := by
  have hlt : ρ.re < 1 := by linarith
  refine tsum_ind_gt _ _ (fun i => by positivity) ⟨ρ, hz, h0, hlt, him⟩ hhalf _ ?_
  have h1 : (1 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    exact_mod_cast hord
  have h2 : 0 ≤ ‖gaussianMellin δ ρ‖ ^ 2 := by positivity
  show Sec45.nTwo / 2 < (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
    ‖gaussianMellin δ ρ‖ ^ 2
  nlinarith

/-- Conditional refutation of the near low cell leaf `leaf_low_mass_lower_half_near_low`: a zero
with `1/4 < re ρ ≤ 1/2`, `|im ρ| ≤ 1/2`, positive multiplicity and squared mass above
`Sec45.nTwo / 8` contradicts it.  The `q = 163` zero meets the hypotheses numerically. -/
theorem not_near_low_of_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hfin : Finite {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1})
    (ρ : ℂ) (hz : DirichletCharacter.LFunction χ ρ = 0) (h0 : 1 / 4 < ρ.re)
    (hhalf : ρ.re ≤ 1 / 2) (him : |ρ.im| ≤ 1 / 2)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    (hG : Sec45.nTwo / 8 < ‖gaussianMellin δ ρ‖ ^ 2) :
    ¬ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩
          {ρ | |ρ.val.im| ≤ 1 / 2})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  have hlt : ρ.re < 1 := by linarith
  have hpos : 0 < ρ.re := by linarith
  have him1 : |ρ.im| ≤ 1 := by linarith
  refine tsum_ind_gt _ _ (fun i => by positivity) ⟨ρ, hz, hpos, hlt, him1⟩
    (by exact And.intro (And.intro hhalf h0) him) _ ?_
  have h1 : (1 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    exact_mod_cast hord
  have h2 : 0 ≤ ‖gaussianMellin δ ρ‖ ^ 2 := by positivity
  show Sec45.nTwo / 8 < (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
    ‖gaussianMellin δ ρ‖ ^ 2
  nlinarith

/-- Conditional refutation of the near high cell leaf `leaf_low_mass_lower_half_near_high`: a
zero with `1/4 < re ρ ≤ 1/2`, `1/2 < |im ρ| ≤ 1`, positive multiplicity and squared mass above
`Sec45.nTwo / 8` contradicts it.  The `q = 43` zero `1/2 + 0.8364 i` meets the hypotheses
numerically. -/
theorem not_near_high_of_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hfin : Finite {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1})
    (ρ : ℂ) (hz : DirichletCharacter.LFunction χ ρ = 0) (h0 : 1 / 4 < ρ.re)
    (hhalf : ρ.re ≤ 1 / 2) (him0 : 1 / 2 < |ρ.im|) (him : |ρ.im| ≤ 1)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    (hG : Sec45.nTwo / 8 < ‖gaussianMellin δ ρ‖ ^ 2) :
    ¬ (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator (({ρ | ρ.val.re ≤ 1 / 2} ∩ {ρ | 1 / 4 < ρ.val.re}) ∩
          {ρ | 1 / 2 < |ρ.val.im|})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  have hlt : ρ.re < 1 := by linarith
  have hpos : 0 < ρ.re := by linarith
  refine tsum_ind_gt _ _ (fun i => by positivity) ⟨ρ, hz, hpos, hlt, him⟩
    (by exact And.intro (And.intro hhalf h0) him0) _ ?_
  have h1 : (1 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    exact_mod_cast hord
  have h2 : 0 ≤ ‖gaussianMellin δ ρ‖ ^ 2 := by positivity
  show Sec45.nTwo / 8 < (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
    ‖gaussianMellin δ ρ‖ ^ 2
  nlinarith

end LeanLab.HelfgottMajor.Feed1122W5LowerHalfFalse

