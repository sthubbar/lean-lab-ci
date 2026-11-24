import LeanLab.HelfgottMajor.SPLIT_leaf_moment_full_mass_plancherel

/-!
Conditional refutation of `leaf_moment_low_mass_le` of
`SPLIT_leaf_moment_full_mass_plancherel.lean`, burst-20261122 S93, Feed1122W5.

The leaf bounds the low band zero mass by the constant `Sec45.nTwo = √π/2`, which is about
0.8862, with no dependence on the conductor `q`. A single zero is enough to break it: the
summand at one zero `ρ` of multiplicity at least one is already `‖gaussianMellin δ ρ‖ ^ 2`.
For `δ = 0` the profile is `2^(s/2-1) Γ(s/2)`, and at `s = 1/2` its squared norm is about 4.647,
so any zero of any `L χ` on the critical line with height at most about 0.85 refutes the leaf.

Numerical witness, mpmath, not checked in Lean: the odd quadratic character mod 163 has a
zero of `L(s, χ)` at `ρ = 1/2 + iγ` with `γ = 0.2029013375`, found as a sign change of the
completed function on the critical line and refined by Newton to residual below 1e-28; there
`‖gaussianMellin 0 ρ‖ ^ 2` is 3.9415844, by the Gamma closed form and by direct quadrature.
More generally the low band carries about `log q / π` zeros, so the low band mass grows like
`log q`; this is the missing conductor factor of Helfgott's bound, P0014 display 4.43 on
page 43, where the zero sum is bounded by a multiple of `log q` plus constants.

The result below proves the refutation in Lean, conditional only on the existence of such a
zero: its hypotheses are the zero, its window conditions, multiplicity at least one, and the
size of the Mellin norm. No admitted step.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122W5LowMassFalse
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.Decomp269a LeanLab.HelfgottMajor.DecompJ1153

/-- Conditional refutation of `leaf_moment_low_mass_le` at `T = 1`: one zero of `L χ` in the
strip with height at most one, multiplicity at least one, and squared Mellin norm above
`Sec45.nTwo` makes the low band mass exceed `Sec45.nTwo`. -/
theorem leaf_moment_low_mass_le_fails (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (him : |ρ.im| ≤ 1)
    (hord : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    (hbig : Sec45.nTwo < ‖gaussianMellin δ ρ‖ ^ 2) :
    ¬ ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo) := by
  classical
  intro hle
  have : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := (leaf_moment_window_finite q χ 1).fintype
  rw [tsum_fintype] at hle
  set ρ0 : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := ⟨ρ, hL, h0, h1, him⟩
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1} =>
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
    (fun x _ => by
      by_cases h : |(x : ℂ).im| ≤ 1
      · simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_true]
        exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      · simp [Set.indicator, h])
    (Finset.mem_univ ρ0)
  have hval : Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
            |ρ.im| ≤ 1} => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ0
      = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
          ‖gaussianMellin δ ρ‖ ^ 2 := by
    simp [Set.indicator, ρ0, him]
  have hord' : (1 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    exact_mod_cast hord
  have hterm : ‖gaussianMellin δ ρ‖ ^ 2 ≤
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * ‖gaussianMellin δ ρ‖ ^ 2 := by
    have := sq_nonneg ‖gaussianMellin δ ρ‖
    nlinarith
  rw [hval] at hsingle
  linarith

end LeanLab.HelfgottMajor.Feed1122W5LowMassFalse

