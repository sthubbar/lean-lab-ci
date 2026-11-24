import LeanLab.HelfgottMajor.SPLIT_leaf_moment_high_mass_le
import LeanLab.HelfgottMajor.Decomp454h

/-!
Feed 1122 wave 3 on `leaf_high_mass_tall_le` of `SPLIT_leaf_moment_high_mass_le.lean`.

Status: the leaf is suspected FALSE in general, recorded as a QUESTION, with no Lean refutation.
Reason.  The right side `Sec45.nLog / 2` is free of the conductor `q`.  On the left, for `δ = 0`
the Mellin transform of the Gaussian is `2^(s/2 - 1) Γ(s/2)`, whose squared norm at height `τ`
is of order `exp(-π |τ| / 2) |τ|^(σ - 1)`, so tiny but positive and independent of `q`.  The
number of zeros of `L(s, χ)` with height in `[100, 200]` grows like `(50 / π) log q` by the
Riemann von Mangoldt formula for Dirichlet L functions, see P0014 around display 4.26 page 38.
So for a primitive character of conductor `q` with `log q` larger than about `exp(330)` and
`T = 200`, the tall band sum exceeds any fixed constant, in particular `Sec45.nLog / 2`.  The
same conductor growth already defeats the bounded height leaf, see `Feed1122W2HighMassBoxes.lean`;
the split's claim that all conductor dependence sits in the bounded height leaf is wrong.  In the
book P0014 the corresponding sums over zeros carry a factor `log q`, page 43 display 4.43.

What is proved here, with no sorry: the degenerate case `T ≤ max 100 (4 π² |δ|)`, where the
window holds no zero of the tall band and the sum is the empty sum `0`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122W3HighMassTall
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.DecompJ1153
open LeanLab.HelfgottMajor.Decomp269a LeanLab.HelfgottMajor.Decomp269b

/-- The tall band leaf holds when the window height `T` is at most the threshold
`max 100 (4 π² |δ|)`: then no zero lies in the tall band and the sum is `0`, which is at most
`Sec45.nLog / 2` since `Sec45.nLog ≥ 0`, P0014 display 4.42 page 43. -/
theorem leaf_high_mass_tall_le_of_T_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : T ≤ max 100 (4 * π ^ 2 * |δ|)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | max 100 (4 * π ^ 2 * |δ|) < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ 1}ᶜ)
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 2 := by
  have hzero : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | max 100 (4 * π ^ 2 * |δ|) < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ 1}ᶜ)
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ = 0 := by
    intro ρ
    apply Set.indicator_of_notMem
    rintro ⟨h1, -⟩
    have h2 := ρ.2.2.2.2
    simp only [Set.mem_ofPred_eq] at h1
    linarith
  rw [tsum_congr hzero, tsum_zero]
  have := (Decomp454h.leaf_plancherel_constants_nonneg).2
  linarith

end LeanLab.HelfgottMajor.Feed1122W3HighMassTall
