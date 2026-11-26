import LeanLab.HelfgottMajor.SPLIT_leaf_moment_high_mass_le

/-!
Burst-20261124 S2 agent G4, unit S2-15, the open leaf `leaf_high_mass_tall_le` of
`SPLIT_leaf_moment_high_mass_le.lean`.

The leaf bounds the zero sum of the tall band `max 100 (4 π² |δ|) < |im ρ| ≤ T` by the constant
`Sec45.nLog / 2`, free of the modulus `q`.  This file proves, with no `sorry`, that the leaf
fails for all `q`, `χ`, `δ`, `T` as soon as two cited facts hold, so it is a CONDITIONAL
refutation, conditional on:

* `hMellin`: a positive lower bound `m` for `‖gaussianMellin 0 s‖ ^ 2` on the rectangle
  `0 < re s < 1`, `100 < |im s| ≤ 100 + H`.  At `δ = 0` the transform is
  `2 ^ (s / 2 - 1) Γ(s / 2)`, which has no zeros, so such an `m` exists; numerically for
  `H = 20` one may take `m = exp (-193)`, see the note.
* `hCount`: the multiplicity count of the zeros of `L χ` in the strip with
  `100 < |im ρ| ≤ 100 + H` is unbounded over `q` and `χ`.  This is the Riemann von Mangoldt
  formula for primitive characters, Davenport chapter 16, main term `(H / π) log q` against an
  error `O (log q (100 + H))`, which tends to infinity for a fixed large enough `H`.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- Conditional refutation of `leaf_high_mass_tall_le`, the universal statement over
`q`, `χ`, `δ`, `T`.  At `δ = 0` the threshold is `100`, so every zero with
`100 < |im ρ| ≤ 100 + H` lies in the tall band of the window `T = 100 + H`; there the summand is
at least `m` times the multiplicity, and an unbounded multiplicity count beats the fixed
constant `Sec45.nLog / 2`. -/
theorem tall_le_false_of (H m : ℝ) (hm : 0 < m)
    (hMellin : ∀ s : ℂ, 0 < s.re → s.re < 1 → 100 < |s.im| → |s.im| ≤ 100 + H →
      m ≤ ‖gaussianMellin 0 s‖ ^ 2)
    (hCount : ∀ M : ℝ, ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      M ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 100 + H},
        Set.indicator {ρ | 100 < |ρ.val.im|}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ),
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator ({ρ | max 100 (4 * π ^ 2 * |δ|) < |ρ.val.im|} ∩
            {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
      Sec45.nLog / 2) := by
  classical
  intro hleaf
  obtain ⟨q, hq, χ, hM⟩ := hCount ((Sec45.nLog / 2 + 1) / m)
  have : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 100 + H} := (leaf_moment_window_finite q χ (100 + H)).fintype
  have hle := hleaf q χ 0 (100 + H)
  rw [tsum_fintype] at hle hM
  have hthr : max (100 : ℝ) (4 * π ^ 2 * |(0 : ℝ)|) = 100 := by simp
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 100 + H},
      m * Set.indicator {ρ | 100 < |ρ.val.im|}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator ({ρ | max 100 (4 * π ^ 2 * |(0 : ℝ)|) < |ρ.val.im|} ∩
            {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin 0 ρ.val‖ ^ 2) ρ := by
    intro ρ
    rw [hthr]
    by_cases h : 100 < |(ρ.val : ℂ).im|
    · have h1 : ¬ |(ρ.val : ℂ).im| ≤ 1 := by linarith
      have hmem : ρ ∈ ({ρ | (100 : ℝ) < |ρ.val.im|} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ :
          Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
            |ρ.im| ≤ 100 + H}) := ⟨h, h1⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 100 + H} |
          (100 : ℝ) < |ρ.val.im|} from h)]
      have hF := hMellin ρ.val ρ.2.2.1 ρ.2.2.2.1 h ρ.2.2.2.2
      have hn : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    · rw [Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 100 + H} |
          (100 : ℝ) < |ρ.val.im|} from h)]
      rw [mul_zero]
      apply Set.indicator_nonneg
      intro x _
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => hpt ρ)
  rw [← Finset.mul_sum] at hsum
  have hM' : Sec45.nLog / 2 + 1 ≤ m * ∑ ρ, Set.indicator {ρ : {ρ : ℂ //
      DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 100 + H} |
      (100 : ℝ) < |ρ.val.im|}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    rw [div_le_iff₀ hm] at hM
    linarith
  have hchain := hM'.trans (hsum.trans hle)
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
