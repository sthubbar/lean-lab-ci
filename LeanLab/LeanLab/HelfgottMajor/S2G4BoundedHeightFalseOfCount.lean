import LeanLab.HelfgottMajor.S2G4BoxFalseOfCount
import LeanLab.HelfgottMajor.SPLIT_leaf_moment_high_mass_le

/-!
Burst-20261124 S2 agent G4, KEEP GOING step on `SPLIT_leaf_moment_high_mass_le.lean`, the open
leaf `leaf_high_mass_bounded_height_le`, the parent of the two box leaves.

Burst-20261122 S94, S95 and S97 found it false numerically.  This file proves, with no `sorry`,
that it fails at `δ = 0`, `T = 100`, CONDITIONAL ON the Riemann von Mangoldt count alone, using
the Mellin lower bound `gaussianMellin_zero_sq_lower_box` of `S2G4BoxFalseOfCount.lean`.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- Refutation of the universal leaf `leaf_high_mass_bounded_height_le`, CONDITIONAL ON the
Riemann von Mangoldt count alone: if the multiplicity count of the zeros of `L χ` with
`1 < |im ρ| ≤ 100` is unbounded over `q` and `χ`, the leaf fails at `δ = 0`, `T = 100`, where its
threshold is `100`.  P0014 Lemma 4.4 display 4.29 carries the matching `log q` factor. -/
theorem bounded_height_le_false_of_count
    (hCount : ∀ M : ℝ, ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      M ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 100},
        Set.indicator {ρ | 1 < |ρ.val.im|}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ),
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator ({ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)} ∩
            {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
      Sec45.nLog / 2) := by
  classical
  obtain ⟨m, hm, hMellin⟩ := gaussianMellin_zero_sq_lower_box 1 100 one_pos
  intro hleaf
  obtain ⟨q, hq, χ, hM⟩ := hCount ((Sec45.nLog / 2 + 1) / m)
  have : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 100} := (leaf_moment_window_finite q χ 100).fintype
  have hle := hleaf q χ 0 100
  have hthr : max (100 : ℝ) (4 * π ^ 2 * |(0 : ℝ)|) = 100 := by simp
  rw [tsum_fintype] at hle hM
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 100},
      m * Set.indicator {ρ | 1 < |ρ.val.im|}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator ({ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |(0 : ℝ)|)} ∩
            {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin 0 ρ.val‖ ^ 2) ρ := by
    intro ρ
    rw [hthr]
    by_cases h : 1 < |(ρ.val : ℂ).im|
    · have h1 : ¬ |(ρ.val : ℂ).im| ≤ 1 := by linarith
      have hmem : ρ ∈ ({ρ | |ρ.val.im| ≤ (100 : ℝ)} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ :
          Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
            |ρ.im| ≤ 100}) := ⟨ρ.2.2.2.2, h1⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 100} |
          (1 : ℝ) < |ρ.val.im|} from h)]
      have hF := hMellin ρ.val ρ.2.2.1 ρ.2.2.2.1 h ρ.2.2.2.2
      have hn : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    · rw [Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 100} |
          (1 : ℝ) < |ρ.val.im|} from h)]
      rw [mul_zero]
      apply Set.indicator_nonneg
      intro x _
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => hpt ρ)
  rw [← Finset.mul_sum] at hsum
  have hM' : Sec45.nLog / 2 + 1 ≤ m * ∑ ρ, Set.indicator {ρ : {ρ : ℂ //
      DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 100} |
      (1 : ℝ) < |ρ.val.im|}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    rw [div_le_iff₀ hm] at hM
    linarith
  have hchain := hM'.trans (hsum.trans hle)
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
