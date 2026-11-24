import LeanLab.HelfgottMajor.SPLIT_leaf_high_mass_bounded_height_le

/-!
Burst 20261122, file W2. Report on the two open leaves of
`SPLIT_leaf_high_mass_bounded_height_le.lean`, `leaf_high_mass_absolute_box_le` and
`leaf_high_mass_delta_box_le`.

Both leaves bound a sum over the zeros of `L χ` in a height box by the constant
`Sec45.nLog / 4`, about `0.487`, which is free of the modulus `q` and of `δ`.  That is not what
P0014 proves.  Lemma 4.4, display 4.29 on pages 38 and 39 of arXiv 1305.2897v4, bounds the
corresponding zero sum by a quantity of order `√T0 log qT0`, and its proof starts from the zero
count `N(1, χ) = O*(0.819 log q + 16.8)`: the number of zeros in a box of fixed height grows like
`log q`.  So the two leaves are believed FALSE, see the QUESTION notes in the burst report; a Lean
refutation needs the existence of zeros of Dirichlet `L` functions, which Mathlib lacks, so no
negation is proved here.

What is proved here, with no `sorry`, are the degenerate cases in which the leaves do hold:
the `δ` selected box is empty when `4 π² |δ| ≤ 100`, and both boxes are empty when `T ≤ 1`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122W2HighMassBoxes
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.DecompJ1153
open LeanLab.HelfgottMajor.SplitGaussian123

/-- The log weighted energy of display 4.42 is nonnegative. -/
theorem nLog_nonneg : 0 ≤ Sec45.nLog := by
  unfold Sec45.nLog
  have heq : π ^ 2 + 2 * eulerMascheroniConstant ^ 2 +
      8 * eulerMascheroniConstant * log 2 + 8 * log 2 ^ 2 =
        π ^ 2 + 2 * (eulerMascheroniConstant + 2 * log 2) ^ 2 := by ring
  rw [heq]
  positivity

/-- The `δ` selected box leaf in the case `4 π² |δ| ≤ 100`: the box is empty, the sum is `0`. -/
theorem leaf_high_mass_delta_box_le_of_small (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hδ : 4 * π ^ 2 * |δ| ≤ 100) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | 100 < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 4 := by
  have hm : max 100 (4 * π ^ 2 * |δ|) = 100 := max_eq_left hδ
  have h0 : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | 100 < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ = 0 := by
    intro ρ
    apply Set.indicator_of_notMem
    rintro ⟨h1, h2⟩
    simp only [Set.mem_ofPred_eq, hm] at h1 h2
    linarith
  rw [tsum_congr h0, tsum_zero]
  linarith [nLog_nonneg]

/-- The absolute height box leaf in the case `T ≤ 1`: no zero of the window has
`1 < |im ρ|`, the sum is `0`. -/
theorem leaf_high_mass_absolute_box_le_of_T_le_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : T ≤ 1) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | |ρ.val.im| ≤ 100} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ)
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 4 := by
  have h0 : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | |ρ.val.im| ≤ 100} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ)
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ = 0 := by
    intro ρ
    apply Set.indicator_of_notMem
    rintro ⟨_, h2⟩
    exact h2 (le_trans ρ.2.2.2.2 hT)
  rw [tsum_congr h0, tsum_zero]
  linarith [nLog_nonneg]

/-- The `δ` selected box leaf in the case `T ≤ 1`. -/
theorem leaf_high_mass_delta_box_le_of_T_le_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : T ≤ 1) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | 100 < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog / 4 := by
  have h0 : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator ({ρ | 100 < |ρ.val.im|} ∩
          {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ = 0 := by
    intro ρ
    apply Set.indicator_of_notMem
    rintro ⟨h1, _⟩
    have := ρ.2.2.2.2
    simp only [Set.mem_ofPred_eq] at h1
    linarith
  rw [tsum_congr h0, tsum_zero]
  linarith [nLog_nonneg]


end LeanLab.HelfgottMajor.Feed1122W2HighMassBoxes
