import LeanLab.HelfgottMajor.S2G4TallFalseOf
import LeanLab.HelfgottMajor.Gaussian309

/-!
Burst-20261124 S2 agent G4, KEEP GOING step after unit S2-15.

`S2G4TallFalseOf.tall_le_false_of` refutes the leaf `leaf_high_mass_tall_le` conditional on two
inputs, `hMellin` and `hCount`.  This file proves `hMellin` outright: at `δ = 0` the Gaussian
Mellin transform is `(1 / 2) 2 ^ (s / 2) Γ(s / 2)`, P0014 page 33 display 4.6 in the lab form
`Gaussian309.mellin_zero_shift`, which is continuous and nonzero on the compact rectangle
`0 ≤ re s ≤ 1`, `100 ≤ |im s| ≤ 100 + H`, so its squared norm has a positive minimum there.
The refutation `tall_le_false_of_count` is then CONDITIONAL only on the Riemann von Mangoldt
count `hCount`.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- At `δ = 0` the squared Mellin norm of the Gaussian profile has a positive lower bound on
the strip piece `0 < re s < 1`, `100 < |im s| ≤ 100 + H`: by P0014 display 4.6 it is the squared
norm of `(1 / 2) 2 ^ (s / 2) Γ(s / 2)`, continuous and nonzero on the closed rectangle. -/
theorem gaussianMellin_zero_sq_lower (H : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ s : ℂ, 0 < s.re → s.re < 1 → 100 < |s.im| → |s.im| ≤ 100 + H →
      m ≤ ‖gaussianMellin 0 s‖ ^ 2 := by
  set K : Set ℂ := {s | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 100 ≤ |s.im| ∧ |s.im| ≤ 100 + H} with hK
  set g : ℂ → ℝ := fun s => ‖(1 / 2 : ℂ) * (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2)‖ ^ 2
    with hg
  have hpole : ∀ s ∈ K, ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro s hs n h
    have hi := congrArg Complex.im h
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im, neg_zero] at hi
    have : s.im = 0 := by linarith
    have h100 := hs.2.2.1
    rw [this, abs_zero] at h100
    linarith
  have hcont : ContinuousOn g K := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    have hG : ContinuousAt (fun z : ℂ => Complex.Gamma (z / 2)) s :=
      ContinuousAt.comp (g := Complex.Gamma) (f := fun z : ℂ => z / 2) (x := s)
        (Complex.differentiableAt_Gamma (s / 2) (hpole s hs)).continuousAt
        ((continuous_id.div_const (2 : ℂ)).continuousAt)
    have hP : ContinuousAt (fun z : ℂ => (2 : ℂ) ^ (z / 2)) s :=
      (continuous_const.cpow (continuous_id.div_const 2) (fun _ => Or.inl (by norm_num))).continuousAt
    exact ((continuousAt_const.mul hP).mul hG).norm.pow 2
  have hclosed : IsClosed K := by
    have h1 : IsClosed {s : ℂ | 0 ≤ s.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {s : ℂ | s.re ≤ 1} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {s : ℂ | 100 ≤ |s.im|} :=
      isClosed_le continuous_const Complex.continuous_im.abs
    have h4 : IsClosed {s : ℂ | |s.im| ≤ 100 + H} :=
      isClosed_le Complex.continuous_im.abs continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  have hbdd : Bornology.IsBounded K := by
    apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + (100 + |H|))).subset
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.1⟩
    have him : |s.im| ≤ 100 + |H| := le_trans hs.2.2.2 (by linarith [le_abs_self H])
    exact le_trans (Complex.norm_le_abs_re_add_abs_im s) (by linarith)
  have hcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hform : ∀ s : ℂ, 0 < s.re → ‖gaussianMellin 0 s‖ ^ 2 = g s := by
    intro s hs
    rw [hg]
    dsimp only
    rw [Gaussian309.mellin_zero_shift s hs]
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, ?_⟩
    intro s h0 h1 h2 h3
    have hs : s ∈ K := ⟨h0.le, h1.le, h2.le, h3⟩
    rw [hE] at hs
    exact absurd hs (Set.notMem_empty s)
  · obtain ⟨x, hx, hmin⟩ := hcpt.exists_isMinOn hne hcont
    refine ⟨g x, ?_, ?_⟩
    · rw [hg]
      dsimp only
      apply pow_pos
      apply norm_pos_iff.mpr
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
      · exact Complex.Gamma_ne_zero (hpole x hx)
    · intro s h0 h1 h2 h3
      have hs : s ∈ K := ⟨h0.le, h1.le, h2.le, h3⟩
      rw [hform s h0]
      exact hmin hs

/-- Refutation of the universal leaf `leaf_high_mass_tall_le`, CONDITIONAL ON the Riemann von
Mangoldt count alone: if the multiplicity count of the zeros of `L χ` in the strip with
`100 < |im ρ| ≤ 100 + H` is unbounded over `q` and `χ`, the leaf fails at `δ = 0`,
`T = 100 + H`. -/
theorem tall_le_false_of_count (H : ℝ)
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
  obtain ⟨m, hm, hMellin⟩ := gaussianMellin_zero_sq_lower H
  exact tall_le_false_of H m hm hMellin hCount

end LeanLab.HelfgottMajor.DecompJ1153
