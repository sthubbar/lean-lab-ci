import LeanLab.HelfgottMajor.SPLIT_leaf_high_mass_bounded_height_le
import LeanLab.HelfgottMajor.Gaussian309

/-!
Burst-20261124 S2 agent G4, KEEP GOING step after unit S2-10, the open leaf
`leaf_high_mass_absolute_box_le` of `SPLIT_leaf_high_mass_bounded_height_le.lean`.

Burst-20261122 S94 found the leaf false numerically at `q = 1`, `δ = 12`, through `δ`.  This file
shows, with no `sorry`, that it also fails at `δ = 0` through the modulus, CONDITIONAL ON the
Riemann von Mangoldt count alone:

* `gaussianMellin_zero_sq_lower_box`: for `0 < a` the squared norm of `gaussianMellin 0 s` has a
  positive lower bound on `0 < re s < 1`, `a < |im s| ≤ b`, from P0014 page 33 display 4.6 in the
  lab form `Gaussian309.mellin_zero_shift`, the Gamma form `(1 / 2) 2 ^ (s / 2) Γ(s / 2)`,
  continuous and nonzero on the compact closed rectangle;
* `absolute_box_le_false_of_count`: an unbounded multiplicity count of zeros of `L χ` in the box
  `1 < |im ρ| ≤ 100` refutes the universal leaf at `δ = 0`, `T = 100`.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- At `δ = 0` the squared Mellin norm of the Gaussian profile has a positive lower bound on
the strip piece `0 < re s < 1`, `a < |im s| ≤ b` with `0 < a`: by P0014 display 4.6 it is the
squared norm of `(1 / 2) 2 ^ (s / 2) Γ(s / 2)`, continuous and nonzero on the closed
rectangle. -/
theorem gaussianMellin_zero_sq_lower_box (a b : ℝ) (ha : 0 < a) :
    ∃ m : ℝ, 0 < m ∧ ∀ s : ℂ, 0 < s.re → s.re < 1 → a < |s.im| → |s.im| ≤ b →
      m ≤ ‖gaussianMellin 0 s‖ ^ 2 := by
  set K : Set ℂ := {s | 0 ≤ s.re ∧ s.re ≤ 1 ∧ a ≤ |s.im| ∧ |s.im| ≤ b} with hK
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
    have h3 : IsClosed {s : ℂ | a ≤ |s.im|} :=
      isClosed_le continuous_const Complex.continuous_im.abs
    have h4 : IsClosed {s : ℂ | |s.im| ≤ b} :=
      isClosed_le Complex.continuous_im.abs continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  have hbdd : Bornology.IsBounded K := by
    apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |b|)).subset
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2.1⟩
    have him : |s.im| ≤ |b| := le_trans hs.2.2.2 (le_abs_self b)
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

/-- Refutation of the universal leaf `leaf_high_mass_absolute_box_le`, CONDITIONAL ON the
Riemann von Mangoldt count alone: if the multiplicity count of the zeros of `L χ` in the strip
with `1 < |im ρ| ≤ 100` is unbounded over `q` and `χ`, the leaf fails at `δ = 0`, `T = 100`.
P0014 Lemma 4.4 display 4.29 carries the matching `log q` factor. -/
theorem absolute_box_le_false_of_count
    (hCount : ∀ M : ℝ, ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      M ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 100},
        Set.indicator {ρ | 1 < |ρ.val.im|}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ),
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator ({ρ | |ρ.val.im| ≤ 100} ∩
            {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
      Sec45.nLog / 4) := by
  classical
  obtain ⟨m, hm, hMellin⟩ := gaussianMellin_zero_sq_lower_box 1 100 one_pos
  intro hleaf
  obtain ⟨q, hq, χ, hM⟩ := hCount ((Sec45.nLog / 4 + 1) / m)
  have : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 100} := (leaf_moment_window_finite q χ 100).fintype
  have hle := hleaf q χ 0 100
  rw [tsum_fintype] at hle hM
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 100},
      m * Set.indicator {ρ | 1 < |ρ.val.im|}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ ≤
        Set.indicator ({ρ | |ρ.val.im| ≤ 100} ∩
            {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin 0 ρ.val‖ ^ 2) ρ := by
    intro ρ
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
  have hM' : Sec45.nLog / 4 + 1 ≤ m * ∑ ρ, Set.indicator {ρ : {ρ : ℂ //
      DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 100} |
      (1 : ℝ) < |ρ.val.im|}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    rw [div_le_iff₀ hm] at hM
    linarith
  have hchain := hM'.trans (hsum.trans hle)
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
