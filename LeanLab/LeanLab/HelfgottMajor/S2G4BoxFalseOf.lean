import LeanLab.HelfgottMajor.SPLIT_leaf_high_mass_bounded_height_le

/-!
Burst-20261124 S2 agent G4, units S2-10 and S2-11, the open leaves
`leaf_high_mass_absolute_box_le` and `leaf_high_mass_delta_box_le` of
`SPLIT_leaf_high_mass_bounded_height_le.lean`.

Both leaves were reported FALSE on numerics at modulus `q = 1` by burst-20261122 S94, with the
falsifier review still pending.  This file adds, with no `sorry`:

* `one_le_analyticOrderNatAt_LFunction`: every zero `ρ ≠ 1` of a Dirichlet `L` function has
  multiplicity at least `1`, so a finite list of zeros gives a lower bound for the zero sums;
* `zero_window_sum_ge`: the window sum of the leaves is at least the plain sum of the squared
  Mellin norms over any finite set of zeros of the box;
* `absolute_box_le_false_of` and `delta_box_le_false_of`: CONDITIONAL refutations of the two
  universal leaves, conditional only on a finite set of zeros of `riemannZeta` in the box whose
  squared Mellin norms add up to more than `Sec45.nLog / 4`.  That input is exactly what the
  numerics of S94 and the independent recomputation of this session check, with the zeta zeros
  of mpmath `zetazero`; a kernel checked refutation needs certified zero locations and Mellin
  values in Lean.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- Every zero `ρ ≠ 1` of `L χ` has analytic multiplicity at least one: `L χ` is analytic off
`1`, not zero at `2`, and its domain is connected, so its order at `ρ` is finite and positive. -/
theorem one_le_analyticOrderNatAt_LFunction (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) (hρ : ρ ≠ 1) (h0 : DirichletCharacter.LFunction χ ρ = 0) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z
      (Or.inl (by simpa using hz))).differentiableWithinAt
  have hnonzero : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
  have horder : analyticOrderAt (DirichletCharacter.LFunction χ) (2 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hnonzero)]
    simp
  have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    hL.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (by norm_num) (by simpa using hρ) horder
  have hpos : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    intro h
    rcases analyticOrderAt_eq_zero.mp h with h | h
    · exact h (hL ρ (by simpa using hρ))
    · exact h h0
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  by_contra hlt
  have h0' : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 0 := by omega
  rw [h0'] at hcast
  exact hpos (by simpa using hcast.symm)

/-- The window sum of the leaves restricted to a set `A` of the window is at least the plain sum
of the squared Mellin norms over any finite set `S` of zeros lying in the window and in `A`. -/
theorem zero_window_sum_ge (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (A : Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T})
    (S : Finset ℂ)
    (hS : ∀ s ∈ S, DirichletCharacter.LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T)
    (hA : ∀ s (h : DirichletCharacter.LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T),
      s ∈ S → (⟨s, h⟩ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
        ρ.re < 1 ∧ |ρ.im| ≤ T}) ∈ A) :
    ∑ s ∈ S, ‖gaussianMellin δ s‖ ^ 2 ≤
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator A
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  classical
  have : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := (leaf_moment_window_finite q χ T).fintype
  rw [tsum_fintype]
  rw [← Finset.sum_subtype_of_mem (fun s => ‖gaussianMellin δ s‖ ^ 2) hS]
  calc ∑ w ∈ S.subtype _, ‖gaussianMellin δ w.val‖ ^ 2
      ≤ ∑ w ∈ S.subtype _, Set.indicator A
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) w := by
        apply Finset.sum_le_sum
        intro w hw
        rw [Finset.mem_subtype] at hw
        have hwA : w ∈ A := hA w.val w.2 hw
        rw [Set.indicator_of_mem hwA]
        have hne : w.val ≠ 1 := by
          intro h
          have := w.2.2.2.1
          rw [h] at this
          simp at this
        have h1 : (1 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) w.val : ℝ) := by
          exact_mod_cast one_le_analyticOrderNatAt_LFunction q χ w.val hne w.2.1
        nlinarith [sq_nonneg ‖gaussianMellin δ w.val‖]
    _ ≤ ∑ w, Set.indicator A
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) w := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro w _ _
        apply Set.indicator_nonneg
        intro x _
        exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- CONDITIONAL refutation of `leaf_high_mass_absolute_box_le`, universal over `q`, `χ`, `δ`,
`T`: a finite set of zeros of `riemannZeta` in the strip with `1 < |im s| ≤ 100` whose squared
Mellin norms at some `δ` add up to more than `Sec45.nLog / 4` contradicts the leaf at `q = 1`,
`T = 100`.  S94 and this session check such a set numerically at `δ = 12`, the 29 zero pairs up
to height `100`, sum about `1.247`. -/
theorem absolute_box_le_false_of (δ : ℝ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 1 < |s.im| ∧ |s.im| ≤ 100)
    (hbig : Sec45.nLog / 4 < ∑ s ∈ S, ‖gaussianMellin δ s‖ ^ 2) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ),
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator ({ρ | |ρ.val.im| ≤ 100} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ)
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
      Sec45.nLog / 4) := by
  intro hleaf
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  have hge := zero_window_sum_ge 1 (1 : DirichletCharacter ℂ 1) δ 100
    ({ρ | |ρ.val.im| ≤ 100} ∩ {ρ | |ρ.val.im| ≤ 1}ᶜ) S
    (fun s hs => by
      obtain ⟨h0, h1, h2, _, h4⟩ := hS s hs
      exact ⟨by rw [hL]; exact h0, h1, h2, h4⟩)
    (fun s _ hs => by
      obtain ⟨_, _, _, h3, h4⟩ := hS s hs
      exact ⟨h4, by intro h; change |s.im| ≤ 1 at h; linarith⟩)
  have := hleaf 1 (1 : DirichletCharacter ℂ 1) δ 100
  linarith

/-- CONDITIONAL refutation of `leaf_high_mass_delta_box_le`, universal over `q`, `χ`, `δ`,
`T`: a finite set of zeros of `riemannZeta` in the strip with
`100 < |im s| ≤ min T (max 100 (4 π² |δ|))` whose squared Mellin norms at `δ` add up to more
than `Sec45.nLog / 4` contradicts the leaf at `q = 1`.  This session checks such a set
numerically at `δ = 20`, the 50 zero pairs with `100 < γ ≤ 200`, sum about `0.661`. -/
theorem delta_box_le_false_of (δ T : ℝ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 100 < |s.im| ∧ |s.im| ≤ T ∧
      |s.im| ≤ max 100 (4 * π ^ 2 * |δ|))
    (hbig : Sec45.nLog / 4 < ∑ s ∈ S, ‖gaussianMellin δ s‖ ^ 2) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ),
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator ({ρ | 100 < |ρ.val.im|} ∩
            {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)})
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
      Sec45.nLog / 4) := by
  intro hleaf
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  have hge := zero_window_sum_ge 1 (1 : DirichletCharacter ℂ 1) δ T
    ({ρ | 100 < |ρ.val.im|} ∩ {ρ | |ρ.val.im| ≤ max 100 (4 * π ^ 2 * |δ|)}) S
    (fun s hs => by
      obtain ⟨h0, h1, h2, _, h4, _⟩ := hS s hs
      exact ⟨by rw [hL]; exact h0, h1, h2, h4⟩)
    (fun s _ hs => by
      obtain ⟨_, _, _, h3, _, h5⟩ := hS s hs
      exact ⟨h3, h5⟩)
  have := hleaf 1 (1 : DirichletCharacter ℂ 1) δ T
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
