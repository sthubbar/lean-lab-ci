import Mathlib
import LeanLab.Pintz2021.DecompJ665

/-!
Audit of `DecompJ803.leaf_truncation_error_2` and its twin `DecompJ834.leaf_truncation_error_3`,
burst-20261122-S105.  AI wrote the Lean code. Goldbach is open.

Both leaves bound the truncation error of display 2.22 of arXiv:1804.05561v1 by
`C' * (Sing m * X * log U / sqrt U)` for EVERY cutoff `U ≥ 2` and every level `1 ≤ P ≤ P0`.
This file proves, sorry free, two facts:

* `error_eventually_lcm_discarded`: once `U` is past a finite threshold, the error equals the
  fixed sum `D` of the pair terms whose lcm `[r₁, r₂]` exceeds `P`; these pairs are discarded at
  every cutoff.
* `lcm_discarded_sum_eq_zero_of_bound`: any bound of the leaf's shape forces `D = 0`, because the
  right hand side tends to zero as `U → ∞`.

So the leaves hold only if the permanently discarded lcm pairs cancel exactly at every admitted
level.  This is the obstruction CODEX task393 named in prose; it is now a Lean statement.  No
refutation is claimed: a refutation would need an explicit pair of L zeros of conductors with
lcm above `P`, which Mathlib cannot construct.
-/

namespace LeanLab.Pintz2021.Feed1122DecompJ803Cancel

open Complex Finset Filter Topology
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DecompJ281 LeanLab.Pintz2021.DecompJ665

attribute [local instance] Classical.propDecidable

/-- Past a finite cutoff the truncation error of display 2.22 is the sum of the pair terms whose
lcm exceeds `P`, a quantity that does not depend on `U`. -/
theorem error_eventually_lcm_discarded (H : ℝ) {X : ℝ} (P ε : ℝ) (m : ℕ)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (E : Finset ExcPair)
    (hE : (E : Set ExcPair) = excSet H (Real.sqrt X) P X) :
    ∃ U0 : ℝ, 2 ≤ U0 ∧ ∀ U : ℝ, U0 ≤ U →
      mainTermPrime (excSet H (Real.sqrt X) P X) Sg ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg ε X P U m =
      ∑ p ∈ (E ×ˢ E).filter (fun p => ¬ ((Nat.lcm p.1.r p.2.r : ℝ) ≤ P)),
        Truncation168.pairTerm Sg ε X m p := by
  let F : ExcPair × ExcPair → ℝ := fun p =>
    max (max |p.1.ρ.im| |p.2.ρ.im|) (UCutoff p.1 p.2 m)
  obtain ⟨B, hB⟩ := ((E ×ˢ E).finite_toSet.image F).bddAbove
  refine ⟨max B 2, le_max_right _ _, fun U hU => ?_⟩
  have hret : Truncation168.retainedPairs E P U m =
      (E ×ˢ E).filter (fun p => (Nat.lcm p.1.r p.2.r : ℝ) ≤ P) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hz, hw, -, -, hl, -⟩ := Truncation168.mem_retainedPairs.mp hp
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hz, hw⟩, hl⟩
    · intro hp
      obtain ⟨hp1, hl⟩ := mem_filter.mp hp
      obtain ⟨hz, hw⟩ := mem_product.mp hp1
      have hb : F p ≤ U :=
        (hB (Set.mem_image_of_mem F hp1)).trans ((le_max_left _ _).trans hU)
      have hb' := max_le_iff.mp hb
      obtain ⟨p1, p2⟩ := p
      exact Truncation168.mem_retainedPairs.mpr
        ⟨hz, hw, (max_le_iff.mp hb'.1).1, (max_le_iff.mp hb'.1).2, hl, hb'.2⟩
  rw [← hE, truncatedPrime_eq_finite, Truncation168.main_partition E Sg ε X P U m,
    add_sub_cancel_left, hret, ← filter_not]

/-- `log U / sqrt U → 0` as `U → ∞`. -/
theorem tendsto_log_div_sqrt :
    Tendsto (fun U : ℝ => Real.log U / Real.sqrt U) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with U hU
  rw [Real.sqrt_eq_rpow]

/-- Any bound of the shape of `leaf_truncation_error_2` at one instance forces the permanently
discarded lcm sum to vanish. -/
theorem lcm_discarded_sum_eq_zero_of_bound (H : ℝ) {X : ℝ} (P ε C' : ℝ) (m : ℕ)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (E : Finset ExcPair)
    (hE : (E : Set ExcPair) = excSet H (Real.sqrt X) P X)
    (hb : ∀ U : ℝ, 2 ≤ U →
      ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg ε X P U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U)) :
    ∑ p ∈ (E ×ˢ E).filter (fun p => ¬ ((Nat.lcm p.1.r p.2.r : ℝ) ≤ P)),
      Truncation168.pairTerm Sg ε X m p = 0 := by
  obtain ⟨U0, hU0, hD⟩ := error_eventually_lcm_discarded H P ε m Sg E hE
  set D := ∑ p ∈ (E ×ˢ E).filter (fun p => ¬ ((Nat.lcm p.1.r p.2.r : ℝ) ≤ P)),
      Truncation168.pairTerm Sg ε X m p
  have hlim : Tendsto (fun U : ℝ => C' * (Sing m * X) * (Real.log U / Real.sqrt U))
      atTop (𝓝 0) := by
    simpa using tendsto_log_div_sqrt.const_mul (C' * (Sing m * X))
  have hle : ∀ᶠ U : ℝ in atTop, ‖D‖ ≤ C' * (Sing m * X) * (Real.log U / Real.sqrt U) := by
    filter_upwards [eventually_ge_atTop U0] with U hU
    have h1 := hb U (hU0.trans hU)
    rw [hD U hU] at h1
    calc ‖D‖ ≤ C' * (Sing m * X * Real.log U / Real.sqrt U) := h1
      _ = C' * (Sing m * X) * (Real.log U / Real.sqrt U) := by ring
  have h0 : ‖D‖ ≤ 0 := ge_of_tendsto hlim hle
  exact norm_le_zero_iff.mp h0

/-- The statement of `DecompJ803.leaf_truncation_error_2`, equal to `DecompJ834.leaf_truncation_error_3`,
taken as a hypothesis, forces exact cancellation of the permanently discarded lcm pairs at every
admitted instance.  Sorry free; the leaf itself is only assumed. -/
theorem leaf_truncation_error_forces_cancellation
    (h : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
        Thm1Hyp_v2 ε H0 X0 H X P0 → 1 ≤ P → P ≤ P0 →
        (excSet H (Real.sqrt X) P X).Finite →
        (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
          Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
        X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
        ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
          mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
        C' * (Sing m * X * Real.log U / Real.sqrt U)) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∃ H0 X0 : ℝ, ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
        Thm1Hyp_v2 ε H0 X0 H X P0 → 1 ≤ P → P ≤ P0 →
        (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
          Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
        X / 4 ≤ m → (m : ℝ) ≤ X / 2 →
        ∀ E : Finset ExcPair, (E : Set ExcPair) = excSet H (Real.sqrt X) P X →
          ∑ p ∈ (E ×ˢ E).filter (fun p => ¬ ((Nat.lcm p.1.r p.2.r : ℝ) ≤ P)),
            Truncation168.pairTerm Sg' ε X m p = 0 := by
  obtain ⟨ε0, hε0, h1⟩ := h
  refine ⟨ε0, hε0, fun ε hε hεlt => ?_⟩
  obtain ⟨H0, C', X0, -, h2⟩ := h1 ε hε hεlt
  refine ⟨H0, X0, fun H X P0 P Sg' m hHyp hP1 hPP0 hSg hm1 hm2 E hE => ?_⟩
  exact lcm_discarded_sum_eq_zero_of_bound H P ε C' m Sg' E hE
    (fun U hU => h2 H X P0 P U Sg' m hHyp hP1 hPP0 (excSet_finite H (Real.sqrt X) P X) hSg hm1 hm2 hU)

end LeanLab.Pintz2021.Feed1122DecompJ803Cancel
