import Mathlib
import LeanLab.Pintz2021.DecompJ281
import LeanLab.Pintz2021.DecompJ665

/-!
Audit of the sealed truncation leaf in `DecompJ281`.

The leaf has no lower bound on the arc level `P`.  Taking `P = 0` removes the pole from the
truncated sum.  The full sum still has the nonzero pole term.  As `U` tends to infinity the
proposed right hand side tends to zero, so no constant can give the claimed uniform bound.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.Pintz2021.DecompJ281Audit

open Complex Finset Filter Topology
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DecompJ281

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The exact sealed truncation leaf is false.

The counterexample uses `P₀ = 1` and `P = 0`.  The exceptional set then consists only of the
pole.  The truncated sum is zero at every cutoff `U`.  The full sum contains
`Sing(m)` times the nonzero pole difference kernel.  The right hand side tends to zero as
`U` tends to infinity.  The scale is chosen above every proposed `X₀`, and the frequency is
a positive even integer in `[X/4, X/2]`.
-/
theorem leaf_truncation_error_false :
    ¬ (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ,
        ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
        Thm1Hyp ε H0 X0 H X P0 → P ≤ P0 →
        (excSet H (Real.sqrt X) P X).Finite →
        (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ,
          0 < n → Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
        X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
        ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
          mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
          C' * (Sing m * X * Real.log U / Real.sqrt U)) := by
  rintro ⟨ε0, hε0, h⟩
  let ε := min (ε0 / 2) (1 / 9)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε0' : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε4 : ε < 4 / 9 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨H0, C', X0, hC', hbound⟩ := h ε hε hε0'
  obtain ⟨H, X, hHyp, hX16, hpow⟩ :=
    LeanLab.Pintz2021.DecompJ665.level_one_tail_hyp hε hε4 H0 X0
  obtain ⟨m, hmpos, hmEven, hmlo, hmhi, hK⟩ :=
    LeanLab.Pintz2021.DecompJ665.positive_even_kernel_in_range hX16 hpow
  have hno := LeanLab.Pintz2021.DecompJ665.level_zero_tail_bound_impossible
    H X ε C' m hmpos hmEven hK
  have hex : ∃ U : ℝ, 2 ≤ U ∧
      ∃ Sg : ExcPair → ExcPair → ℕ → ℂ,
        (∀ z ∈ excSet H (Real.sqrt X) 0 X, ∀ w ∈ excSet H (Real.sqrt X) 0 X,
          ∀ n : ℕ, 0 < n → Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg z w n))) ∧
        ¬ ‖mainTermPrime (excSet H (Real.sqrt X) 0 X) Sg ε X m -
            mainTermTruncatedPrime (excSet H (Real.sqrt X) 0 X) Sg ε X 0 U m‖ ≤
          C' * (Sing m * X * Real.log U / Real.sqrt U) := by
    classical
    by_contra hcon
    apply hno
    intro U hU Sg hconv
    by_contra hnot
    apply hcon
    exact ⟨U, hU, Sg, hconv, hnot⟩
  obtain ⟨U, hU, Sg, hconv, hbad⟩ := hex
  have hclaim := hbound H X 1 0 U Sg m hHyp (by norm_num)
    (LeanLab.Pintz2021.DecompJ665.excSet_finite H (Real.sqrt X) 0 X)
    hconv hmlo hmhi hU
  exact hbad hclaim

end

end LeanLab.Pintz2021.DecompJ281Audit

#print axioms LeanLab.Pintz2021.DecompJ281Audit.leaf_truncation_error_false
