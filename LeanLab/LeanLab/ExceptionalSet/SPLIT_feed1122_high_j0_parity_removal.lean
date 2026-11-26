import LeanLab.ExceptionalSet.Feed1122_high_j0_large_phase_strip
import LeanLab.ExceptionalSet.SPLIT_feed1122_parity_removal_core

/-!
Split of `Decomp553b.feed1122_high_j0_parity_removal`, the Fourier removal of the
parity condition `ν_n ≡ 0 mod 2` on the upper block, P0082 section 7 page 370,
displays (40) and (41) with Lemma 4 on page 359.

The assembly below has the statement of the leaf verbatim. It is proved from
`Feed1122ParityCore.parity_core`, which is CONDITIONAL ON the two leaves of
`SPLIT_feed1122_parity_removal_core`: the trapezoid Fourier expansion, display
(40), and Lemma 4 at `α = 1`. The only extra input is the proved comparison
`ℰ ^ 2 ≤ X ^ δ` for large `N`, so that every `|h| ≤ ℰ ^ 2` used by the core is
covered by the hypothesis on `|h| ≤ X ^ δ`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553b

open Real Finset
open LeanLab.ExceptionalSet.U1539 (nu calE eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.Decomp553a
open LeanLab.ExceptionalSet.Feed1122ParityCore

/-- Assembly, statement copied verbatim from `feed1122_high_j0_parity_removal`.
CONDITIONAL ON the two leaves of `SPLIT_feed1122_parity_removal_core`. -/
theorem feed1122_high_j0_parity_removal_of_core (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
          (∀ h : ℤ, (|h| : ℝ) ≤ F γ N ^ δ →
            ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => ¬ n ≤ 3 * N / 4),
                eC ((t + (h : ℝ) / 2) * F γ n)‖ ≤ (N : ℝ) * calE γ κ N ^ (-2 : ℝ)) →
          ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) t‖ ≤
            (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨κ₀, hκ₀, HC⟩ := parity_core γ h1 h2
  refine ⟨1, one_pos, fun δ hδ _ => ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩⟩
  obtain ⟨NC, HC⟩ := HC κ hκ hκs
  obtain ⟨NW, HW⟩ := LeanLab.ExceptionalSet.UpJ200.Decomp404e.calE_power_le_F_power
    γ κ 2 δ h1 hδ
  refine ⟨max NC NW, fun N hN t hyp => ?_⟩
  have hEF := HW N ((le_max_right _ _).trans hN)
  have hB : (Finset.Ioc (N / 2) N).filter (fun n => ¬ n ≤ 3 * N / 4) ⊆
      Finset.Ioc (N / 2) N := Finset.filter_subset _ _
  have hres := HC N ((le_max_left _ _).trans hN) _ hB 0 t (fun h hh => by
    rw [shift_sum_norm]
    exact hyp h (hh.trans hEF))
  have hset : indices_high_j0 γ N = ((Finset.Ioc (N / 2) N).filter
      (fun n => ¬ n ≤ 3 * N / 4)).filter (fun n : ℕ => Even ⌊F γ n - ((0 : ℤ) : ℝ)⌋) := by
    unfold indices_high_j0
    rw [Finset.filter_filter, Finset.filter_filter]
    refine Finset.filter_congr (fun n _ => ?_)
    simp only [Int.cast_zero, sub_zero, add_zero]
    unfold U1539.nu
    exact and_comm
  unfold blockPhase
  rw [hset]
  exact hres

end LeanLab.ExceptionalSet.Decomp553b
