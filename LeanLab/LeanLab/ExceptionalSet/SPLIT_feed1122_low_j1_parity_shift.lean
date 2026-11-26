import LeanLab.ExceptionalSet.Feed1122_low_j1_large_phase_localizes
import LeanLab.ExceptionalSet.SPLIT_feed1122_parity_removal_core

/-!
Split of `Decomp553c.leaf_low_j1_parity_shift`, the Fourier removal of the parity
condition `ν_n + 1 ≡ 0 mod 2` on the lower block, P0082 section 7 page 370,
displays (40) and (41) with Lemma 4 on page 359.

The assembly below has the statement of the leaf verbatim. It is the
contrapositive of `Feed1122ParityCore.parity_core` on the sub-block
`N / 2 < n ≤ 3 N / 4` with the shift `j = 1`, which is CONDITIONAL ON the two
leaves of `SPLIT_feed1122_parity_removal_core`: the trapezoid Fourier expansion,
display (40), and Lemma 4 at `α = 1`. The hypothesis `|t| ≤ 2 ℰ ^ (2 / 3)` is not
needed.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553c

open Real Finset
open LeanLab.ExceptionalSet.U1539 (nu calE eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.Decomp553a
open LeanLab.ExceptionalSet.Feed1122ParityCore

/-- Assembly, statement copied verbatim from `leaf_low_j1_parity_shift`.
CONDITIONAL ON the two leaves of `SPLIT_feed1122_parity_removal_core`. -/
theorem leaf_low_j1_parity_shift_of_core (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
        |t| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) →
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
            ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) t‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 : ℝ) ∧
            (N : ℝ) * calE γ κ N ^ (-(2 : ℝ)) <
              ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4),
                eC ((t - (h : ℝ) / 2) * F γ n)‖ := by
  obtain ⟨κ₀, hκ₀, HC⟩ := parity_core γ h1 h2
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨NC, HC⟩ := HC κ hκ hκs
  refine ⟨NC, fun N hN t _ hlarge => ?_⟩
  by_contra hno
  push_neg at hno
  have hB : (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) ⊆
      Finset.Ioc (N / 2) N := Finset.filter_subset _ _
  have hres := HC N hN _ hB 1 t (fun h hh => by
    rw [shift_sum_norm]
    have hh' : (|(((-h : ℤ)) : ℝ)|) ≤ calE γ κ N ^ (2 : ℝ) := by
      rw [Int.cast_neg, abs_neg]; exact hh
    have := hno (-h) hh'
    have he : t - (((-h : ℤ) : ℝ)) / 2 = t + (h : ℝ) / 2 := by push_cast; ring
    rw [he] at this
    exact this)
  have hset : indices_low_j1 γ N = ((Finset.Ioc (N / 2) N).filter
      (fun n => n ≤ 3 * N / 4)).filter (fun n : ℕ => Even ⌊F γ n - ((1 : ℤ) : ℝ)⌋) := by
    unfold indices_low_j1
    rw [Finset.filter_filter, Finset.filter_filter]
    refine Finset.filter_congr (fun n _ => ?_)
    unfold U1539.nu
    rw [Int.cast_one, Int.floor_sub_one, Int.even_add_one, Int.even_sub_one]
    exact and_comm
  have : ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) t‖ ≤
      (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
    unfold blockPhase
    rw [hset]
    exact hres
  linarith

end LeanLab.ExceptionalSet.Decomp553c
