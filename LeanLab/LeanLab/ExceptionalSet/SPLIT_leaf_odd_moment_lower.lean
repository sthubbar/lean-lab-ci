import LeanLab.ExceptionalSet.SPLIT_leaf_odd_moment

/-!
Split of `leaf_odd_moment_lower`, the lower of the two odd-coefficient second moments of section 6.

The lower piece of the odd moment is cut again at its own quarter point `⌊(N+1)/2⌋ + ⌊N/8⌋`: the
odd second moment over `Icc ⌊(N+1)/2⌋ (⌊(N+1)/2⌋+⌊N/8⌋)` and the odd second moment over the rest
`Icc (⌊(N+1)/2⌋+⌊N/8⌋+1) (⌊(N+1)/2⌋+⌊N/4⌋)` are bounded separately, each with its own caps and
its own constant, and the assembly minimises the two `δ` caps and the two `κ` caps and adds the two
moment constants, absorbing the resulting `+ 1` into a single constant `B`. Each piece is a sum over
strictly fewer indices than the piece being split, so each is strictly weaker than it.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. First half of the odd second moment over the lower window: the sum of `‖R₁(ν_n)‖²` over
the odd members of `Icc ⌊(N+1)/2⌋ (⌊(N+1)/2⌋ + ⌊N/8⌋)`, eventually at most
`B N F(γ,N)² ℰ^(-1/3)` with `B > 0` and `N₀` chosen after `κ`. This is the step that supplies the
estimate on the first half of the index range; it is a sum over strictly fewer indices than the
lower piece, hence strictly weaker than it (all terms are nonnegative squares). -/
theorem leaf_odd_moment_lower_first_half (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 8)).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  sorry

/-- LEAF. Second half of the odd second moment over the lower window: the sum of `‖R₁(ν_n)‖²` over
the odd members of the remainder `Icc (⌊(N+1)/2⌋ + ⌊N/8⌋ + 1) (⌊(N+1)/2⌋ + ⌊N/4⌋)`, eventually at
most `B N F(γ,N)² ℰ^(-1/3)` with `B > 0` and `N₀` chosen after `κ`. This is the step that supplies
the estimate on the second half of the index range; again a sum over strictly fewer indices than the
lower piece, hence strictly weaker than it. -/
theorem leaf_odd_moment_lower_second_half (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2 + N / 8 + 1) ((N + 1) / 2 + N / 4)).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  sorry

/-- Assembly. The lower odd second moment of the floor window follows from its two halves: the
window `Icc ⌊(N+1)/2⌋ (⌊(N+1)/2⌋+⌊N/4⌋)` is the union of `Icc ⌊(N+1)/2⌋ (⌊(N+1)/2⌋+⌊N/8⌋)` and
`Icc (⌊(N+1)/2⌋+⌊N/8⌋+1) (⌊(N+1)/2⌋+⌊N/4⌋)` (its quarter point is at least its eighth point, so the
two closed ranges meet without a gap), the two moment bounds are added, and their constants are
merged into one positive `B`. No sorry. -/
theorem leaf_odd_moment_lower_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  classical
  obtain ⟨δa, hδa, ha⟩ := leaf_odd_moment_lower_first_half γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_odd_moment_lower_second_half γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδs => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (lt_of_lt_of_le hδs (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (lt_of_lt_of_le hδs (min_le_right _ _))
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκs => ?_⟩
  obtain ⟨Ba, hBa, Na, ha⟩ := ha κ hκ (le_trans hκs (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (le_trans hκs (min_le_right _ _))
  refine ⟨Ba + Bb + 1, by linarith, max Na Nb, fun N hN => ?_⟩
  have hNa : Na ≤ N := (le_max_left _ _).trans hN
  have hNb : Nb ≤ N := (le_max_right _ _).trans hN
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hK : 0 ≤ N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
      (Real.rpow_pos_of_pos hE _).le
  have h84 : N / 8 ≤ N / 4 := by omega
  have hsplit : Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)
      = Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 8)
        ∪ Finset.Icc ((N + 1) / 2 + N / 8 + 1) ((N + 1) / 2 + N / 4) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint
      ((Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 8)).filter
        (fun n : ℕ => Odd (nu γ n)))
      ((Finset.Icc ((N + 1) / 2 + N / 8 + 1) ((N + 1) / 2 + N / 4)).filter
        (fun n : ℕ => Odd (nu γ n))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
    omega
  rw [hsplit, Finset.filter_union, Finset.sum_union hdisj]
  calc (∑ n ∈ (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 8)).filter
            (fun n : ℕ => Odd (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) +
        ∑ n ∈ (Finset.Icc ((N + 1) / 2 + N / 8 + 1) ((N + 1) / 2 + N / 4)).filter
            (fun n : ℕ => Odd (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2
      ≤ Ba * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) +
          Bb * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) :=
        add_le_add (ha N hNa) (hb N hNb)
    _ = (Ba + Bb) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
        ring
    _ ≤ (Ba + Bb + 1) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hK

end LeanLab.ExceptionalSet.Decomp371c
