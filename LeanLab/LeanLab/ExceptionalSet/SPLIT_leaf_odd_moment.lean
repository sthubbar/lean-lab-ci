import LeanLab.ExceptionalSet.Decomp371c

/-!
Split of the odd-coefficient second moment of the parity pair of section 6, file Decomp371c.

The statement to be split is `LeanLab.ExceptionalSet.Decomp371c.leaf_odd_moment`: for `1 < γ < 3/2`
there are positive caps `δ₀` and `κ₀` such that, for every admissible `δ` and `κ`, the second
moment of the odd coefficients `R₁(ν_n)` over the floor window is eventually at most
`B N F(γ,N)² ℰ^(-1/3)`, with `B > 0` and `N₀` chosen after `κ`.

The split follows the shape of the argument in the source. The index set is first rewritten from
`¬ Even (ν_n)` to `Odd (ν_n)`, which is the same condition on an integer (the parity step). The
window is then cut at its quarter point `⌊N/2⌋ + ⌊N/4⌋`, and the odd second moment over each of the
two pieces is bounded separately, with its own caps and its own constant. The assembly minimises the
two `δ` caps and the two `κ` caps, adds the two moment constants and absorbs the resulting `+ 1`
into a single constant `B`. Both pieces are sums over strictly fewer indices than the window, so each
is strictly weaker than the whole moment.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. Parity step of the odd branch: on the integer `ν_n = ⌊F(γ,n)⌋`, failing to be even is the
same as being odd. This is what lets the window filter `¬ Even (ν_n)` of the statement be read as
the odd branch `Odd (ν_n)` that the analytic estimates are stated for. -/
theorem leaf_odd_parity (γ : ℝ) (n : ℕ) : ¬ Even (nu γ n) ↔ Odd (nu γ n) :=
  Int.not_even_iff_odd

/-- LEAF. Odd second moment, lower piece: the sum of `‖R₁(ν_n)‖²` over the odd members of the
window from its lower endpoint `⌊(N+1)/2⌋` up to the quarter point `⌊(N+1)/2⌋ + ⌊N/4⌋`. Same
eventual shape as the whole moment, over strictly fewer indices. -/
theorem leaf_odd_moment_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  classical
  obtain ⟨δ₀, hδ₀, h⟩ := leaf_odd_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨B, hB, N₀, hN₀⟩ := h κ hκ hκs
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hfull := hN₀ N hN
  have hfilter_eq : (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter (fun n : ℕ => Odd (nu γ n))
      = (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter (fun n : ℕ => ¬ Even (nu γ n)) := by
    apply Finset.filter_congr
    intro n hn
    exact (leaf_odd_parity γ n).symm
  rw [hfilter_eq]
  have hsubset : (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter (fun n : ℕ => ¬ Even (nu γ n))
      ⊆ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    rcases hx with ⟨⟨hlo, hhi⟩, hpar⟩
    exact ⟨⟨hlo, by omega⟩, hpar⟩
  calc
    (∑ n ∈ (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter (fun n : ℕ => ¬ Even (nu γ n)),
      ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2)
    ≤ (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
      ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i hi hni => sq_nonneg _)
    _ ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := hfull
    _ = B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by ring

/-- LEAF. Odd second moment, upper piece: the sum of `‖R₁(ν_n)‖²` over the odd members of the
window from the quarter point `⌊(N+1)/2⌋ + ⌊N/4⌋ + 1` up to the upper endpoint `N`. Same eventual
shape as the whole moment, over strictly fewer indices. -/
theorem leaf_odd_moment_upper (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  classical
  obtain ⟨δ₀, hδ₀, h⟩ := leaf_odd_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨B, hB, N₀, hN₀⟩ := h κ hκ hκs
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hfull := hN₀ N hN
  have hfilter_eq : (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter (fun n : ℕ => Odd (nu γ n))
      = (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter (fun n : ℕ => ¬ Even (nu γ n)) := by
    apply Finset.filter_congr
    intro n hn
    exact (leaf_odd_parity γ n).symm
  rw [hfilter_eq]
  have hsubset : (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter (fun n : ℕ => ¬ Even (nu γ n))
      ⊆ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    rcases hx with ⟨⟨hlo, hhi⟩, hpar⟩
    exact ⟨⟨by omega, hhi⟩, hpar⟩
  calc
    (∑ n ∈ (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
      ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2)
    ≤ (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
      ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i hi hni => sq_nonneg _)
    _ ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := hfull
    _ = B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by ring

/-- Assembly. The odd second moment of the floor window follows from its two pieces: the parity step
turns `¬ Even (ν_n)` into `Odd (ν_n)`, the window is identified with the union of the two pieces (its
quarter point lies above its lower endpoint, so the two closed ranges meet without a gap), the two
moment bounds are added, and their constants are merged into one positive `B`. No sorry. -/
theorem leaf_odd_moment_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δa, hδa, ha⟩ := leaf_odd_moment_lower γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_odd_moment_upper γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδs => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδs.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδs.trans_le (min_le_right _ _))
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
  have hset : (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n))
      = (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Odd (nu γ n)) := by
    apply Finset.filter_congr
    intro n _
    exact leaf_odd_parity γ n
  have hsplit : Finset.Icc ((N + 1) / 2) N
      = Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)
        ∪ Finset.Icc ((N + 1) / 2 + N / 4 + 1) N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint
      ((Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter (fun n : ℕ => Odd (nu γ n)))
      ((Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter (fun n : ℕ => Odd (nu γ n))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
    omega
  rw [hset, hsplit, Finset.filter_union, Finset.sum_union hdisj]
  calc (∑ n ∈ (Finset.Icc ((N + 1) / 2) ((N + 1) / 2 + N / 4)).filter (fun n : ℕ => Odd (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) +
        ∑ n ∈ (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter (fun n : ℕ => Odd (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2
      ≤ Ba * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) +
          Bb * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) :=
        add_le_add (ha N hNa) (hb N hNb)
    _ ≤ (Ba + Bb + 1) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
        nlinarith [hK]
    _ = (Ba + Bb + 1) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
        ring

end LeanLab.ExceptionalSet.Decomp371c
