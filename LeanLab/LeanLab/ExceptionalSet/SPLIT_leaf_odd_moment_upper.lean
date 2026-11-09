import LeanLab.ExceptionalSet.SPLIT_leaf_odd_moment

/-!
Split of `leaf_odd_moment_upper` of `SPLIT_leaf_odd_moment.lean`: the second moment of the odd
coefficients over the upper part of the floor window.

The statement bounds the sum of `‖R₁(ν_n)‖²` over the odd `ν_n` with
`(N+1)/2 + N/4 + 1 ≤ n ≤ N` by `B · (N · F(γ,N)² · ℰ^(-1/3))`, with the caps `δ₀` and `κ₀` on `δ`
and `κ` chosen first, and `B` and the threshold `N₀` chosen after them.

The work is cut into five steps. The window `Icc a N`, with `a = (N+1)/2 + N/4 + 1`, is cut at the
midpoint `b = a + (N - a)/2` into the two consecutive closed intervals `Icc a b` and
`Icc (b+1) N`. Two of the steps are the moment bound itself, taken over each of those two halves;
since the halves are pieces of the window, each of them sums the same nonnegative terms over a
strictly smaller index set, so each is strictly weaker than the target. Two further steps record
that the window really is the union of the halves and that the halves do not meet. The last step is
the arithmetic that adds two bounds sharing one right-hand factor and merges their constants.

The assembly takes the smaller of the two `δ` caps and the smaller of the two `κ` caps, the larger
of the two thresholds, rewrites the window as the union of its halves, splits the filtered sum,
applies the two moment bounds and merges their constants into `B₁ + B₂ + 1`. No step is assumed.

AI wrote this Lean code.  Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. Step of the proof: the lower half of the window, the indices from `a` up to the midpoint
`b = a + (N - a)/2`. The same second moment bound as the target, with the sum taken over the odd
`ν_n` of that half only. This is the target's inequality over a subset of the target's index set, so
it is strictly weaker than the target. Not empty in range: at `N = 100` the half is `Icc 76 88`. At
`N = 0` and `N = 1` the half is empty, so the inequality reads `0 ≤ B · (N · F² · ℰ^(-1/3))`, true
because the right-hand side is `0` at `N = 0`. -/
theorem leaf_odd_moment_upper_half_low (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2 + N / 4 + 1)
                (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2)).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨δ₀, hδ₀, hparent⟩ := leaf_odd_moment_upper γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨κ₀, hκ₀, hparent⟩ := hparent δ hδ hδlt
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₀, hparent⟩ := hparent κ hκ hκle
  refine ⟨B, hB, max N₀ 2, fun N hN => ?_⟩
  have hN₀ : N₀ ≤ N := (le_max_left N₀ 2).trans hN
  have hN2 : 2 ≤ N := (le_max_right N₀ 2).trans hN
  have H := hparent N hN₀
  have ha_le_N : (N + 1) / 2 + N / 4 + 1 ≤ N := by omega
  have hb_le_N : (N + 1) / 2 + N / 4 + 1 +
      (N - ((N + 1) / 2 + N / 4 + 1)) / 2 ≤ N := by omega
  have hsub : Finset.Icc ((N + 1) / 2 + N / 4 + 1)
      (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2) ⊆
      Finset.Icc ((N + 1) / 2 + N / 4 + 1) N := by
    exact Finset.Icc_subset_Icc le_rfl hb_le_N
  have hsub_filter : (Finset.Icc ((N + 1) / 2 + N / 4 + 1)
      (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2)).filter
        (fun n : ℕ => Odd (nu γ n)) ⊆
      (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter
        (fun n : ℕ => Odd (nu γ n)) := by
    exact Finset.filter_subset_filter _ hsub
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_filter
    (fun _ _ _ => sq_nonneg _)).trans H


/-- LEAF. Step of the proof: the upper half of the window, the indices from `b + 1` up to `N`, where
`b = a + (N - a)/2` is the midpoint of the window. The same second moment bound as the target, over
that half only. Again the target's inequality over a subset of the target's index set, hence
strictly weaker. Not empty in range: at `N = 100` the half is `Icc 89 100`. At `N = 0` and `N = 1`
the half is `Icc 1 0` and `Icc 2 1`, both empty, and the inequality reads
`0 ≤ B · (N · F² · ℰ^(-1/3))`. -/
theorem leaf_odd_moment_upper_half_high (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 + 1) N).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  sorry


/-- LEAF. Step of the proof: the window is the union of its two halves. For every `N ≥ 100` the
upper endpoint of the lower half and the lower endpoint of the upper half meet without a gap, and
the midpoint `a + (N - a)/2` does not pass `N`, so the two closed intervals `Icc a b` and
`Icc (b+1) N` cover exactly the window `Icc a N` and nothing else. -/
theorem leaf_odd_upper_window_split (N : ℕ) (hN : 100 ≤ N) :
    Finset.Icc ((N + 1) / 2 + N / 4 + 1) N =
      Finset.Icc ((N + 1) / 2 + N / 4 + 1)
          (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2) ∪
        Finset.Icc (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 + 1) N := by
  ext x
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega


/-- LEAF. Step of the proof: the two halves do not meet. A natural number cannot be both at most the
midpoint `a + (N - a)/2` and at least `a + (N - a)/2 + 1`, whatever the parity of `N` is, so the
two filtered halves are disjoint; this is what lets the second moment of the window be written as
the sum of the second moments of the halves. -/
theorem leaf_odd_upper_window_disjoint (γ : ℝ) (N : ℕ) :
    Disjoint
      ((Finset.Icc ((N + 1) / 2 + N / 4 + 1)
          (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2)).filter
        (fun n : ℕ => Odd (nu γ n)))
      ((Finset.Icc (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 + 1) N).filter
        (fun n : ℕ => Odd (nu γ n))) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
  omega


/-- LEAF. Step of the proof: two upper bounds with one common right-hand factor can be added, at the
price of one extra unit in the constant. If `x ≤ A · M` and `y ≤ B · M` with `M ≥ 0`, then
`x + y ≤ (A + B + 1) · M`. The extra unit is what pays for the passage from `A + B` to `A + B + 1`;
no positivity of `A` or `B` is needed, and the estimate also holds for negative `A`, `B`, `x`, `y`,
and reads `0 ≤ M` when all of them are `0`. -/
theorem leaf_odd_moment_add_const (M x y A B : ℝ) (hM : 0 ≤ M)
    (hx : x ≤ A * M) (hy : y ≤ B * M) : x + y ≤ (A + B + 1) * M := by
  calc x + y ≤ A * M + B * M := add_le_add hx hy
       _ = (A + B) * M := by ring
       _ ≤ (A + B + 1) * M := by nlinarith [hM]


/-- Assembly. The statement of `leaf_odd_moment_upper` of `SPLIT_leaf_odd_moment.lean`, from the five
steps: the caps on `δ` and `κ` are the smaller of the two pairs, the constant is `B₁ + B₂ + 1`, the
threshold is the larger of `100` and the two thresholds, the window is rewritten as the union of its
two halves, the filtered sum is split over them, the two moment bounds are applied and their
constants are merged. No `sorry` is used and the statement `leaf_odd_moment_upper` itself is not
used. -/
theorem leaf_odd_moment_upper_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2 + N / 4 + 1) N).filter
              (fun n : ℕ => Odd (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
  classical
  obtain ⟨δa, hδa, ha⟩ := leaf_odd_moment_upper_half_low γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_odd_moment_upper_half_high γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδs => ?_⟩
  have hδa' : δ < δa := hδs.trans_le (min_le_left _ _)
  have hδb' : δ < δb := hδs.trans_le (min_le_right _ _)
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ hδa'
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ hδb'
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκs => ?_⟩
  have hκa' : κ ≤ κa := hκs.trans (min_le_left _ _)
  have hκb' : κ ≤ κb := hκs.trans (min_le_right _ _)
  obtain ⟨Ba, hBa, Na, ha⟩ := ha κ hκ hκa'
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ hκb'
  refine ⟨Ba + Bb + 1, by linarith, max 100 (max Na Nb), fun N hN => ?_⟩
  have hN100 : 100 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := ((le_max_left Na Nb).trans (le_max_right _ _)).trans hN
  have hNb : Nb ≤ N := ((le_max_right Na Nb).trans (le_max_right _ _)).trans hN
  have hsplit := leaf_odd_upper_window_split N hN100
  have hdisj := leaf_odd_upper_window_disjoint γ N
  have hM : 0 ≤ N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
      (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  rw [hsplit, Finset.filter_union, Finset.sum_union hdisj]
  exact leaf_odd_moment_add_const
    (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) _ _ _ _ hM (ha N hNa) (hb N hNb)

#print axioms leaf_odd_moment_upper_split

end LeanLab.ExceptionalSet.Decomp371c
