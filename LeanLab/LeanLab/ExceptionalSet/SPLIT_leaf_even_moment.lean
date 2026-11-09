import LeanLab.ExceptionalSet.Decomp371c

/-!
Split of `LeanLab.ExceptionalSet.Decomp371c.leaf_even_moment` into three leaves.

The target is the even branch of the second moment of the adjacent major arc
coefficient over the half window `((N+1)/2, N]`.  The split cuts the index range
at its midpoint `2 * n ≤ N + (N + 1) / 2`: one leaf is the range dissection
itself (an identity between finite sums), and one leaf each is the second moment
estimate on the lower and on the upper half of the range.  Each estimate is
strictly weaker than the target, because it is a sub-sum of the target's sum, and
the two together with the dissection give the target with the constant
`B₁ + B₂`.

AI wrote this Lean code.  Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371c.Split

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. Step of the proof: the range dissection, no estimate enters.  The
second moment of the adjacent coefficient over the even indices of the half
window equals the sum of the same quantity over the two halves of the index
range, cut at the midpoint `2 * n ≤ N + (N + 1) / 2`.  This is the finite sum
split `Finset.sum_filter_add_sum_filter_not` applied to the even filtered range.
At `N = 0` and `N = 1` the upper block is empty and both sides vanish. -/
theorem leaf_even_moment_block_split (γ δ κ : ℝ) (N : ℕ) :
    (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
      = (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
            (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
        + (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
            (fun n : ℕ => Even (nu γ n) ∧ ¬ (2 * n ≤ N + (N + 1) / 2)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)))
        (fun n : ℕ => 2 * n ≤ N + (N + 1) / 2)]
  congr 1
  · rw [Finset.filter_filter]
  · rw [Finset.filter_filter]

/-- LEAF. Step of the proof: the second moment estimate of the even branch on
the lower half of the index range, that is on the even `n` of the half window
with `2 * n ≤ N + (N + 1) / 2`.  This is the same bound as the target but for a
sub-range of the sum, so it is strictly weaker than the target.  At `N = 1` the
lower block is the single index `n = 1`, so the range is not empty. -/
theorem leaf_even_moment_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
                (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hparent⟩ := LeanLab.ExceptionalSet.Decomp371c.leaf_even_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨κ₀, hκ₀, hparent⟩ := hparent δ hδ hδlt
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₀, hparent⟩ := hparent κ hκ hκle
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hparent' := hparent N hN
  have hsub : (Finset.Icc ((N + 1) / 2) N).filter
        (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2)
      ⊆ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  have hsum : (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
        (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
      ≤ (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  exact hsum.trans hparent'

/-- LEAF. Step of the proof: the second moment estimate of the even branch on
the upper half of the index range, that is on the even `n` of the half window
with `¬ (2 * n ≤ N + (N + 1) / 2)`.  Again a sub-sum of the target's sum, hence
strictly weaker.  At `N = 0` and `N = 1` this block is empty and the estimate
reduces to `0 ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3))`. -/
theorem leaf_even_moment_upper (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
                (fun n : ℕ => Even (nu γ n) ∧ ¬ (2 * n ≤ N + (N + 1) / 2)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hparent⟩ := LeanLab.ExceptionalSet.Decomp371c.leaf_even_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨κ₀, hκ₀, hparent⟩ := hparent δ hδ hδlt
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨B, hB, N₀, hparent⟩ := hparent κ hκ hκle
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hparent' := hparent N hN
  have hsub : (Finset.Icc ((N + 1) / 2) N).filter
        (fun n : ℕ => Even (nu γ n) ∧ ¬ (2 * n ≤ N + (N + 1) / 2))
      ⊆ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  have hsum : (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
        (fun n : ℕ => Even (nu γ n) ∧ ¬ (2 * n ≤ N + (N + 1) / 2)),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
      ≤ (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  exact hsum.trans hparent'

/-- Assembly.  The exact statement of `leaf_even_moment`, from the range
dissection and the two half range second moment estimates.  The caps are the
minima of the two pairs of caps, the constant is the sum of the two constants,
and the threshold is the maximum of the two thresholds. -/
theorem leaf_even_moment_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₁, hδ₁, hlow⟩ := leaf_even_moment_lower γ h1 h2
  obtain ⟨δ₂, hδ₂, hupp⟩ := leaf_even_moment_upper γ h1 h2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₁, hκ₁, hlow⟩ := hlow δ hδ (lt_of_lt_of_le hδsmall (min_le_left _ _))
  obtain ⟨κ₂, hκ₂, hupp⟩ := hupp δ hδ (lt_of_lt_of_le hδsmall (min_le_right _ _))
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B₁, hB₁, N₁, hlow⟩ := hlow κ hκ (le_trans hκsmall (min_le_left _ _))
  obtain ⟨B₂, hB₂, N₂, hupp⟩ := hupp κ hκ (le_trans hκsmall (min_le_right _ _))
  refine ⟨B₁ + B₂, add_pos hB₁ hB₂, max N₁ N₂, fun N hN => ?_⟩
  have h₁ : (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
        (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2),
      ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
        B₁ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    hlow N ((le_max_left _ _).trans hN)
  have h₂ : (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
        (fun n : ℕ => Even (nu γ n) ∧ ¬ (2 * n ≤ N + (N + 1) / 2)),
      ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
        B₂ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    hupp N ((le_max_right _ _).trans hN)
  rw [leaf_even_moment_block_split γ δ κ N]
  calc
    (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
          (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) +
      (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
          (fun n : ℕ => Even (nu γ n) ∧ ¬ (2 * n ≤ N + (N + 1) / 2)),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
        ≤ B₁ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
            B₂ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := add_le_add h₁ h₂
    _ = (B₁ + B₂) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by ring

end LeanLab.ExceptionalSet.Decomp371c.Split

#print axioms LeanLab.ExceptionalSet.Decomp371c.Split.leaf_even_moment_split
