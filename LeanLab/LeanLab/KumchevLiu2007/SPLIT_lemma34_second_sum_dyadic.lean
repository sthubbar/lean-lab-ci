/-
Kumchev and Liu 2007, page 11 Lemma 3.4 applied on page 15 to the second sum
of display 52, for one dyadic block M at most p below 2M.

This file splits the sealed statement `lemma34_second_sum_dyadic` of
`LeanLab.KumchevLiu2007.Eq33RouteD` into four leaves and proves the sealed
statement from them. The estimate is cut on the two axes that it really has,
in the same way as the split of the first sum of display 52 in the sibling
file `SPLIT_lemma34_first_sum`:

* the position of the dyadic block relative to the two cut-offs. The block is
  empty when it lies at or above the sieve cutoff z0 = Y^(1/4) (log X)^(-2B),
  and empty when it lies at or below the rough cutoff z1 = Y^(1/6 + eps/2).
  In both cases the coefficient of the sum is identically zero, so the
  integral is zero. These two leaves are proved.
* the two halves of the t window. Near Y / 4 the short sum has twice as many
  terms as near Y, so the two halves are the two different counting regimes,
  and the integral over the whole window is the sum of the two. The interior
  case, where z1 < 2M and M < z0, keeps one half each in the two open leaves.

That gives four leaves, each the estimate on a subset of its parameter range: a
block range where the sum is empty, or an integration interval strictly
smaller than the whole window. No leaf implies the target and no leaf assumes
it. The assembly splits the window at Y / 2, adds the two half integrals and
takes the larger of the two constants; in the two empty cases the integral is
zero.

The H range above Y, recorded as a question in the parent file, is left inside
each leaf: every leaf keeps the whole written range of H.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD
import LeanLab.KumchevLiu2007.SPLIT_lemma34_second_sum_dyadic_interior_Leaves

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: the dyadic block of primes lies at or above the sieve cutoff z0, so
the inner filter is empty for every m and the coefficient of the second sum is
identically zero. This is the case M at least z0 of the block. -/
theorem leaf_block_empty_above_cutoff (X ε B M : ℝ) (m : ℕ)
    (hcut : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ M) :
                (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp1, hMp, hp2M⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, hpp, hpz1, hpz0, hpm⟩ := Finset.mem_filter.mp hp1
  linarith

/-- LEAF: the dyadic block of primes lies at or below the rough cutoff z1, so
the block contains no prime at least z1 and the coefficient of the second sum
is identically zero. This is the case 2 M at most z1 of the block, with M at
least one. -/
theorem leaf_block_empty_below_rough_cutoff (X ε B M : ℝ) (m : ℕ)
    (hcut : 2 * M ≤ windowY X ε ^ (1 / 6 + ε / 2)) :
                (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp1, hMp, hp2M⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, hpp, hpz1, hpz0, hpm⟩ := Finset.mem_filter.mp hp1
  linarith

/-- LEAF: the interior case z1 < 2 M and M < z0 of the dyadic block, on the
left half [Y / 4, Y / 2] of the t window, where the short sum has the larger
number of terms. The estimate is Lemma 3.4 with (m, k) = (p, m / p), the block
being admissible, together with the mean square in t over that half. -/
theorem leaf_interior_left_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  exact leaf_interior_left_half_from_leaves A hA

/-- LEAF: the interior case z1 < 2 M and M < z0 of the dyadic block, on the
right half [Y / 2, Y] of the t window, where the short sum has the smaller
number of terms. The estimate is Lemma 3.4 with (m, k) = (p, m / p), the block
being admissible, together with the mean square in t over that half. -/
theorem leaf_interior_right_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  exact leaf_interior_right_half_from_leaves A hA

theorem lemma34_second_sum_dyadic_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B3, hB3, h3⟩ := leaf_interior_left_half A hA
  obtain ⟨B4, hB4, h4⟩ := leaf_interior_right_half A hA
  refine ⟨max B3 B4, lt_of_lt_of_le hB3 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C3, X3, hC3, hX3, k3⟩ := h3 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C4, X4, hC4, hX4, k4⟩ := h4 B ((le_max_right _ _).trans hB) ε hε
  have hCpos : 0 < 2 * max C3 C4 := by
    have hMx : 0 < max C3 C4 := lt_of_lt_of_le hC3 (le_max_left _ _)
    linarith
  refine ⟨2 * max C3 C4, max X3 X4, hCpos, hX3.trans (le_max_left _ _), ?_⟩
  intro X H hX hHl hHu α q a hcop hqP hqQ hclose M hM
  have hXa : X3 ≤ X := (le_max_left _ _).trans hX
  have hXb : X4 ≤ X := (le_max_right _ _).trans hX
  have h1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos h1
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (by positivity) (Real.rpow_pos_of_pos hL A).le
  by_cases htop : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ M
  · have hzero : ∀ t : ℝ,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 = (0 : ℝ) := by
      intro t
      have hsum : ∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        rw [leaf_block_empty_above_cutoff X ε B M m htop, zero_mul]
      rw [hsum]
      simp
    have hInt : (∫ t in windowY X ε / 4..windowY X ε, ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) = 0 := by
      rw [show (fun t : ℝ => ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) = fun _ => (0 : ℝ) from funext hzero]
      simp
    rw [hInt]
    refine div_nonneg (mul_nonneg (le_of_lt hCpos)
      (by positivity)) (Real.rpow_pos_of_pos hL A).le
  · push Not at htop
    by_cases hlow : 2 * M ≤ windowY X ε ^ (1 / 6 + ε / 2)
    · have hzero : ∀ t : ℝ,
        ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 = (0 : ℝ) := by
        intro t
        have hsum : ∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) = 0 := by
          apply Finset.sum_eq_zero
          intro m _
          rw [leaf_block_empty_below_rough_cutoff X ε B M m hlow, zero_mul]
        rw [hsum]
        simp
      have hInt : (∫ t in windowY X ε / 4..windowY X ε, ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) = 0 := by
        rw [show (fun t : ℝ => ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) = fun _ => (0 : ℝ) from funext hzero]
        simp
      rw [hInt]
      refine div_nonneg (mul_nonneg (le_of_lt hCpos)
        (by positivity)) (Real.rpow_pos_of_pos hL A).le
    · push Not at hlow
      have hint1 : IntervalIntegrable (fun t : ℝ => ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) volume
          (windowY X ε / 4) (windowY X ε / 2) :=
        short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
          (fun m : ℕ => (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
      have hint2 : IntervalIntegrable (fun t : ℝ => ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) volume
          (windowY X ε / 2) (windowY X ε) :=
        short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
          (fun m : ℕ => (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
      rw [(intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm]
      have e1 := k3 X H hXa hHl hHu α q a hcop hqP hqQ hclose M hM htop hlow
      have e2 := k4 X H hXb hHl hHu α q a hcop hqP hqQ hclose M hM htop hlow
      have hkey3 : C3 * H ^ 2 / Real.log X ^ A = C3 * (H ^ 2 / Real.log X ^ A) := by ring
      have hkey4 : C4 * H ^ 2 / Real.log X ^ A = C4 * (H ^ 2 / Real.log X ^ A) := by ring
      have hkeyC : (2 * max C3 C4) * H ^ 2 / Real.log X ^ A =
          (2 * max C3 C4) * (H ^ 2 / Real.log X ^ A) := by ring
      rw [hkey3] at e1
      rw [hkey4] at e2
      rw [hkeyC] at ⊢
      have hb3 : C3 * (H ^ 2 / Real.log X ^ A) ≤
          max C3 C4 * (H ^ 2 / Real.log X ^ A) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hq
      have hb4 : C4 * (H ^ 2 / Real.log X ^ A) ≤
          max C3 C4 * (H ^ 2 / Real.log X ^ A) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hq
      have hsum : (∫ t in (windowY X ε / 4)..(windowY X ε / 2), ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
          (∫ t in (windowY X ε / 2)..windowY X ε, ‖∑ m ∈ (squareWindow (windowY X ε)).filter
            (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          2 * max C3 C4 * (H ^ 2 / Real.log X ^ A) := by
        linarith
      exact hsum

end LeanLab.KumchevLiu2007.Eq33RouteD
