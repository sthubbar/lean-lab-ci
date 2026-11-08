import LeanLab.ExceptionalSet.SPLIT_leaf_even_moment

/-!
Split of the lower half of the even second moment, the statement
`LeanLab.ExceptionalSet.Decomp371c.Split.leaf_even_moment_lower` of
`SPLIT_leaf_even_moment.lean`, into three leaves and an assembly.

The statement bounds the second moment of the adjacent major arc coefficient `R₁(ν_n + 1)`, summed
over the even `ν_n` of the half window `Icc ((N+1)/2) N` that also satisfy `2 n ≤ N + (N+1)/2`, by
`B N F(γ,N)² ξ^(-1/3)`, for a constant `B` chosen after `δ` and `κ`, and for all `N` past a
threshold chosen after `B`.

The index set of the sum is cut into three consecutive pieces at the two points
`(N+1)/2 + N/16` and `(N+1)/2 + N/8`.  Each leaf carries the two index conditions of the target
together with the condition that places `n` in one piece, so each leaf sums the same nonnegative
terms over a subset of the target's index set: the target's inequality implies each leaf, and the
leaves are therefore strictly weaker than the target.

The assembly writes the filtered sum as a sum of the corresponding indicator functions, splits the
indicator of the target's index set into the indicators of the three pieces (which partition it),
turns each of the three back into a filtered sum, adds the three leaf estimates and merges their
constants into `B₁ + B₂ + B₃ + 1`.  The caps are the minima of the three pairs of caps and the
threshold is the maximum of the three thresholds.
-/

namespace LeanLab.ExceptionalSet.Decomp371c.Split

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF 1 of 3. Step of the proof: the first piece of the index set, up to the lower cut point
`(N + 1) / 2 + N / 16`.  The same second moment bound as the target, for the sum restricted to the
indices `n ≤ (N + 1) / 2 + N / 16` of the target's index set.  This is a sum of the target's
nonnegative terms over a subset of its index set.  At `N = 0` and `N = 1` the sum is empty, since
`ν_0 = ν_1 = 1` is odd, and the bound reads `0 ≤ B * N * F(γ,N)² ξ^(-1/3)`. -/
theorem leaf_even_moment_lower_first (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
                (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
                  n ≤ (N + 1) / 2 + N / 16),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- LEAF 2 of 3. Step of the proof: the middle piece of the index set, between the two cut points.
The same second moment bound as the target, for the sum restricted to the indices
`(N + 1) / 2 + N / 16 < n ≤ (N + 1) / 2 + N / 8` of the target's index set.  Again a sum of the
target's nonnegative terms over a subset of its index set, hence strictly weaker.  At `N = 0` and
`N = 1` this piece is empty. -/
theorem leaf_even_moment_lower_middle (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
                (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
                  (N + 1) / 2 + N / 16 < n ∧ n ≤ (N + 1) / 2 + N / 8),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- LEAF 3 of 3. Step of the proof: the last piece of the index set, past the upper cut point
`(N + 1) / 2 + N / 8`.  The same second moment bound as the target, for the sum restricted to the
indices `(N + 1) / 2 + N / 8 < n` of the target's index set.  This is the piece on which the
constraint `2 n ≤ N + (N + 1) / 2` is genuinely restrictive.  At `N = 0` and `N = 1` this piece is
empty. -/
theorem leaf_even_moment_lower_last (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
                (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
                  (N + 1) / 2 + N / 8 < n),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- Assembly.  `leaf_even_moment_lower` of `SPLIT_leaf_even_moment.lean`, from the three pieces:
the filtered sum is written as a sum of indicators, the indicator of the target's index condition
splits into the three pieces, and the three estimates are added.  The caps are the minima of the
three pairs, the constant is `B₁ + B₂ + B₃ + 1`, the threshold the maximum of the three, and no
`sorry` is used. -/
theorem leaf_even_moment_lower_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
                (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₁, hδ₁, h₁⟩ := leaf_even_moment_lower_first γ h1 h2
  obtain ⟨δ₂, hδ₂, h₂⟩ := leaf_even_moment_lower_middle γ h1 h2
  obtain ⟨δ₃, hδ₃, h₃⟩ := leaf_even_moment_lower_last γ h1 h2
  refine ⟨min (min δ₁ δ₂) δ₃, lt_min (lt_min hδ₁ hδ₂) hδ₃, fun δ hδ hδs => ?_⟩
  have hδ1 : δ < δ₁ := hδs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ < δ₂ := hδs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3 : δ < δ₃ := hδs.trans_le (min_le_right _ _)
  obtain ⟨κ₁, hκ₁, h₁⟩ := h₁ δ hδ hδ1
  obtain ⟨κ₂, hκ₂, h₂⟩ := h₂ δ hδ hδ2
  obtain ⟨κ₃, hκ₃, h₃⟩ := h₃ δ hδ hδ3
  refine ⟨min (min κ₁ κ₂) κ₃, lt_min (lt_min hκ₁ hκ₂) hκ₃, fun κ hκ hκs => ?_⟩
  have hκ1 : κ ≤ κ₁ := hκs.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hκ2 : κ ≤ κ₂ := hκs.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hκ3 : κ ≤ κ₃ := hκs.trans (min_le_right _ _)
  obtain ⟨B₁, hB₁, N₁, h₁⟩ := h₁ κ hκ hκ1
  obtain ⟨B₂, hB₂, N₂, h₂⟩ := h₂ κ hκ hκ2
  obtain ⟨B₃, hB₃, N₃, h₃⟩ := h₃ κ hκ hκ3
  refine ⟨B₁ + B₂ + B₃ + 1, by linarith, max (max N₁ N₂) N₃, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans hN
  have h₁' := h₁ N hN1
  have h₂' := h₂ N hN2
  have h₃' := h₃ N hN3
  have hbc : (N + 1) / 2 + N / 16 ≤ (N + 1) / 2 + N / 8 := by omega
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hK : 0 ≤ N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
      (Real.rpow_pos_of_pos hE _).le
  have hpt : ∀ n : ℕ,
      (if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 then
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0) =
        (if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
            n ≤ (N + 1) / 2 + N / 16 then
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0) +
        (if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
            (N + 1) / 2 + N / 16 < n ∧ n ≤ (N + 1) / 2 + N / 8 then
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0) +
        (if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
            (N + 1) / 2 + N / 8 < n then
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0) := by
    intro n
    by_cases hP : Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2
    · by_cases h1 : n ≤ (N + 1) / 2 + N / 16
      · have h2 : n ≤ (N + 1) / 2 + N / 8 := le_trans h1 hbc
        have h1' : ¬ (N + 1) / 2 + N / 16 < n := not_lt_of_ge h1
        have h2' : ¬ (N + 1) / 2 + N / 8 < n := not_lt_of_ge h2
        simp [hP, h1, h2, h1', h2']
      · have h1' : (N + 1) / 2 + N / 16 < n := Nat.lt_of_not_le h1
        by_cases h2 : n ≤ (N + 1) / 2 + N / 8
        · have h2' : ¬ (N + 1) / 2 + N / 8 < n := not_lt_of_ge h2
          simp [hP, h1, h1', h2, h2']
        · have h2' : (N + 1) / 2 + N / 8 < n := Nat.lt_of_not_le h2
          simp [hP, h1, h1', h2, h2']
    · have e1 : ¬ (Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
          n ≤ (N + 1) / 2 + N / 16) := fun h => hP ⟨h.1, h.2.1⟩
      have e2 : ¬ (Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
          (N + 1) / 2 + N / 16 < n ∧ n ≤ (N + 1) / 2 + N / 8) := fun h => hP ⟨h.1, h.2.1⟩
      have e3 : ¬ (Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
          (N + 1) / 2 + N / 8 < n) := fun h => hP ⟨h.1, h.2.1⟩
      rw [if_neg hP, if_neg e1, if_neg e2, if_neg e3]
      ring
  calc (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
          (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
      = ∑ n ∈ (Finset.Icc ((N + 1) / 2) N),
          (if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 then
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0) := by
        rw [Finset.sum_filter]
    _ = ∑ n ∈ (Finset.Icc ((N + 1) / 2) N),
          ((if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
              n ≤ (N + 1) / 2 + N / 16 then
              ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0) +
            (if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
              (N + 1) / 2 + N / 16 < n ∧ n ≤ (N + 1) / 2 + N / 8 then
              ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0) +
          (if Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
              (N + 1) / 2 + N / 8 < n then
              ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 else 0)) :=
        Finset.sum_congr rfl (fun n _ => hpt n)
    _ = (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
            (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
              n ≤ (N + 1) / 2 + N / 16),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) +
        (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
            (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
              (N + 1) / 2 + N / 16 < n ∧ n ≤ (N + 1) / 2 + N / 8),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) +
        (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter
            (fun n : ℕ => Even (nu γ n) ∧ 2 * n ≤ N + (N + 1) / 2 ∧
              (N + 1) / 2 + N / 8 < n),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [← Finset.sum_filter]
    _ ≤ B₁ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
          B₂ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
        B₃ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
        add_le_add (add_le_add h₁' h₂') h₃'
    _ = (B₁ + B₂ + B₃) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by ring
    _ ≤ (B₁ + B₂ + B₃ + 1) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
        have hstep : B₁ + B₂ + B₃ ≤ B₁ + B₂ + B₃ + 1 := by linarith
        have hmul := mul_le_mul_of_nonneg_right hstep hK
        calc (B₁ + B₂ + B₃) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))
            = (B₁ + B₂ + B₃) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by
              ring
          _ ≤ (B₁ + B₂ + B₃ + 1) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := hmul
          _ = (B₁ + B₂ + B₃ + 1) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
              ring

#print axioms leaf_even_moment_lower_split

end LeanLab.ExceptionalSet.Decomp371c.Split
