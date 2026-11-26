/-
P0068 Zhan 1991, Theorem 2, the reduction of the middle range `N^{2/3} ≤ A ≤ N L⁻¹` to the small
range `A ≤ N^{2/3}`, page 262 last display and page 263 first line. burst-20261124, unit S9-09.
Source: papers/P0068.pdf, journal pages 262 and 263, and its text copy.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Reading. The paper cuts `(N - A, N]` into `J` blocks of length `A₁ ∈ [N^{2/3}/2, N^{2/3}]` and
applies (1.3) to each block with the same `α`. Condition (1.2) for a block asks `q ≤ τ₁` with
`τ₁ = A₁² N⁻¹ L^{-c₁}`, which the `q` of the long window need not meet. The route below first
takes a fresh Dirichlet approximation `a₁/q₁` of `α` with parameter `τ₁ = N^{1/3} L^{-c₁} / 4`:
* if `q₁ ≥ L^{c₂}`, the blockwise step of the paper applies with `a₁/q₁`, LEAF `middle_block_leaf`;
* if `q₁ < L^{c₂}`, `α` is close to a fraction with small denominator, `a/q ≠ a₁/q₁`, so
  `|λ₁| ≥ 1/(2 q q₁)`, and the long sum is a major arc sum with oscillating phase, of size
  about `A L^{-c₁-1}`; this case is not argued in the paper, LEAF `middle_major_leaf`, and it
  needs `c₁` large in terms of `B`.

QUESTION, statement suspected false: `MiddleReduction` of SPLIT_theorem2_1122 quantifies every
`c₁ > 0`. For `c₁ < B - 1` its conclusion fails: with `A = N L⁻¹`, `q` a prime near
`τ = A² N⁻¹ L^{-c₁}`, `a = 1` and `α = 1/q - 1/(qτ)`, condition (1.2) holds, `α A` is about
`L^{c₁+1}`, and by the prime number theorem `S(α; N, A)` is about `A L^{-c₁-1}`, larger than any
`K A L^{-B}`. So `MiddleReduction` holds at such `c₁` only if the small range estimate fails
there for every `K, N₀`, which is not expected. The corrected reduction
`middleReductionLarge_of_leaves` asks `c₁ ≥ c₁m`, and `theorem2_of_ranges_large` assembles
Theorem 2 from it; both are PROVED from the LEAFs.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: page 262 last display, the fresh rational approximation behind the block cut; it is
Dirichlet's approximation theorem with parameter `τ₁ = N^{1/3} L^{-c₁} / 4`, which is `≥ 1`
for large `N`. Class EASY. -/
theorem middle_dirichlet_leaf (c1 : ℝ) :
    ∃ N₁ : ℝ, ∀ N : ℕ, N₁ ≤ N → ∀ α : ℝ, ∃ (a1 : ℤ) (q1 : ℕ),
      Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 (α - a1 / q1) := by
  sorry

/-- LEAF: page 262 last display and page 263 first line, the blockwise step of the paper when
the fresh approximation `a₁/q₁` with parameter `τ₁ = N^{1/3} L^{-c₁} / 4` has `q₁ ≥ L^{c₂}`:
cut `(N - A, N]` into blocks whose lengths `A_b` give each block exactly the parameter `τ₁`,
`A_b² / N_b · (log N_b)^{-c₁} = τ₁`, so (1.2) holds on every block, apply (1.3) of the small
range to each and sum, `≪ J · A_b L^{-B} ≪ A L^{-B}`; the last block is closed by a difference
of two such windows, leaving `O(N^{1/3})` terms bounded trivially. Class HARD. -/
theorem middle_block_leaf : ∀ B c1 c2 c3 K N₀ : ℝ, 0 < B → 0 < c1 → 0 < c2 → 0 < c3 →
    Est13 B c1 c2 K N₀ (fun N => (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3)
      (fun N => (N : ℝ) ^ (2 / 3 : ℝ)) →
    ∃ K' N₀' : ℝ, ∀ (N : ℕ) (A α : ℝ) (a1 : ℤ) (q1 : ℕ) (lam1 : ℝ), N₀' ≤ N →
      (N : ℝ) ^ (2 / 3 : ℝ) ≤ A → A ≤ (N : ℝ) / Real.log N →
      Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1 →
      Real.log N ^ c2 ≤ q1 → ‖Sexp α N A‖ ≤ K' * A * Real.log N ^ (-B) := by
  sorry

/-- LEAF: page 262 last display, the case the blockwise step does not cover, not argued in the
paper: (1.2) holds with `τ = A² N⁻¹ L^{-c₁}` and `q ≥ L^{c₂}`, but the fresh approximation with
`τ₁ = N^{1/3} L^{-c₁} / 4` has `q₁ < L^{c₂}`. Then `a/q ≠ a₁/q₁`, `|λ₁| ≥ 1/(2 q q₁)`,
`|λ₁| A ≥ L^{c₁+1} / (2 q₁)`, and the Siegel and Walfisz theorem on the window, `A ≥ N^{2/3}`,
gives `S ≪ (q₁/φ(q₁)) A L^{-c₁-1} + A L^{-B}`. Class HARD. -/
theorem middle_major_leaf : ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∀ c2 : ℝ, 0 < c2 →
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) (a1 : ℤ) (q1 : ℕ) (lam1 : ℝ),
      N₀ ≤ N → (N : ℝ) ^ (2 / 3 : ℝ) ≤ A → A ≤ (N : ℝ) / Real.log N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam → Real.log N ^ c2 ≤ q →
      Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1 →
      (q1 : ℝ) < Real.log N ^ c2 → ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B) := by
  sorry

/-- Page 262 last display and page 263 first line, the corrected reduction: for `c₁` large in
terms of `B`, (1.3) on the small range gives (1.3) on `N^{2/3} ≤ A ≤ N L⁻¹`. PROVED from the
three LEAFs `middle_dirichlet_leaf`, `middle_block_leaf`, `middle_major_leaf`. -/
theorem middleReductionLarge_of_leaves : ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m,
    ∀ c2 c3 K N₀ : ℝ, 0 < c2 → 0 < c3 →
    Est13 B c1 c2 K N₀ (fun N => (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3)
      (fun N => (N : ℝ) ^ (2 / 3 : ℝ)) →
    ∃ K' N₀' : ℝ, Est13 B c1 c2 K' N₀' (fun N => (N : ℝ) ^ (2 / 3 : ℝ))
      (fun N => (N : ℝ) / Real.log N) := by
  intro B hB
  obtain ⟨c1m, hmaj⟩ := middle_major_leaf B hB
  refine ⟨max c1m 1, fun c1 hc1 c2 c3 K N₀ hc2 hc3 hE => ?_⟩
  have hc1pos : 0 < c1 := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hc1)
  obtain ⟨Kb, Nb, hblock⟩ := middle_block_leaf B c1 c2 c3 K N₀ hB hc1pos hc2 hc3 hE
  obtain ⟨Km, Nm, hmaj'⟩ := hmaj c1 (le_trans (le_max_left _ _) hc1) c2 hc2
  obtain ⟨N₁, hdir⟩ := middle_dirichlet_leaf c1
  refine ⟨max Kb Km, max (max Nb Nm) N₁, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  have hNb : Nb ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNm : Nm ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_max_right _ _) hN
  have hA : 0 ≤ A := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hlo
  have hX : 0 ≤ A * Real.log N ^ (-B) :=
    mul_nonneg hA (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  have key : ∀ K', K' ≤ max Kb Km →
      K' * A * Real.log N ^ (-B) ≤ max Kb Km * A * Real.log N ^ (-B) := by
    intro K' hK'
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hK' hX
  obtain ⟨a1, q1, h1⟩ := hdir N hN1 α
  rcases le_or_gt (Real.log N ^ c2) (q1 : ℝ) with hq1 | hq1
  · exact le_trans (hblock N A α a1 q1 _ hNb hlo hhi h1 hq1) (key _ (le_max_left _ _))
  · exact le_trans (hmaj' N A α lam a q a1 q1 _ hNm hlo hhi hcond hq h1 hq1)
      (key _ (le_max_right _ _))

/-- Theorem 2 from the three ranges of pages 262 and 263, with the corrected middle reduction
that asks `c₁` large. PROVED from its three hypotheses, as `theorem2_of_ranges`. -/
theorem theorem2_of_ranges_large (hs : SmallRange)
    (hr : ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∀ c2 c3 K N₀ : ℝ, 0 < c2 → 0 < c3 →
      Est13 B c1 c2 K N₀ (fun N => (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3)
        (fun N => (N : ℝ) ^ (2 / 3 : ℝ)) →
      ∃ K' N₀' : ℝ, Est13 B c1 c2 K' N₀' (fun N => (N : ℝ) ^ (2 / 3 : ℝ))
        (fun N => (N : ℝ) / Real.log N))
    (hl : LargeRange) : Theorem2 := by
  intro B hB
  obtain ⟨a1, h1⟩ := hs B hB
  obtain ⟨a2, h2⟩ := hr B hB
  obtain ⟨a3, h3⟩ := hl B hB
  set C1 := max (max a1 a3) (max a2 1) with hC1
  have hC1a1 : a1 ≤ C1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC1a3 : a3 ≤ C1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC1a2 : a2 ≤ C1 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hc1 : (0 : ℝ) < C1 :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨b1, h1'⟩ := h1 C1 hC1a1
  obtain ⟨b3, h3'⟩ := h3 C1 hC1a3
  set C2 := max (max b1 b3) 1 with hC2
  obtain ⟨c3, hc3, K1, N1, e1⟩ := h1' C2 (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨K3, N3, e3⟩ := h3' C2 (le_trans (le_max_right _ _) (le_max_left _ _))
  have hc2 : (0 : ℝ) < C2 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨K2, N2, e2⟩ := h2 C1 hC1a2 C2 c3 K1 N1 hc2 hc3 e1
  refine ⟨C1, C2, c3, hc1, hc2, hc3, max (max K1 K2) K3, max (max N1 N2) N3, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hA : 0 ≤ A := le_trans (by positivity) hlo
  have hX : 0 ≤ A * Real.log N ^ (-B) := mul_nonneg hA (Real.rpow_nonneg hL _)
  have key : ∀ K', K' ≤ max (max K1 K2) K3 →
      K' * A * Real.log N ^ (-B) ≤ max (max K1 K2) K3 * A * Real.log N ^ (-B) := by
    intro K' hK'
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hK' hX
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 ≤ N := le_trans (le_max_right _ _) hN
  rcases le_total A ((N : ℝ) ^ (2 / 3 : ℝ)) with h | h
  · exact le_trans (e1 N A α lam a q hN1 hlo h hcond hq)
      (key _ (le_trans (le_max_left _ _) (le_max_left _ _)))
  · rcases le_total A ((N : ℝ) / Real.log N) with h' | h'
    · exact le_trans (e2 N A α lam a q hN2 h h' hcond hq)
        (key _ (le_trans (le_max_right _ _) (le_max_left _ _)))
    · exact le_trans (e3 N A α lam a q hN3 h' hhi hcond hq) (key _ (le_max_right _ _))

/-- Theorem 2 assembled from the LEAF chain with the corrected middle reduction in place of
`middle_reduction_leaf`. Its axioms include `sorryAx` through the LEAFs. -/
theorem theorem2_from_leaves_large : Theorem2 :=
  theorem2_of_ranges_large
    (smallRange_of_wellKnown_eq31 wellKnown_leaf
      (eq31_of_eq38_leaf (eq38_of_eq311_eq312_leaf eq311_leaf eq312_leaf)))
    middleReductionLarge_of_leaves large_range_leaf

end

end LeanLab.Zhan1991
