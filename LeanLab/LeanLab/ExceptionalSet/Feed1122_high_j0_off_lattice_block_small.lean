import LeanLab.ExceptionalSet.SPLIT_leaf_high_j0_large_phase_strip

/-!
Feed for `leaf_high_j0_off_lattice_block_small`, P0082 section 7 page 370, proof
of Lemma 9. The parity restricted block phase is written exactly as one half of
the unrestricted block phase plus one half of the sign twisted block phase, the
twist being `(-1) ^ nu n`. Each of the two sums is then a HARD leaf: the
unrestricted one is Theorem 2 of page 354, the twisted one is the parity removal
of displays 40 and 41 followed by Theorem 2. AI wrote the Lean code. Binary
Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553b

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- The high block `3N/4 < n ≤ N` without the parity condition. -/
noncomputable def feed1122_highFull (N : ℕ) : Finset ℕ :=
  (Finset.Ioc (N / 2) N).filter (fun n => ¬ n ≤ 3 * N / 4)

/-- LEAF: P0082 page 354 Theorem 2 applied on page 370 to the high block
`3N/4 < n ≤ N` without parity condition: off the half integer strips the
unrestricted exponential sum over `F γ n` is at most `N E ^ (-(5/6))`. HARD. -/
theorem leaf_feed1122_high_j0_full_block_small (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖∑ n ∈ feed1122_highFull N, eC ((b - a) * F γ n)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  sorry

/-- LEAF: P0082 page 370 displays 40 and 41, parity removal: the sign twist
`(-1) ^ nu n` with `nu n = ⌊F γ n⌋` is removed and the twisted sum over the high
block is reduced to Theorem 2 of page 354, giving the same bound
`N E ^ (-(5/6))` off the half integer strips. HARD. -/
theorem leaf_feed1122_high_j0_twisted_block_small (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖∑ n ∈ feed1122_highFull N, eC ((b - a) * F γ n) * (-1 : ℂ) ^ (nu γ n)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  sorry

/-- The parity restricted block is the high block filtered by evenness. -/
theorem feed1122_indices_eq (γ : ℝ) (N : ℕ) :
    indices_high_j0 γ N = (feed1122_highFull N).filter (fun n => Even (nu γ n)) := by
  ext n
  simp [indices_high_j0, feed1122_highFull]
  tauto

/-- Exact parity identity: restricted phase is the average of the plain and the
twisted phase. -/
theorem feed1122_parity_identity (γ : ℝ) (N : ℕ) (t : ℝ) :
    blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) t =
      ((∑ n ∈ feed1122_highFull N, eC (t * F γ n)) +
        ∑ n ∈ feed1122_highFull N, eC (t * F γ n) * (-1 : ℂ) ^ (nu γ n)) / 2 := by
  rw [blockPhase, feed1122_indices_eq, Finset.sum_filter, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Int.cast_zero, sub_zero]
  rcases Int.even_or_odd (nu γ n) with he | ho
  · rw [if_pos he, he.neg_one_zpow]; ring
  · rw [if_neg (Int.not_even_iff_odd.mpr ho), ho.neg_one_zpow]; ring

theorem leaf_high_j0_off_lattice_block_small_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨d1, hd1, H1⟩ := leaf_feed1122_high_j0_full_block_small γ h1 h2
  obtain ⟨d2, hd2, H2⟩ := leaf_feed1122_high_j0_twisted_block_small γ h1 h2
  refine ⟨min d1 d2, lt_min hd1 hd2, fun δ hδ hδ' => ?_⟩
  obtain ⟨k1, hk1, K1⟩ := H1 δ hδ (lt_of_lt_of_le hδ' (min_le_left _ _))
  obtain ⟨k2, hk2, K2⟩ := H2 δ hδ (lt_of_lt_of_le hδ' (min_le_right _ _))
  refine ⟨min k1 k2, lt_min hk1 hk2, fun κ hκ hκ' => ?_⟩
  obtain ⟨n1, M1⟩ := K1 κ hκ (hκ'.trans (min_le_left _ _))
  obtain ⟨n2, M2⟩ := K2 κ hκ (hκ'.trans (min_le_right _ _))
  refine ⟨max n1 n2, fun N hN a ha b hb hoff => ?_⟩
  have A := M1 N ((le_max_left _ _).trans hN) a ha b hb hoff
  have B := M2 N ((le_max_right _ _).trans hN) a ha b hb hoff
  rw [feed1122_parity_identity, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2n, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add A B
    _ = _ := by ring

end LeanLab.ExceptionalSet.Decomp553b
