/-
Split of `lemma6` of this folder into the steps of its proof in section 6: the
parity split of the coefficient `R₁(ν°_n)`, the second moment of display 29 on the
even branch, the second moment of display 30 on the odd branch, and the finite
Chebyshev step that turns a second moment into an exceptional count.

`lemma6_split` below states `Lemma6` unchanged and is assembled from the four
leaves, so it carries no `sorry` of its own. Each leaf carries exactly one step
and is strictly weaker than the split's main statement.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.SPLIT_leaf_even_moment
import LeanLab.ExceptionalSet.SPLIT_leaf_odd_moment

namespace LeanLab.ExceptionalSet.U1539

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step of the proof, the parity split of the coefficient, no estimate
enters. The coefficient at the odd member `ν°_n` of the pair is `R₁(ν_n + 1)` when
`ν_n` is even and `R₁(ν_n)` when `ν_n` is odd, so the second moment over the whole
window is the sum of its two parity branches. A finite sum split, valid for every
`δ` and every `N`: at `N = 0` and `N = 1` both sides vanish, and the two filtered
sums are sub-sums of the left side. -/
theorem leaf_moment_parity (γ δ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc ((N + 1) / 2) N,
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2)
      = (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
        + (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) := by
  classical
  rw [← sum_filter_add_sum_filter_not (Finset.Icc ((N + 1) / 2) N) (fun n : ℕ => Even (nu γ n)) (fun n => ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2)]
  congr 1
  · apply sum_congr rfl
    intro x hx
    have h1 : Even (nu γ x) := (Finset.mem_filter.1 hx).2
    have h2 : ¬ Odd (nu γ x) := mt Int.not_even_iff_odd.mpr (not_not.mpr h1)
    have h3 : nuOdd γ x = nu γ x + 1 := by
      unfold nuOdd
      simp [h2]
    rw [h3]
  · apply sum_congr rfl
    intro x hx
    have h1 : ¬ Even (nu γ x) := (Finset.mem_filter.1 hx).2
    have h2 : Odd (nu γ x) := Int.not_even_iff_odd.mp h1
    have h3 : nuOdd γ x = nu γ x := by
      unfold nuOdd
      simp [h2]
    rw [h3]

/-- LEAF. Step of the proof, the even branch: display 29. For `1 < γ < 3/2` the
second moment of the adjacent coefficient `R₁(ν_n + 1)` over the even `ν_n` of the
window is eventually at most `B N F(γ,N)² ℰ(γ,κ,N)^(-1/3)`, for every small enough
`δ` and every `κ` below a positive cap. This is the analytic content of the even
half of section 6; it is an inequality about a sum of squares, with no exceptional
set and no counting step in it. -/
theorem leaf_even_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  exact LeanLab.ExceptionalSet.Decomp371c.Split.leaf_even_moment_split γ h1 h2

/-- LEAF. Step of the proof, the odd branch: display 30 with the reflected kernel.
For `1 < γ < 3/2` the second moment of `R₁(ν_n)` over the odd `ν_n` of the window,
that is over `ν_n` itself rather than its neighbour, is eventually at most
`B N F(γ,N)² ℰ(γ,κ,N)^(-1/3)`. Not being even is the same as being odd for the
integer `ν_n`, so this is the exact complement of the even branch. Again an
inequality about a sum of squares only. -/
theorem leaf_odd_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  exact LeanLab.ExceptionalSet.Decomp371c.leaf_odd_moment_split γ h1 h2

/-- LEAF. Step of the proof, the finite Chebyshev step after display 30, with no
analysis in it. A nonnegative sequence whose squares sum to at most `A` exceeds
`T > 0` on at most `A / T²` indices, because each such index contributes more than
`T²` to the same sum. Stated for an arbitrary finite index set and an arbitrary
nonnegative sequence; at an empty index set both sides vanish and at `A = 0` the
filtered set is empty, so no hypothesis is vacuous. -/
theorem leaf_count_of_moment (s : Finset ℕ) (g : ℕ → ℝ) (T A : ℝ) (hT : 0 < T)
    (hmoment : (∑ n ∈ s, g n ^ 2) ≤ A) :
    (((s.filter (fun n => T < g n)).card : ℝ) * T ^ 2) ≤ A := by
  classical
  calc (((s.filter (fun n => T < g n)).card : ℝ) * T ^ 2) =
      ∑ n ∈ s.filter (fun n => T < g n), T ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ s.filter (fun n => T < g n), g n ^ 2 := by
      apply sum_le_sum
      intro i hi
      have h1 : T < g i := (Finset.mem_filter.1 hi).2
      have h2 : 0 < g i := hT.trans h1
      nlinarith
    _ ≤ ∑ n ∈ s, g n ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro i _ _
      positivity
    _ ≤ A := hmoment

/-! ### Assembly -/

/-- Lemma 6 from the four leaves above: the unchanged statement of `lemma6`. The
two moment leaves are minimised in their two caps and added in their constants,
and the counting leaf at the threshold `B F(γ,N) ℰ^(-1/8)` converts the sum of
squares at the exponent `-1/3` into the exceptional count at the exponent `-1/12`. -/
theorem lemma6_split : Lemma6 := by
  classical
  intro γ h1 h2
  obtain ⟨δa, hδa, ha⟩ := leaf_even_moment γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_odd_moment γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  let κ := min κa κb
  have hκ : 0 < κ := lt_min hκa hκb
  obtain ⟨Ba, hBa, Na, ha⟩ := ha κ hκ (min_le_left _ _)
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (min_le_right _ _)
  let B : ℝ := Ba + Bb + 1
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨κ, B, hκ, max Na Nb, fun N hN => ?_⟩
  have hNa : Na ≤ N := (le_max_left _ _).trans hN
  have hNb : Nb ≤ N := (le_max_right _ _).trans hN
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hT : 0 < B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by positivity
  have hmom : (∑ n ∈ Finset.Icc ((N + 1) / 2) N,
      ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2) ≤
      (Ba + Bb) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
    rw [leaf_moment_parity γ δ N]
    calc _ ≤ Ba * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
          Bb * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
        add_le_add (ha N hNa) (hb N hNb)
      _ = _ := by ring
  have hc := leaf_count_of_moment (Finset.Icc ((N + 1) / 2) N)
    (fun n : ℕ => ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖)
    (B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ)))
    ((Ba + Bb) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) hT hmom
  have hp : calE γ κ N ^ (-(1 / 3 : ℝ)) =
      calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_add hE]
    congr 1
    norm_num
  have hkey : Ba + Bb ≤ B ^ 3 := by
    have h1 : Ba + Bb ≤ B := by dsimp [B]; linarith
    have hB0 : (0 : ℝ) < B := hB
    have hB1 : (1 : ℝ) ≤ B := by dsimp [B]; linarith
    have hB2 : (1 : ℝ) ≤ B ^ 2 := by nlinarith
    calc Ba + Bb ≤ B := h1
      _ = B * 1 := by ring
      _ ≤ B * B ^ 2 := mul_le_mul_of_nonneg_left hB2 hB0.le
      _ = B ^ 3 := by ring
  have hpos : (0 : ℝ) ≤ (N : ℝ) * F γ N ^ 2 *
      (calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2) := by
    have h1 : (0 : ℝ) < calE γ κ N ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hE _
    have h2 : (0 : ℝ) ≤ calE γ κ N ^ (-(1 / 8 : ℝ)) := (Real.rpow_pos_of_pos hE _).le
    positivity
  have hbound : (Ba + Bb) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) ≤
      (B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) *
        (B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 := by
    rw [hp]
    calc (Ba + Bb) * N * F γ N ^ 2 *
          (calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2)
        = (Ba + Bb) * ((N : ℝ) * F γ N ^ 2 *
            (calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2)) := by
          ring
      _ ≤ B ^ 3 * ((N : ℝ) * F γ N ^ 2 *
            (calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2)) :=
          mul_le_mul_of_nonneg_right hkey hpos
      _ = (B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) *
            (B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 := by ring
  exact (mul_le_mul_iff_left₀ (pow_pos hT 2)).mp (hc.trans hbound)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma6_split
