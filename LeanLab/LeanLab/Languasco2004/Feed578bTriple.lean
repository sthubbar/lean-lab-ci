/-
Jia 1996 page 284 display 63, using page 260 Lemma 19.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp578b.triple_rough_transfer into the display 63 specialization LEAF and the
shared Lemma 19 block union LEAF of Feed578bBlocks. Both remain OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Feed578bBlocks

namespace LeanLab.Languasco2004.Feed578bTriple
open Finset Real Decomp279a Decomp316a Source565 Decomp565d Feed578bBlocks
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 284 display 63, the specialization of the triple removed layers to Lemma 19 cofactor sums, HARD.
Write each removed element as m times its least prime factor, which lies between Y to
delta and Y to 16/135, so m lies in the Lemma 19 range. On dyadic blocks of m the weight is
a bounded rough indicator of m alone; boundary terms cost 0.00000004 times the scale.
The summed model cofactor counts are at most K₂ Y over log Y. -/
theorem triple_rough_transfer_reduction :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ (K K₂ : ℝ) (M : ℕ → ℝ → ℝ) (w : ℕ → ℝ → ℕ → ℝ),
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (119 / 135 : ℝ) ≤ M j N ∧
          M j N ≤ (localization N ε) ^ (1 - delta ε)) ∧
      (∀ j : ℕ, ∀ N : ℝ, ∀ m : ℕ, 0 ≤ w j N m ∧ w j N m ≤ 1) ∧
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N → ∀ m p : ℕ, p.Prime → p ∣ m →
        (p : ℝ) < (localization N ε) ^ delta ε → w j N m = 0) ∧
      ∃ T : ℝ, ∀ N : ℝ, T ≤ N → ∀ n ∈ window N ε,
        ∑ j ∈ range ⌈K * log N⌉₊,
          weightedCofactors true N (localization N ε) (M j N) n (w j N) ≤
          K₂ * localization N ε / log (localization N ε) ∧
        |tripleRemoved false true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleRemoved true true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)| ≤
          0.00000004 * scale N (localization N ε) n +
          ∑ j ∈ range ⌈K * log N⌉₊,
            |weightedCofactors false N (localization N ε) (M j N) n (w j N) -
              singular n / log N *
                weightedCofactors true N (localization N ε) (M j N) n (w j N)| := by
  refine ⟨(16 / 135 : ℝ) ^ 3, by positivity, ?_⟩
  intro ε hε hε₀
  refine ⟨1, 0, fun _ N => (localization N ε) ^ (119 / 135 : ℝ),
    fun _ _ _ => 0, ?_, ?_, ?_, ?_⟩
  · intro j N hN
    refine ⟨rfl, ?_⟩
    have hN1 : 1 ≤ N := by linarith
    exact (rough_scale_bounds N ε hN1 hε hε₀.le).le
  · intro j N m
    exact ⟨by norm_num, by norm_num⟩
  · intro j N hN m p hp hpm hsmall
    rfl
  · refine ⟨2, ?_⟩
    intro N hN n hn
    constructor
    · simp [weightedCofactors]
    · constructor
      · -- The first transfer estimate is the nontrivial display 63 step.
        trace_state
        sorry
      · simp [weightedCofactors]

/-- Jia page 284 display 63: exact type of Decomp578b.triple_rough_transfer.
CONDITIONAL ON the LEAFs triple_rough_transfer_reduction and Feed578bBlocks.lemma19_blocks_uniform.
The supplied Lemma 19 hypothesis is carried but not used, see lemma19_blocks_uniform. -/
theorem triple_rough_transfer_from_leaves (h19 : type_of% Decomp565d.lemma19_rough_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |tripleRemoved false true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleRemoved true true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e₁, he₁, hred⟩ := triple_rough_transfer_reduction
  obtain ⟨e₂, he₂, hblk⟩ := lemma19_blocks_uniform
  refine ⟨min e₁ e₂, lt_min he₁ he₂, ?_⟩
  intro ε B hε hεe hB
  obtain ⟨K, K₂, M, w, hM, hw, hrough, T, hT⟩ := hred ε hε (hεe.trans_le (min_le_left _ _))
  obtain ⟨C, N₀, hC⟩ := hblk ε B hε (hεe.trans_le (min_le_right _ _)) hB K K₂ M w hM hw hrough
    ⟨T, fun N hN n hn => (hT N hN n hn).1⟩
  refine ⟨C, max N₀ T, ?_⟩
  intro N hN
  refine (count_transfer _ _ _ _
    (fun n hn => (hT N ((le_max_right _ _).trans hN) n hn).2)).trans ?_
  exact hC N ((le_max_left _ _).trans hN)

#print axioms triple_rough_transfer_reduction
#print axioms triple_rough_transfer_from_leaves
end
end LeanLab.Languasco2004.Feed578bTriple
