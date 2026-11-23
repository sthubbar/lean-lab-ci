/-
Wiring unit integrate1122d-wire, burst-20261122, session S111. P0088, Kumchev and Liu,
arXiv 0801.0130, Theorem 1 on the written range of page 16, the Prop
Task129W.kumchev_liu_thm1_written, assembled one level deeper than
DQThm1Integrate1122c.thm1_written_integrated.

DQThm1Integrate1122c still called these leaves: the three case leaves of
Prep1122KLLemma34Cases through Split1122KLLemma34M1.lemma34_unit_coefficient, the three
case leaves of Split1122SecondDyadicBlock, Burst1122B27.kernel_sum_bound, and
Prep1122KLGallagherCut.saffari_vaughan_device. Each leaf is called inside a proof, not
taken as an argument, and the twin files import the files that hold the leaves, so each
assembly step above a leaf is copied here verbatim with the leaf call replaced by the
deepest twin:

* page 11 Lemma 3.4, M = 1: Lemma34UnitWired1122.lemma34_unit_wired, resting on the
  LEAFs Prep1122KLLemma31Cases.lemma31, lemma32 and
  Lemma34Case3General1122.leaf_case3_lemma33_general; feeds the first sum of display 52,
  page 15, through the halves of Split1122KLLemma34M1 and Split1122KLFirstRoughHalves.
* page 11 and 12, Cases 1 to 3 on the second sum of display 52: SecondDyadicCases1122
  with the interior LEAFs replaced by SecondDyadicInterior1122.case1_interior_of_lemma31
  and case2_interior_of_lemma32, leaving the edge LEAFs case1_edge and case2_edge, and
  SecondDyadicCase3Split1122.case3_large_D_of_split, leaving case3_interior and case3_edge.
* page 7, the display before 27: KernelSumSplit1122.kernel_sum_bound_split, leaving the
  MEDIUM LEAFs inner_window_bound and outer_square_bound.
* page 6, the display before 20: saffari_vaughan_device has no twin and stays.

CONDITIONAL ON the cited A12Corr and A22Corr. Every theorem of this file is closed in Lean, no proof hole.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.DQThm1Integrate1122c
import LeanLab.KumchevLiu2007.Lemma34UnitWired1122
import LeanLab.KumchevLiu2007.SecondDyadicInterior1122
import LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122
import LeanLab.KumchevLiu2007.KernelSumSplit1122

namespace LeanLab.KumchevLiu2007.DQThm1Integrate1122d

section FirstSum

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open LeanLab.KumchevLiu2007.Split1122KLLemma34M1
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 11 Lemma 3.4 with M = 1, the exact statement of
Split1122KLLemma34M1.lemma34_unit_coefficient, from Lemma34UnitWired1122.lemma34_unit_wired
by dropping its extra conclusion 2 at most x0. CONDITIONAL ON the LEAFs lemma31, lemma32
of Prep1122KLLemma31Cases and leaf_case3_lemma33_general of Lemma34Case3General1122. -/
theorem lemma34_unit_coefficient_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        (∫ t in x..2 * x,
          ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
            roughWeight z k *
              fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  obtain ⟨B0, hB0, h⟩ := Lemma34UnitWired1122.lemma34_unit_wired A hA
  refine ⟨B0, hB0, fun B hB => ?_⟩
  obtain ⟨C, x0, hC, -, hk⟩ := h B hB
  exact ⟨C, x0, hC, hk⟩

/-- P0088 page 11 Lemma 3.4 with x = Y/4 applied on page 15, the exact statement of Split1122KLFirstRoughHalves.block_rough_left_half; the proof of Split1122KLLemma34M1.block_rough_left_half_of_lemma34 with lemma34_unit_coefficient_d in place of the old leaf. -/
theorem block_rough_left_half_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε / 2,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, hlem⟩ := lemma34_unit_coefficient_d A hA
  refine ⟨max B1 (A / 4), lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := hB1.trans_le hBB1
  obtain ⟨C, x0, hC, hL⟩ := hlem B hBB1
  obtain ⟨X1, hX1, hbig⟩ := block_large_X B ε x0 hBpos hε hε'
  refine ⟨C * 2 ^ A, X1, by positivity, hX1, ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  obtain ⟨hL1, hP2, hgap, hhalf, hx0⟩ := hbig X hX
  have hX2 : 2 ≤ X := hX1.trans hX
  have hYge : X ^ (7 / 12 : ℝ) ≤ windowY X ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨hsx, hHx, hq1, hq2, hdir, hzz, -, -, -, hlx0, hlogx⟩ :=
    block_hyps B ε X H (windowY X ε / 4) z α q a hBpos hε hε' hX2 hL1 hP2 hgap hhalf
      hlo hhi hqP hqQ hclose hz le_rfl (by linarith)
  have hmain := hL (windowY X ε / 4) H (by linarith) hsx hHx α q a hcop hq1 hq2 hdir
    z hz2.le hzz
  rw [show 2 * (windowY X ε / 4) = windowY X ε / 2 by ring] at hmain
  have hcongr : (∫ t in windowY X ε / 4..windowY X ε / 2,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      ∫ t in windowY X ε / 4..windowY X ε / 2,
      ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (windowY X ε / 4))⌋₊ + 1)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [window_filter_eq (windowY X ε) (windowY X ε / 4) t H le_rfl ht.1
      (by linarith [ht.2]) hHx (by linarith [ht.2])]
  rw [hcongr]
  exact hmain.trans (log_saving_conv C H _ _ A hC.le hA (by linarith) hlx0 hlogx)

/-- P0088 page 11 Lemma 3.4 with x = Y/2 applied on page 15, the exact statement of Split1122KLFirstRoughHalves.block_rough_right_half; the proof of Split1122KLLemma34M1.block_rough_right_half_of_lemma34 with lemma34_unit_coefficient_d. -/
theorem block_rough_right_half_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 2..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, hlem⟩ := lemma34_unit_coefficient_d A hA
  refine ⟨max B1 (A / 4), lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hBA : A / 4 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := hB1.trans_le hBB1
  obtain ⟨C, x0, hC, hL⟩ := hlem B hBB1
  obtain ⟨X1, hX1, hbig⟩ := block_large_X B ε x0 hBpos hε hε'
  refine ⟨C * 2 ^ A + 8, X1, by positivity, hX1, ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  obtain ⟨hL1, hP2, hgap, hhalf, hx0⟩ := hbig X hX
  have hX2 : 2 ≤ X := hX1.trans hX
  have hYge : X ^ (7 / 12 : ℝ) ≤ windowY X ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨hsx, hHx, hq1, hq2, hdir, hzz, hsY, hH4, hHP, hlx0, hlogx⟩ :=
    block_hyps B ε X H (windowY X ε / 2) z α q a hBpos hε hε' hX2 hL1 hP2 hgap hhalf
      hlo hhi hqP hqQ hclose hz (by linarith) (by linarith)
  have hH0 : 0 < H := lt_of_lt_of_le (Real.sqrt_pos.mpr hY0) hsY
  have hmain := hL (windowY X ε / 2) H (by linarith) hsx hHx α q a hcop hq1 hq2 hdir
    z hz2.le hzz
  rw [show 2 * (windowY X ε / 2) = windowY X ε by ring] at hmain
  have hint := fun (S : Finset ℕ) (u v : ℝ) => short_sum_sq_intervalIntegrable S
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H u v
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (squareWindow (windowY X ε)) (windowY X ε / 2) (windowY X ε - 2 * H))
    (hint (squareWindow (windowY X ε)) (windowY X ε - 2 * H) (windowY X ε))]
  have hcongr : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      ∫ t in windowY X ε / 2..windowY X ε - 2 * H,
      ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (windowY X ε / 2))⌋₊ + 1)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [window_filter_eq (windowY X ε) (windowY X ε / 2) t H (by linarith) ht.1
      (by linarith [ht.2]) hHx (by linarith [ht.2])]
  have p1 : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      C * 2 ^ A * H ^ 2 / Real.log X ^ A := by
    rw [hcongr]
    refine le_trans ?_ (hmain.trans
      (log_saving_conv C H _ _ A hC.le hA (by linarith) hlx0 hlogx))
    exact intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => by simp only [Pi.zero_apply]; positivity))
      (hint _ _ _)
  have p2 : (∫ t in windowY X ε - 2 * H..windowY X ε,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      8 * H ^ 2 / Real.log X ^ A := by
    refine le_trans ?_ (tail_arith H (windowY X ε) (Real.log X) A B hY0 hsY hHP hL1 hBA)
    refine le_trans (intervalIntegral.integral_mono_on (by linarith) (hint _ _ _)
      intervalIntegrable_const (fun t ht => short_sum_sq_le _ z α (windowY X ε) t H hY0
        (by linarith [ht.1]) hH0.le)) ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have e : (C * 2 ^ A + 8) * H ^ 2 / Real.log X ^ A =
      C * 2 ^ A * H ^ 2 / Real.log X ^ A + 8 * H ^ 2 / Real.log X ^ A := by ring
  rw [e]
  exact add_le_add p1 p2

/-- P0088 page 15 display 52 first sum, large cutoff, the exact statement of Prep1121DKLRoughCut.first_rough_block; the proof of Split1122KLFirstRoughHalves.first_rough_block_of_halves with the two _d halves. -/
theorem first_rough_block_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := block_rough_left_half_d A hA
  obtain ⟨B2, hB2, h2⟩ := block_rough_right_half_d A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, by linarith, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  have hint1 := Eq33RouteD.short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H
      (windowY X ε / 4) (windowY X ε / 2)
  have hint2 := Eq33RouteD.short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H
      (windowY X ε / 2) (windowY X ε)
  rw [(intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm]
  have hsum : (C1 + C2) * H ^ 2 / Real.log X ^ A =
      C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := by ring
  rw [hsum]
  exact add_le_add e1 e2

/-- P0088 page 15 display 52 first sum, the exact statement of Prep1121KLRough.first_sum_block; the proof of Split1122KLFirstRoughHalves.first_sum_block_of_halves with first_rough_block_d. -/
theorem first_sum_block_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := Prep1121DKLRoughCut.first_small_block A hA
  obtain ⟨B2, hB2, h2⟩ := first_rough_block_d A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨max C1 C2, max X1 X2, lt_max_of_lt_left hC1, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hq : 0 ≤ H ^ 2 / Real.log X ^ A := by positivity
  have r1 : C1 * H ^ 2 / Real.log X ^ A ≤ max C1 C2 * H ^ 2 / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  have r2 : C2 * H ^ 2 / Real.log X ^ A ≤ max C1 C2 * H ^ 2 / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hq
  by_cases hz2 : z ≤ 2
  · simp only [Prep1121DKLRoughCut.roughWeight_eq_one_of_le_two hz2, one_mul]
    exact (k1 X H hXa hlo hhi α q a hcop hqP hqQ hclose).trans r1
  · exact (k2 X H hXb hlo hhi α q a hcop hqP hqQ hclose z (lt_of_not_ge hz2) hz).trans r2

end FirstSum

section SecondSum

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 11 Case 1 of the proof of Lemma 3.4 applied on page 15, the exact statement of Split1122SecondDyadicBlock.case1_small_D; the proof of SecondDyadicCases1122.case1_small_D_of_split with the interior LEAF replaced by its proof SecondDyadicInterior1122.case1_interior_of_lemma31. CONDITIONAL ON lemma31 and the LEAF SecondDyadicCases1122.case1_edge. -/
theorem case1_small_D_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := SecondDyadicInterior1122.case1_interior_of_lemma31 A hA
  obtain ⟨B2, hB2, h2⟩ := SecondDyadicCases1122.case1_edge A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, add_pos hC1 hC2, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD1 hD2
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  refine le_of_eq_of_le (intervalIntegral.integral_add_adjacent_intervals
    (b := windowY X ε - 2 * H) ?_ ?_).symm ?_
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · calc _ ≤ C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := add_le_add e1 e2
      _ = (C1 + C2) * H ^ 2 / Real.log X ^ A := by ring

/-- P0088 page 11 Case 2 of the proof of Lemma 3.4 applied on page 15, the exact statement of Split1122SecondDyadicBlock.case2_middle_D; the proof of SecondDyadicCases1122.case2_middle_D_of_split with the interior LEAF replaced by SecondDyadicInterior1122.case2_interior_of_lemma32. CONDITIONAL ON lemma32 and the LEAF SecondDyadicCases1122.case2_edge. -/
theorem case2_middle_D_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, Real.log X ^ B < D →
        D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := SecondDyadicInterior1122.case2_interior_of_lemma32 A hA
  obtain ⟨B2, hB2, h2⟩ := SecondDyadicCases1122.case2_edge A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, add_pos hC1 hC2, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD1 hD2
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  refine le_of_eq_of_le (intervalIntegral.integral_add_adjacent_intervals
    (b := windowY X ε - 2 * H) ?_ ?_).symm ?_
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · calc _ ≤ C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := add_le_add e1 e2
      _ = (C1 + C2) * H ^ 2 / Real.log X ^ A := by ring

/-- P0088 page 11 display 42 for one dyadic block D, the exact statement of Split1122SecondDyadicBlock.display42_block; its proof with the three case leaves replaced by case1_small_D_d, case2_middle_D_d and SecondDyadicCase3Split1122.case3_large_D_of_split. -/
theorem display42_block_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := case1_small_D_d A hA
  obtain ⟨B2, hB2, h2⟩ := case2_middle_D_d A hA
  obtain ⟨B3, hB3, h3⟩ := SecondDyadicCase3Split1122.case3_large_D_of_split A hA
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  have hb1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hb2 : B2 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hb3 : B3 ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B hb1 ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B hb2 ε hε hε'
  obtain ⟨C3, X3, hC3, hX3, k3⟩ := h3 B hb3 ε hε hε'
  refine ⟨max C1 (max C2 C3), max X1 (max X2 X3), lt_max_of_lt_left hC1,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hq : 0 ≤ H ^ 2 / Real.log X ^ A := div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hL A).le
  have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
    fun c => by ring
  by_cases hc1 : D ≤ Real.log X ^ B
  · have e := k1 X H hXa hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD hc1
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · push Not at hc1
    by_cases hc2 : D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B)
    · have e := k2 X H hXb hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hc1 hc2
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) hq)
    · push Not at hc2
      have e := k3 X H hXc hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hc2
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) hq)

/-- P0088 page 11, the reduction of Lemma 3.4 to display 42 for one dyadic block of primes, the exact statement of Split1122SecondDyadicBlock.interior_core; its proof with display42_block_d. -/
theorem interior_core_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
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
  obtain ⟨B2, hB2, h2⟩ := display42_block_d (A + 2) (by linarith)
  refine ⟨B2, hB2, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h2 B hB ε hε hε'
  refine ⟨9 * C, max X0 3, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose M hM htop hlow
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hY0 : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
      _ = X := Real.rpow_one X
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, X < (2 : ℝ) ^ J ∧ (J : ℝ) ≤ 3 * Real.log X := by
    refine ⟨⌊Real.logb 2 X⌋₊ + 1, ?_, ?_⟩
    · have h1 : Real.logb 2 X < ((⌊Real.logb 2 X⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at h2
    · push_cast
      have hlb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1.le
      have h1 : (⌊Real.logb 2 X⌋₊ : ℝ) ≤ Real.logb 2 X := Nat.floor_le hlb
      have h2 : Real.logb 2 X ≤ 2 * Real.log X := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [Real.log_two_gt_d9]
      linarith
  have hmJ : ∀ m ∈ squareWindow (windowY X ε), m < 2 ^ J := by
    intro m hm
    have hm' := (Finset.mem_filter.mp hm).2.2
    have hs : Real.sqrt (windowY X ε) ≤ X := by
      calc Real.sqrt (windowY X ε) ≤ Real.sqrt X := Real.sqrt_le_sqrt hYX
        _ ≤ X := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
    have : (m : ℝ) < (2 : ℝ) ^ J := by linarith
    exact_mod_cast this
  have hfun : ∀ t : ℝ,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 =
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ j ∈ Finset.range J,
          ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    intro t
    congr 2
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [block_coeff_eq_sum_dyadic _ _ M J m (hmJ m (Finset.mem_filter.mp hm).1)]
  rw [intervalIntegral.integral_congr (fun t _ => hfun t)]
  refine (dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
            (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
            p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
              (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
              (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ (C * H ^ 2 / Real.log X ^ (A + 2)) (by linarith)
    (fun j _ => k X H hXa hH hHX α q a hcop hqP hqQ hclose M hM htop hlow ((2 : ℝ) ^ j)
      (one_le_pow₀ (by norm_num)))).trans ?_
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
    rw [Real.rpow_add hL, Real.rpow_two]
  rw [hpow]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log X ^ 2 := by nlinarith
  have hK : 0 ≤ C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2) :=
    div_nonneg (by positivity) (mul_pos hLA (pow_pos hL 2)).le
  calc
    _ ≤ 9 * Real.log X ^ 2 * (C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2)) :=
      mul_le_mul_of_nonneg_right hJsq hK
    _ = 9 * C * H ^ 2 / Real.log X ^ A := by
      field_simp

/-- P0088 page 11 Lemma 3.4 on one dyadic block of primes, the exact statement of Prep1121DKLRoughCut.second_dyadic_block; the proof of Split1122SecondDyadicBlock.second_dyadic_block_of_cases with interior_core_d. -/
theorem second_dyadic_block_d (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
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
  obtain ⟨B1, hB1, h1⟩ := interior_core_d A hA
  refine ⟨max B1 1, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε hε' => ?_⟩
  have hB0 : 0 ≤ B := le_trans zero_le_one ((le_max_right _ _).trans hB)
  by_cases hbig : 1 / 6 ≤ ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX _ _ α q a _ _ _ _ M _
    have he : Real.exp 1 ≤ X := by
      have := Real.exp_one_lt_d9
      linarith
    exact interior_integral_le_of_large_eps A ε B X H α M _ _ 1 he hB0 hbig zero_le_one
  · push Not at hbig
    obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hbig
    refine ⟨C1, X1, hC1, hX1, ?_⟩
    intro X H hX hHl hHu α q a hcop hqP hqQ hclose M hM
    have hL : 0 < Real.log X := Real.log_pos (by linarith)
    have hRHS : 0 ≤ C1 * H ^ 2 / Real.log X ^ A :=
      div_nonneg (mul_nonneg hC1.le (sq_nonneg _)) (Real.rpow_pos_of_pos hL A).le
    by_cases htop : M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)
    · by_cases hlow : windowY X ε ^ (1 / 6 + ε / 2) < 2 * M
      · exact k1 X H hX hHl hHu α q a hcop hqP hqQ hclose M hM htop hlow
      · push Not at hlow
        have h0 : ∀ m : ℕ, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
          intro m
          apply Finset.sum_eq_zero
          intro p hp
          obtain ⟨hp1, -, hp2M⟩ := Finset.mem_filter.mp hp
          obtain ⟨-, -, hpz1, -, -⟩ := Finset.mem_filter.mp hp1
          linarith
        simp only [h0, zero_mul, Finset.sum_const_zero, norm_zero]
        simpa using hRHS
    · push Not at htop
      have h0 : ∀ m : ℕ, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
              windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
              (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
              p ∣ m)).filter
              (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
            roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
        intro m
        apply Finset.sum_eq_zero
        intro p hp
        obtain ⟨hp1, hMp, -⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, -, -, hpz0, -⟩ := Finset.mem_filter.mp hp1
        linarith
      simp only [h0, zero_mul, Finset.sum_const_zero, norm_zero]
      simpa using hRHS

end SecondSum

section Major

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.Prep1121KLMajor LeanLab.KumchevLiu2007.Burst1122B27
open scoped BigOperators Topology

/-- P0088 page 7, the display before 27, the exact statement of Burst1122B27.tail_bound; its proof with KernelSumSplit1122.kernel_sum_bound_split in place of the LEAF kernel_sum_bound. CONDITIONAL ON the LEAFs inner_window_bound and outer_square_bound of KernelSumSplit1122. -/
theorem tail_bound_d :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n : ℕ,
        ‖(∫ β in (-(1 / 2 : ℝ))..(1 / 2),
            fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) *
              (T1 X (windowY X ε) β * T2 (windowY X ε) (Real.log X ^ B) β)) -
          ∫ β in -((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q)..
              ((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q),
            fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) *
              (T1 X (windowY X ε) β * T2 (windowY X ε) (Real.log X ^ B) β)‖ ≤
          C * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-2 : ℤ) := by
  intro B hB ε hε hε'
  obtain ⟨C, X0, hC, hK⟩ := KernelSumSplit1122.kernel_sum_bound_split B hB ε hε hε'
  refine ⟨C, X0, hC, fun X hX q hq1 hqP n => ?_⟩
  rw [tail_kernel_identity, Complex.norm_real, Real.norm_eq_abs]
  exact hK X hX q hq1 hqP n

/-- P0088 page 7 display 27, the exact statement of Burst1122B27.bound27_of_leaves; its proof with tail_bound_d. -/
theorem bound27_d (_h1 : T1BoundProp) (_h2 : T2BoundProp) :
    BlockErrorBound (fun X Y H P n => termA X Y H P n - series2 n P * (singInt X Y P n : ℂ)) := by
  intro B hB ε hε hε'
  obtain ⟨X1, hA⟩ := termA_arc_sum B hB ε hε hε'
  obtain ⟨X2, hR⟩ := arc_sum_regroup B hB ε hε hε'
  obtain ⟨C, X3, hC, hT⟩ := tail_bound_d B hB ε hε hε'
  refine ⟨C, max (max X1 X2) (max X3 3), hC, ?_⟩
  intro X H hX hlo hhi n
  have hX1 : X1 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hX
  have hX2 : X2 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _)) hX
  have hX4 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _)) hX
  set Y := windowY X ε with hY
  set P := Real.log X ^ B with hP
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX4
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hPpos : 0 < P := by linarith
  set F : ℝ → ℂ := fun β => fourier (-(n : ℤ)) (β : AddCircle (1 : ℝ)) *
    (T1 X Y β * T2 Y P β) with hF
  set b : ℕ → ℝ := fun q => (Y * P ^ (-2 : ℤ) / P)⁻¹ / q with hb
  have hfull : (singInt X Y P n : ℂ) = ∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β :=
    (fourier_completion X Y P n).symm
  have hser : series2 n P = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q := rfl
  have hid : termA X Y H P n - series2 n P * (singInt X Y P n : ℂ) =
      -∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q *
        ((∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β) - ∫ β in -(b q)..(b q), F β) := by
    rw [hA X H hX1 hlo hhi n, hR X hX2 n, hfull, hser, Finset.sum_mul,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  show ‖termA X Y H P n - series2 n P * (singInt X Y P n : ℂ)‖ ≤ _
  rw [hid, norm_neg]
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊P⌋₊, ‖U1534.A2 n q *
      ((∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β) - ∫ β in -(b q)..(b q), F β)‖ ≤
        C * Real.sqrt Y * P ^ (-2 : ℤ) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hq1 : 1 ≤ q := hq.1
    have hqP : (q : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hPpos.le)
    rw [norm_mul]
    calc ‖U1534.A2 n q‖ * ‖(∫ β in (-(1 / 2 : ℝ))..(1 / 2), F β) -
          ∫ β in -(b q)..(b q), F β‖
        ≤ 1 * (C * Real.sqrt Y * P ^ (-2 : ℤ)) :=
          mul_le_mul (A2_norm_le_one n q) (hT X hX3 q hq1 hqP n) (norm_nonneg _) zero_le_one
      _ = C * Real.sqrt Y * P ^ (-2 : ℤ) := one_mul _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hfl : ((⌊P⌋₊ : ℕ) : ℝ) ≤ P := Nat.floor_le hPpos.le
  have hs : 0 ≤ C * Real.sqrt Y := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hz : P * P ^ (-2 : ℤ) ≤ P ^ (-(1 / 4 : ℝ)) := by
    have e1 : P * P ^ (-2 : ℤ) = P ^ (-1 : ℝ) := by
      rw [show (-1 : ℝ) = ((-2 : ℤ) : ℝ) + 1 by norm_num,
        Real.rpow_add hPpos, Real.rpow_intCast, Real.rpow_one, mul_comm]
    rw [e1]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
  have hzpos : 0 ≤ P ^ (-2 : ℤ) := (zpow_pos hPpos _).le
  calc ((⌊P⌋₊ : ℕ) : ℝ) * (C * Real.sqrt Y * P ^ (-2 : ℤ))
      ≤ P * (C * Real.sqrt Y * P ^ (-2 : ℤ)) := by
        gcongr
    _ = C * Real.sqrt Y * (P * P ^ (-2 : ℤ)) := by ring
    _ ≤ C * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by gcongr

end Major

open LeanLab.KumchevLiu2007 Prep1121KLMajor

/-- The rough block bulk, the exact statement of Task628.rough_block_bulk, P0088 page 15
after display 52, from first_sum_block_d and second_dyadic_block_d through the proved
assembly steps of DQThm1Char and DQThm1Integrate1122c. No proof hole of its own. -/
theorem rough_block_bulk_d : type_of% @Task628.rough_block_bulk :=
  DQThm1Char.rough_block_bulk_of_sums first_sum_block_d
    (DQThm1Integrate1122c.second_sum_block_of_dyadic_hyp second_dyadic_block_d)

/-- P0088 page 7 display 28 squared, DQMajorArcBlock.MajorArcBlockHyp, from bound27_d and
the twins of displays 20, 24 and 26 used by DQThm1Integrate1122c. CONDITIONAL ON A12Corr
and A22Corr. -/
theorem majorArcBlockHyp_d (hA12 : A12Corr) (hA22 : A22Corr) :
    DQMajorArcBlock.MajorArcBlockHyp :=
  DQMajorArcChar.major_arc_block_of_bounds
    (bound27_d T1_bound T2_bound)
    (DQThm1Integrate1122c.bound20_of_mean
      Prep1122KLGallagherCut.S2_sub_S2star_major_mean_square_of_pieces hA22)
    S2starMinorSplit1122.bound24_unconditional
    (DQThm1Integrate1122c.bound26_of_parts Prep1122S1StarM0Cut.S1_sub_S1star_on_M0_of_leaves
      Integrate1122cS2starL1.S2star_M0_L1_of_pieces hA12 T2_bound)

/-- Unit integrate1122d-wire, the Palomar headline one level deeper: P0088 Theorem 1 on the
written range of page 16, exactly Task129W.kumchev_liu_thm1_written. CONDITIONAL ON the
cited A12Corr and A22Corr. No proof hole of its own; its open LEAF pieces are those of the
twin files named in the header. -/
theorem thm1_written_integrated_d (hA12 : A12Corr) (hA22 : A22Corr) :
    Task129W.kumchev_liu_thm1_written :=
  DQMajorArcBlock.thm1_written_of_hyps (majorArcBlockHyp_d hA12 hA22) rough_block_bulk_d

/-- Bridge toward Task129.thm1_from_leaves: the exact statement of the CITED input
Task628.major_arc_block, P0088 page 7 display 28 squared, from majorArcBlockHyp_d by
DQMajorArcBlock.major_arc_block_of_hyp. CONDITIONAL ON A12Corr and A22Corr. The input
Task628.rough_block_bulk is rough_block_bulk_d above. -/
theorem major_arc_block_d (hA12 : A12Corr) (hA22 : A22Corr) :
    type_of% @Task628.major_arc_block :=
  DQMajorArcBlock.major_arc_block_of_hyp (majorArcBlockHyp_d hA12 hA22)

/-- Type check: exactly the type of thm1_written_integrated. -/
example : type_of% @thm1_written_integrated_d =
    type_of% @DQThm1Integrate1122c.thm1_written_integrated := rfl

example : type_of% @lemma34_unit_coefficient_d =
    type_of% @Split1122KLLemma34M1.lemma34_unit_coefficient := rfl
example : type_of% @block_rough_left_half_d =
    type_of% @Split1122KLFirstRoughHalves.block_rough_left_half := rfl
example : type_of% @block_rough_right_half_d =
    type_of% @Split1122KLFirstRoughHalves.block_rough_right_half := rfl
example : type_of% @first_rough_block_d =
    type_of% @Split1122KLFirstRoughHalves.first_rough_block_of_halves := rfl
example : type_of% @first_sum_block_d =
    type_of% @Split1122KLFirstRoughHalves.first_sum_block_of_halves := rfl
example : type_of% @case1_small_D_d = type_of% @Split1122SecondDyadicBlock.case1_small_D := rfl
example : type_of% @case2_middle_D_d = type_of% @Split1122SecondDyadicBlock.case2_middle_D := rfl
example : type_of% @display42_block_d =
    type_of% @Split1122SecondDyadicBlock.display42_block := rfl
example : type_of% @interior_core_d = type_of% @Split1122SecondDyadicBlock.interior_core := rfl
example : type_of% @second_dyadic_block_d =
    type_of% @Split1122SecondDyadicBlock.second_dyadic_block_of_cases := rfl
example : type_of% @tail_bound_d = type_of% @Burst1122B27.tail_bound := rfl
example : type_of% @bound27_d = type_of% @Burst1122B27.bound27_of_leaves := rfl
example : type_of% @rough_block_bulk_d = type_of% @DQThm1Integrate1122c.rough_block_bulk_twin := rfl
example : type_of% @majorArcBlockHyp_d =
    type_of% @DQThm1Integrate1122c.majorArcBlockHyp_twin := rfl

end LeanLab.KumchevLiu2007.DQThm1Integrate1122d
