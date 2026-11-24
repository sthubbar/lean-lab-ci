/-
Schoenfeld 1976, Math. Comp. 30, p. 340: "A direct calculation shows that (6.18) holds for
2,657 ≤ x < 2,659". The one numerical input of SchoenfeldFiniteS70.lean is the enclosure
`399.59 ≤ li 2657 ≤ 399.61`, true value `li 2657 = 399.596817`.

Here that enclosure is split into much smaller numerical LEAFs:
* `liPV 2 ≥ 1.045`, true `1.0451638`; the upper bound `liPV 2 ≤ 1.046` is already PROVED
  in LiTwo.lean.
* eleven dyadic pieces `∫_a^b dt / log t` on `[2, 4], [4, 8], ..., [1024, 2048], [2048, 2657]`,
  each enclosed to about `1e-4`, values from mpmath at 30 digits.
The assembly `liPV_2657_encl_S76`, with exactly the statement of the LEAF
`SchoenfeldFiniteS70.liPV_2657_encl`, is PROVED from these through `liPV_eq_add` and
additivity of the interval integral.

AI wrote this Lean code, Claude, ROUTE BURST S76 burst-20261122, step direct_2657_li.
Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.SchoenfeldFiniteS70
import LeanLab.BS2022GRH.LiTwo

namespace LeanLab.BS2022GRH.SchoenfeldLiS76
open Real MeasureTheory intervalIntegral Set

noncomputable section

/-- `1 / log t` is interval integrable on `[u, v]` when `2 ≤ u, v`. -/
lemma ii_inv_log {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t => 1 / log t) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => by
      rw [Set.mem_uIcc] at ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
  · intro t ht
    rw [Set.mem_uIcc] at ht
    have : (1 : ℝ) < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact (Real.log_pos this).ne'

/-- Additivity of `∫ dt / log t` over adjacent intervals in `[2, ∞)`. -/
lemma split {a b c : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    (∫ t in a..c, 1 / log t) = (∫ t in a..b, 1 / log t) + ∫ t in b..c, 1 / log t :=
  (intervalIntegral.integral_add_adjacent_intervals (ii_inv_log ha hb) (ii_inv_log hb hc)).symm

/-- LEAF: Schoenfeld 1976 p. 340, the constant `li 2` inside `li 2657 ≅ 399.5968`, lower
bound. EASY. True value `li 2 = 1.0451637801`; the matching upper bound `1.046` is
`LiTwo.liPV_two_le_1046`. -/
theorem liPV_two_ge : 1.045 ≤ liPV 2 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_2^4 dt / log t`. EASY.
True value `1.9224213149`. -/
theorem piece_2_4 : 1.9223 ≤ (∫ t in (2 : ℝ)..4, 1 / log t) ∧
    (∫ t in (2 : ℝ)..4, 1 / log t) ≤ 1.9225 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_4^8 dt / log t`. EASY.
True value `2.2861332045`. -/
theorem piece_4_8 : 2.2860 ≤ (∫ t in (4 : ℝ)..8, 1 / log t) ∧
    (∫ t in (4 : ℝ)..8, 1 / log t) ≤ 2.2862 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_8^16 dt / log t`. EASY.
True value `3.2659981642`. -/
theorem piece_8_16 : 3.2659 ≤ (∫ t in (8 : ℝ)..16, 1 / log t) ∧
    (∫ t in (8 : ℝ)..16, 1 / log t) ≤ 3.2661 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_16^32 dt / log t`. EASY.
True value `5.0853757134`. -/
theorem piece_16_32 : 5.0853 ≤ (∫ t in (16 : ℝ)..32, 1 / log t) ∧
    (∫ t in (16 : ℝ)..32, 1 / log t) ≤ 5.0855 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_32^64 dt / log t`. EASY.
True value `8.3295761510`. -/
theorem piece_32_64 : 8.3295 ≤ (∫ t in (32 : ℝ)..64, 1 / log t) ∧
    (∫ t in (32 : ℝ)..64, 1 / log t) ≤ 8.3297 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_64^128 dt / log t`. EASY.
True value `14.107879989`. -/
theorem piece_64_128 : 14.1078 ≤ (∫ t in (64 : ℝ)..128, 1 / log t) ∧
    (∫ t in (64 : ℝ)..128, 1 / log t) ≤ 14.1080 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_128^256 dt / log t`. EASY.
True value `24.470517021`. -/
theorem piece_128_256 : 24.4704 ≤ (∫ t in (128 : ℝ)..256, 1 / log t) ∧
    (∫ t in (128 : ℝ)..256, 1 / log t) ≤ 24.4706 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_256^512 dt / log t`. EASY.
True value `43.208051831`. -/
theorem piece_256_512 : 43.2080 ≤ (∫ t in (256 : ℝ)..512, 1 / log t) ∧
    (∫ t in (256 : ℝ)..512, 1 / log t) ≤ 43.2082 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_512^1024 dt / log t`. EASY.
True value `77.356922513`. -/
theorem piece_512_1024 : 77.3568 ≤ (∫ t in (512 : ℝ)..1024, 1 / log t) ∧
    (∫ t in (512 : ℝ)..1024, 1 / log t) ≤ 77.3570 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_1024^2048 dt / log t`. EASY.
True value `140.03637599`. -/
theorem piece_1024_2048 : 140.0363 ≤ (∫ t in (1024 : ℝ)..2048, 1 / log t) ∧
    (∫ t in (1024 : ℝ)..2048, 1 / log t) ≤ 140.0365 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, piece of `li 2657`: `∫_2048^2657 dt / log t`. EASY.
True value `78.482401275`. -/
theorem piece_2048_2657 : 78.4823 ≤ (∫ t in (2048 : ℝ)..2657, 1 / log t) ∧
    (∫ t in (2048 : ℝ)..2657, 1 / log t) ≤ 78.4825 := by
  sorry

/-- Schoenfeld 1976 p. 340, `li 2657 ≅ 399.5968`, the exact statement of the LEAF
`SchoenfeldFiniteS70.liPV_2657_encl`. PROVED from the twelve LEAFs above. -/
theorem liPV_2657_encl_S76 : 399.59 ≤ liPV 2657 ∧ liPV 2657 ≤ 399.61 := by
  rw [liPV_eq_add (by norm_num : (2 : ℝ) ≤ 2657)]
  rw [split (b := 4) (by norm_num) (by norm_num) (by norm_num),
    split (a := 4) (b := 8) (by norm_num) (by norm_num) (by norm_num),
    split (a := 8) (b := 16) (by norm_num) (by norm_num) (by norm_num),
    split (a := 16) (b := 32) (by norm_num) (by norm_num) (by norm_num),
    split (a := 32) (b := 64) (by norm_num) (by norm_num) (by norm_num),
    split (a := 64) (b := 128) (by norm_num) (by norm_num) (by norm_num),
    split (a := 128) (b := 256) (by norm_num) (by norm_num) (by norm_num),
    split (a := 256) (b := 512) (by norm_num) (by norm_num) (by norm_num),
    split (a := 512) (b := 1024) (by norm_num) (by norm_num) (by norm_num),
    split (a := 1024) (b := 2048) (by norm_num) (by norm_num) (by norm_num)]
  have h0 := liPV_two_ge
  have h0' := LiTwo.liPV_two_le_1046
  obtain ⟨a1, b1⟩ := piece_2_4
  obtain ⟨a2, b2⟩ := piece_4_8
  obtain ⟨a3, b3⟩ := piece_8_16
  obtain ⟨a4, b4⟩ := piece_16_32
  obtain ⟨a5, b5⟩ := piece_32_64
  obtain ⟨a6, b6⟩ := piece_64_128
  obtain ⟨a7, b7⟩ := piece_128_256
  obtain ⟨a8, b8⟩ := piece_256_512
  obtain ⟨a9, b9⟩ := piece_512_1024
  obtain ⟨a10, b10⟩ := piece_1024_2048
  obtain ⟨a11, b11⟩ := piece_2048_2657
  constructor <;> linarith

end

end LeanLab.BS2022GRH.SchoenfeldLiS76

#print axioms LeanLab.BS2022GRH.SchoenfeldLiS76.split
#print axioms LeanLab.BS2022GRH.SchoenfeldLiS76.liPV_2657_encl_S76
