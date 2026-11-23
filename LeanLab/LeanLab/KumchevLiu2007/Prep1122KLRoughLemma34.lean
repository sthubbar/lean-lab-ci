/-
BURST 2026-11-22, session S39, unit P1122-0141. Splits the leaf
Prep1121DKLRoughCut.first_rough_block, the genuinely rough case of Lemma 3.4
applied to the first sum of display 52, into two pieces. Kumchev and Liu 2007,
P0088, arXiv 0801.0130, page 11 Lemma 3.4 and page 15 after display 52.

* lemma34_unit, LEAF HARD: Lemma 3.4 of page 11 exactly as printed, in the
  case M = 1 with a_1 = 1, so that the sum runs over k alone with the weight
  Phi of k and z. Its proof on pages 11 and 12 rests on Lemmas 3.1 and 3.2,
  whose proofs the paper omits and cites to Kumchev 2006 reference 14, and on
  Lemma 3.3, cited to Kumchev reference 12 Lemma 2.7: a citation wall.
* window_edge, PROVED: the last stretch Y - 2H to Y of the window, where the
  square root window of page 2 display 5 cuts the short sum of page 7 A2.3.
  The trivial bound, at most 3H/sqrt Y terms of modulus at most one.
* first_rough_block_of_pieces, no sorry of its own: the exact statement of
  first_rough_block. The window Y/4 to Y is cut at Y/2 and Y - 2H; the two
  pieces up to Y - 2H are Lemma 3.4 with x = Y/4 and x = Y/2, y = H.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLRoughCut

namespace LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4, the case M = 1 and a_1 = 1, with L = log x,
display 41 for alpha, a and q, and Phi of k and z from page 4 display 10. For
t in x to 2x and y at most x every k with k^2 at most t + y is at most the
square root of 3x, so the range cap on k leaves the sum of the paper unchanged.
Class HARD. CITED-LEFT: the proof on pages 11 and 12 uses Lemmas 3.1 and 3.2,
proofs omitted in the paper, and Lemma 3.3, Kumchev reference 12 Lemma 2.7. -/
theorem lemma34_unit (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        (∫ t in x..2 * x,
          ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
            roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  sorry

/-- PROVED. The window edge of P0088 page 15, the step from A2.3 of page 7 to the
square root window I2 of page 2 display 5 that Gallagher's lemma on page 8 uses.
For t from Y - 2H to Y every k in the sum has Y - 2H below k^2 below Y, so at
most 3H/sqrt Y terms of modulus at most one remain. Class EASY. -/
theorem window_edge (Y H z α : ℝ) (hY : 0 < Y) (hH : Real.sqrt Y ≤ H) (hHY : 4 * H ≤ Y) :
    (∫ t in Y - 2 * H..Y,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      18 * H ^ 3 / Y := by
  have hs0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hH0 : 0 < H := hs0.trans_le hH
  have hY2H : 0 ≤ Y - 2 * H := by linarith
  have hss : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY.le
  have hrr : Real.sqrt (Y - 2 * H) ^ 2 = Y - 2 * H := Real.sq_sqrt hY2H
  have hr0 : 0 ≤ Real.sqrt (Y - 2 * H) := Real.sqrt_nonneg _
  have hrs : Real.sqrt (Y - 2 * H) ≤ Real.sqrt Y := Real.sqrt_le_sqrt (by linarith)
  have hcount : ∀ t : ℝ, Y - 2 * H ≤ t →
      (((squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)).card : ℝ) ≤
        3 * H / Real.sqrt Y := by
    intro t ht
    have hsub : (squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) ⊆
        Finset.Ico ⌈Real.sqrt (Y - 2 * H)⌉₊ ⌈Real.sqrt Y⌉₊ := by
      intro k hk
      simp only [squareWindow, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨⟨_, _, hks⟩, hkt, _⟩ := hk
      rw [Finset.mem_Ico]
      refine ⟨Nat.ceil_le.mpr ?_, Nat.lt_ceil.mpr hks⟩
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [← Real.sqrt_sq hk0]
      exact Real.sqrt_le_sqrt (by linarith)
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    generalize ((squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)).card = N at hc ⊢
    have hmain : (N : ℝ) ≤ Real.sqrt Y + 1 - Real.sqrt (Y - 2 * H) := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · rw [h0]
        push_cast
        linarith
      · have h1 : N + ⌈Real.sqrt (Y - 2 * H)⌉₊ ≤ ⌈Real.sqrt Y⌉₊ := by omega
        have h2 : ((N + ⌈Real.sqrt (Y - 2 * H)⌉₊ : ℕ) : ℝ) ≤ (⌈Real.sqrt Y⌉₊ : ℝ) := by
          exact_mod_cast h1
        push_cast at h2
        have h3 : (⌈Real.sqrt Y⌉₊ : ℝ) < Real.sqrt Y + 1 := Nat.ceil_lt_add_one hs0.le
        have h4 : Real.sqrt (Y - 2 * H) ≤ (⌈Real.sqrt (Y - 2 * H)⌉₊ : ℝ) := Nat.le_ceil _
        linarith
    have hsr : (Real.sqrt Y - Real.sqrt (Y - 2 * H)) * Real.sqrt Y ≤ 2 * H := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hr0]
    have h5 : Real.sqrt Y - Real.sqrt (Y - 2 * H) ≤ 2 * H / Real.sqrt Y := by
      rw [le_div_iff₀ hs0]
      linarith
    have h6 : 1 ≤ H / Real.sqrt Y := by
      rw [le_div_iff₀ hs0]
      linarith
    have h7 : 3 * H / Real.sqrt Y = 2 * H / Real.sqrt Y + H / Real.sqrt Y := by ring
    linarith
  have hpt : ∀ t ∈ Set.Icc (Y - 2 * H) Y,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 ≤
        9 * H ^ 2 / Y := by
    intro t ht
    have hn : ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ≤
        (((squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun m _ => ?_).trans (by simp)
      rw [norm_mul]
      have hf : ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 := by
        simp only [fourier_apply, Circle.norm_coe]
      rw [hf, mul_one]
      exact roughWeight_norm_le_one z m
    have hb := (norm_nonneg _).trans hn
    have h3 := (hn.trans (hcount t ht.1))
    have h9 : (3 * H / Real.sqrt Y) ^ 2 = 9 * H ^ 2 / Y := by
      rw [div_pow, hss]
      ring
    rw [← h9]
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hmono := intervalIntegral.integral_mono_on (by linarith : Y - 2 * H ≤ Y)
    (short_sum_sq_intervalIntegrable (squareWindow Y)
      (fun m : ℕ => roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _)
    intervalIntegrable_const hpt
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- P0088 page 2 display 5: inside the window, for Y/4 at most t and t + H
below Y, the square root window adds no condition to the short sum, and nor
does the cap k at most the square root of 3x once t + H is at most 3x. -/
theorem window_filter_eq {Y H x t : ℝ} (_hY : 0 ≤ Y) (ht : Y / 4 ≤ t) (htH : t + H < Y)
    (h3 : t + H ≤ 3 * x) :
    (squareWindow Y).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) =
      (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) := by
  ext k
  simp only [squareWindow, Finset.mem_filter, Finset.mem_range]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsk : Real.sqrt ((k : ℝ) ^ 2) = k := Real.sqrt_sq hk0
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), h1, h2⟩
    rw [← hsk]
    exact Real.sqrt_le_sqrt (h2.trans h3)
  · rintro ⟨_, h1, h2⟩
    have hlt : (k : ℝ) < Real.sqrt Y := by
      rw [← hsk]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (lt_of_le_of_lt h2 htH)
    refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hlt.le), ?_, hlt⟩, h1, h2⟩
    have h4 : Real.sqrt Y / 2 = Real.sqrt (Y / 4) := by
      rw [Real.sqrt_div' Y (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4, ← hsk]
    exact Real.sqrt_le_sqrt (ht.trans h1.le)

/-- Parameter step of P0088 page 15: with Y = X^(7/12 + eps/2) and X at least
4^12, log of Y/4 is at least half of log X. -/
theorem log_quarter_window {X ε : ℝ} (hX : (4 : ℝ) ^ 12 ≤ X) (hε : 0 ≤ ε) :
    Real.log X / 2 ≤ Real.log (windowY X ε / 4) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos hX0 _
  rw [Real.log_div hY0.ne' (by norm_num), windowY, Real.log_rpow hX0]
  have h12 : 12 * Real.log 4 ≤ Real.log X := by
    have := Real.log_le_log (by norm_num) hX
    rwa [Real.log_pow] at this
  have hL : 0 ≤ Real.log X := le_trans (by positivity) h12
  nlinarith

/-- Exponent step of P0088 page 15: z1 Y^(1/2) = X^((7/12 + eps/2)(2/3 + eps/2))
sits below X^(7/18 + eps) with room X^(5 eps/18) to spare, for eps at most 7/18. -/
theorem exponent_margin {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 7 / 18) :
    (7 / 12 + ε / 2) * (2 / 3 + ε / 2) + 5 * ε / 18 ≤ 7 / 18 + ε := by
  nlinarith [mul_le_mul_of_nonneg_left hε' hε]

set_option maxHeartbeats 800000 in
/-- The exact statement of Prep1121DKLRoughCut.first_rough_block, from
lemma34_unit with x = Y/4 and x = Y/2, y = H, and window_edge. No sorry of its own. -/
theorem first_rough_block_of_pieces (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B1, hB1, hlem⟩ := lemma34_unit A hA
  refine ⟨max B1 (max 1 A), lt_max_of_lt_left hB1, ?_⟩
  intro B hB ε hε hε'
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hB1' : 1 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hBA : A ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  obtain ⟨C, x0, hC, hx0, hk⟩ := hlem B hBB1
  obtain ⟨T1, ht1⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (4 * B) (by norm_num : (0 : ℝ) < 7 / 72)).bound
      (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T2, ht2⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (6 * B) (by positivity : (0 : ℝ) < 5 * ε / 18)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨2 * C * 2 ^ A + 18, max ((4 : ℝ) ^ 12) (max ((4 * x0) ^ (12 / 7 : ℝ)) (max T1 T2)),
    by positivity, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose z hz2 hz
  -- the size of X
  have hX12 : (4 : ℝ) ^ 12 ≤ X := (le_max_left _ _).trans hX
  have hXx0 : (4 * x0) ^ (12 / 7 : ℝ) ≤ X :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXT1 : T1 ≤ X :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hXT2 : T2 ≤ X :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX12
  have hX1 : 1 ≤ X := le_trans (by norm_num) hX12
  have hL16 : 12 * Real.log 4 ≤ Real.log X := by
    have := Real.log_le_log (by norm_num) hX12
    rwa [Real.log_pow] at this
  have hlog4 : 1 < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hL2 : 2 ≤ Real.log X := by linarith
  have hL1 : 1 ≤ Real.log X := by linarith
  have hL : 0 < Real.log X := by linarith
  set L := Real.log X with hLdef
  set Y := windowY X ε with hYdef
  have hlogq : L / 2 ≤ Real.log (Y / 4) := log_quarter_window hX12 hε.le
  clear_value L Y
  have hY0 : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hX0 _
  have hP : 0 < L ^ B := Real.rpow_pos_of_pos hL _
  have hP1 : L ≤ L ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 hB1'
  have hP4 : 0 < (L ^ B) ^ 4 := by positivity
  have hlow' : X ^ (7 / 18 + ε) / (L ^ B) ^ 4 ≤ H := by
    simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using hlow
  have hhigh' : H ≤ Y / (L ^ B) ^ 4 := by
    simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using hhigh
  have hP4eq : (L ^ B) ^ 4 = L ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    ring
  -- square root of Y is at most H
  have hR : Real.sqrt Y = X ^ (7 / 24 + ε / 4) := by
    rw [Real.sqrt_eq_rpow, hYdef, windowY, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hR0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hAbs1 : L ^ (4 * B) ≤ X ^ (7 / 72 : ℝ) := by
    have h := ht1 X hXT1
    rw [← hLdef] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (4 * B)),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 72 : ℝ)), one_mul] at h
    exact h
  have hroot : Real.sqrt Y ≤ H := by
    refine le_trans ((le_div_iff₀ hP4).mpr ?_) hlow'
    calc
      Real.sqrt Y * (L ^ B) ^ 4 ≤ Real.sqrt Y * X ^ (7 / 72 : ℝ) := by
        rw [hP4eq]
        exact mul_le_mul_of_nonneg_left hAbs1 hR0.le
      _ = X ^ (7 / 24 + ε / 4 + 7 / 72) := by rw [hR, ← Real.rpow_add hX0]
      _ ≤ X ^ (7 / 18 + ε) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hH0 : 0 < H := hR0.trans_le hroot
  -- H is at most Y/4
  have hP16 : 4 ≤ (L ^ B) ^ 4 := by
    have h2 : 2 ≤ L ^ B := hL2.trans hP1
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 4]
  have hHY : 4 * H ≤ Y := by
    have := (le_div_iff₀ hP4).mp hhigh'
    nlinarith
  -- logs of the two half windows
  have hYX : Y ≤ X := by
    simpa [hYdef, windowY, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : 7 / 12 + ε / 2 ≤ (1 : ℝ))
  -- x0 is at most Y/4
  have hx0Y : x0 ≤ Y / 4 := by
    have h1 : X ^ (7 / 12 : ℝ) ≤ Y := by
      rw [hYdef]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h2 : 4 * x0 ≤ X ^ (7 / 12 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hXx0 (by norm_num : (0 : ℝ) ≤ 7 / 12)
      rwa [← Real.rpow_mul (by positivity), show (12 / 7 : ℝ) * (7 / 12) = 1 by norm_num,
        Real.rpow_one] at this
    linarith
  have hY4 : 2 ≤ Y / 4 := hx0.trans hx0Y
  -- the hypotheses of Lemma 3.4 for x = Y/4 and x = Y/2
  have hqpos : (0 : ℝ) < q := hP.trans hqP
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have happ : |α - (v : ℝ) / q| < 1 / (q : ℝ) ^ 2 :=
    Eq33RouteD.display41_of_minor hq0 hqQ hclose
  have hAbs2 : L ^ (6 * B) ≤ X ^ (5 * ε / 18) := by
    have h := ht2 X hXT2
    rw [← hLdef] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (6 * B)),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (5 * ε / 18)), one_mul] at h
    exact h
  have hzY : Y ^ (1 / 6 + ε / 2) * Real.sqrt Y * L ^ (2 * B) ≤ H := by
    refine le_trans ((le_div_iff₀ hP4).mpr ?_) hlow'
    have hexp : Y ^ (1 / 6 + ε / 2) * Real.sqrt Y = X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hY0, hYdef, windowY, ← Real.rpow_mul hX0.le]
      congr 1
      ring
    calc
      Y ^ (1 / 6 + ε / 2) * Real.sqrt Y * L ^ (2 * B) * (L ^ B) ^ 4
          = X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 2)) * L ^ (6 * B) := by
        rw [hexp, hP4eq, mul_assoc, ← Real.rpow_add hL]
        congr 2
        ring
      _ ≤ X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 2)) * X ^ (5 * ε / 18) :=
        mul_le_mul_of_nonneg_left hAbs2 (by positivity)
      _ = X ^ ((7 / 12 + ε / 2) * (2 / 3 + ε / 2) + 5 * ε / 18) := by
        rw [← Real.rpow_add hX0]
      _ ≤ X ^ (7 / 18 + ε) := Real.rpow_le_rpow_of_exponent_le hX1 (exponent_margin hε.le hε')
  have hyp : ∀ x : ℝ, Y / 4 ≤ x → x ≤ Y / 2 →
      (∫ t in x..2 * x,
          ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + H),
            roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * 2 ^ A * (H ^ 2 / L ^ A) := by
    intro x hx1 hx2
    have hxpos : 0 < x := by linarith
    have hxX : x ≤ X := by linarith
    have hlx1 : 1 ≤ Real.log x := by
      have := hlogq.trans (Real.log_le_log (by linarith) hx1)
      linarith
    have hlx0 : 0 < Real.log x := lt_of_lt_of_le one_pos hlx1
    have hlxL : Real.log x ≤ L := by
      rw [hLdef]
      exact Real.log_le_log hxpos hxX
    have hlxh : L / 2 ≤ Real.log x := hlogq.trans (Real.log_le_log (by linarith) hx1)
    have hPx : Real.log x ^ B ≤ L ^ B :=
      Real.rpow_le_rpow hlx0.le hlxL (by linarith)
    have hPx0 : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hlx0 _
    have hsx : Real.sqrt x ≤ Real.sqrt Y := Real.sqrt_le_sqrt (by linarith)
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hz' : z ≤ H / Real.sqrt x / Real.log x ^ (2 * B) := by
      have h2B : Real.log x ^ (2 * B) ≤ L ^ (2 * B) :=
        Real.rpow_le_rpow hlx0.le hlxL (by linarith)
      have h2B0 : 0 < Real.log x ^ (2 * B) := Real.rpow_pos_of_pos hlx0 _
      rw [le_div_iff₀ h2B0, le_div_iff₀ hsx0]
      calc
        z * Real.log x ^ (2 * B) * Real.sqrt x ≤ Y ^ (1 / 6 + ε / 2) * L ^ (2 * B) * Real.sqrt Y := by
          gcongr
        _ = Y ^ (1 / 6 + ε / 2) * Real.sqrt Y * L ^ (2 * B) := by ring
        _ ≤ H := hzY
    have hk' := hk x H (hx0Y.trans hx1) (hsx.trans hroot) (by linarith) α q v hcop
      (hPx.trans hqP.le)
      (hqQ.trans (div_le_div_of_nonneg_left hH0.le hPx0 hPx)) happ z hz2.le hz'
    refine hk'.trans ?_
    have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL _
    have hxA : L ^ A / 2 ^ A ≤ Real.log x ^ A := by
      rw [← Real.div_rpow hL.le (by norm_num)]
      exact Real.rpow_le_rpow (by positivity) hlxh hA.le
    have hxA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlx0 _
    have h2A : 0 < (2 : ℝ) ^ A := by positivity
    rw [div_le_iff₀ hxA0]
    have hkey : C * 2 ^ A * (H ^ 2 / L ^ A) * Real.log x ^ A ≥
        C * 2 ^ A * (H ^ 2 / L ^ A) * (L ^ A / 2 ^ A) :=
      mul_le_mul_of_nonneg_left hxA (by positivity)
    have hval : C * 2 ^ A * (H ^ 2 / L ^ A) * (L ^ A / 2 ^ A) = C * H ^ 2 := by
      field_simp
    linarith
  -- the integrand
  set F : ℝ → ℝ := fun t => ‖∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 with hF
  have hFi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b =>
    short_sum_sq_intervalIntegrable (squareWindow Y)
      (fun m : ℕ => roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H a b
  set G : ℝ → ℝ → ℝ := fun x t => ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
      (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + H),
        roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 with hG
  have hGi : ∀ x a b : ℝ, IntervalIntegrable (G x) volume a b := fun x a b =>
    short_sum_sq_intervalIntegrable _
      (fun k : ℕ => roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H a b
  -- split the window
  have hsplit : (∫ t in Y / 4..Y, F t) =
      (∫ t in Y / 4..Y / 2, F t) + (∫ t in Y / 2..Y - 2 * H, F t) + ∫ t in Y - 2 * H..Y, F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hFi _ _) (hFi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hFi _ _) (hFi _ _)]
  have hleft : (∫ t in Y / 4..Y / 2, F t) = ∫ t in Y / 4..2 * (Y / 4), G (Y / 4) t := by
    rw [show 2 * (Y / 4) = Y / 2 by ring]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [hF, hG]
    rw [window_filter_eq (x := Y / 4) hY0.le ht.1 (by linarith [ht.2]) (by linarith [ht.2])]
  have hmid : (∫ t in Y / 2..Y - 2 * H, F t) = ∫ t in Y / 2..Y - 2 * H, G (Y / 2) t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [hF, hG]
    rw [window_filter_eq (x := Y / 2) hY0.le (by linarith [ht.1]) (by linarith [ht.2]) (by linarith [ht.2])]
  have hmid2 : (∫ t in Y / 2..Y - 2 * H, G (Y / 2) t) ≤ ∫ t in Y / 2..2 * (Y / 2), G (Y / 2) t :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun t => by simp only [hG]; positivity) (hGi _ _ _)
  have hedge := window_edge Y H z α hY0 hroot hHY
  have hedge2 : 18 * H ^ 3 / Y ≤ 18 * (H ^ 2 / L ^ A) := by
    have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL _
    have hAB : L ^ A ≤ (L ^ B) ^ 4 := by
      rw [hP4eq]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hHLY : H * L ^ A ≤ Y :=
      (mul_le_mul_of_nonneg_left hAB hH0.le).trans ((le_div_iff₀ hP4).mp hhigh')
    rw [div_le_iff₀ hY0]
    have : 18 * (H ^ 2 / L ^ A) * Y ≥ 18 * (H ^ 2 / L ^ A) * (H * L ^ A) :=
      mul_le_mul_of_nonneg_left hHLY (by positivity)
    have hval : 18 * (H ^ 2 / L ^ A) * (H * L ^ A) = 18 * H ^ 3 := by
      field_simp
    rw [← hval]
    exact this
  have e1 := hyp (Y / 4) le_rfl (by linarith)
  have e2 := hyp (Y / 2) (by linarith) le_rfl
  have hfin : C * H ^ 2 / L ^ A = C * (H ^ 2 / L ^ A) := by ring
  show (∫ t in Y / 4..Y, F t) ≤ (2 * C * 2 ^ A + 18) * H ^ 2 / L ^ A
  rw [hsplit, hleft, hmid]
  have hgoal : (2 * C * 2 ^ A + 18) * H ^ 2 / L ^ A =
      C * 2 ^ A * (H ^ 2 / L ^ A) + C * 2 ^ A * (H ^ 2 / L ^ A) + 18 * (H ^ 2 / L ^ A) := by
    ring
  rw [hgoal]
  exact add_le_add (add_le_add e1 (hmid2.trans e2)) (hedge.trans hedge2)

example : type_of% @Prep1121DKLRoughCut.first_rough_block := first_rough_block_of_pieces

end LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34

#print axioms LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34.window_edge
#print axioms LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34.window_filter_eq
#print axioms LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34.log_quarter_window
#print axioms LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34.exponent_margin
#print axioms LeanLab.KumchevLiu2007.Prep1122KLRoughLemma34.first_rough_block_of_pieces
