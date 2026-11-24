/-
burst-20261122 S111 sixth-root-twin-p2. Kumchev and Liu 2007, P0088, arXiv 0801.0130,
page 11 Lemma 3.4 applied on page 15 to the first sum of display 52.

Reduces the four leaves of SPLIT_leaf_large_cutoff_left_half_twin.lean,
leaf_lower_quarter_small_cutoff_real, leaf_upper_quarter_small_cutoff_real,
leaf_lower_quarter_large_cutoff_real and leaf_upper_quarter_large_cutoff_real,
and also Eq33RouteD.leaf_large_cutoff_left_half of SPLIT_lemma34_first_sum.lean,
to one finer LEAF, leaf_left_half_middle_H, by splitting on the size of H
against the window Y = windowY X ε:

* H at most Y P^(-4), P = (log X)^B: the left half estimate is
  Split1122KLLemma34M1.block_rough_left_half_of_lemma34, Lemma 3.4 with x = Y/4,
  for every cut-off 2 < z <= Y^(1/6 + ε/2), so both cut-off regimes at once.
* H at least Y (log X)^(A/2): the trivial bound, PROVED here: the short sum has at
  most sqrt Y + 1 terms of modulus at most one, so the integral over [Y/4, Y/2]
  is at most Y^2 <= H^2 (log X)^(-A).
* Y P^(-4) < H < Y (log X)^(A/2): the LEAF leaf_left_half_middle_H.
* ε > 7/18: the H range X^(7/18+ε) <= H <= X^(1-ε) is empty.

Each quarter integral is at most the half integral, the integrand being a square.
Every reduced statement is checked by type_of% against the original.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_leaf_large_cutoff_left_half_twin
import LeanLab.KumchevLiu2007.Split1122KLLemma34M1
import LeanLab.KumchevLiu2007.InteriorHalvesAux

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SixthQuartersByH1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15 to the first sum of display 52,
left half [Y/4, Y/2] of the window, in the middle range of H only:
Y P^(-4) < H < Y (log X)^(A/2), with P = (log X)^B and Y = windowY X ε.
Below this range Lemma 3.4 with x = Y/4, y = H applies, and above it the trivial
bound suffices; both are proved in this file. Here y = H exceeds x = Y/4 up to a
power of log X, outside the y <= x hypothesis of Lemma 3.4, see the QUESTION in the
notes of S111 sixth-root-twin-p2. Class HARD. -/
theorem leaf_left_half_middle_H (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) < H →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- PROVED. The trivial bound on the left half for H at least Y (log X)^(A/2):
at most sqrt Y + 1 terms, each of modulus at most one by page 4 display 10. -/
theorem left_half_trivial_large_H (A ε X H z α : ℝ) (hX : 1 < X) (hε : 0 ≤ ε)
    (hH : windowY X ε * Real.log X ^ (A / 2) ≤ H) :
    (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      H ^ 2 / Real.log X ^ A := by
  have hY : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX.le (by linarith)
  have hL : 0 < Real.log X := Real.log_pos hX
  have hcard : ((squareWindow (windowY X ε)).card : ℝ) ≤ Real.sqrt (windowY X ε) + 1 := by
    have h : (squareWindow (windowY X ε)).card ≤ ⌊Real.sqrt (windowY X ε)⌋₊ + 1 := by
      unfold squareWindow
      exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : ((⌊Real.sqrt (windowY X ε)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (windowY X ε) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : ((squareWindow (windowY X ε)).card : ℝ) ≤
        ((⌊Real.sqrt (windowY X ε)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hs1 : 1 ≤ Real.sqrt (windowY X ε) := Real.one_le_sqrt.mpr hY
  have hss : Real.sqrt (windowY X ε) ^ 2 = windowY X ε := Real.sq_sqrt (by linarith)
  have h1 : (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      (windowY X ε / 2 - windowY X ε / 4) * (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2 :=
    short_sum_mean_sq_trivial (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) 1
      (fun m _ => Split1122KLLemma34M1.summand_norm_le_one z α m) H _ _ (by linarith)
  have hc0 : (0 : ℝ) ≤ ((squareWindow (windowY X ε)).card : ℝ) := Nat.cast_nonneg _
  have hsq : (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2 ≤ 4 * windowY X ε := by
    have hle : ((squareWindow (windowY X ε)).card : ℝ) * 1 ≤ 2 * Real.sqrt (windowY X ε) := by
      linarith
    have := pow_le_pow_left₀ (by positivity) hle 2
    calc (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2
        ≤ (2 * Real.sqrt (windowY X ε)) ^ 2 := this
      _ = 4 * windowY X ε := by rw [mul_pow, hss]; norm_num
  have h2 : (windowY X ε / 2 - windowY X ε / 4) *
      (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2 ≤ windowY X ε ^ 2 := by
    calc (windowY X ε / 2 - windowY X ε / 4) *
        (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2
        ≤ (windowY X ε / 4) * (4 * windowY X ε) :=
          mul_le_mul (by linarith) hsq (sq_nonneg _) (by linarith)
      _ = windowY X ε ^ 2 := by ring
  have hpow : (Real.log X ^ (A / 2)) ^ 2 = Real.log X ^ A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    ring
  have h3 : windowY X ε ^ 2 ≤ H ^ 2 / Real.log X ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hL A)]
    calc windowY X ε ^ 2 * Real.log X ^ A
        = (windowY X ε * Real.log X ^ (A / 2)) ^ 2 := by rw [mul_pow, hpow]
      _ ≤ H ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (by linarith) (Real.rpow_pos_of_pos hL _).le) hH 2
  linarith

/-- PROVED. A sub interval of [Y/4, Y/2] carries at most the mean square of the
whole half, the integrand being a square. -/
theorem sub_le_half (Y H z α a b : ℝ) (h1 : Y / 4 ≤ a) (hab : a ≤ b) (h2 : b ≤ Y / 2) :
    (∫ t in a..b,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
    (∫ t in (Y / 4)..(Y / 2),
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) :=
  intervalIntegral.integral_mono_interval h1 hab h2
    (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    (short_sum_sq_intervalIntegrable (squareWindow Y)
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _)

/-- PROVED from leaf_left_half_middle_H, Split1122KLLemma34M1.block_rough_left_half_of_lemma34
and the trivial bound. The exact statement of Eq33RouteD.leaf_large_cutoff_left_half,
P0088 page 11 Lemma 3.4 on page 15, left half of the window. -/
theorem left_half_of_middle (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, hlem⟩ := Split1122KLLemma34M1.block_rough_left_half_of_lemma34 A hA
  obtain ⟨B2, hB2, hmid⟩ := leaf_left_half_middle_H A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hBB2 : B2 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := hB1.trans_le hBB1
  by_cases hε' : ε ≤ 7 / 18
  · obtain ⟨C1, X1, hC1, hX1, k1⟩ := hlem B hBB1 ε hε hε'
    obtain ⟨C2, X2, hC2, hX2, k2⟩ := hmid B hBB2 ε hε
    refine ⟨C1 + C2 + 1, max (max X1 X2) 3, by linarith,
      hX1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
    intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzY
    have hXa : X1 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
    have hXb : X2 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
    have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
    have hX1' : 1 < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos hX1'
    have hL1 : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
    have hq0 : 0 ≤ H ^ 2 / Real.log X ^ A := div_nonneg (sq_nonneg _) hLA.le
    have hkey : ∀ D : ℝ, D * H ^ 2 / Real.log X ^ A = D * (H ^ 2 / Real.log X ^ A) :=
      fun D => by ring
    rcases le_or_gt H (windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) with hlo | hlo
    · have hPB : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hBpos.le
      have hP4 : (Real.log X ^ B) ^ (-4 : ℤ) ≤ 1 := by
        rw [zpow_neg, zpow_ofNat]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ hPB)
      have hP4' : 0 ≤ (Real.log X ^ B) ^ (-4 : ℤ) := by positivity
      have hXp : 0 ≤ X ^ (7 / 18 + ε) := Real.rpow_nonneg (by linarith) _
      have hHlow : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H :=
        (mul_le_of_le_one_right hXp hP4).trans hH
      have e := k1 X H hXa hHlow hlo α q a hcop hqP hqQ hclose z hz hzY
      rw [hkey] at e
      rw [hkey]
      have : C1 * (H ^ 2 / Real.log X ^ A) ≤ (C1 + C2 + 1) * (H ^ 2 / Real.log X ^ A) :=
        mul_le_mul_of_nonneg_right (by linarith) hq0
      linarith
    · rcases lt_or_ge H (windowY X ε * Real.log X ^ (A / 2)) with hhi | hhi
      · have e := k2 X H hXb hH hHU hlo hhi α q a hcop hqP hqQ hclose z hz hzY
        rw [hkey] at e
        rw [hkey]
        have : C2 * (H ^ 2 / Real.log X ^ A) ≤ (C1 + C2 + 1) * (H ^ 2 / Real.log X ^ A) :=
          mul_le_mul_of_nonneg_right (by linarith) hq0
        linarith
      · have e := left_half_trivial_large_H A ε X H z α hX1' hε.le hhi
        rw [hkey]
        have : (H ^ 2 / Real.log X ^ A) ≤ (C1 + C2 + 1) * (H ^ 2 / Real.log X ^ A) := by
          nlinarith
        linarith
  · refine ⟨1, 2, one_pos, le_rfl, ?_⟩
    intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzY
    exfalso
    have hlt : X ^ (1 - ε) < X ^ (7 / 18 + ε) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
    linarith

/-- PROVED. The exact type of Eq33RouteD.leaf_large_cutoff_left_half. -/
example : type_of% @left_half_of_middle = type_of% @Eq33RouteD.leaf_large_cutoff_left_half :=
  rfl

/-- PROVED. Window facts used by the quarter lemmas. -/
theorem window_one_le (X ε : ℝ) (hX : 2 ≤ X) (hε : 0 < ε) : 1 ≤ windowY X ε := by
  unfold windowY
  exact Real.one_le_rpow (by linarith) (by linarith)

/-- PROVED from left_half_of_middle. The exact statement of
SixthTwin1122.leaf_lower_quarter_small_cutoff_real, P0088 page 11 Lemma 3.4 on page 15. -/
theorem lower_quarter_small_cutoff_real (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ ((1 : ℝ) / 6) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := left_half_of_middle A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0, fun X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzc => ?_⟩
  have hY1 := window_one_le X ε (hX0.trans hX) hε
  have hzY : z ≤ windowY X ε ^ (1 / 6 + ε / 2) :=
    hzc.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
  exact (sub_le_half _ H z α _ _ le_rfl (by linarith) (by linarith)).trans
    (k X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzY)

/-- PROVED from left_half_of_middle. The exact statement of
SixthTwin1122.leaf_upper_quarter_small_cutoff_real, P0088 page 11 Lemma 3.4 on page 15. -/
theorem upper_quarter_small_cutoff_real (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ ((1 : ℝ) / 6) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := left_half_of_middle A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0, fun X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzc => ?_⟩
  have hY1 := window_one_le X ε (hX0.trans hX) hε
  have hzY : z ≤ windowY X ε ^ (1 / 6 + ε / 2) :=
    hzc.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
  exact (sub_le_half _ H z α _ _ (by linarith) (by linarith) le_rfl).trans
    (k X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzY)

/-- PROVED from left_half_of_middle. The exact statement of
SixthTwin1122.leaf_lower_quarter_large_cutoff_real, P0088 page 11 Lemma 3.4 on page 15. -/
theorem lower_quarter_large_cutoff_real (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(3 * windowY X ε / 8),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := left_half_of_middle A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0,
    fun X H hX hH hHU α q a hcop hqP hqQ hclose z hz _ hzY => ?_⟩
  have hY1 := window_one_le X ε (hX0.trans hX) hε
  exact (sub_le_half _ H z α _ _ le_rfl (by linarith) (by linarith)).trans
    (k X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzY)

/-- PROVED from left_half_of_middle. The exact statement of
SixthTwin1122.leaf_upper_quarter_large_cutoff_real, P0088 page 11 Lemma 3.4 on page 15. -/
theorem upper_quarter_large_cutoff_real (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := left_half_of_middle A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0,
    fun X H hX hH hHU α q a hcop hqP hqQ hclose z hz _ hzY => ?_⟩
  have hY1 := window_one_le X ε (hX0.trans hX) hε
  exact (sub_le_half _ H z α _ _ (by linarith) (by linarith) le_rfl).trans
    (k X H hX hH hHU α q a hcop hqP hqQ hclose z hz hzY)

example : type_of% @lower_quarter_small_cutoff_real =
    type_of% @SixthTwin1122.leaf_lower_quarter_small_cutoff_real := rfl
example : type_of% @upper_quarter_small_cutoff_real =
    type_of% @SixthTwin1122.leaf_upper_quarter_small_cutoff_real := rfl
example : type_of% @lower_quarter_large_cutoff_real =
    type_of% @SixthTwin1122.leaf_lower_quarter_large_cutoff_real := rfl
example : type_of% @upper_quarter_large_cutoff_real =
    type_of% @SixthTwin1122.leaf_upper_quarter_large_cutoff_real := rfl

end LeanLab.KumchevLiu2007.Eq33RouteD.SixthQuartersByH1122
