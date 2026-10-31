/-
P0054 J. Pintz 2021, Section 3, the Remark before Theorem 3': choosing
`P ∈ [X^{7/25+ε}, X^{7/25+2ε}]` gives Theorem 3', `E(X) < X^{0.72}` for `X > X₀`.
Unit U-6771, session 20261020T2317Z-cloud53.

* `block_bound_at`: the one block count of `Applications.block_bound` at a general level `P = Y^ϑ`.
* `eventuallyBelow_of_inputAt`: if the Section 3 inputs hold at `P = Y^ϑ` with threshold
  `Y^{1-ε}` and `ϑ > 0.28 + 3ε`, then Theorem 3', the lab's `EventuallyBelow 0.72`, CONDITIONAL.
* `minor31_at`: (3.1) from Lemma 1 at any `P = X^ϑ` with `ϑ ≤ 2/5`, the condition of (3.1).
* `theorem3'_of_majorAt`: Theorem 3' CONDITIONAL ON Lemma 1 and the major arc output at one
  level `ϑ ∈ (0.28 + 3ε, 2/5]`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21.
-/
import Mathlib
import LeanLab.Pintz2021.Reduction3

namespace LeanLab.Pintz2021.Theorem3Prime

open Real Finset Filter Topology MeasureTheory LeanLab.ExceptionalSet
open LeanLab.Pintz2021.Applications LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.PNTPort.LargeSieve

attribute [local instance] Classical.propDecidable

theorem block_exponent_at {y : ℝ} (hy : 0 < y) (ϑ ε : ℝ) :
    y ^ 3 / y ^ ϑ / (y ^ (1 - ε)) ^ 2 = y ^ (1 - ϑ + 2 * ε) := by
  rw [← rpow_natCast, ← rpow_natCast (y ^ (1 - ε)), ← rpow_mul hy.le, ← rpow_sub hy,
    ← rpow_sub hy]
  congr 1; push_cast; ring

/-- One block at `P = Y^ϑ`: `D Exc Y ≤ M C Y / Y^ϑ + K Y^{1-ϑ+2ε} (log Y)^k`. -/
theorem block_bound_at {ϑ ε K : ℝ} {k C M Y : ℕ} (hC : 0 < C) (hY : 0 < Y) (R1 R2 : ℕ → ℂ)
    (𝓡 : Finset ℕ)
    (hGold : ∀ m ∈ Ioc (Y / 2) Y, Even m → 0 < (R1 m + R2 m).re → IsGoldbachSum m)
    (hMinor : ∑ m ∈ Ioc (Y / 2) Y, ‖R2 m‖ ^ 2 ≤
      K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ ϑ)
    (hMajor : ∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 m).re ≤ (Y : ℝ) ^ (1 - ε) →
      ∃ R0 ∈ 𝓡, R0 ∣ C * m)
    (hP : ∀ R0 ∈ 𝓡, (Y : ℝ) ^ ϑ ≤ R0) (hM : 𝓡.card ≤ M) :
    (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      M * (C * Y / (Y : ℝ) ^ ϑ) +
        K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hPpos : 0 < (Y : ℝ) ^ ϑ := rpow_pos_of_pos hYr _
  set s := (Ioc (Y / 2) Y).filter Even
  set T : ℝ := (Y : ℝ) ^ (1 - ε)
  have hT : 0 < T := rpow_pos_of_pos hYr _
  set bad1 := s.filter (fun m => ∃ R0 ∈ 𝓡, R0 ∣ C * m)
  have hcount := block_count_sq (s := s) (good := IsGoldbachSum) R1 R2 hT bad1
    (fun m hm => hGold m (mem_filter.mp hm).1 (mem_filter.mp hm).2)
    ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans hMinor)
    (fun m hm h => mem_filter.mpr ⟨hm, hMajor m (mem_filter.mp hm).1 (mem_filter.mp hm).2 h⟩)
  -- D Exc Y is at most the count of the non-Goldbach even `m` in the block
  have hD : (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      ((s.filter (fun m => ¬ IsGoldbachSum m)).card : ℝ) := by
    unfold Pintz2018Reduction.D Pintz2018Reduction.Exc
    exact_mod_cast card_le_card (fun m hm => by
      simp only [s, mem_filter] at hm ⊢
      exact ⟨⟨hm.1, hm.2.2.1⟩, hm.2.2.2⟩)
  -- the Case 1 classes
  have hclass : ∀ R0 ∈ 𝓡, ((s.filter (fun m => R0 ∣ C * m)).card : ℝ) ≤
      C * Y / (Y : ℝ) ^ ϑ := by
    intro R0 hR0
    have hR0pos : (0 : ℝ) < R0 := lt_of_lt_of_le hPpos (hP R0 hR0)
    have hsub : s.filter (fun m => R0 ∣ C * m) ⊆ (Ioc 0 Y).filter (fun m => R0 ∣ C * m) := by
      intro m hm
      simp only [s, mem_filter, mem_Ioc] at hm ⊢
      exact ⟨⟨by omega, hm.1.1.2⟩, hm.2⟩
    have h1 := card_dvd_mul_le R0 C Y (by exact_mod_cast hR0pos) hC
    have h2 : (C : ℝ) * Y / R0 ≤ C * Y / (Y : ℝ) ^ ϑ :=
      div_le_div_of_nonneg_left (by positivity) hPpos (hP R0 hR0)
    calc ((s.filter (fun m => R0 ∣ C * m)).card : ℝ)
        ≤ (((Ioc 0 Y).filter (fun m => R0 ∣ C * m)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ _ := h1.trans h2
  have hbad1 : (bad1.card : ℝ) ≤ M * (C * Y / (Y : ℝ) ^ ϑ) := by
    have := card_classes_le (s := s) 𝓡 (fun R0 m => R0 ∣ C * m) hclass
    have hMr : (𝓡.card : ℝ) ≤ M := by exact_mod_cast hM
    calc (bad1.card : ℝ) ≤ 𝓡.card * (C * Y / (Y : ℝ) ^ ϑ) := this
      _ ≤ M * (C * Y / (Y : ℝ) ^ ϑ) :=
          mul_le_mul_of_nonneg_right hMr (by positivity)
  have hB : K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ ϑ / T ^ 2 =
      K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
    rw [← block_exponent_at hYr ϑ ε]; ring
  linarith

/-- The Section 3 inputs at the level `P = Y^ϑ`; `Section3Input ε` is the case `ϑ = 7/25`. -/
def Section3InputAt (ϑ ε : ℝ) : Prop :=
  ∃ (K : ℝ) (k C M Y0 : ℕ), 0 < C ∧ ∀ Y : ℕ, Y0 < Y → ∃ (R1 R2 : ℕ → ℂ) (𝓡 : Finset ℕ),
    (∀ m ∈ Ioc (Y / 2) Y, Even m → 0 < (R1 m + R2 m).re → IsGoldbachSum m) ∧
    ∑ m ∈ Ioc (Y / 2) Y, ‖R2 m‖ ^ 2 ≤ K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ ϑ ∧
    (∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 m).re ≤ (Y : ℝ) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m) ∧
    (∀ R0 ∈ 𝓡, (Y : ℝ) ^ ϑ ≤ R0) ∧ 𝓡.card ≤ M

/-- CONDITIONAL ON `Section3InputAt ϑ ε` with `0.28 + 3ε < ϑ ≤ 1`: Theorem 3',
`E(X) < X^{0.72}` for all large `X`. -/
theorem eventuallyBelow_of_inputAt {ϑ ε : ℝ} (hε : 0 < ε) (hϑ : 0.28 + 3 * ε < ϑ)
    (hϑ1 : ϑ ≤ 1) (h : Section3InputAt ϑ ε) : EventuallyBelow 0.72 := by
  obtain ⟨K, k, C, M, Y0, hC, hin⟩ := h
  obtain ⟨A1, hA1, hlog⟩ := log_pow_le k hε
  set β : ℝ := 1 - ϑ + 3 * ε
  have hblocks : ∀ Y : ℕ, Y0 < Y → (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      (M * C + |K| * A1) * (Y : ℝ) ^ β := by
    intro Y hY
    obtain ⟨R1, R2, 𝓡, hG, hMi, hMa, hP, hM⟩ := hin Y hY
    have hY0 : 0 < Y := by omega
    have hYr : (0 : ℝ) < Y := by exact_mod_cast hY0
    have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY0
    have hb := block_bound_at hC hY0 R1 R2 𝓡 hG hMi hMa hP hM
    have hfirst : (C : ℝ) * Y / (Y : ℝ) ^ ϑ ≤ C * (Y : ℝ) ^ β := by
      have hYe : (Y : ℝ) / (Y : ℝ) ^ ϑ = (Y : ℝ) ^ (1 - ϑ) := by
        rw [rpow_sub hYr, rpow_one]
      have hmono : (Y : ℝ) ^ (1 - ϑ) ≤ (Y : ℝ) ^ β :=
        rpow_le_rpow_of_exponent_le hY1 (by simp only [β]; linarith)
      rw [mul_div_assoc, hYe]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    have hsecond : K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) ≤
        |K| * A1 * (Y : ℝ) ^ β := by
      have hl := hlog Y hY1
      have hl0 : 0 ≤ Real.log Y ^ k := pow_nonneg (Real.log_nonneg hY1) k
      have hYa : 0 ≤ (Y : ℝ) ^ (1 - ϑ + 2 * ε) := rpow_nonneg hYr.le _
      have hsplit : (Y : ℝ) ^ β = (Y : ℝ) ^ ε * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
        rw [← rpow_add hYr]; congr 1; simp only [β]; ring
      calc K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε)
          ≤ |K| * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
            apply mul_le_mul_of_nonneg_right _ hYa
            exact mul_le_mul_of_nonneg_right (le_abs_self K) hl0
        _ ≤ |K| * (A1 * (Y : ℝ) ^ ε) * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
            apply mul_le_mul_of_nonneg_right _ hYa
            exact mul_le_mul_of_nonneg_left hl (abs_nonneg K)
        _ = |K| * A1 * (Y : ℝ) ^ β := by rw [hsplit]; ring
    have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have : (M : ℝ) * (C * Y / (Y : ℝ) ^ ϑ) ≤ M * (C * (Y : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left hfirst hMr
    nlinarith
  obtain ⟨X0, hX0⟩ := Pintz2018Reduction.eventually_lt_of_bigO Pintz2018Reduction.Exc
    (α := 0.72) (β := β) (by simp only [β]; linarith) (by simp only [β]; linarith) hblocks
  exact ⟨X0, fun X hX => by rw [Pintz2018Reduction.E_eq_T]; exact hX0 X hX⟩

/-- (3.1) from Lemma 1 at `P = X^ϑ`, `0 ≤ ϑ ≤ 2/5`: `∑_{m<M} ‖R₂(m)‖² ≤ 8 A² X³ L^{10} / P`. -/
theorem minor31_at {A X1 X ϑ : ℝ} (hA : 0 ≤ A) (hX : 1 ≤ X) (hϑ : ϑ ≤ 2 / 5) (mi : Set ℝ)
    (hmi : MeasurableSet mi) (h1 : Lemma1On A X1 X (X ^ ϑ) mi) (M : ℕ) :
    ∑ m ∈ range M, ‖R2 (S X1 X) mi m‖ ^ 2 ≤ 8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ ϑ := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hP : 0 < X ^ ϑ := rpow_pos_of_pos hX0 _
  have hsqrt : X / Real.sqrt (X ^ ϑ) = X ^ (1 - ϑ / 2) := by
    rw [Real.sqrt_eq_rpow, ← rpow_mul hX0.le, rpow_sub hX0, rpow_one]; ring_nf
  have h45 : X ^ (4 / 5 : ℝ) ≤ X ^ (1 - ϑ / 2) := rpow_le_rpow_of_exponent_le hX (by linarith)
  set B : ℝ := A * (2 * X ^ (1 - ϑ / 2)) * Real.log X ^ 4
  have hB : ∀ β ∈ mi, ‖S X1 X β‖ ≤ B := by
    intro β hβ
    have := h1 β hβ
    rw [hsqrt] at this
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL0 4)
    exact mul_le_mul_of_nonneg_left (by linarith) hA
  have hmain := sum_R2_sq_le (aS X1 X) (⌊X⌋₊ + 1) mi hmi hB M
  have hsum := sum_aS_sq_le X1 hX
  have hB0 : 0 ≤ B ^ 2 := sq_nonneg _
  have hfin : B ^ 2 * (2 * X * Real.log X ^ 2) =
      8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ ϑ := by
    have hpow : (X ^ (1 - ϑ / 2)) ^ 2 * X = X ^ 3 / X ^ ϑ := by
      rw [eq_div_iff hP.ne', ← rpow_natCast, ← rpow_natCast, ← rpow_mul hX0.le]
      rw [show X ^ ((1 - ϑ / 2) * ((2 : ℕ) : ℝ)) * X * X ^ ϑ =
          X ^ ((1 - ϑ / 2) * ((2 : ℕ) : ℝ)) * X ^ (1 : ℝ) * X ^ ϑ by rw [rpow_one]]
      rw [← rpow_add hX0, ← rpow_add hX0]; congr 1; push_cast; ring
    simp only [B]
    rw [show 8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ ϑ =
      8 * A ^ 2 * Real.log X ^ 10 * (X ^ 3 / X ^ ϑ) by ring, ← hpow]
    ring
  calc ∑ m ∈ range M, ‖R2 (S X1 X) mi m‖ ^ 2 ≤ B ^ 2 * ∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2 :=
        hmain
    _ ≤ B ^ 2 * (2 * X * Real.log X ^ 2) := mul_le_mul_of_nonneg_left hsum hB0
    _ = _ := hfin

/-- The remaining inputs at level `P = Y^ϑ`: Lemma 1 on `mi` and the major arc output. -/
def Section3MajorInputAt (ϑ ε : ℝ) : Prop :=
  ∃ (A : ℝ) (C M Y0 : ℕ), 0 ≤ A ∧ 0 < C ∧ ∀ Y : ℕ, Y0 < Y → ∃ (X1 : ℝ) (mi : Set ℝ)
    (𝓡 : Finset ℕ), MeasurableSet mi ∧ Lemma1On A X1 Y ((Y : ℝ) ^ ϑ) mi ∧
    (∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 (S X1 Y) mi m).re ≤ (Y : ℝ) ^ (1 - ε) →
      ∃ R0 ∈ 𝓡, R0 ∣ C * m) ∧
    (∀ R0 ∈ 𝓡, (Y : ℝ) ^ ϑ ≤ R0) ∧ 𝓡.card ≤ M

theorem inputAt_of_majorAt {ϑ ε : ℝ} (hϑ : ϑ ≤ 2 / 5) (h : Section3MajorInputAt ϑ ε) :
    Section3InputAt ϑ ε := by
  obtain ⟨A, C, M, Y0, hA, hC, hin⟩ := h
  refine ⟨8 * A ^ 2, 10, C, M, Y0, hC, fun Y hY => ?_⟩
  obtain ⟨X1, mi, 𝓡, hmi, hL1, hMa, hP, hM⟩ := hin Y hY
  refine ⟨R1 (S X1 Y) mi, R2 (S X1 Y) mi, 𝓡, ?_, ?_, hMa, hP, hM⟩
  · intro m _ _ hpos
    rw [R1_add_R2 _ (continuous_S X1 Y) mi hmi] at hpos
    exact goldbach_of_re_pos X1 Y m hpos
  · have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
    have hsub : Ioc (Y / 2) Y ⊆ range (Y + 1) := by
      intro m hm; rw [mem_range]; have := (mem_Ioc.mp hm).2; omega
    calc ∑ m ∈ Ioc (Y / 2) Y, ‖R2 (S X1 Y) mi m‖ ^ 2
        ≤ ∑ m ∈ range (Y + 1), ‖R2 (S X1 Y) mi m‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      _ ≤ _ := minor31_at hA hY1 hϑ mi hmi hL1 (Y + 1)

/-- CONDITIONAL ON Lemma 1 and the major arc output at one level `ϑ` with
`0.28 + 3ε < ϑ ≤ 2/5`: Theorem 3', `E(X) < X^{0.72}` for `X > X₀`. -/
theorem theorem3'_of_majorAt {ϑ ε : ℝ} (hε : 0 < ε) (hϑ : 0.28 + 3 * ε < ϑ) (hϑ2 : ϑ ≤ 2 / 5)
    (h : Section3MajorInputAt ϑ ε) : EventuallyBelow 0.72 :=
  eventuallyBelow_of_inputAt hε hϑ (by linarith) (inputAt_of_majorAt hϑ2 h)

/-- The Remark's range is admissible: `ϑ = 7/25 + 4ε` lies in `(0.28 + 3ε, 2/5]` for
`0 < ε ≤ 0.03`. -/
theorem remark_range {ε : ℝ} (hε : 0 < ε) (hε3 : ε ≤ 0.03) :
    0.28 + 3 * ε < 7 / 25 + 4 * ε ∧ 7 / 25 + 4 * ε ≤ (2 / 5 : ℝ) := by
  constructor <;> linarith

end LeanLab.Pintz2021.Theorem3Prime

#print axioms LeanLab.Pintz2021.Theorem3Prime.block_bound_at
#print axioms LeanLab.Pintz2021.Theorem3Prime.eventuallyBelow_of_inputAt
#print axioms LeanLab.Pintz2021.Theorem3Prime.minor31_at
#print axioms LeanLab.Pintz2021.Theorem3Prime.inputAt_of_majorAt
#print axioms LeanLab.Pintz2021.Theorem3Prime.theorem3'_of_majorAt
#print axioms LeanLab.Pintz2021.Theorem3Prime.remark_range

