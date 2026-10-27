/-
P0054 J. Pintz 2021, Section 3: the exceptional set exponent as an explicit function of the
two levels of the circle method. Unit U-1341, PC run 20261021T0303Z-27628, track T2.

The chain of `Theorem3Prime` proves `EventuallyBelow 0.72` from the Section 3 inputs at one
level `P = Y^ϑ`. Here the two roles of `ϑ` are separated:
* `ϑ`, the minor arc level, the mean square (3.1) saves `Y^ϑ`; Lemma 1 gives it for `ϑ ≤ 2/5`;
* `κ`, the major arc level, every Case 1 class modulus `R0` is at least `Y^κ`.
`eventuallyBelow_of_levels`: if `max(1-ϑ, 1-κ) + 3ε < α` then `EventuallyBelow α`, CONDITIONAL.
`exponent_of_majorLevels`: the same from Lemma 1 at `P = Y^ϑ`, `ϑ ≤ 2/5`, and the major arc
output with classes at least `Y^κ`, CONDITIONAL.
`theorem3'_recovered`: `κ = ϑ`, `0.28 + 3ε < ϑ` gives back Theorem 3', `E(X) < X^{0.72}`.
`minor_ceiling`: with `ϑ ≤ 2/5` this chain never reaches an exponent below `3/5`.
No improvement on 0.72 is claimed. Binary Goldbach is OPEN. AI-written Lean code, Claude.
-/
import Mathlib
import LeanLab.Pintz2021.Theorem3Prime

namespace LeanLab.Pintz2021.ExponentU1341

open Real Finset Filter Topology MeasureTheory LeanLab.ExceptionalSet
open LeanLab.Pintz2021.Applications LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.Theorem3Prime

attribute [local instance] Classical.propDecidable

/-- One block with two levels: `D Exc Y ≤ M C Y / Y^κ + K Y^{1-ϑ+2ε} (log Y)^k`. -/
theorem block_bound_levels {ϑ κ ε K : ℝ} {k C M Y : ℕ} (hC : 0 < C) (hY : 0 < Y)
    (R1 R2 : ℕ → ℂ) (𝓡 : Finset ℕ)
    (hGold : ∀ m ∈ Ioc (Y / 2) Y, Even m → 0 < (R1 m + R2 m).re → IsGoldbachSum m)
    (hMinor : ∑ m ∈ Ioc (Y / 2) Y, ‖R2 m‖ ^ 2 ≤
      K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ ϑ)
    (hMajor : ∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 m).re ≤ (Y : ℝ) ^ (1 - ε) →
      ∃ R0 ∈ 𝓡, R0 ∣ C * m)
    (hP : ∀ R0 ∈ 𝓡, (Y : ℝ) ^ κ ≤ R0) (hM : 𝓡.card ≤ M) :
    (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      M * (C * Y / (Y : ℝ) ^ κ) +
        K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hPpos : 0 < (Y : ℝ) ^ κ := rpow_pos_of_pos hYr _
  set s := (Ioc (Y / 2) Y).filter Even
  set T : ℝ := (Y : ℝ) ^ (1 - ε)
  have hT : 0 < T := rpow_pos_of_pos hYr _
  set bad1 := s.filter (fun m => ∃ R0 ∈ 𝓡, R0 ∣ C * m)
  have hcount := block_count_sq (s := s) (good := IsGoldbachSum) R1 R2 hT bad1
    (fun m hm => hGold m (mem_filter.mp hm).1 (mem_filter.mp hm).2)
    ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans hMinor)
    (fun m hm h => mem_filter.mpr ⟨hm, hMajor m (mem_filter.mp hm).1 (mem_filter.mp hm).2 h⟩)
  have hD : (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      ((s.filter (fun m => ¬ IsGoldbachSum m)).card : ℝ) := by
    unfold Pintz2018Reduction.D Pintz2018Reduction.Exc
    exact_mod_cast card_le_card (fun m hm => by
      simp only [s, mem_filter] at hm ⊢
      exact ⟨⟨hm.1, hm.2.2.1⟩, hm.2.2.2⟩)
  have hclass : ∀ R0 ∈ 𝓡, ((s.filter (fun m => R0 ∣ C * m)).card : ℝ) ≤
      C * Y / (Y : ℝ) ^ κ := by
    intro R0 hR0
    have hR0pos : (0 : ℝ) < R0 := lt_of_lt_of_le hPpos (hP R0 hR0)
    have hsub : s.filter (fun m => R0 ∣ C * m) ⊆ (Ioc 0 Y).filter (fun m => R0 ∣ C * m) := by
      intro m hm
      simp only [s, mem_filter, mem_Ioc] at hm ⊢
      exact ⟨⟨by omega, hm.1.1.2⟩, hm.2⟩
    have h1 := card_dvd_mul_le R0 C Y (by exact_mod_cast hR0pos) hC
    have h2 : (C : ℝ) * Y / R0 ≤ C * Y / (Y : ℝ) ^ κ :=
      div_le_div_of_nonneg_left (by positivity) hPpos (hP R0 hR0)
    calc ((s.filter (fun m => R0 ∣ C * m)).card : ℝ)
        ≤ (((Ioc 0 Y).filter (fun m => R0 ∣ C * m)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ _ := h1.trans h2
  have hbad1 : (bad1.card : ℝ) ≤ M * (C * Y / (Y : ℝ) ^ κ) := by
    have := card_classes_le (s := s) 𝓡 (fun R0 m => R0 ∣ C * m) hclass
    have hMr : (𝓡.card : ℝ) ≤ M := by exact_mod_cast hM
    calc (bad1.card : ℝ) ≤ 𝓡.card * (C * Y / (Y : ℝ) ^ κ) := this
      _ ≤ M * (C * Y / (Y : ℝ) ^ κ) :=
          mul_le_mul_of_nonneg_right hMr (by positivity)
  have hB : K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ ϑ / T ^ 2 =
      K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
    rw [← block_exponent_at hYr ϑ ε]; ring
  linarith

/-- The Section 3 inputs with two levels: mean square saving `Y^ϑ`, classes at least `Y^κ`. -/
def Section3InputLevels (ϑ κ ε : ℝ) : Prop :=
  ∃ (K : ℝ) (k C M Y0 : ℕ), 0 < C ∧ ∀ Y : ℕ, Y0 < Y → ∃ (R1 R2 : ℕ → ℂ) (𝓡 : Finset ℕ),
    (∀ m ∈ Ioc (Y / 2) Y, Even m → 0 < (R1 m + R2 m).re → IsGoldbachSum m) ∧
    ∑ m ∈ Ioc (Y / 2) Y, ‖R2 m‖ ^ 2 ≤ K * (Y : ℝ) ^ 3 * Real.log Y ^ k / (Y : ℝ) ^ ϑ ∧
    (∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 m).re ≤ (Y : ℝ) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m) ∧
    (∀ R0 ∈ 𝓡, (Y : ℝ) ^ κ ≤ R0) ∧ 𝓡.card ≤ M

/-- At `κ = ϑ` the two-level input is the lab's `Section3InputAt ϑ ε`. -/
theorem levels_eq_inputAt (ϑ ε : ℝ) : Section3InputLevels ϑ ϑ ε ↔ Section3InputAt ϑ ε :=
  Iff.rfl

/-- CONDITIONAL ON `Section3InputLevels ϑ κ ε`: the explicit implication to the exponent,
`max(1-ϑ, 1-κ) + 3ε < α` gives `E(X) < X^α` for all large `X`. -/
theorem eventuallyBelow_of_levels {ϑ κ ε α : ℝ} (hε : 0 < ε) (hϑ1 : ϑ ≤ 1) (hκ1 : κ ≤ 1)
    (hαϑ : 1 - ϑ + 3 * ε < α) (hακ : 1 - κ + 3 * ε < α)
    (h : Section3InputLevels ϑ κ ε) : EventuallyBelow α := by
  obtain ⟨K, k, C, M, Y0, hC, hin⟩ := h
  obtain ⟨A1, hA1, hlog⟩ := log_pow_le k hε
  set β : ℝ := max (1 - ϑ) (1 - κ) + 3 * ε
  have hβϑ : 1 - ϑ + 3 * ε ≤ β := by simp only [β]; linarith [le_max_left (1 - ϑ) (1 - κ)]
  have hβκ : 1 - κ + 3 * ε ≤ β := by simp only [β]; linarith [le_max_right (1 - ϑ) (1 - κ)]
  have hβα : β < α := by
    simp only [β]
    rcases le_total (1 - ϑ) (1 - κ) with hle | hle
    · rw [max_eq_right hle]; linarith
    · rw [max_eq_left hle]; linarith
  have hblocks : ∀ Y : ℕ, Y0 < Y → (Pintz2018Reduction.D Pintz2018Reduction.Exc Y : ℝ) ≤
      (M * C + |K| * A1) * (Y : ℝ) ^ β := by
    intro Y hY
    obtain ⟨R1, R2, 𝓡, hG, hMi, hMa, hP, hM⟩ := hin Y hY
    have hY0 : 0 < Y := by omega
    have hYr : (0 : ℝ) < Y := by exact_mod_cast hY0
    have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY0
    have hb := block_bound_levels (κ := κ) hC hY0 R1 R2 𝓡 hG hMi hMa hP hM
    have hfirst : (C : ℝ) * Y / (Y : ℝ) ^ κ ≤ C * (Y : ℝ) ^ β := by
      have hYe : (Y : ℝ) / (Y : ℝ) ^ κ = (Y : ℝ) ^ (1 - κ) := by
        rw [rpow_sub hYr, rpow_one]
      have hmono : (Y : ℝ) ^ (1 - κ) ≤ (Y : ℝ) ^ β :=
        rpow_le_rpow_of_exponent_le hY1 (by linarith)
      rw [mul_div_assoc, hYe]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    have hsecond : K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) ≤
        |K| * A1 * (Y : ℝ) ^ β := by
      have hl := hlog Y hY1
      have hl0 : 0 ≤ Real.log Y ^ k := pow_nonneg (Real.log_nonneg hY1) k
      have hYa : 0 ≤ (Y : ℝ) ^ (1 - ϑ + 2 * ε) := rpow_nonneg hYr.le _
      have hmono : (Y : ℝ) ^ ε * (Y : ℝ) ^ (1 - ϑ + 2 * ε) ≤ (Y : ℝ) ^ β := by
        rw [← rpow_add hYr]
        exact rpow_le_rpow_of_exponent_le hY1 (by linarith)
      have hKA : 0 ≤ |K| * A1 := mul_nonneg (abs_nonneg K) hA1.le
      calc K * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε)
          ≤ |K| * Real.log Y ^ k * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
            apply mul_le_mul_of_nonneg_right _ hYa
            exact mul_le_mul_of_nonneg_right (le_abs_self K) hl0
        _ ≤ |K| * (A1 * (Y : ℝ) ^ ε) * (Y : ℝ) ^ (1 - ϑ + 2 * ε) := by
            apply mul_le_mul_of_nonneg_right _ hYa
            exact mul_le_mul_of_nonneg_left hl (abs_nonneg K)
        _ = |K| * A1 * ((Y : ℝ) ^ ε * (Y : ℝ) ^ (1 - ϑ + 2 * ε)) := by ring
        _ ≤ |K| * A1 * (Y : ℝ) ^ β := mul_le_mul_of_nonneg_left hmono hKA
    have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have : (M : ℝ) * (C * Y / (Y : ℝ) ^ κ) ≤ M * (C * (Y : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left hfirst hMr
    nlinarith
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨X0, hX0⟩ := Pintz2018Reduction.eventually_lt_of_bigO Pintz2018Reduction.Exc
    (α := α) (β := β) hβ0 hβα hblocks
  exact ⟨X0, fun X hX => by rw [Pintz2018Reduction.E_eq_T]; exact hX0 X hX⟩

/-- The remaining inputs with two levels: Lemma 1 at `P = Y^ϑ` on `mi` and the major arc
output with every Case 1 class modulus at least `Y^κ`. -/
def Section3MajorInputLevels (ϑ κ ε : ℝ) : Prop :=
  ∃ (A : ℝ) (C M Y0 : ℕ), 0 ≤ A ∧ 0 < C ∧ ∀ Y : ℕ, Y0 < Y → ∃ (X1 : ℝ) (mi : Set ℝ)
    (𝓡 : Finset ℕ), MeasurableSet mi ∧ Lemma1On A X1 Y ((Y : ℝ) ^ ϑ) mi ∧
    (∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 (S X1 Y) mi m).re ≤ (Y : ℝ) ^ (1 - ε) →
      ∃ R0 ∈ 𝓡, R0 ∣ C * m) ∧
    (∀ R0 ∈ 𝓡, (Y : ℝ) ^ κ ≤ R0) ∧ 𝓡.card ≤ M

theorem levels_of_majorLevels {ϑ κ ε : ℝ} (hϑ : ϑ ≤ 2 / 5) (h : Section3MajorInputLevels ϑ κ ε) :
    Section3InputLevels ϑ κ ε := by
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

/-- CONDITIONAL ON Lemma 1 at `P = Y^ϑ`, `ϑ ≤ 2/5`, and the major arc output with classes
at least `Y^κ`, `κ ≤ 1`: `max(1-ϑ, 1-κ) + 3ε < α` gives `E(X) < X^α` for large `X`. -/
theorem exponent_of_majorLevels {ϑ κ ε α : ℝ} (hε : 0 < ε) (hϑ : ϑ ≤ 2 / 5) (hκ1 : κ ≤ 1)
    (hαϑ : 1 - ϑ + 3 * ε < α) (hακ : 1 - κ + 3 * ε < α)
    (h : Section3MajorInputLevels ϑ κ ε) : EventuallyBelow α :=
  eventuallyBelow_of_levels hε (by linarith) hκ1 hαϑ hακ (levels_of_majorLevels hϑ h)

/-- CONDITIONAL, the limit form: if the inputs hold at levels `ϑ ≤ 2/5`, `κ ≤ 1` for every
`ε > 0`, then `E(X) < X^α` eventually for every `α > max(1-ϑ, 1-κ)`. -/
theorem exponent_limit {ϑ κ α : ℝ} (hϑ : ϑ ≤ 2 / 5) (hκ1 : κ ≤ 1)
    (hαϑ : 1 - ϑ < α) (hακ : 1 - κ < α)
    (h : ∀ ε : ℝ, 0 < ε → Section3MajorInputLevels ϑ κ ε) : EventuallyBelow α := by
  set ε : ℝ := min (α - (1 - ϑ)) (α - (1 - κ)) / 4
  have hm : 0 < min (α - (1 - ϑ)) (α - (1 - κ)) := lt_min (by linarith) (by linarith)
  have hε : 0 < ε := by simp only [ε]; linarith
  have h1 : min (α - (1 - ϑ)) (α - (1 - κ)) ≤ α - (1 - ϑ) := min_le_left _ _
  have h2 : min (α - (1 - ϑ)) (α - (1 - κ)) ≤ α - (1 - κ) := min_le_right _ _
  exact exponent_of_majorLevels hε hϑ hκ1 (by simp only [ε]; linarith)
    (by simp only [ε]; linarith) (h ε hε)

/-- Theorem 3' recovered, CONDITIONAL: `κ = ϑ`, `0.28 + 3ε < ϑ ≤ 2/5` gives `E(X) < X^{0.72}`. -/
theorem theorem3'_recovered {ϑ ε : ℝ} (hε : 0 < ε) (hϑ : 0.28 + 3 * ε < ϑ) (hϑ2 : ϑ ≤ 2 / 5)
    (h : Section3MajorInputAt ϑ ε) : EventuallyBelow 0.72 :=
  exponent_of_majorLevels hε hϑ2 (by linarith) (by linarith) (by linarith) h

/-- The ceiling of this chain: with the minor arc level `ϑ ≤ 2/5` of (3.1), the exponent
condition `1 - ϑ + 3ε < α` forces `α > 3/5`. -/
theorem minor_ceiling {ϑ ε α : ℝ} (hε : 0 < ε) (hϑ : ϑ ≤ 2 / 5) (hα : 1 - ϑ + 3 * ε < α) :
    3 / 5 < α := by linarith

/-- Which levels reach which exponent: at `ϑ = 2/5` the chain gives every `α > max(3/5, 1-κ)`;
to pass 0.72 one needs `κ > 0.28`, the numbered target T-1341-1. -/
theorem target_levels {κ α : ℝ} (hκ : 0.28 < κ) (hα : max (3 / 5) (1 - κ) < α) :
    1 - 2 / 5 < α ∧ 1 - κ < α ∧ (1 - κ < 0.72) :=
  ⟨by linarith [le_max_left (3 / 5 : ℝ) (1 - κ)], by linarith [le_max_right (3 / 5 : ℝ) (1 - κ)],
    by linarith⟩

/-- Vacuity: binary Goldbach, which is OPEN, implies the two-level input at every level,
with `R₁ = Y`, `R₂ = 0` and no classes. -/
theorem levels_of_binaryGoldbach (hBG : BinaryGoldbach) {ϑ κ ε : ℝ} (hε : 0 < ε) :
    Section3InputLevels ϑ κ ε := by
  refine ⟨0, 0, 1, 0, 8, one_pos, fun Y hY => ⟨fun _ => (Y : ℂ), fun _ => 0, ∅, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro m hm he _
    have := (mem_Ioc.mp hm).1
    exact hBG m he (by omega)
  · simp
  · intro m _ _ h
    exfalso
    have hY1 : (1 : ℝ) < Y := by exact_mod_cast (by omega : 1 < Y)
    have : (Y : ℝ) ^ (1 - ε) < (Y : ℝ) ^ (1 : ℝ) :=
      rpow_lt_rpow_of_exponent_lt hY1 (by linarith)
    rw [rpow_one] at this
    simp at h
    linarith
  · simp
  · simp

end LeanLab.Pintz2021.ExponentU1341
