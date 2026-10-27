/-
P0016 Pintz 2018, arXiv 1804.09084v2, unit U-1278, PC run 20261020T2004Z-7678.
The reduction from the paper's inputs to Theorem 1, `E(X) < X^{0.72}` for `X > X₂`.

Read 2026-10-20 by WebFetch of arxiv.org/html/1804.09084v2, Sections 1 to 8; Section 9 lies
past the fetch limit. What the text gives:
* (1.9) Theorem 1: an ineffective `X₂` with `E(X) < X^{0.72}` for `X > X₂`.
* (2.4) the paper studies even `m ∈ [X/2, X]`; no dyadic remark passes to all `n ≤ X`.
* (2.16), (2.17) Theorem B: a Siegel zero gives `E(X) < X^{3/5+ε'}`; the Remark fixes `ε' = 10⁻³`.
* (2.6), (2.22) minor arcs: exceptions in `[X/2, X]` are `o(X^{1-ϑ})`.
* (2.28), (2.29) deleted classes, `q(𝓡') > X^ϑ`: at most `C₁(ε) X^{1-ϑ}` each, `C₂(ε)` classes,
  so `O_ε(X^{1-ϑ})`, not `o`.
* (2.33) `A = 1/ϑ`; Theorem A needs `ε < ϑ < 4/9 - ε`, the Remark after (2.18) `ϑ ≤ 0.44`.
The text never writes `ϑ = 0.28`; `1 - ϑ = 0.72` and the weight `e^{-(25/7)λ}` of Section 9
give `ϑ = 7/25`, `A = 25/7`.

PROVED here, elementary: the exponent arithmetic; the dyadic step `T(X) = D(X) + T(⌊X/2⌋)`
and its two summed forms; `case8_A`, Case 8 for every weight `e^{-2Aλ}` with `A ≥ 7/2`.
CONDITIONAL: `pintz_of_inputs`, on Theorem B and on a non-Siegel count with exponent
`1 - ϑ'` for some `ϑ' > 0.28`; `pintz_of_inputs_littleO`, on Theorem B and an `o(Y^{0.72})` count.
The analytic inputs, Theorems A to L, are not proved. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ExceptionalSet.Statements
import LeanLab.ExceptionalSet.Pintz2018

namespace LeanLab.ExceptionalSet.Pintz2018Reduction
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-! ### Exponent arithmetic -/

/-- `ϑ = 7/25` gives the exponent `1 - ϑ = 0.72` of (1.9). -/
theorem one_sub_theta : (1 : ℝ) - 7 / 25 = 0.72 := by norm_num

/-- (2.33) `A = 1/ϑ = 25/7`, and `2A = 50/7`, the weight of Case 8. -/
theorem A_val : (1 : ℝ) / (7 / 25) = 25 / 7 ∧ 2 * ((25 : ℝ) / 7) = 50 / 7 := by
  constructor <;> norm_num

/-- `ϑ = 7/25` meets Theorem A's range for `ε = 10⁻³` and the Remark's `ϑ ≤ 0.44`. -/
theorem theta_admissible :
    (10 : ℝ)⁻¹ ^ 3 < 7 / 25 ∧ (7 : ℝ) / 25 < 4 / 9 - (10 : ℝ)⁻¹ ^ 3 ∧ (7 : ℝ) / 25 ≤ 0.44 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- (2.17) with `ε' = 10⁻³`: `3/5 + ε' = 0.601 < 0.72`. -/
theorem siegel_exponent : (3 : ℝ) / 5 + (10 : ℝ)⁻¹ ^ 3 = 0.601 ∧ (0.601 : ℝ) < 0.72 := by
  constructor <;> norm_num

/-! ### The dyadic step, for any set of naturals -/

section Dyadic
variable (p : ℕ → Prop)

/-- `T p X = #{n ∈ (0, X] : p n}`. -/
noncomputable def T (X : ℕ) : ℕ := ((Finset.Ioc 0 X).filter p).card

/-- `D p Y = #{n ∈ (⌊Y/2⌋, Y] : p n}`, the paper's `[X/2, X]` block. -/
noncomputable def D (Y : ℕ) : ℕ := ((Finset.Ioc (Y / 2) Y).filter p).card

theorem T_split (X : ℕ) : T p X = D p X + T p (X / 2) := by
  unfold T D
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le (X / 2)) (Nat.div_le_self X 2),
    Finset.filter_union, Finset.card_union_of_disjoint, add_comm]
  exact Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)

theorem T_mono {X Y : ℕ} (h : X ≤ Y) : T p X ≤ T p Y := by
  unfold T
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right h))

theorem D_le_T (Y : ℕ) : D p Y ≤ T p Y := by
  rw [T_split p Y]; omega

/-- Summing the blocks: `D p Y ≤ c Y^α` for `Y > Y₀` gives
`T p X ≤ c/(1 - 2^{-α}) X^α + T p Y₀` for every `X`. -/
theorem T_le {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c) {Y0 : ℕ}
    (hD : ∀ Y : ℕ, Y0 < Y → (D p Y : ℝ) ≤ c * (Y : ℝ) ^ α) (X : ℕ) :
    (T p X : ℝ) ≤ c / (1 - (2 : ℝ) ^ (-α)) * (X : ℝ) ^ α + T p Y0 := by
  set r : ℝ := (2 : ℝ) ^ (-α) with hr
  have hr0 : 0 < r := rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := c / (1 - r) with hK
  have hK0 : 0 ≤ K := div_nonneg hc (by linarith)
  have hKr : K * (1 - r) = c := by rw [hK]; field_simp
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    rcases le_or_gt X Y0 with hX | hX
    · have := T_mono p hX
      have : (0 : ℝ) ≤ K * (X : ℝ) ^ α := mul_nonneg hK0 (rpow_nonneg (Nat.cast_nonneg _) _)
      have : (T p X : ℝ) ≤ T p Y0 := by exact_mod_cast T_mono p hX
      linarith
    · have hX1 : 0 < X := lt_of_le_of_lt (Nat.zero_le _) hX
      have hlt : X / 2 < X := Nat.div_lt_self hX1 (by norm_num)
      have h1 := ih (X / 2) hlt
      have h2 := hD X hX
      have hhalf : ((X / 2 : ℕ) : ℝ) ^ α ≤ (X : ℝ) ^ α * r := by
        have hc2 : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 := Nat.cast_div_le
        calc ((X / 2 : ℕ) : ℝ) ^ α ≤ ((X : ℝ) / 2) ^ α :=
              rpow_le_rpow (Nat.cast_nonneg _) hc2 hα.le
          _ = (X : ℝ) ^ α * r := by
              rw [div_rpow (Nat.cast_nonneg _) (by norm_num), hr, rpow_neg (by norm_num),
                div_eq_mul_inv]
      have hsplit : (T p X : ℝ) = D p X + T p (X / 2) := by exact_mod_cast T_split p X
      have hXa : 0 ≤ (X : ℝ) ^ α := rpow_nonneg (Nat.cast_nonneg _) _
      have : K * ((X / 2 : ℕ) : ℝ) ^ α ≤ K * ((X : ℝ) ^ α * r) :=
        mul_le_mul_of_nonneg_left hhalf hK0
      nlinarith

/-- The `o` form: if for every `c > 0` the blocks satisfy `D p Y ≤ c Y^α` eventually, then
`T p X < X^α` for all large `X`, with no constant. -/
theorem eventually_lt_of_littleO {α : ℝ} (hα : 0 < α)
    (h : ∀ c : ℝ, 0 < c → ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → (D p Y : ℝ) ≤ c * (Y : ℝ) ^ α) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → (T p X : ℝ) < (X : ℝ) ^ α := by
  set r : ℝ := (2 : ℝ) ^ (-α)
  have hr1 : r < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨Y0, hY0⟩ := h ((1 - r) / 2) (by linarith)
  have hb := T_le p hα (by linarith) hY0
  have hK : (1 - r) / 2 / (1 - r) = 1 / 2 := by field_simp
  have ht : Tendsto (fun X : ℕ => (X : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (ht.eventually_gt_atTop (2 * (T p Y0 : ℝ)))
  refine ⟨X0, fun X hX => ?_⟩
  have h1 := hb X
  have h2 := hX0 X hX
  rw [hK] at h1
  linarith

/-- The slack form: `D p Y ≤ C Y^β` eventually with `0 ≤ β < α` gives `T p X < X^α` eventually. -/
theorem eventually_lt_of_bigO {α β C : ℝ} (hβ : 0 ≤ β) (hβα : β < α) {Y1 : ℕ}
    (h : ∀ Y : ℕ, Y1 < Y → (D p Y : ℝ) ≤ C * (Y : ℝ) ^ β) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → (T p X : ℝ) < (X : ℝ) ^ α := by
  have hα : 0 < α := lt_of_le_of_lt hβ hβα
  apply eventually_lt_of_littleO p hα
  intro c hc
  -- `C Y^{β-α} → 0`
  have ht : Tendsto (fun Y : ℕ => |C| * (Y : ℝ) ^ (-(α - β))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < α - β)).comp
      tendsto_natCast_atTop_atTop).const_mul |C|
    simpa using this
  obtain ⟨Y2, hY2⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
  refine ⟨max Y1 (max Y2 1), fun Y hY => ?_⟩
  have hY1 : Y1 < Y := lt_of_le_of_lt (le_max_left _ _) hY
  have hYpos : (0 : ℝ) < Y := by
    have : 1 < Y := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hY
    exact_mod_cast (by omega : 0 < Y)
  have hsmall := hY2 Y (by
    have := (le_max_left Y2 1).trans (le_max_right Y1 (max Y2 1)); omega)
  have hsplit : (Y : ℝ) ^ β = (Y : ℝ) ^ α * (Y : ℝ) ^ (-(α - β)) := by
    rw [← rpow_add hYpos]; ring_nf
  have hYa : 0 < (Y : ℝ) ^ α := rpow_pos_of_pos hYpos _
  calc (D p Y : ℝ) ≤ C * (Y : ℝ) ^ β := h Y hY1
    _ ≤ |C| * (Y : ℝ) ^ β := mul_le_mul_of_nonneg_right (le_abs_self C)
          (rpow_nonneg hYpos.le _)
    _ = (|C| * (Y : ℝ) ^ (-(α - β))) * (Y : ℝ) ^ α := by rw [hsplit]; ring
    _ ≤ c * (Y : ℝ) ^ α := mul_le_mul_of_nonneg_right hsmall.le hYa.le

/-- Vacuity: the hypothesis of `eventually_lt_of_littleO` holds for the empty predicate. -/
theorem vacuity_littleO (α : ℝ) :
    ∀ c : ℝ, 0 < c → ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y →
      (D (fun _ => False) Y : ℝ) ≤ c * (Y : ℝ) ^ α := by
  intro c hc
  refine ⟨0, fun Y _ => ?_⟩
  have hD : D (fun _ => False) Y = 0 := by simp [D]
  rw [hD, Nat.cast_zero]
  exact mul_nonneg hc.le (rpow_nonneg (Nat.cast_nonneg _) _)

/-- Nontriviality: for the full predicate the conclusion fails at `α = 0.72`. -/
theorem not_eventually_lt_true :
    ¬ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → (T (fun _ => True) X : ℝ) < (X : ℝ) ^ (0.72 : ℝ) := by
  rintro ⟨X0, hX0⟩
  have h := hX0 (X0 + 1) (by omega)
  have hT : T (fun _ => True) (X0 + 1) = X0 + 1 := by simp [T]
  rw [hT] at h
  have h1 : (1 : ℝ) ≤ ((X0 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ X0 + 1)
  have : ((X0 + 1 : ℕ) : ℝ) ^ (0.72 : ℝ) ≤ ((X0 + 1 : ℕ) : ℝ) ^ (1 : ℝ) :=
    rpow_le_rpow_of_exponent_le h1 (by norm_num)
  rw [rpow_one] at this
  linarith

end Dyadic

/-! ### The Goldbach instance -/

/-- The predicate counted by `E`. -/
def Exc (n : ℕ) : Prop := 4 ≤ n ∧ Even n ∧ ¬ IsGoldbachSum n

theorem E_eq_T (X : ℕ) : E X = T Exc X := by
  unfold E T Exc
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h4, hX⟩, he, hg⟩; exact ⟨⟨by omega, hX⟩, h4, he, hg⟩
  · rintro ⟨⟨_, hX⟩, h4, he, hg⟩; exact ⟨⟨h4, hX⟩, he, hg⟩

/-- Input, Theorem B, (2.16) and (2.17) with `ε' = 10⁻³`: whenever the Siegel case holds at `Y`,
`E(Y) < Y^{0.601}`, for `Y` beyond an ineffective `Y₀`. `Siegel Y` stands for the paper's
condition, a zero `β₁ > 1 - h/log Y` of some `L(s, χ₁)` with `cond χ₁ ≤ Y^{4/9-ε'}`. -/
def TheoremBInput (Siegel : ℕ → Prop) : Prop :=
  ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → Siegel Y → (E Y : ℝ) < (Y : ℝ) ^ (0.601 : ℝ)

/-- Input, the non-Siegel analysis at level `ϑ`: Theorem A, the minor arcs (2.6), (2.22), the
deleted classes (2.29), and Section 9's `S₀ < 1 - 2ε` together bound the exceptional even `m`
in `(⌊Y/2⌋, Y]` by `C Y^{1-ϑ}` outside the Siegel case. -/
def NonSiegelInput (Siegel : ℕ → Prop) (ϑ C : ℝ) : Prop :=
  ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → ¬ Siegel Y → (D Exc Y : ℝ) ≤ C * (Y : ℝ) ^ (1 - ϑ)

/-- The same at `ϑ = 0.28` in the `o` form that (2.22) states for the minor arcs. -/
def NonSiegelInputLittleO (Siegel : ℕ → Prop) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → ¬ Siegel Y →
    (D Exc Y : ℝ) ≤ c * (Y : ℝ) ^ (0.72 : ℝ)

/-- `Y^{0.601} ≤ c Y^{0.72}` for large `Y`, any `c > 0`. -/
theorem siegel_absorb {c : ℝ} (hc : 0 < c) :
    ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → (Y : ℝ) ^ (0.601 : ℝ) ≤ c * (Y : ℝ) ^ (0.72 : ℝ) := by
  have ht : Tendsto (fun Y : ℕ => (Y : ℝ) ^ (-(0.119 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Y2, hY2⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
  refine ⟨Y2, fun Y hY => ?_⟩
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hs := hY2 Y hY.le
  have hsplit : (Y : ℝ) ^ (0.601 : ℝ) = (Y : ℝ) ^ (0.72 : ℝ) * (Y : ℝ) ^ (-(0.119 : ℝ)) := by
    rw [← rpow_add hYpos]; norm_num
  rw [hsplit, mul_comm c]
  exact mul_le_mul_of_nonneg_left hs.le (rpow_nonneg hYpos.le _)

/-- Siegel blocks: under Theorem B the blocks in the Siegel case are `o(Y^{0.72})`. -/
theorem siegel_blocks {Siegel : ℕ → Prop} (hB : TheoremBInput Siegel) {c : ℝ} (hc : 0 < c) :
    ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y → Siegel Y → (D Exc Y : ℝ) ≤ c * (Y : ℝ) ^ (0.72 : ℝ) := by
  obtain ⟨Y1, hY1⟩ := hB
  obtain ⟨Y2, hY2⟩ := siegel_absorb hc
  refine ⟨max Y1 Y2, fun Y hY hS => ?_⟩
  have h1 := hY1 Y (lt_of_le_of_lt (le_max_left _ _) hY) hS
  have h2 := hY2 Y (lt_of_le_of_lt (le_max_right _ _) hY)
  have h3 : (D Exc Y : ℝ) ≤ E Y := by rw [E_eq_T]; exact_mod_cast D_le_T Exc Y
  linarith

/-- CONDITIONAL ON Theorem B and `NonSiegelInputLittleO`: Theorem 1, `E(X) < X^{0.72}` for
large `X`. -/
theorem pintz_of_inputs_littleO {Siegel : ℕ → Prop} (hB : TheoremBInput Siegel)
    (hA : NonSiegelInputLittleO Siegel) : EventuallyBelow 0.72 := by
  have h := eventually_lt_of_littleO Exc (α := 0.72) (by norm_num) (fun c hc => by
    obtain ⟨Y1, hY1⟩ := siegel_blocks hB hc
    obtain ⟨Y2, hY2⟩ := hA c hc
    refine ⟨max Y1 Y2, fun Y hY => ?_⟩
    by_cases hS : Siegel Y
    · exact hY1 Y (lt_of_le_of_lt (le_max_left _ _) hY) hS
    · exact hY2 Y (lt_of_le_of_lt (le_max_right _ _) hY) hS)
  obtain ⟨X0, hX0⟩ := h
  exact ⟨X0, fun X hX => by rw [E_eq_T]; exact hX0 X hX⟩

/-- CONDITIONAL ON Theorem B and `NonSiegelInput` at some `ϑ' > 0.28` with any constant:
Theorem 1. The slack `ϑ' > 0.28` absorbs the `O_ε` constants of (2.29). -/
theorem pintz_of_inputs {Siegel : ℕ → Prop} {ϑ C : ℝ} (hϑ : 0.28 < ϑ)
    (hB : TheoremBInput Siegel) (hA : NonSiegelInput Siegel ϑ C) : EventuallyBelow 0.72 := by
  apply pintz_of_inputs_littleO hB
  intro c hc
  obtain ⟨Y1, hY1⟩ := hA
  -- the non-Siegel blocks satisfy the `o` bound by `eventually_lt_of_bigO`'s absorption step
  have ht : Tendsto (fun Y : ℕ => |C| * (Y : ℝ) ^ (-(ϑ - 0.28))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < ϑ - 0.28)).comp
      tendsto_natCast_atTop_atTop).const_mul |C|
    simpa using this
  obtain ⟨Y2, hY2⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
  refine ⟨max Y1 Y2, fun Y hY hS => ?_⟩
  have hYpos : (0 : ℝ) < Y := by
    have := lt_of_le_of_lt (Nat.zero_le _) hY; exact_mod_cast this
  have hs := hY2 Y ((le_max_right _ _).trans hY.le)
  have hsplit : (Y : ℝ) ^ (1 - ϑ) = (Y : ℝ) ^ (0.72 : ℝ) * (Y : ℝ) ^ (-(ϑ - 0.28)) := by
    rw [← rpow_add hYpos]; ring_nf
  have hYa : 0 < (Y : ℝ) ^ (0.72 : ℝ) := rpow_pos_of_pos hYpos _
  calc (D Exc Y : ℝ) ≤ C * (Y : ℝ) ^ (1 - ϑ) := hY1 Y (lt_of_le_of_lt (le_max_left _ _) hY) hS
    _ ≤ |C| * (Y : ℝ) ^ (1 - ϑ) := mul_le_mul_of_nonneg_right (le_abs_self C)
          (rpow_nonneg hYpos.le _)
    _ = (|C| * (Y : ℝ) ^ (-(ϑ - 0.28))) * (Y : ℝ) ^ (0.72 : ℝ) := by rw [hsplit]; ring
    _ ≤ c * (Y : ℝ) ^ (0.72 : ℝ) := mul_le_mul_of_nonneg_right hs.le hYa.le

/-- Vacuity of the Siegel split: with `Siegel` never true, `TheoremBInput` holds outright. -/
theorem vacuity_theoremB : TheoremBInput (fun _ => False) := ⟨0, fun _ _ h => h.elim⟩

/-! ### Case 8 with slack in `A` -/

/-- Case 8, (9.36), for every weight `e^{-2Aλ}` with `A ≥ 7/2`, so for `ϑ = 1/A ≤ 2/7`, a
range that contains `ϑ' ∈ (0.28, 0.2857]`. The second term `2.87 · 10.4 · λ^{11/7}` is taken as
printed at `A = 25/7`; Section 9 was not reachable this run to check whether it depends on `A`. -/
theorem case8_A {A l : ℝ} (hA : 7 / 2 ≤ A) (h0 : 0 < l) (h1 : l ≤ 0.04) :
    exp (-(2 * A) * l) + 2.87 * 10.4 * l ^ (11 / 7 : ℝ) < 1 := by
  have he : exp (-(2 * A) * l) ≤ exp (-(50 / 7) * l) + (exp (-7 * l) - exp (-(50 / 7) * l)) := by
    have : exp (-(2 * A) * l) ≤ exp (-7 * l) := exp_le_exp.mpr (by nlinarith)
    linarith
  have hq : l ^ (4 / 7 : ℝ) ≤ 0.1675 := by
    have hp : 0 ≤ l ^ (4 / 7 : ℝ) := rpow_nonneg h0.le _
    have h7 : (l ^ (4 / 7 : ℝ)) ^ (7 : ℕ) = l ^ 4 := by
      rw [← rpow_natCast, ← rpow_mul h0.le]; norm_num
    have hl4 : l ^ 4 ≤ (0.04 : ℝ) ^ 4 := pow_le_pow_left₀ h0.le h1 4
    by_contra hc
    push Not at hc
    have : (0.1675 : ℝ) ^ 7 < (l ^ (4 / 7 : ℝ)) ^ 7 :=
      pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [h7] at this
    norm_num at this hl4; linarith
  have hsplit : l ^ (11 / 7 : ℝ) = l * l ^ (4 / 7 : ℝ) := by
    rw [show (11 / 7 : ℝ) = 1 + 4 / 7 by norm_num, rpow_add h0, rpow_one]
  have hb : 2.87 * 10.4 * l ^ (11 / 7 : ℝ) ≤ 5 * l := by
    rw [hsplit]; nlinarith
  have := Pintz2018.case8_core h0 h1
  linarith

end LeanLab.ExceptionalSet.Pintz2018Reduction

#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.T_le
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.eventually_lt_of_littleO
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.eventually_lt_of_bigO
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.not_eventually_lt_true
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.pintz_of_inputs
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.pintz_of_inputs_littleO
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.case8_A
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.theta_admissible
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.one_sub_theta
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.A_val
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.siegel_exponent
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.T_split
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.T_mono
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.D_le_T
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.vacuity_littleO
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.E_eq_T
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.siegel_absorb
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.siegel_blocks
#print axioms LeanLab.ExceptionalSet.Pintz2018Reduction.vacuity_theoremB
