/-
P0029 Bhowmik, Grimmelt, The exceptional set of the Goldbach problem, arXiv 2607.27282v2,
Theorem 8.2 on pages 31 and 32, with a general exception exponent `σ` in place of `3/5`.
Unit U-6726, idea I-0091, second half.

The proof of Theorem 8.2 uses `3/5` in two places only: the `X^{3/5}` exceptions of (8.4), and the
`X^{3/5+ε}` exceptions of Proposition 8.1, which come from Vinogradov's minor arc bound and force
`ϑ ≥ 2/5`, page 31. A minor arc bound `X^{(1+σ)/2}` gives exceptions `X^{σ+ε}` and needs `ϑ ≥ 1 - σ`,
so `r̃ = X^{1/A} < X^{1-σ} ≤ R`, which is `σ < 1 - 1/A`, the condition used on page 32.
At MPR's `19/24`, `σ = 2 · 19/24 - 1 = 7/12` and the condition `A > 5/2` becomes `A > 12/5`.

STATEMENTS, each Lean statement with its plain math twin, source and vacuity test.

* `HL84σ σ r δ X`. Twin: `δ 𝔖(N) N ≤ r₂(N) ≤ (2 - δ) 𝔖(N) N` for all but at most `X^σ` even
  `N ∈ [X/2, X]` with `r ∣ N`. Source (8.4), page 31, with `X^σ` for `X^{3/5}`.
  `HL84σ (3/5) = HL84` by `rfl`, `HL84σ_three_fifths`. Vacuity: `vacuity_HL84σ`, it holds at
  `r = 1`, `X = 1` for every `σ`, `δ`.
* `Prop81AtMultiplesσ σ`. Twin: for `δ ∈ (0,1)` there is `c > 0` such that for each `A > 0` with
  `σ < 1 - 1/A` there is `r₀` so that for every `r̃ ≥ r₀` and primitive real `χ̃` mod `r̃` with a real
  zero `β ∈ (1 - c/log X, 1)`, `X = r̃^A`, some set `B` with `|B| + X^σ` below the number of even
  multiples of `r̃` in `[X/2, X]` has, for every other such multiple `N`,
  `r₂(N) = (1 + χ̃(-1) b) 𝔖(N) N + E`, `|b - 1| < 3δ/4`, `|E| ≤ δ/4 𝔖(N) N`.
  Source: page 32, the consequence of Proposition 8.1, page 30, (8.3) with `X^{σ+ε}` exceptions
  for `X^{3/5+ε}`, and (8.1). CITED, a hypothesis Prop; at `σ = 3/5` it is exactly the lab's
  `Prop81AtMultiples`, `prop81σ_three_fifths`. For `σ = 7/12` it is what Proposition 8.1 would
  give with `ϑ = 5/12` from a minor arc bound `X^{19/24+ε}` for all but `X^{7/12+ε}` even `N`;
  that input is NOT in the paper and NOT in the lab. Vacuity: the range condition holds at
  `A = 2.45`, `σ = 7/12`, `vacuity_range_7_12`; `0 < A` is needed, else the conclusion
  `|B| + X^σ < 0` would make the Prop false and the theorem empty.
* `Theorem82σ σ`. Twin: for `δ ∈ (0,1)` there is `c > 0` such that for each `A > 0` with
  `σ < 1 - 1/A` there is `r₀` so that for `r̃ ≥ r₀`, `X = r̃^A`, (8.4) with `X^σ` exceptions implies
  no primitive real character mod `r̃` has a real zero `β > 1 - c/log X`. Source Theorem 8.2,
  page 31, with `σ` for `3/5`. `theorem82σ_three_fifths`: `Theorem82σ (3/5) ↔ Theorem82`.
* `theorem82σ_of_prop81σ σ : Prop81AtMultiplesσ σ → Theorem82σ σ`, any real `σ`.
  PROVED CONDITIONAL ON `Prop81AtMultiplesσ σ`, following `theorem82_of_prop81`.
* `range_three_fifths`: `0 < A ∧ 3/5 < 1 - 1/A ↔ 5/2 < A`.
  `range_seven_twelfths`: `0 < A ∧ 7/12 < 1 - 1/A ↔ 12/5 < A`.
  `mpr_sigma`: `2 · 19/24 - 1 = 7/12`.
  `rpow_inv_le_five_twelfths_iff`: for `X > 1`, `A > 0`, `X^{1/A} ≤ X^{5/12} ↔ 12/5 ≤ A`.
  `r_lt_R_sigma`: for `r > 1`, `A > 0`, `σ < 1 - 1/A`, `r < (r^A)^{1-σ}`, so `r̃ < R = X^{1-σ}`.

KNOWN-LIKELY, I-0091: the paper's own argument with another minor arc exponent; not claimed new.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ExceptionalSet.BhowmikGrimmelt2026

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset

noncomputable section

/-- (8.4) with at most `X^σ` exceptions among the even multiples of `r` in `[X/2, X]`. -/
def HL84σ (σ : ℝ) (r : ℕ) (δ X : ℝ) : Prop :=
  (((evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N))).card : ℝ) ≤ X ^ σ

theorem HL84σ_three_fifths (r : ℕ) (δ X : ℝ) : HL84σ (3 / 5) r δ X ↔ HL84 r δ X := Iff.rfl

/-- Theorem 8.2 with exception exponent `σ` and range `0 < A`, `σ < 1 - 1/A`. -/
def Theorem82σ (σ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 < A → σ < 1 - 1 / A →
    ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
    HL84σ σ r δ ((r : ℝ) ^ A) → ¬ HasRealZeroAbove r (1 - c / Real.log ((r : ℝ) ^ A))

/-- The page 32 consequence of Proposition 8.1 with `X^σ` in place of `X^{3/5}`. CITED. -/
def Prop81AtMultiplesσ (σ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 < A → σ < 1 - 1 / A →
    ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
    ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → (∀ a, (χ a).im = 0) →
    (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ β = 0) →
    ∃ B : Finset ℕ, (B.card : ℝ) + ((r : ℝ) ^ A) ^ σ < (evenMult r ((r : ℝ) ^ A)).card ∧
      ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
        |E| ≤ δ / 4 * (Sing N * N) ∧ r2 N = (1 + (χ (-1)).re * b) * (Sing N * N) + E

/-! ### Exponent arithmetic -/

theorem range_three_fifths (A : ℝ) : (0 < A ∧ (3 / 5 : ℝ) < 1 - 1 / A) ↔ 5 / 2 < A := by
  constructor
  · rintro ⟨hA, h⟩
    have : 1 / A < 2 / 5 := by linarith
    rw [div_lt_div_iff₀ hA (by norm_num)] at this; linarith
  · intro h
    have hA : 0 < A := by linarith
    refine ⟨hA, ?_⟩
    have : 1 / A < 2 / 5 := by rw [div_lt_div_iff₀ hA (by norm_num)]; linarith
    linarith

theorem range_seven_twelfths (A : ℝ) : (0 < A ∧ (7 / 12 : ℝ) < 1 - 1 / A) ↔ 12 / 5 < A := by
  constructor
  · rintro ⟨hA, h⟩
    have : 1 / A < 5 / 12 := by linarith
    rw [div_lt_div_iff₀ hA (by norm_num)] at this; linarith
  · intro h
    have hA : 0 < A := by linarith
    refine ⟨hA, ?_⟩
    have : 1 / A < 5 / 12 := by rw [div_lt_div_iff₀ hA (by norm_num)]; linarith
    linarith

/-- MPR's minor arc exponent `19/24` gives the exception exponent `2 · 19/24 - 1 = 7/12`. -/
theorem mpr_sigma : (2 : ℝ) * (19 / 24) - 1 = 7 / 12 := by norm_num

/-- `r̃ = X^{1/A} ≤ X^{5/12}` exactly when `A ≥ 12/5`, for `X > 1`, `A > 0`. -/
theorem rpow_inv_le_five_twelfths_iff {X A : ℝ} (hX : 1 < X) (hA : 0 < A) :
    X ^ (1 / A) ≤ X ^ (5 / 12 : ℝ) ↔ 12 / 5 ≤ A := by
  rw [Real.rpow_le_rpow_left_iff hX, div_le_div_iff₀ hA (by norm_num)]
  constructor <;> intro h <;> linarith

/-- The same in terms of `r̃`: `r ≤ (r^A)^{5/12}` exactly when `A ≥ 12/5`, for `r > 1`, `A > 0`. -/
theorem r_le_five_twelfths_iff {r A : ℝ} (hr : 1 < r) (hA : 0 < A) :
    r ≤ (r ^ A) ^ (5 / 12 : ℝ) ↔ 12 / 5 ≤ A := by
  rw [← Real.rpow_mul (by linarith)]
  have h1 : r ≤ r ^ (A * (5 / 12 : ℝ)) ↔ r ^ (1 : ℝ) ≤ r ^ (A * (5 / 12 : ℝ)) := by
    rw [Real.rpow_one]
  rw [h1, Real.rpow_le_rpow_left_iff hr]
  constructor <;> intro h <;> linarith

/-- `r̃ < R = X^{1-σ}` in the range of `Theorem82σ`. -/
theorem r_lt_R_sigma {σ A r : ℝ} (hA : 0 < A) (hσ : σ < 1 - 1 / A) (hr : 1 < r) :
    r < (r ^ A) ^ (1 - σ) := by
  rw [← Real.rpow_mul (by linarith)]
  conv_lhs => rw [← Real.rpow_one r]
  rw [Real.rpow_lt_rpow_left_iff hr]
  have h1 : 1 / A < 1 - σ := by linarith
  have h2 : A * (1 / A) = 1 := by field_simp
  nlinarith

/-- Vacuity test: the range holds at `A = 2.45`, `σ = 7/12`. -/
theorem vacuity_range_7_12 : (0 : ℝ) < 2.45 ∧ (7 / 12 : ℝ) < 1 - 1 / 2.45 := by norm_num

/-- Vacuity test: (8.4) with `X^σ` exceptions holds at `r = 1`, `X = 1`. -/
theorem vacuity_HL84σ (σ δ : ℝ) : HL84σ σ 1 δ 1 := by
  have h := vacuity_HL84 δ
  unfold HL84 at h
  unfold HL84σ
  simpa [Real.one_rpow] using h

/-! ### σ = 3/5 recovers the existing statements -/

theorem theorem82σ_three_fifths : Theorem82σ (3 / 5) ↔ Theorem82 := by
  constructor
  · intro h δ hδ hδ1
    obtain ⟨c, hc, hA⟩ := h δ hδ hδ1
    refine ⟨c, hc, fun A hA52 => ?_⟩
    have := (range_three_fifths A).mpr hA52
    exact hA A this.1 this.2
  · intro h δ hδ hδ1
    obtain ⟨c, hc, hA⟩ := h δ hδ hδ1
    exact ⟨c, hc, fun A h0 h1 => hA A ((range_three_fifths A).mp ⟨h0, h1⟩)⟩

theorem prop81σ_three_fifths : Prop81AtMultiplesσ (3 / 5) ↔ Prop81AtMultiples := by
  constructor
  · intro h δ hδ hδ1
    obtain ⟨c, hc, hA⟩ := h δ hδ hδ1
    refine ⟨c, hc, fun A hA52 => ?_⟩
    have := (range_three_fifths A).mpr hA52
    exact hA A this.1 this.2
  · intro h δ hδ hδ1
    obtain ⟨c, hc, hA⟩ := h δ hδ hδ1
    exact ⟨c, hc, fun A h0 h1 => hA A ((range_three_fifths A).mp ⟨h0, h1⟩)⟩

/-! ### The theorem -/

/-- Pigeonhole with `X^σ` exceptions. -/
theorem exists_good_multipleσ {σ : ℝ} {r : ℕ} {δ X : ℝ} (B : Finset ℕ) (h84 : HL84σ σ r δ X)
    (hcard : (B.card : ℝ) + X ^ σ < (evenMult r X).card) :
    ∃ N ∈ evenMult r X, N ∉ B ∧ δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N := by
  by_contra hno
  push Not at hno
  have hsub : evenMult r X ⊆ B ∪ (evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N)) := by
    intro N hN
    by_cases hB : N ∈ B
    · exact mem_union_left _ hB
    · apply mem_union_right
      rw [mem_filter]
      refine ⟨hN, fun h => ?_⟩
      exact absurd h.2 (not_le.mpr (hno N hN hB h.1))
  have h1 := card_le_card hsub
  have h2 := card_union_le B ((evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N)))
  have h3 : ((evenMult r X).card : ℝ) ≤ B.card + ((evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N))).card := by
    exact_mod_cast h1.trans h2
  unfold HL84σ at h84
  linarith

/-- Theorem 8.2 with exception exponent `σ`, CONDITIONAL ON `Prop81AtMultiplesσ σ`. -/
theorem theorem82σ_of_prop81σ (σ : ℝ) (h81 : Prop81AtMultiplesσ σ) : Theorem82σ σ := by
  intro δ hδ hδ1
  obtain ⟨c, hc, hA⟩ := h81 δ hδ hδ1
  refine ⟨c, hc, fun A hA0 hAσ => ?_⟩
  obtain ⟨r0, hr0⟩ := hA A hA0 hAσ
  refine ⟨max r0 1, fun r _ hr h84 => ?_⟩
  rintro ⟨χ, hprim, hreal, hzero⟩
  obtain ⟨B, hBcard, hBN⟩ := hr0 r (le_of_max_le_left hr) χ hprim hreal hzero
  obtain ⟨N, hN, hNB, hlo, hhi⟩ := exists_good_multipleσ B h84 hBcard
  obtain ⟨b, E, hb, hE, hrN⟩ := hBN N hN hNB
  have hNpos : (0 : ℝ) < N := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast le_of_max_le_right hr
    have hX : (1 : ℝ) ≤ (r : ℝ) ^ A := Real.one_le_rpow hr1 hA0.le
    unfold evenMult at hN
    rw [mem_filter, mem_Icc] at hN
    have hc : 0 < ⌈(r : ℝ) ^ A / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
    exact_mod_cast lt_of_lt_of_le hc hN.1.1
  have hM : 0 < Sing N * N := mul_pos (Sing_pos N) hNpos
  have hs : (χ (-1)).re = 1 ∨ (χ (-1)).re = -1 := by
    rcases sq_eq_one_of_dirichlet_neg_one χ with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  refine dichotomy hM hs hb hE hrN ⟨?_, ?_⟩
  · linarith [show δ * Sing N * N = δ * (Sing N * N) by ring]
  · linarith [show (2 - δ) * Sing N * N = (2 - δ) * (Sing N * N) by ring]

/-- The MPR case: Theorem 8.2 for `A > 12/5` with `X^{7/12}` exceptions,
CONDITIONAL ON `Prop81AtMultiplesσ (7/12)`. -/
theorem theorem82_seven_twelfths (h81 : Prop81AtMultiplesσ (7 / 12)) :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 12 / 5 < A →
    ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
    HL84σ (7 / 12) r δ ((r : ℝ) ^ A) → ¬ HasRealZeroAbove r (1 - c / Real.log ((r : ℝ) ^ A)) := by
  intro δ hδ hδ1
  obtain ⟨c, hc, hA⟩ := theorem82σ_of_prop81σ _ h81 δ hδ hδ1
  exact ⟨c, hc, fun A h => hA A ((range_seven_twelfths A).mpr h).1 ((range_seven_twelfths A).mpr h).2⟩

end

end LeanLab.ExceptionalSet.BG2026
