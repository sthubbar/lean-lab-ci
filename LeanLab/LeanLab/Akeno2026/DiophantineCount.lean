/-
P0087 Akeno 2026 Lemma 2.3 equation 5 on pages 4 to 5.
Integer numerator and denominator intervals for the rational approximation count.
The full estimate is stated as a proposition. DiophantineBlocks supplies a proof.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Akeno2026.DiophantineCount
open Finset

noncomputable def denominatorRange (M : ℝ) : Finset ℤ := Finset.Ioc ⌊M⌋ ⌊2 * M⌋
noncomputable def numeratorRange (α δ : ℝ) (m : ℤ) : Finset ℤ :=
  Finset.Icc ⌈(m : ℝ) * (α - δ)⌉ ⌊(m : ℝ) * (α + δ)⌋
noncomputable def pairCount (α M δ : ℝ) : ℕ :=
  ∑ m ∈ denominatorRange M, (numeratorRange α δ m).card

/-- The absolute constant version of the printed Lemma 2.3 estimate. Proved in DiophantineBlocks. -/
def Lemma23Bound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 →
    |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
    ∀ M δ : ℝ, 0 < M → 0 < δ →
      (pairCount α M δ : ℝ) ≤ C * M * (1 / (q : ℝ) + q * δ + δ * M)

theorem mem_denominatorRange {M : ℝ} {m : ℤ} :
    m ∈ denominatorRange M ↔ M < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M := by
  simp only [denominatorRange, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

theorem numerator_bounds {α δ : ℝ} {m n : ℤ} (hm : 0 < (m : ℝ))
    (h : |α - (n : ℝ) / m| ≤ δ) :
    (m : ℝ) * (α - δ) ≤ n ∧ (n : ℝ) ≤ (m : ℝ) * (α + δ) := by
  obtain ⟨h0, h1⟩ := abs_le.mp h
  constructor
  · have hh := (le_div_iff₀ hm).mp (show α - δ ≤ (n : ℝ) / m by linarith)
    nlinarith
  · have hh := (div_le_iff₀ hm).mp (show (n : ℝ) / m ≤ α + δ by linarith)
    nlinarith

theorem mem_numeratorRange {α δ : ℝ} {m n : ℤ} (hm : 0 < (m : ℝ)) :
    n ∈ numeratorRange α δ m ↔ |α - (n : ℝ) / m| ≤ δ := by
  rw [numeratorRange, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · intro h
    apply abs_le.mpr
    have h0 := (le_div_iff₀ hm).mpr
      (show (α - δ) * (m : ℝ) ≤ n by nlinarith [h.1])
    have h1 := (div_le_iff₀ hm).mpr
      (show (n : ℝ) ≤ (α + δ) * m by nlinarith [h.2])
    constructor <;> linarith
  · exact numerator_bounds hm

/-- In the small delta case of page 4, a fixed denominator has at most one numerator. -/
theorem numerator_unique {α M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    (hsmall : M * δ < 1 / 4) {m n₁ n₂ : ℤ}
    (hm : M < (m : ℝ)) (hm' : (m : ℝ) ≤ 2 * M)
    (h1 : |α - (n₁ : ℝ) / m| ≤ δ) (h2 : |α - (n₂ : ℝ) / m| ≤ δ) : n₁ = n₂ := by
  have hm0 : 0 < (m : ℝ) := hM.trans hm
  have b1 := numerator_bounds hm0 h1
  have b2 := numerator_bounds hm0 h2
  have hmul := mul_le_mul_of_nonneg_left hm' hδ.le
  have hd1 : (-1 : ℝ) < (n₁ : ℝ) - (n₂ : ℝ) := by nlinarith [b1.1, b1.2, b2.1, b2.2]
  have hd2 : (n₁ : ℝ) - (n₂ : ℝ) < 1 := by nlinarith [b1.1, b1.2, b2.1, b2.2]
  have hi1 : (-1 : ℤ) < n₁ - n₂ := by exact_mod_cast hd1
  have hi2 : n₁ - n₂ < (1 : ℤ) := by exact_mod_cast hd2
  omega

/-- A real interval of length b minus a contains at most that length plus one integers. -/
theorem card_integer_interval_le {a b : ℝ} (hab : a ≤ b) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ b - a + 1 := by
  by_cases h : ⌈a⌉ ≤ ⌊b⌋
  · have hc := Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ (show ⌈a⌉ ≤ ⌊b⌋ + 1 by omega)
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hc
    push_cast at hr
    have hf := Int.floor_le b
    have he := Int.le_ceil a
    linarith
  · have he : Finset.Icc ⌈a⌉ ⌊b⌋ = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

theorem numerator_card_le {α δ : ℝ} {m : ℤ} (hδ : 0 ≤ δ) (hm : 0 ≤ (m : ℝ)) :
    ((numeratorRange α δ m).card : ℝ) ≤ 2 * δ * m + 1 := by
  have hab : (m : ℝ) * (α - δ) ≤ (m : ℝ) * (α + δ) := by nlinarith
  have h := card_integer_interval_le hab
  unfold numeratorRange
  nlinarith

theorem denominator_card_le {M : ℝ} (hM : 0 < M) :
    ((denominatorRange M).card : ℝ) ≤ 2 * M := by
  have hm : ⌊M⌋ ≤ ⌊2 * M⌋ := Int.floor_mono (by linarith)
  have hc := Int.card_Ioc_of_le ⌊M⌋ ⌊2 * M⌋ hm
  have hr := congrArg (fun z : ℤ => (z : ℝ)) hc
  push_cast at hr
  have hf := Int.floor_le (2 * M)
  have hn : (0 : ℤ) ≤ ⌊M⌋ := Int.floor_nonneg.mpr hM.le
  have hn' : (0 : ℝ) ≤ (⌊M⌋ : ℤ) := by exact_mod_cast hn
  unfold denominatorRange
  linarith

/-- The large delta branch of the page 4 proof, with an explicit constant 16. -/
theorem pairCount_large_delta {α M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    (hlarge : 1 / 4 ≤ M * δ) :
    (pairCount α M δ : ℝ) ≤ 16 * δ * M ^ 2 := by
  have hfiber : ∀ m ∈ denominatorRange M, ((numeratorRange α δ m).card : ℝ) ≤ 8 * δ * M := by
    intro m hm
    obtain ⟨hm0, hm1⟩ := mem_denominatorRange.mp hm
    have hc := numerator_card_le (α := α) hδ.le (hM.trans hm0).le
    have hmul := mul_le_mul_of_nonneg_left hm1 hδ.le
    nlinarith
  have hsum : (pairCount α M δ : ℝ) ≤ ((denominatorRange M).card : ℝ) * (8 * δ * M) := by
    unfold pairCount
    push_cast
    calc
      ∑ m ∈ denominatorRange M, ((numeratorRange α δ m).card : ℝ) ≤
          ∑ _m ∈ denominatorRange M, 8 * δ * M := Finset.sum_le_sum hfiber
      _ = ((denominatorRange M).card : ℝ) * (8 * δ * M) := by simp
  have hd := denominator_card_le hM
  have hmul := mul_le_mul_of_nonneg_right hd (show 0 ≤ 8 * δ * M by positivity)
  nlinarith

end LeanLab.Akeno2026.DiophantineCount
