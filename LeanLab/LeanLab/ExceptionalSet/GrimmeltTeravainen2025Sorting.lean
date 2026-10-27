/-
P0039 L. Grimmelt, J. Teräväinen, arXiv 2508.16400v2, copy papers/P0039.pdf. Unit U-6790,
CLOUD 20261021T0117Z-cloud55. AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.

The last sentence of both cases of the proof of Theorem 1.1, p.67 and p.69: the exceptions are
counted for `m ∈ [5N/4, 7N/4]`, and Theorem 1.1 follows "after sorting m into intervals of the
form [5N/4, 7N/4]". We prove this sorting step for any set of bad integers: a power saving
bound on every window `[5N/4, 7N/4]` gives a power saving bound on `[1, X]`. Applied to the
`m ≡ 4 mod 6` that are not sums of two Chen primes, Theorem 1.1 in the lab's form `GT11` is
PROVED CONDITIONAL ON `IntervalBound`, the window statement that Sections 3 to 8 establish.
-/
import LeanLab.ExceptionalSet.ChenPrimes

open Finset

namespace LeanLab.ExceptionalSet.GT2025

open LeanLab.ExceptionalSet

/-- Bad integers in the window `5N/4 ≤ m ≤ 7N/4`. -/
noncomputable def cntI (Bad : ℕ → Prop) [DecidablePred Bad] (N : ℕ) : ℕ :=
  #{m ∈ range (2 * N + 1) | 5 * N ≤ 4 * m ∧ 4 * m ≤ 7 * N ∧ Bad m}

/-- Bad integers in `[1, X]`. -/
noncomputable def cnt (Bad : ℕ → Prop) [DecidablePred Bad] (X : ℕ) : ℕ :=
  #{m ∈ Icc 1 X | Bad m}

/-- A power saving on every window from some point on. -/
def WindowBound (Bad : ℕ → Prop) [DecidablePred Bad] : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (cntI Bad N : ℝ) ≤ C * (N : ℝ) ^ (1 - η)

/-- A power saving on `[1, X]` for every `X ≥ 1`, the shape of Theorem 1.1. -/
def PowerBound (Bad : ℕ → Prop) [DecidablePred Bad] : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ, ∀ X : ℕ, 1 ≤ X → (cnt Bad X : ℝ) ≤ K * (X : ℝ) ^ (1 - δ)

/-- One step of the sorting: for `X ≥ 23` and `N = ⌈4X/7⌉`, the integers in `(⌊3X/4⌋, X]`
lie in the window of `N`. -/
theorem cnt_step (Bad : ℕ → Prop) [DecidablePred Bad] {X : ℕ} (hX : 23 ≤ X) :
    cnt Bad X ≤ cnt Bad (3 * X / 4) + cntI Bad ((4 * X + 6) / 7) := by
  unfold cnt cntI
  refine le_trans (card_le_card ?_) (card_union_le _ _)
  intro m hm
  simp only [mem_filter, mem_Icc, mem_union, mem_range] at hm ⊢
  by_cases h : m ≤ 3 * X / 4
  · exact Or.inl ⟨⟨hm.1.1, h⟩, hm.2⟩
  · right
    refine ⟨by omega, by omega, by omega, hm.2⟩

/-- **The sorting step of p.67:** window bounds give a power saving bound. -/
theorem powerBound_of_windowBound (Bad : ℕ → Prop) [DecidablePred Bad]
    (h : WindowBound Bad) : PowerBound Bad := by
  obtain ⟨η, hη, C, N₀, hC⟩ := h
  set e : ℝ := min η (1 / 2) with he
  have he0 : 0 < e := lt_min hη (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have heη : e ≤ η := min_le_left _ _
  set a : ℝ := 1 - e with ha
  have ha0 : 0 < a := by linarith
  set θ : ℝ := (3 / 4 : ℝ) ^ a with hθ
  have hθ1 : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha0
  have hθ0 : 0 ≤ θ := by positivity
  set C' : ℝ := max C 0
  set X₁ : ℕ := max 23 (2 * N₀)
  set K : ℝ := max (X₁ : ℝ) (C' / (1 - θ))
  have hK0 : 0 ≤ K := le_trans (Nat.cast_nonneg _) (le_max_left _ _)
  have hKC : C' ≤ K * (1 - θ) := by
    have : C' / (1 - θ) ≤ K := le_max_right _ _
    rwa [div_le_iff₀ (by linarith)] at this
  refine ⟨e, he0, K, ?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
  intro hX1
  have hXa : (1 : ℝ) ≤ (X : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hX1) ha0.le
  by_cases hsmall : X < X₁
  · have h1 : (cnt Bad X : ℝ) ≤ X := by
      have : cnt Bad X ≤ X := by
        unfold cnt
        exact le_trans (card_filter_le _ _) (by simp)
      exact_mod_cast this
    have h2 : (X : ℝ) ≤ X₁ := by exact_mod_cast hsmall.le
    have h3 : (X₁ : ℝ) ≤ K := le_max_left _ _
    calc (cnt Bad X : ℝ) ≤ K := by linarith
      _ = K * 1 := by ring
      _ ≤ K * (X : ℝ) ^ a := mul_le_mul_of_nonneg_left hXa hK0
  · push Not at hsmall
    have h23 : 23 ≤ X := le_trans (le_max_left _ _) hsmall
    have hN0 : N₀ ≤ (4 * X + 6) / 7 := by
      have : 2 * N₀ ≤ X := le_trans (le_max_right _ _) hsmall
      omega
    set N := (4 * X + 6) / 7 with hN
    set Y := 3 * X / 4 with hY
    have hNX : N ≤ X := by omega
    have hN1 : 1 ≤ N := by omega
    have hY1 : 1 ≤ Y := by omega
    have hYX : Y < X := by omega
    have hstep := cnt_step Bad h23
    -- the window term
    have hwin : (cntI Bad N : ℝ) ≤ C' * (X : ℝ) ^ a := by
      have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      calc (cntI Bad N : ℝ) ≤ C * (N : ℝ) ^ (1 - η) := hC N hN0
        _ ≤ C' * (N : ℝ) ^ (1 - η) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ C' * (N : ℝ) ^ a :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith))
              (le_max_right _ _)
        _ ≤ C' * (X : ℝ) ^ a :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hNX) ha0.le)
              (le_max_right _ _)
    -- the recursive term
    have hrec : (cnt Bad Y : ℝ) ≤ K * θ * (X : ℝ) ^ a := by
      have hY' : (Y : ℝ) ≤ 3 / 4 * X := by
        have : 4 * Y ≤ 3 * X := by omega
        have : (4 * Y : ℝ) ≤ 3 * X := by exact_mod_cast this
        linarith
      calc (cnt Bad Y : ℝ) ≤ K * (Y : ℝ) ^ a := ih Y hYX hY1
        _ ≤ K * (3 / 4 * (X : ℝ)) ^ a :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hY' ha0.le) hK0
        _ = K * θ * (X : ℝ) ^ a := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    have hcast : (cnt Bad X : ℝ) ≤ cnt Bad Y + cntI Bad N := by exact_mod_cast hstep
    have hXa0 : 0 ≤ (X : ℝ) ^ a := by positivity
    calc (cnt Bad X : ℝ) ≤ K * θ * (X : ℝ) ^ a + C' * (X : ℝ) ^ a := by linarith
      _ = (K * θ + C') * (X : ℝ) ^ a := by ring
      _ ≤ K * (X : ℝ) ^ a := mul_le_mul_of_nonneg_right (by linarith) hXa0

/-- Vacuity of the sorting step: a nonempty bad set, the `m < 100` with `m ≡ 4 mod 6`, meets
`WindowBound` with `η = 1/2, C = 100`, so the hypotheses are satisfiable by a nonempty set. -/
theorem windowBound_vacuity : WindowBound (fun m => m % 6 = 4 ∧ m < 100) := by
  refine ⟨1 / 2, by norm_num, 100, 1, fun N hN => ?_⟩
  have h1 : (cntI (fun m => m % 6 = 4 ∧ m < 100) N : ℝ) ≤ 100 := by
    have : cntI (fun m => m % 6 = 4 ∧ m < 100) N ≤ 100 := by
      unfold cntI
      calc _ ≤ #(range 100) := by
              apply card_le_card
              intro m hm
              simp only [mem_filter, mem_range] at hm ⊢
              exact hm.2.2.2.2
        _ = 100 := card_range _
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - 1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  nlinarith

/-! ### Application to Theorem 1.1 -/

attribute [local instance] Classical.propDecidable

/-- The bad set of Theorem 1.1. -/
def ChenBad (m : ℕ) : Prop := m % 6 = 4 ∧ ¬ ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m

/-- **The window statement of p.67 and p.69:** for some `η > 0`, from some `N₀` on, at most
`C N^{1-η}` of the `m ∈ [5N/4, 7N/4]`, `m ≡ 4 mod 6`, are not sums of two Chen primes. The
paper proves it with `η = (δ₁/10)⁴`. Named input, not proved here. -/
def IntervalBound : Prop := WindowBound ChenBad

theorem echen_eq_cnt (N : ℕ) : EChen N = cnt ChenBad N := by
  unfold EChen cnt ChenBad
  congr 1
  convert rfl

/-- **Theorem 1.1, PROVED CONDITIONAL ON `IntervalBound`:** the sorting step of p.67. -/
theorem gt11_of_intervalBound (h : IntervalBound) : GT11 := by
  obtain ⟨δ, hδ, K, hK⟩ := powerBound_of_windowBound ChenBad h
  exact ⟨δ, hδ, K, fun N hN => by rw [echen_eq_cnt]; exact hK N hN⟩

/-- Conversely the window statement follows from `GT11`, so `IntervalBound` is equivalent to
Theorem 1.1 in the lab's form: the window form loses nothing. -/
theorem intervalBound_of_gt11 (h : GT11) : IntervalBound := by
  obtain ⟨δ, hδ, C, hC⟩ := h
  refine ⟨δ, hδ, max C 0 * 2, 1, fun N hN => ?_⟩
  have hsub : cntI ChenBad N ≤ cnt ChenBad (2 * N) := by
    unfold cntI cnt
    apply card_le_card
    intro m hm
    simp only [mem_filter, mem_range, mem_Icc] at hm ⊢
    refine ⟨⟨by omega, by omega⟩, hm.2.2.2⟩
  have h2N : 1 ≤ 2 * N := by omega
  have hb := hC (2 * N) h2N
  rw [echen_eq_cnt] at hb
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : ((2 * N : ℕ) : ℝ) ^ (1 - δ) ≤ 2 * (N : ℝ) ^ (1 - δ) := by
    push_cast
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    gcongr
    by_cases h1 : 1 - δ ≤ 1
    · calc (2 : ℝ) ^ (1 - δ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        _ = 2 := by norm_num
    · linarith
  calc (cntI ChenBad N : ℝ) ≤ cnt ChenBad (2 * N) := by exact_mod_cast hsub
    _ ≤ C * ((2 * N : ℕ) : ℝ) ^ (1 - δ) := hb
    _ ≤ max C 0 * ((2 * N : ℕ) : ℝ) ^ (1 - δ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (2 * (N : ℝ) ^ (1 - δ)) :=
        mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ = max C 0 * 2 * (N : ℝ) ^ (1 - δ) := by ring

end LeanLab.ExceptionalSet.GT2025
