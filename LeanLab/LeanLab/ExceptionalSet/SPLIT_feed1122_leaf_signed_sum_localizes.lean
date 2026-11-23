/-
Split of the LEAF statement `leaf_signed_sum_localizes` of
`LeanLab.ExceptionalSet.SPLIT_leaf_gap_core`, unit U-1539, P0082 Bruedern and Perelli 1998.

The parent says that a value of the parity signed sum
`Σ_{N/2 < n ≤ N} (-1)^{ν_n} e(α F(n))` above `N ℰ^(-1/3)`, with `|α| ≤ F γ N ^ δ`, forces `α`
within `F γ N ^ (δ - 1)` of a half-integer.  The paper's argument is §7, p. 369 to 370, the
proof of Lemma 9: the parity condition is expanded in a smoothed Fourier series, display (41),
so that the sum becomes `Σ_h c_h Φ(α + h/2)` up to an error, with `Φ` the full sum and the
coefficients bounded by display (40); the terms with large `|h|` are dropped; and Theorem 2
bounds every remaining `Φ(α + h/2)` with `|α + h/2| > F γ N ^ (δ - 1)`.  The split follows
those two steps:

* `leaf_signed_fourier_large_translate`, displays (40) and (41) with the large `|h|` removed:
  a large signed sum forces a large full sum `‖Φ(α + h/2)‖ > N ℰ^(-1)` at some integer
  `|h| ≤ ℰ`.
* `leaf_full_sum_translate_range`, Theorem 2 in the range of the translates: the full sum is at
  most `N ℰ^(-1)` for `F γ N ^ (δ - 1) < |β| ≤ F γ N ^ δ + ℰ`.  This one is proved here from the
  lab's statement `theorem2` of `State1539` and the proved comparisons of
  `SPLIT_feed1122_leaf_full_sum_minor_arc`, up to the LEAF `leaf_translate_large_beta` for the
  translates beyond the range of Theorem 2, which is eventually empty when `δ < (γ - 1) / 2`.

The assembly then takes `-h` as the required integer.  The paper takes `Δ = ℰ^(-1/3)` and
`|h| ≤ ℰ^(2/3)`; with those choices the error of (41) and the tail beyond `ℰ^(2/3)` are both of
the size of the threshold `N ℰ^(-1/3)` itself, so the leaf allows `|h| ≤ ℰ`, which leaves room
for `Δ = ℰ^(-1/2)`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_full_sum_minor_arc

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: the truncated Fourier expansion step, displays (40) and (41), p. 370, applied to the
parity signed sum, together with the removal of the terms with large `|h|`.  For
`1 < γ < 3/2` and `0 < δ < 1`, uniformly in every sufficiently small `κ`, eventually: if
`|α| ≤ F γ N ^ δ` and the signed sum exceeds `N ℰ^(-1/3)` in modulus, then some integer `h`
with `|h| ≤ ℰ` has `‖Σ_{N/2 < n ≤ N} e((α + h/2) F(n))‖ > N ℰ^(-1)`.  HARD: it needs the
smoothed square wave of display (40) and the count of `n` with `F(n)` near an integer, which
is Lemma 4 and display (31) of the paper. -/
theorem leaf_signed_fourier_large_translate (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
          N * calE γ κ N ^ (-(1 / 3 : ℝ))
              < ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ →
        ∃ h : ℤ, |(h : ℝ)| ≤ calE γ κ N ∧
          N * calE γ κ N ^ (-1 : ℝ)
            < ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ := by
  sorry

/-- LEAF: the full sum on the translates beyond the range of Theorem 2.  For `1 < γ < 3/2` and
`0 < δ < 1`, uniformly in every sufficiently small `κ`, eventually: if
`F γ N ^ ((γ - 1) / 2) < |β| ≤ F γ N ^ δ + ℰ` then `‖Σ_{N/2 < n ≤ N} e(β F(n))‖ ≤ N ℰ^(-1)`.
This is the part of the translate range of Lemma 9, p. 370, outside the range `C < γ - 1` of
Theorem 2, p. 354.  For `δ < (γ - 1) / 2` it is eventually empty, since `F γ N ^ δ + ℰ` is then
below `F γ N ^ ((γ - 1) / 2)`; the paper's `δ` is small.  HARD: an exponential sum estimate for
large `β`. -/
theorem leaf_translate_large_beta (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
        F γ N ^ ((γ - 1) / 2) < |β| → |β| ≤ F γ N ^ δ + calE γ κ N →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (β * F γ n)‖ ≤ N * calE γ κ N ^ (-1 : ℝ) := by
  sorry

/-- `ℰ` at `3κ` to the power `-1/3` is `ℰ` at `κ` to the power `-1`. -/
private theorem calE_three_mul (γ κ : ℝ) (N : ℕ) :
    calE γ (3 * κ) N ^ (-(1 / 3 : ℝ)) = calE γ κ N ^ (-1 : ℝ) := by
  unfold calE
  rw [← Real.exp_mul, ← Real.exp_mul]
  congr 1
  ring

/-- Theorem 2, p. 354, in the range of the translates `α + h/2` of Lemma 9, p. 370: for
`F γ N ^ (δ - 1) < |β| ≤ F γ N ^ δ + ℰ` the full sum is at most `N ℰ^(-1)`, uniformly in every
sufficiently small `κ`.  Proved from the lab's statement `theorem2` of `State1539` through the
proved transport and comparisons of `SPLIT_feed1122_leaf_full_sum_minor_arc`, and from
`leaf_translate_large_beta` beyond the range of Theorem 2. -/
theorem leaf_full_sum_translate_range (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
        F γ N ^ (δ - 1) < |β| → |β| ≤ F γ N ^ δ + calE γ κ N →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (β * F γ n)‖ ≤ N * calE γ κ N ^ (-1 : ℝ) := by
  have hγ1 : 0 < γ - 1 := by linarith
  obtain ⟨κT, B, hκT, hT⟩ := theorem2 γ hγ₁ hγ₂ (1 - δ / 2) (3 * (γ - 1) / 4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  set κ₁ : ℝ := min κT 1 with hκ₁
  have hκ₁pos : 0 < κ₁ := lt_min hκT one_pos
  obtain ⟨κ₂, hκ₂pos, hlarge⟩ := leaf_translate_large_beta γ δ hγ₁ hγ₂ hδ₀ hδ₁
  refine ⟨min (κ₁ / 3) κ₂, lt_min (by linarith) hκ₂pos, ?_⟩
  intro κ hκ hκle
  have hκ3 : 3 * κ ≤ κ₁ := by
    have := le_trans hκle (min_le_left _ _); linarith
  obtain ⟨N₁, hN₁⟩ := hlarge κ hκ (le_trans hκle (min_le_right _ _))
  obtain ⟨N₂, hN₂⟩ := leaf_fsm_low_end γ δ (1 - δ / 2) hγ₁ hδ₀ hδ₁ (by linarith)
  obtain ⟨N₃, hN₃⟩ := leaf_fsm_high_end γ ((γ - 1) / 2) (3 * (γ - 1) / 4) hγ₁ (by linarith)
    (by linarith)
  obtain ⟨N₄, hN₄⟩ := leaf_fsm_saving γ κ₁ (max B 0) hγ₁ hγ₂ hκ₁pos (min_le_right _ _)
  refine ⟨N₁ + N₂ + N₃ + N₄ + 2, ?_⟩
  intro N hN β hlow hhigh
  by_cases hcase : |β| ≤ F γ N ^ ((γ - 1) / 2)
  · have hM1 : 1 ≤ N / 2 := by omega
    have hβ1 : F γ (2 * ((N / 2 : ℕ) : ℝ)) ^ (-(1 - δ / 2)) ≤ |β| :=
      le_trans (hN₂ N (by omega)) hlow.le
    have hβ2 : |β| ≤ F γ ((N / 2 : ℕ) : ℝ) ^ (3 * (γ - 1) / 4) :=
      le_trans hcase (hN₃ N (by omega))
    have hTb := hT (N / 2) hM1 β hβ1 hβ2
    have hL : 0 ≤ Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ) := by
      apply Real.rpow_nonneg
      apply Real.log_nonneg
      exact_mod_cast hM1
    have hM0 : (0 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hexp : Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
        ≤ Real.exp (-κ₁ * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
      apply Real.exp_le_exp.mpr
      have : κ₁ ≤ κT := min_le_left _ _
      nlinarith
    have hB : B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
        ≤ max B 0 * ((N / 2 : ℕ) : ℝ) *
            Real.exp (-κ₁ * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
      have h1 : B * ((N / 2 : ℕ) : ℝ) ≤ max B 0 * ((N / 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hM0
      have h2 : 0 ≤ max B 0 * ((N / 2 : ℕ) : ℝ) := mul_nonneg (le_max_right _ _) hM0
      calc B * ((N / 2 : ℕ) : ℝ) * Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ))
          ≤ max B 0 * ((N / 2 : ℕ) : ℝ) *
              Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp h2
    have hS := hN₄ N (by omega) (3 * κ) (by linarith) hκ3
    rw [calE_three_mul] at hS
    have hD := leaf_fsm_dyadic_transport γ β N
    have hTb' : ‖expSumF γ β (N / 2)‖ ≤ B * ((N / 2 : ℕ) : ℝ) *
        Real.exp (-κT * Real.log ((N / 2 : ℕ) : ℝ) ^ (3 - 2 * γ)) := by
      simpa using hTb
    have hE : 0 ≤ (N : ℝ) * calE γ κ N ^ (-1 : ℝ) := by
      apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.rpow_nonneg
      unfold calE
      exact (Real.exp_pos _).le
    linarith
  · push_neg at hcase
    exact hN₁ N (by omega) β hcase hhigh

/-- `leaf_signed_sum_localizes` from the two leaves. -/
theorem leaf_signed_sum_localizes_split (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
          N * calE γ κ N ^ (-(1 / 3 : ℝ))
              < ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ →
        ∃ h : ℤ, |α - h / 2| ≤ F γ N ^ (δ - 1) := by
  obtain ⟨κ₁, hκ₁, hF⟩ := leaf_signed_fourier_large_translate γ δ hγ₁ hγ₂ hδ₀ hδ₁
  obtain ⟨κ₂, hκ₂, hT⟩ := leaf_full_sum_translate_range γ δ hγ₁ hγ₂ hδ₀ hδ₁
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, ?_⟩
  intro κ hκ hκle
  obtain ⟨N₁, hN₁⟩ := hF κ hκ (le_trans hκle (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hT κ hκ (le_trans hκle (min_le_right _ _))
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN α hα hlarge
  obtain ⟨h, hh, hbig⟩ := hN₁ N (le_trans (le_max_left _ _) hN) α hα hlarge
  refine ⟨-h, ?_⟩
  have hrw : α - ((-h : ℤ) : ℝ) / 2 = α + (h : ℝ) / 2 := by push_cast; ring
  rw [hrw]
  by_contra hfar
  push_neg at hfar
  have hE : 0 < calE γ κ N := by
    unfold calE
    exact Real.exp_pos _
  have hβ : |α + (h : ℝ) / 2| ≤ F γ N ^ δ + calE γ κ N := by
    have h1 : |α + (h : ℝ) / 2| ≤ |α| + |(h : ℝ) / 2| := abs_add_le _ _
    have h2 : |(h : ℝ) / 2| = |(h : ℝ)| / 2 := by
      rw [abs_div, abs_two]
    linarith
  have hsmall := hN₂ N (le_trans (le_max_right _ _) hN) (α + (h : ℝ) / 2) hfar hβ
  linarith

end LeanLab.ExceptionalSet.U1539
