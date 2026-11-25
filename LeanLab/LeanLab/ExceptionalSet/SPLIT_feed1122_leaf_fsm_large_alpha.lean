/-
Reduction of the LEAF statement `leaf_fsm_large_alpha` of
`LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_full_sum_minor_arc`, unit U-1539, P0082 Bruedern
and Perelli 1998, to the LEAF `leaf_translate_large_beta` of
`LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_signed_sum_localizes`.

The translate leaf covers every `β` with `F γ N ^ ((γ - 1) / 2) < |β| ≤ F γ N ^ δ + ℰ`, which
contains the range `F γ N ^ ((γ - 1) / 2) < |α| ≤ F γ N ^ δ` of `leaf_fsm_large_alpha`, and its
bound `N ℰ^(-1)` is eventually below `N ℰ^(-1/3) / 8`, since `ℰ = exp(κ (log N)^(3-2γ))`
tends to infinity.  So the two HARD leaves of the large range reduce to the single one,
`leaf_translate_large_beta`.  No new leaf.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_signed_sum_localizes

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- Comparison of the two thresholds.  For `γ < 3/2` and `κ > 0`, eventually
`N ℰ^(-1) ≤ N ℰ^(-1/3) / 8`, since `κ (log N)^(3-2γ)` tends to infinity.  Proved. -/
theorem calE_inv_le_third (γ κ : ℝ) (hγ₂ : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * calE γ κ N ^ (-1 : ℝ) ≤ (N : ℝ) * calE γ κ N ^ (-(1 / 3 : ℝ)) / 8 := by
  set g : ℝ := 3 - 2 * γ with hg
  have hg0 : 0 < g := by linarith
  set A : ℝ := (11 / κ) ^ g⁻¹ with hA
  refine ⟨⌈Real.exp A⌉₊ + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNA : Real.exp A ≤ (N : ℝ) := by
    have := Nat.le_ceil (Real.exp A)
    have h' : (⌈Real.exp A⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hlogA : A ≤ Real.log N := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hNA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  set L := Real.log (N : ℝ) ^ g with hL
  have hLT : 11 / κ ≤ L := by
    have h1 : ((11 / κ) ^ g⁻¹) ^ g ≤ L :=
      Real.rpow_le_rpow hA0 hlogA hg0.le
    rwa [Real.rpow_inv_rpow (by positivity) hg0.ne'] at h1
  have hx : 11 ≤ κ * L := by
    have := mul_le_mul_of_nonneg_left hLT hκ.le
    have h6 : κ * (11 / κ) = 11 := by field_simp
    linarith
  have h1 : calE γ κ N ^ (-1 : ℝ) = Real.exp (-(κ * L)) := by
    unfold calE
    rw [← Real.exp_mul]; congr 1; rw [hL]; ring
  have h3 : calE γ κ N ^ (-(1 / 3 : ℝ)) = Real.exp (-(κ * L) / 3) := by
    unfold calE
    rw [← Real.exp_mul]; congr 1; rw [hL]; ring
  rw [h1, h3]
  have hkey : 8 * Real.exp (-(κ * L)) ≤ Real.exp (-(κ * L) / 3) := by
    have he : Real.exp (-(κ * L) / 3) = Real.exp (2 * (κ * L) / 3) * Real.exp (-(κ * L)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]
    have h8 : 8 ≤ Real.exp (2 * (κ * L) / 3) := by
      have := Real.add_one_le_exp (2 * (κ * L) / 3)
      linarith
    exact mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left hkey hNpos.le
  linarith

/-- The exact statement of `leaf_fsm_large_alpha`, proved from the LEAF
`leaf_translate_large_beta`: the range of `α` lies inside the translate range, and the bound
`N ℰ^(-1)` is eventually below `N ℰ^(-1/3) / 8`.  Proved from that leaf. -/
theorem leaf_fsm_large_alpha_of_leaves (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        F γ N ^ ((γ - 1) / 2) < |α| → |α| ≤ F γ N ^ δ →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (α * F γ n)‖
          ≤ (N : ℝ) * calE γ κ N ^ (-(1 / 3 : ℝ)) / 8 := by
  obtain ⟨κ₀, hκ₀, hT⟩ := leaf_translate_large_beta γ δ hγ₁ hγ₂ hδ₀ hδ₁
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hT κ hκ hκle
  obtain ⟨N₂, hN₂⟩ := calE_inv_le_third γ κ hγ₂ hκ
  refine ⟨max N₁ N₂, fun N hN α hlo hhi => ?_⟩
  have hE : 0 ≤ calE γ κ N := (Real.exp_pos _).le
  have hb := hN₁ N (le_trans (le_max_left _ _) hN) α hlo (by linarith)
  exact le_trans hb (hN₂ N (le_trans (le_max_right _ _) hN))

end LeanLab.ExceptionalSet.U1539
