/-
P0100 Dudek 2014, Section 2.2, pages 4 to 6: DECOMPOSE of display_of.
AI-written Lean code, Gemini.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Dudek2014.Display

namespace LeanLab.Dudek2014.Section22
open Real Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- LEAF: Lemma 5 and the Σ bound. Page 6. -/
theorem display_leaf1 {S : ℝ → ℝ → ℝ} (h5 : Lemma5 S) (hS : SigmaBd S) {x : ℝ} (hx : 65000 ≤ x) :
    let h := hD x
    h - (2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) * log (2 * x / h)) - 48 / (5 * h) < WS x h := by
  obtain ⟨hh0, hhx⟩ := hD_small hx
  have h1 := h5 x (hD x) hh0 (by linarith)
  have h2 := hS x hx
  have hpi := pi_pos
  have hsq : 0 < √(x - hD x) := sqrt_pos.2 (by linarith [hD_small hx])
  have e : (2 * x * hD x / (π * √(x - hD x)) + 4 * hD x * (x + hD x) ^ (3 / 2 : ℝ) / (π * 2 * x)) *
      log (2 * x / hD x) / hD x =
      2 / π * (x / √(x - hD x) + (x + hD x) ^ (3 / 2 : ℝ) / x) * log (2 * x / hD x) := by
    field_simp; ring
  have h3 : S x (hD x) / (hD x) ≤ |S x (hD x)| / (hD x) := div_le_div_of_nonneg_right (le_abs_self _) hh0.le
  have h4 : |S x (hD x)| / (hD x) ≤ 2 / π * (x / √(x - hD x) + (x + hD x) ^ (3 / 2 : ℝ) / x) *
      log (2 * x / hD x) := by
    rw [← e]; exact div_le_div_of_nonneg_right h2 hh0.le
  have := (abs_lt.1 h1).1
  linarith

/-- LEAF: WS ≤ Σ_{x-h<n≤x+h} Λ(n). Page 6. -/
theorem display_leaf2 {x : ℝ} (hx : 65000 ≤ x) :
    WS x (hD x) ≤ ∑ n ∈ Ioc ⌊x - (hD x)⌋₊ ⌊x + (hD x)⌋₊, Λ n := by
  obtain ⟨hh0, hhx⟩ := hD_small hx
  have hab : ⌊x - hD x⌋₊ ≤ ⌊x + hD x⌋₊ := Nat.floor_le_floor (by linarith [hD_small hx])
  unfold WS
  rw [← Iic_union_Ioc_eq_Iic hab, sum_union (Iic_disjoint_Ioc le_rfl)]
  have hz : ∑ n ∈ Iic ⌊x - hD x⌋₊, Λ n * w x (hD x) n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [mem_Iic] at hn
    have hnr : (n : ℝ) ≤ x - hD x := by
      have := Nat.floor_le (show 0 ≤ x - hD x by linarith)
      have : (n : ℝ) ≤ ⌊x - hD x⌋₊ := by exact_mod_cast hn
      linarith
    have hw : w x (hD x) n = 0 := by
      unfold w
      apply max_eq_left
      rw [sub_nonpos, le_div_iff₀ hh0, one_mul, abs_of_nonpos (by linarith)]
      linarith
    rw [hw, mul_zero]
  rw [hz, zero_add]
  apply sum_le_sum
  intro n _
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hw1 : w x (hD x) n ≤ 1 := by
    unfold w
    apply max_le (by norm_num)
    have : 0 ≤ |(n : ℝ) - x| / (hD x) := div_nonneg (abs_nonneg _) hh0.le
    linarith
  have hw2 : 0 ≤ w x (hD x) n := le_max_left _ _
  nlinarith

/-- LEAF: ψ and θ differences. Page 6. -/
theorem display_leaf3 (hSch : Schoenfeld) {x : ℝ} (hx : 65000 ≤ x) :
    let h := hD x
    ∑ n ∈ Ioc ⌊x - h⌋₊ ⌊x + h⌋₊, Λ n ≤
      psiF (x + h) - psiF (x - h) ∧
    (∑ p ∈ (Ioc ⌊x - h⌋₊ ⌊x + h⌋₊).filter Nat.Prime, log p) =
      thetaF (x + h) - thetaF (x - h) ∧
    0.98 * √(x - h) < psiF (x - h) - thetaF (x - h) ∧
    psiF (x + h) - thetaF (x + h) < 1.11 * √(x + h) + 3 * (x + h) ^ (1 / 3 : ℝ) := by
  have hab : ⌊x - hD x⌋₊ ≤ ⌊x + hD x⌋₊ := Nat.floor_le_floor (by linarith [hD_small hx])
  have hlo : (121 : ℝ) ≤ x - hD x := by linarith [hD_small hx]
  have hpsi : psiF (x + hD x) - psiF (x - hD x) = ∑ n ∈ Ioc ⌊x - hD x⌋₊ ⌊x + hD x⌋₊, Λ n :=
    sum_Iic_sub hab
  have htheta : thetaF (x + hD x) - thetaF (x - hD x) =
      ∑ p ∈ (Ioc ⌊x - hD x⌋₊ ⌊x + hD x⌋₊).filter Nat.Prime, log p := by
    unfold thetaF
    rw [sum_filter, sum_filter, sum_filter]
    exact sum_Iic_sub hab
  obtain ⟨hA1, -⟩ := hSch (x - hD x) hlo
  obtain ⟨-, hB2⟩ := hSch (x + hD x) (by linarith [hD_small hx])
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **`Display22` from Lemma 5, the Σ bounds and Schoenfeld's bounds.** -/
theorem display_of_decomp {S : ℝ → ℝ → ℝ} (h5 : Lemma5 S) (hS : SigmaBd S) (hSch : Schoenfeld) :
    Display22 := by
  intro x hx
  obtain ⟨hh0, hhx⟩ := hD_small hx
  set h := hD x with hhdef
  have hx0 : 0 < x := by linarith
  have hlo : (121 : ℝ) ≤ x - h := by linarith
  have hab : ⌊x - h⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)

  -- Lemma 5 and the Σ bound
  have hW : h - (2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) * log (2 * x / h))
      - 48 / (5 * h) < WS x h := by
    have hl1 := display_leaf1 h5 hS hx
    exact hl1

  -- WS ≤ Σ_{x-h<n≤x+h} Λ(n)
  have hWle : WS x h ≤ ∑ n ∈ Ioc ⌊x - h⌋₊ ⌊x + h⌋₊, Λ n := by
    have hl2 := display_leaf2 hx
    exact hl2

  -- ψ and θ differences
  have ⟨hpsi, htheta, hSch1, hSch2⟩ := display_leaf3 hSch hx
  have hpsi_eq : psiF (x + h) - psiF (x - h) = ∑ n ∈ Ioc ⌊x - h⌋₊ ⌊x + h⌋₊, Λ n :=
    sum_Iic_sub hab

  rw [htheta]
  unfold rhs
  rw [← hhdef]
  linarith

end
end LeanLab.Dudek2014.Section22
