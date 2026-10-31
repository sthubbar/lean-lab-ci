import Mathlib
import LeanLab.Zhao2025.Section4
import LeanLab.Zhao2025.Zhao2025U6837Cases
import LeanLab.Zhao2025.Zhao2025U6906Sub
import LeanLab.Zhao2025.Zhao2025U6909Sub030
import LeanLab.Zhao2025.Zhao2025U6910Sub040

/-!
# Zhao 2025, the case split behind Theorem 1.2, a wrapper

G. Zhao, arXiv 2511.05631v2, a preprint.  GEMINI task32, reviewed by a Claude cloud session.
AI wrote the Lean code.  Binary Goldbach is open.

Theorem 1.2, display (1.10), states `Σ_i (Σ_{ϱ ∈ Zᵢ} e^{-10λ/3})² ≤ 1 - c₁` with `c₁ > 0` depending
only on `c₀`.  This file does NOT prove that.  `theorem1_2_conditional` is the disjunction of the
ten case theorems already in the folder: from the per case display inputs, bundled as
`Lemma24_dichotomy`, it concludes the bound of whichever case holds, mostly in the weakened form
`< 1`.  Cases λ₁,₁ ≥ 0.40 conclude on the lab layout variables `R`, `T`, which are not linked to
`S` here, and no uniform `c₁` is extracted.  `Lemma24_dichotomy` is not Lemma 2.4 itself but the
display inputs each case uses.  CONDITIONAL ON those displays, Lemma 2.4 and Pintz's Theorems I to K.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Zhao2025.U6837 LeanLab.Zhao2025

/-- The per case display inputs of Theorem 1.2, one disjunct per λ₁,₁ range. Not Lemma 2.4 itself. -/
def Lemma24_dichotomy (n : ℕ) (l11 : ℝ) (R T S : ℕ → ℝ) : Prop :=
  -- Case 1: λ₁,₁ ≤ 0.01
  (0 < l11 ∧ l11 ≤ 0.01 ∧ 0 ≤ S 0 ∧ (∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.001) ∧
    ∑ i ∈ Finset.range n, S (i + 1) ≤ 0.001 ∧ 0 ≤ (5.2 : ℝ) ∧ Real.exp (-(5.2 / 1.09)) ≤ l11 ∧
    S 0 ≤ Real.exp (-(20 / 3) * l11) + 202 * Real.exp (-2.22 * 5.2) ∧
    ∑ i ∈ Finset.range (n + 1), S i ^ 2 ≤ Real.exp (-(20 / 3) * l11) + 202 * Real.exp (-2.22 * 5.2)) ∨
  -- Case 2: λ₁,₁ ∈ [0.01, 0.10]
  (0.01 ≤ l11 ∧ l11 ≤ 0.10 ∧ 0 ≤ S 0 ∧ S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.0042 ∧
    (∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0018) ∧
    ∑ i ∈ Finset.range n, S (i + 1) ≤ 0.6150) ∨
  -- Case 3: λ₁,₁ ∈ [0.10, 0.30]
  (0.10 ≤ l11 ∧ l11 ≤ 0.30 ∧ 0 ≤ S 0 ∧ S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.0690 ∧
    (∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0464) ∧
    ∑ i ∈ Finset.range n, S (i + 1) ≤ 4.951) ∨
  -- Case 4: λ₁,₁ ∈ [0.30, 0.40]
  (0.30 ≤ l11 ∧ l11 ≤ 0.40 ∧ 0 ≤ S 0 ∧ S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.1231 ∧
    (∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0971) ∧
    ∑ i ∈ Finset.range n, S (i + 1) ≤ 6.85) ∨
  -- Case 5: λ₁,₁ ∈ [0.40, 0.60]
  (0.40 ≤ l11 ∧ l11 ≤ 0.60 ∧
    ((0 ≤ S 0 ∧ S 0 ≤ 0.374 + 0.0808 ∧ 0 ≤ S 1 ∧ S 1 ≤ 0.374 + 0.0808 ∧
      (∀ i, i < n → 0 ≤ R i ∧ R i ≤ 0.157) ∧ (∀ i, i < n → 0 ≤ T i ∧ T i ≤ 0.0704) ∧
      ∑ i ∈ Finset.range n, R i ≤ 0.457 ∧ ∑ i ∈ Finset.range n, T i ≤ 6.33) ∨
     (0 ≤ S 0 ∧ S 0 ≤ 0.556 + 0.0808 ∧
      (∀ i, i < n → 0 ≤ R i ∧ R i ≤ 0.157) ∧ (∀ i, i < n → 0 ≤ T i ∧ T i ≤ 0.0704) ∧
      ∑ i ∈ Finset.range n, R i ≤ 0.457 ∧ ∑ i ∈ Finset.range n, T i ≤ 6.33))) ∨
  -- Case 6: λ₁,₁ ∈ [0.60, 0.62]
  (0.60 ≤ l11 ∧ l11 ≤ 0.62 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.57982 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.6236 ∧
    ((∀ i, R i ≤ hd 0.29940 0.14790 0.14790 0.14790 0.14790 i ∧ T i ≤ hd 0.10023 0.09272 0.09272 0.09272 0.09272 i) ∨
     (∀ i, R i ≤ hd 0.23508 0.23508 0.14790 0.14790 0.14790 i ∧ T i ≤ hd 0.10023 0.10023 0.09272 0.09272 0.09272 i))) ∨
  -- Case 7: λ₁,₁ ∈ [0.62, 0.64]
  (0.62 ≤ l11 ∧ l11 ≤ 0.64 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.59615 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.5381 ∧
    ((∀ i, R i ≤ hd 0.29306 0.19150 0.19150 0.19150 0.19150 i ∧ T i ≤ hd 0.09797 0.09241 0.09241 0.09241 0.09230 i) ∨
     (∀ i, R i ≤ hd 0.25205 0.25205 0.19150 0.19150 0.19150 i ∧ T i ≤ hd 0.09797 0.09797 0.09241 0.09241 0.09230 i))) ∨
  -- Case 8: λ₁,₁ ∈ [0.64, 0.66]
  (0.64 ≤ l11 ∧ l11 ≤ 0.66 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.66426 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.4466 ∧
    ((∀ i, R i ≤ hd 0.29738 0.24889 0.24889 0.24889 0.24889 i ∧ T i ≤ hd 0.09572 0.09321 0.09321 0.09321 0.09063 i) ∨
     (∀ i, R i ≤ hd 0.27836 0.27836 0.24889 0.24889 0.24889 i ∧ T i ≤ hd 0.09572 0.09572 0.09321 0.09321 0.09063 i))) ∨
  -- Case 9: λ₁,₁ ∈ [0.66, 0.68]
  (0.66 ≤ l11 ∧ l11 ≤ 0.68 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.64932 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.3632 ∧
    ((∀ i, R i ≤ hd 0.28824 0.25104 0.25104 0.25104 0.25104 i ∧ T i ≤ hd 0.09359 0.09166 0.09166 0.09166 0.08900 i) ∨
     (∀ i, R i ≤ hd 0.27380 0.27380 0.25104 0.25104 0.25104 i ∧ T i ≤ hd 0.09359 0.09359 0.09166 0.09166 0.08900 i))) ∨
  -- Case 10: λ₁,₁ ≥ 0.68
  (0.68 ≤ l11 ∧ (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.67914 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.2739 ∧
    ((∀ i, R i ≤ hd 0.28735 0.27703 0.27703 0.27703 0.27703 i ∧ T i ≤ hd 0.09121 0.09112 0.09112 0.09112 0.08733 i) ∨
     (∀ i, R i ≤ hd 0.28342 0.28342 0.27703 0.27703 0.27703 i ∧ T i ≤ hd 0.09121 0.09121 0.09112 0.09112 0.08733 i)))

/-- The union of the ten case theorems; not display (1.10) with a uniform `c₁`. CONDITIONAL ON the display inputs. -/
theorem theorem1_2_conditional (n : ℕ) (l11 : ℝ) (R T S : ℕ → ℝ)
    (hc1 : Lemma24_dichotomy n l11 R T S) :
    (0 < l11 ∧ l11 ≤ 0.01 ∧ ∑ i ∈ Finset.range (n + 1), S i ^ 2 ≤ 1 - 4 * l11) ∨
    (0.01 ≤ l11 ∧ l11 ≤ 0.40 ∧ ∑ i ∈ Finset.range (n + 1), S i ^ 2 < 1) ∨
    (0.40 ≤ l11 ∧ l11 ≤ 0.60 ∧ S 0 ^ 2 + S 1 ^ 2 + ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1) ∨
    (0.40 ≤ l11 ∧ l11 ≤ 0.60 ∧ S 0 ^ 2 + ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1) ∨
    (0.60 ≤ l11 ∧ ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1) := by
  rcases hc1 with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨hl, hl', hS0, hS, hsum, hL, hL2, h0, H⟩ := h
    have hbound := case1_bound l11 5.2 hl hl' hL hL2
    exact Or.inl ⟨hl, hl', H.trans hbound⟩
  · obtain ⟨hl, hl', hS0, h0, hS, hsum⟩ := h
    have := sub001_closes n S l11 hl hS0 h0 hS hsum
    exact Or.inr <| Or.inl ⟨hl, by linarith, this.trans_le (by norm_num)⟩
  · obtain ⟨hl, hl', hS0, h0, hS, hsum⟩ := h
    have := sub010_closes n S l11 hl hS0 h0 hS hsum
    exact Or.inr <| Or.inl ⟨by linarith, by linarith, this.trans_le (by norm_num)⟩
  · obtain ⟨hl, hl', hS0, h0, hS, hsum⟩ := h
    have := sub030_closes n S l11 hl hS0 h0 hS hsum
    exact Or.inr <| Or.inl ⟨by linarith, by linarith, this.trans_le (by norm_num)⟩
  · obtain ⟨hl, hl', H⟩ := h
    rcases H with ⟨hS0, hS0', hS1, hS1', hR, hT, hsR, hsT⟩ | ⟨hS0, hS0', hR, hT, hsR, hsT⟩
    · have := sub040_i02_closes n R T (S 0) (S 1) ⟨hS0, hS0'⟩ ⟨hS1, hS1'⟩ hR hT hsR hsT
      exact Or.inr <| Or.inr <| Or.inl ⟨hl, hl', this.trans_le (by norm_num)⟩
    · have := sub040_i01_closes n R T (S 0) ⟨hS0, hS0'⟩ hR hT hsR hsT
      exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hl, hl', this.trans_le (by norm_num)⟩
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    have := case060_closes n R T hR0 hT0 hsR hsT hcfg
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨hl, this⟩
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    have := case062_closes n R T hR0 hT0 hsR hsT hcfg
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨by linarith, this⟩
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    have := case064_closes n R T hR0 hT0 hsR hsT hcfg
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨by linarith, this⟩
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    have := case066_closes n R T hR0 hT0 hsR hsT hcfg
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨by linarith, this⟩
  · obtain ⟨hl, hR0, hT0, hsR, hsT, hcfg⟩ := h
    have := case068_closes n R T hR0 hT0 hsR hsT hcfg
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨by linarith, this⟩

end LeanLab.Zhao2025.U6900
