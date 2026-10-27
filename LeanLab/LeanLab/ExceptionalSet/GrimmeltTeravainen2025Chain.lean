/-
P0039 L. Grimmelt, J. Teräväinen, The Exceptional Set in Goldbach's Problem with two Chen
Primes, arXiv 2508.16400v2 of 2026-07-29, copy papers/P0039.pdf. Unit U-6807, CLOUD
20261021T0217Z-cloud56. AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.

Elementary steps of Proposition 3.4 and of Section 8, read from the rendered pages 8, 15 to 17,
65 to 67:
* the passage from (3.11) to (3.12), p.15, pointwise, settling QUESTION Q-6790a: (3.12) as
  printed is false at every squarefree `n ∈ B₁ ∪ B₂`, and holds with the factor `r_{N^{1/10}}(n)`
  restored on `c_{E₃*}(n) Λ_{E₃*}(n)`;
* the normalised indicator `r_z(n)` of p.8 is at least 2 on `z`-rough `n` for `z ≥ 3`;
* the Chen switching bookkeeping of pp.16 to 17, settling QUESTION Q-6790b: with the factor
  restored the Mertens ratio enters `g₂` exactly once;
* the constant `c₁` of Lemma 8.3, p.67, from (3.9);
* the closing chain of the proof of Theorem 1.1 in the unexceptional case, p.67.
-/
import Mathlib

open Finset

namespace LeanLab.ExceptionalSet.GT2025

noncomputable section

/-! ### (3.11) and (3.12), p.15

Pointwise values at one `n`: `r = r_{N^{1/10}}(n)`, `S` the number of `p ∣ n` with
`N^{1/10} ≤ p ≤ N^{1/3-δ₁}`, `b₁ = 1_{n ∈ B₁}`, `b₂ = 1_{n ∈ B₂}`, `e = E'(n)`, and
`E(n) = r e`. By (3.3), `c_{E₃*}(n) Λ_{E₃*}(n) = b₁/2 + b₂`. -/

/-- Right side of (3.11). -/
def rhs311 (r S b₁ b₂ e : ℝ) : ℝ := r * (1 - S / 2 - b₁ / 2 - b₂ - e)

/-- Right side of (3.12) as printed: `r (1 - S/2) - c_{E₃*} Λ_{E₃*} - E`. -/
def rhs312printed (r S b₁ b₂ e : ℝ) : ℝ := r * (1 - S / 2) - (b₁ / 2 + b₂) - r * e

/-- Right side of (3.12) with the factor `r_{N^{1/10}}(n)` on `c_{E₃*} Λ_{E₃*}`. -/
def rhs312corrected (r S b₁ b₂ e : ℝ) : ℝ := r * (1 - S / 2) - r * (b₁ / 2 + b₂) - r * e

/-- With the factor restored, (3.12) is (3.11) rearranged, so it follows from (3.11). -/
theorem rhs312corrected_eq (r S b₁ b₂ e : ℝ) :
    rhs312corrected r S b₁ b₂ e = rhs311 r S b₁ b₂ e := by
  unfold rhs312corrected rhs311; ring

theorem eq312corrected_of_eq311 {L r S b₁ b₂ e : ℝ} (h : rhs311 r S b₁ b₂ e ≤ L) :
    rhs312corrected r S b₁ b₂ e ≤ L := by
  rwa [rhs312corrected_eq]

/-- For `r ≥ 1` and nonnegative indicators the printed right side is at least the right side
of (3.11): printed (3.12) is a stronger claim than (3.11), so it does not follow from it. -/
theorem rhs312printed_ge {r S b₁ b₂ e : ℝ} (hr : 1 ≤ r) (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ b₂) :
    rhs311 r S b₁ b₂ e ≤ rhs312printed r S b₁ b₂ e := by
  unfold rhs311 rhs312printed
  nlinarith

/-- **Q-6790a, case `B₁`.** For squarefree `n = p₁p₂p₃ ∈ B₁` exactly one prime factor, `p₁`,
lies in `[N^{1/10}, N^{1/3-δ₁}]`, `n ∉ P₂` so `Λ₂(n) = 0`, and `E'(n) = 0`. Then (3.11)
holds with equality and (3.12) as printed fails as soon as `r > 1`. -/
theorem eq312printed_fails_B1 {r : ℝ} (hr : 1 < r) :
    rhs311 r 1 1 0 0 = 0 ∧ (0 : ℝ) < rhs312printed r 1 1 0 0 := by
  unfold rhs311 rhs312printed
  constructor
  · ring
  · linarith

/-- **Q-6790a, case `B₂`.** For squarefree `n ∈ B₂`, no prime factor lies in the range, so
`S = 0`, and again (3.11) holds with equality while printed (3.12) fails for `r > 1`. -/
theorem eq312printed_fails_B2 {r : ℝ} (hr : 1 < r) :
    rhs311 r 0 0 1 0 = 0 ∧ (0 : ℝ) < rhs312printed r 0 0 1 0 := by
  unfold rhs311 rhs312printed
  constructor
  · ring
  · linarith

/-! ### The normalised indicator `r_z`, p.8 -/

/-- `r_z(n) = ∏_{p < z} (1 - 1/p)^{-1} 1_{p ∤ n}`, p.8. -/
noncomputable def rz (z n : ℕ) : ℝ :=
  ∏ p ∈ (range z).filter Nat.Prime, if p ∣ n then 0 else (p : ℝ) / (p - 1)

/-- On `z`-rough `n` with `z ≥ 3`, `r_z(n) ≥ 2`: the factor at `p = 2` is already 2. So the
hypothesis `r > 1` of `eq312printed_fails_B1` and `_B2` holds for every `n ∈ B₁ ∪ B₂` once
`N^{1/10} ≥ 3`. -/
theorem two_le_rz {z n : ℕ} (hz : 3 ≤ z) (hn : ∀ p, p.Prime → p < z → ¬ p ∣ n) :
    2 ≤ rz z n := by
  unfold rz
  set s := (range z).filter Nat.Prime
  have h2 : 2 ∈ s := by
    simp only [s, mem_filter, mem_range]; exact ⟨by omega, Nat.prime_two⟩
  have hfac : ∀ p ∈ s, (if p ∣ n then (0 : ℝ) else (p : ℝ) / (p - 1)) = (p : ℝ) / (p - 1) := by
    intro p hp
    simp only [s, mem_filter, mem_range] at hp
    simp [hn p hp.2 hp.1]
  rw [prod_congr rfl hfac, ← mul_prod_erase s _ h2]
  have hone : (1 : ℝ) ≤ ∏ p ∈ s.erase 2, (p : ℝ) / (p - 1) := by
    apply Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    · intro a b ha hb; exact one_le_mul_of_one_le_of_one_le ha hb
    · exact le_refl 1
    · intro p hp
      simp only [s, mem_erase, mem_filter, mem_range] at hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.2.two_le
      rw [le_div_iff₀ (by linarith)]
      linarith
  have h2v : ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 := by norm_num
  rw [h2v]
  linarith

/-! ### Chen switching, pp.16 and 17

Abstract values: `P₁₀ = ∏_{p<N^{1/10}} (1 - 1/p)`, `κ = ∏_{N^{1/10} ≤ p < N^{1/6}} (1 - 1/p)`, so
`∏_{p<N^{1/6}} (1 - 1/p) = P₁₀ κ`, and `κ → 3/5` by Mertens. `W = Ω(n) Ω_M(n) ≥ 0` with
`Ω_M` normalised on its own range `[P₁, N^{1/6})`, `x = c_{E₃*}(n+2) Λ_{E₃*}(n+2) ≥ 0`. -/

/-- **Q-6790b.** From the p.16 majorant `Λ(n) ≤ log N · P₁₀ κ · W`, the switched term of the
corrected (3.12), which carries `r_{N^{1/10}}(n+2) = P₁₀⁻¹` on `B₁ ∪ B₂`, is at most
`κ · log N · W x`: the product over `p < N^{1/10}` cancels against `r_{N^{1/10}}(n+2)` and the
Mertens ratio `κ` enters exactly once, as in `g₂` and in the final bound on p.17. -/
theorem switch_bound {Λ L P₁₀ κ W x : ℝ} (hP : 0 < P₁₀) (hx : 0 ≤ x)
    (hΛ : Λ ≤ L * (P₁₀ * κ) * W) :
    Λ * P₁₀⁻¹ * x ≤ κ * L * W * x := by
  have hPi : 0 ≤ P₁₀⁻¹ := inv_nonneg.2 hP.le
  calc Λ * P₁₀⁻¹ * x ≤ L * (P₁₀ * κ) * W * P₁₀⁻¹ * x := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_right hΛ hPi
    _ = κ * L * W * x * (P₁₀ * P₁₀⁻¹) := by ring
    _ = κ * L * W * x := by rw [mul_inv_cancel₀ hP.ne', mul_one]

/-- Without the factor, as (3.12) is printed, the same majorant leaves `P₁₀ κ`, which tends to
0 like `1/log N`: the term would be negligible and no constant `3/5` could arise. -/
theorem switch_bound_printed {Λ L P₁₀ κ W x : ℝ} (hx : 0 ≤ x)
    (hΛ : Λ ≤ L * (P₁₀ * κ) * W) :
    Λ * x ≤ P₁₀ * κ * L * W * x := by
  have := mul_le_mul_of_nonneg_right hΛ hx
  linarith

/-! ### Lemma 8.3 and the end of the proof of Theorem 1.1, p.67 -/

/-- **Lemma 8.3, p.67:** the leading constant `V(ω_M) - V(Ω_M)(3/5 + δ₁) c_{E₃*}` is at least
the `c₀ > 0` of (3.9), so `c₁ > 0`. -/
theorem lemma83_c1 {Vω VΩ cE δ c₀ : ℝ} (h39 : c₀ ≤ Vω - (3 / 5 + δ) * cE * VΩ) (hc₀ : 0 < c₀) :
    0 < Vω - VΩ * (3 / 5 + δ) * cE := by
  nlinarith

/-- **Closing chain of the unexceptional case, p.67.** With `A = ΛΛ₂⁺ * ΛΛ₂⁺(m)`,
`B = ΛΛ₂⁺ * r_{P₁}r_{P₁}⁺(m)`, `C = r_{P₁}r_{P₁}⁺ * r_{P₁}r_{P₁}⁺(m)`, `S = m 𝔖(m) > 0`:
from `A ≥ c₁ B + e₁`, `c₁ B ≥ c₁² C + e₂`, `|C - S| ≤ η S`, `|eᵢ| ≤ ε S`, with `η ≤ 1/4` and
`8ε ≤ c₁²`, we get `A ≥ c₁²/2 · S`. The paper's smallness of `e^{-δ₁^{-1}/10}` and
`δ₁^{-8} e^{-cδ₁^{-1/2}}` is the pair `η, ε`. -/
theorem final_chain {A B C S c₁ e₁ e₂ η ε : ℝ} (hS : 0 < S)
    (h1 : c₁ * B + e₁ ≤ A) (h2 : c₁ ^ 2 * C + e₂ ≤ c₁ * B)
    (hC : |C - S| ≤ η * S) (he₁ : |e₁| ≤ ε * S) (he₂ : |e₂| ≤ ε * S)
    (hη : η ≤ 1 / 4) (hε : 8 * ε ≤ c₁ ^ 2) :
    c₁ ^ 2 / 2 * S ≤ A := by
  have hC' : (1 - η) * S ≤ C := by
    have := neg_abs_le (C - S); nlinarith
  have he₁' := neg_abs_le e₁
  have he₂' := neg_abs_le e₂
  have hc2 : 0 ≤ c₁ ^ 2 := sq_nonneg _
  have : c₁ ^ 2 * ((1 - η) * S) ≤ c₁ ^ 2 * C := mul_le_mul_of_nonneg_left hC' hc2
  have : c₁ ^ 2 * (3 / 4 * S) ≤ c₁ ^ 2 * ((1 - η) * S) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hc2
  nlinarith

/-- Vacuity of `final_chain`: all hypotheses hold, with `c₁ = 1`, `S = 1`, `η = 1/4`,
`ε = 1/8`, nonzero errors, at a point where the conclusion is tight up to `1/8`. -/
theorem final_chain_vacuity :
    (1 : ℝ) * (3 / 4) + (-1 / 8) ≤ 5 / 8 ∧ (1 : ℝ) ^ 2 * (7 / 8) + (-1 / 8) ≤ 1 * (3 / 4) ∧
      |(7 / 8 : ℝ) - 1| ≤ 1 / 4 * 1 ∧ |(-1 / 8 : ℝ)| ≤ 1 / 8 * 1 ∧ 8 * (1 / 8 : ℝ) ≤ 1 ^ 2 ∧
      (1 : ℝ) ^ 2 / 2 * 1 ≤ 5 / 8 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num⟩ <;>
    rw [abs_le] <;> constructor <;> norm_num

/-- The hypothesis `8 ε ≤ c₁²` of `final_chain` cannot be dropped: with `ε = 1` the errors
`e₁ = e₂ = -1` and `B = C = S = 1`, `c₁ = 1`, `A = 0` meet all other hypotheses. -/
theorem final_chain_needs_eps :
    (1 : ℝ) * 1 + (-1) ≤ 0 ∧ (1 : ℝ) ^ 2 * 1 + (-1) ≤ 1 * 1 ∧ ¬ ((1 : ℝ) ^ 2 / 2 * 1 ≤ 0) := by
  norm_num

end

end LeanLab.ExceptionalSet.GT2025
