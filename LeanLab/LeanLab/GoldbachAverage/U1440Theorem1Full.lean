import LeanLab.GoldbachAverage.GSTheorem1
import LeanLab.PNTPort.ExplicitPsi1.DudekLemma4

/-!
# P0051 Goldston-Suriajaya Theorem 1, full printed form, eq. (11), proved

Unit U-1440, run PC 20261021T1603Z-28836. AI wrote this Lean code, Claude. Known mathematics.

D. A. Goldston, A. I. Suriajaya, On an average Goldbach representation formula of Fujii,
arXiv 2110.14250v2, Theorem 1, eq. (11), page 3: for `N ≥ 2`,

`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2) N + 2 (ζ'/ζ)(-1)
   - Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) + E(N)`,

an exact identity, with `E(N)` of eq. (12). The lab's earlier `gs_theorem1_proved` is the
"in particular" form eq. (13), with the three explicit lower terms put into `O(N)`.

Route: the identity `Σ G = E(N) + 2ψ₁(N) - N(N - 1)/2` of GSTheorem1.lean, `EGS_eq` and `sum_dc`,
and the exact explicit formula for `ψ₁` with the trivial zeros, Davenport chapter 17, the lab's
`PNTPort.ExplicitPsi1.Trivial.explicit_formula_psi1_trivial`, with `ζ'(0)/ζ(0) = log 2π`.
No cited input. Binary Goldbach is open; this is an average over n.
-/

open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section
namespace LeanLab.GoldbachAverage.U1440

open LeanLab.GoldbachAverage LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- The trivial zero sum of eq. (11), `Σ_{k ≥ 1} N^{1-2k}/(k(2k-1))`, written with `k + 1`
for `k ≥ 0`. -/
def trivSum (N : ℝ) : ℝ :=
  ∑' k : ℕ, N ^ (1 - 2 * ((k : ℝ) + 1)) / (((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) - 1))

lemma trivSum_eq {N : ℝ} (hN : 0 < N) : trivSum N = 2 * N * ∑' n, tb N n := by
  rw [trivSum, ← tsum_mul_left]
  apply tsum_congr; intro k
  unfold tb
  have e : N ^ (1 - 2 * ((k : ℝ) + 1)) = N * N ^ (-2 * ((k : ℝ) + 1)) := by
    rw [show (1 - 2 * ((k : ℝ) + 1)) = 1 + (-2 * ((k : ℝ) + 1)) by ring,
      Real.rpow_add hN, Real.rpow_one]
  rw [e, show (2 * ((k : ℝ) + 1) - 1) = 2 * k + 1 by ring]
  have h1 : ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (k : ℝ) + 2) * (2 * k + 1) ≠ 0 := by positivity
  field_simp

lemma trivSum_bounds {N : ℝ} (hN : 1 ≤ N) : 0 ≤ trivSum N ∧ trivSum N ≤ π ^ 2 / 3 := by
  rw [trivSum_eq (by linarith)]
  obtain ⟨h0, h1⟩ := y_tsum_tb_bounds hN
  constructor <;> nlinarith

/-- **Goldston-Suriajaya Theorem 1, eq. (11), the full printed statement**, unconditional:
for every integer `N ≥ 2` and every `0 < r < 1`,
`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2) N + 2 (ζ'/ζ)(-1)
   - Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) + E(N)`. -/
theorem gs_theorem1_full (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) =
      (N : ℂ) ^ 2 / 2 - 2 * Z1 N - ((2 * Real.log (2 * π) - 1 / 2 : ℝ) : ℂ) * N
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)) - ((trivSum N : ℝ) : ℂ)
        + EGS N r := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (0 : ℝ) < N := by linarith
  set P := ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) with hPdef
  have hRg : LZCesaroShort.Rg N (N : ℝ) = P := by
    rw [LZCesaroShort.Rg]; apply sum_congr rfl; intro a ha; rw [mem_range] at ha
    have : (a : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp ha
    rw [max_eq_right (by linarith)]
  -- `ψ₁(N) = N Σ Λ(n) w₁(n/N)`
  have hP : ((P : ℝ) : ℂ) = ((N : ℝ) : ℂ) *
      ∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / (N : ℝ)) := by
    rw [← hRg]; exact LZCesaroShort.Rg_eq hN0 le_rfl
  -- the exact explicit formula with the trivial zeros
  have hS := explicit_formula_psi1_trivial hN1
  rw [logDeriv_zeta_zero, Complex.cpow_neg_one] at hS
  -- the nontrivial zero sum is `Z1`
  have hZ : ((N : ℝ) : ℂ) * ∑' ρ : Zall, zterm (N : ℝ) ρ = Z1 N := by
    rw [LZCesaroShort.uZ_eq hN0, LZCesaroShort.Wf, Z1, zeroSum]
    have e : (∑' ρ : Zall, LZCesaroShort.wterm (N : ℝ) ρ.1) =
        ∑' ρ : NontrivialZero, LZCesaroShort.wterm (N : ℝ) ρ.1 := by
      rw [Zall_eq]; rfl
    rw [e]; rfl
  -- the trivial zero sum
  have hT : ∑' n : ℕ, tterm (N : ℝ) n = ((∑' n, tb (N : ℝ) n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact tsum_congr (tterm_eq hN0)
  have hTr : ((trivSum N : ℝ) : ℂ) = 2 * ((N : ℝ) : ℂ) * ((∑' n, tb (N : ℝ) n : ℝ) : ℂ) := by
    rw [trivSum_eq hN0]; push_cast; ring
  have hinv : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast hN0.ne')
  -- orthogonality and the expansion
  have hE : EGS N r = ((∑ n ∈ range (N + 1), G n - 2 * P + (N : ℝ) * (N - 1) / 2 : ℝ) : ℂ) := by
    rw [EGS_eq N hr0 hr, sum_dc]
  rw [hE]
  push_cast at hP hS hZ hT hTr hinv ⊢
  set d1 := deriv riemannZeta (-1) / riemannZeta (-1)
  linear_combination 2 * hP + 2 * (N : ℂ) * hS - 2 * hZ +
    2 * d1 * hinv - 2 * (N : ℂ) * hT + hTr

/-- **Faithfulness twin**: the full form implies the lab's simplified form, eq. (13), i.e. the
statement of the cited `gs_theorem1`, so the full theorem is at least as strong. -/
theorem gs_theorem1_of_full : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ r : ℝ, 0 < r → r < 1 →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N r‖ ≤ K * N := by
  set L := Real.log (2 * π)
  set d1 := deriv riemannZeta (-1) / riemannZeta (-1)
  refine ⟨2 * |L| + 1 + 2 * ‖d1‖ + 4, fun N hN r hr0 hr => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  rw [gs_theorem1_full N hN r hr0 hr]
  have e : (N : ℂ) ^ 2 / 2 - 2 * Z1 N - ((2 * L - 1 / 2 : ℝ) : ℂ) * N + 2 * d1 -
      ((trivSum N : ℝ) : ℂ) + EGS N r - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N r =
      -(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ)) + 2 * d1 - ((trivSum N : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  obtain ⟨t0, t1⟩ := trivSum_bounds hN1
  have hpi : π ^ 2 / 3 ≤ 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have n1 : ‖-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ))‖ ≤ (2 * |L| + 1) * N := by
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < N)]
    have : |2 * L - 1 / 2| ≤ 2 * |L| + 1 := by
      have := abs_sub (2 * L) (1 / 2)
      rw [abs_mul, abs_two] at this
      norm_num at this ⊢; linarith
    nlinarith
  have n2 : ‖2 * d1‖ ≤ 2 * ‖d1‖ * N := by
    rw [norm_mul, Complex.norm_two]; nlinarith [norm_nonneg d1]
  have n3 : ‖((trivSum N : ℝ) : ℂ)‖ ≤ 4 * N := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t0]; nlinarith
  calc ‖-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ)) + 2 * d1 - ((trivSum N : ℝ) : ℂ)‖
      ≤ ‖-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ))‖ + ‖2 * d1‖ +
          ‖((trivSum N : ℝ) : ℂ)‖ := by
        have a1 := norm_sub_le (-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ)) + 2 * d1)
          ((trivSum N : ℝ) : ℂ)
        have a2 := norm_add_le (-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ))) (2 * d1)
        linarith
    _ ≤ (2 * |L| + 1) * N + 2 * ‖d1‖ * N + 4 * N := by linarith
    _ = (2 * |L| + 1 + 2 * ‖d1‖ + 4) * N := by ring

/-- The twin has exactly the type of the cited `gs_theorem1`, eq. (13). -/
example : type_of% gs_theorem1 := gs_theorem1_of_full

/-- **Vacuity test**: the hypotheses hold at `N = 2`, `r = 1/2`, and the identity there reads
`0 = 2 - 2 Σ_ρ 2^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2)·2 + 2 (ζ'/ζ)(-1) - Σ_k 2^{1-2k}/(k(2k-1)) + E(2)`,
since `Σ_{n ≤ 2} ψ₂(n) = 0`. -/
theorem gs_theorem1_full_at_two :
    (0 : ℂ) = (2 : ℂ) ^ 2 / 2 - 2 * Z1 2 - ((2 * Real.log (2 * π) - 1 / 2 : ℝ) : ℂ) * 2
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)) - ((trivSum 2 : ℝ) : ℂ)
        + EGS 2 (1 / 2) := by
  have h := gs_theorem1_full 2 le_rfl (1 / 2) (by norm_num) (by norm_num)
  have hG : ∑ n ∈ range (2 + 1), G n = 0 := by
    simp [Finset.sum_range_succ, G, Finset.Nat.antidiagonal_succ,
      ArithmeticFunction.vonMangoldt_apply_one]
  rw [hG] at h
  push_cast at h ⊢
  exact h

end LeanLab.GoldbachAverage.U1440

#print axioms LeanLab.GoldbachAverage.U1440.gs_theorem1_full
#print axioms LeanLab.GoldbachAverage.U1440.gs_theorem1_of_full
#print axioms LeanLab.GoldbachAverage.U1440.gs_theorem1_full_at_two
#print axioms LeanLab.GoldbachAverage.U1440.trivSum_bounds
