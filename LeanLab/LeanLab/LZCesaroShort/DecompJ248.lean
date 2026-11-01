import LeanLab.LZCesaroShort.Statements
import LeanLab.LZCesaroShort.Lemma5
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace LeanLab.LZCesaroShort

open Complex MeasureTheory Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt

/-- LEAF arXiv:1606.00869v2 page 2, bound for the exponential sum TH. -/
theorem lemma5_bound_TH_leaf : ∃ K : ℝ, ∀ N H : ℕ, ∀ α : ℝ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖TH N H H α‖ ≤ K * min (H : ℝ) (1 / ‖α‖) := by sorry

/-- `α ↦ e (n * α)` is continuous. -/
private lemma continuous_e_mul_freq (n : ℕ) :
    Continuous fun α : ℝ => LeanLab.PNTPort.LargeSieve.e (n * α) := by
  unfold LeanLab.PNTPort.LargeSieve.e
  fun_prop

/-- One period of a nonzero frequency: `∫_{-(1/2)}^{1/2} e (n α) = 0` for `n ≠ 0`. -/
private lemma integral_period_e_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), LeanLab.PNTPort.LargeSieve.e (n * α) = 0 := by
  set c : ℂ := (n : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I with hc_def
  have hc : c ≠ 0 := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    rw [hc_def]
    exact mul_ne_zero (mul_ne_zero hn' h2) Complex.I_ne_zero
  have hfun : ∀ α : ℝ,
      LeanLab.PNTPort.LargeSieve.e (n * α) = Complex.exp (c * (α : ℂ)) := by
    intro α
    unfold LeanLab.PNTPort.LargeSieve.e
    rw [hc_def]
    congr 1
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_exp_mul_complex hc]
  have key : Complex.exp (c * ((1 / 2 : ℝ) : ℂ))
      = Complex.exp (c * ((-(1 / 2) : ℝ) : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exp_sub_eq_one]
    have hsub : c * ((1 / 2 : ℝ) : ℂ) - c * ((-(1 / 2) : ℝ) : ℂ) = c := by
      push_cast
      ring
    rw [hsub, Complex.exp_eq_one_iff]
    refine ⟨(n : ℤ), ?_⟩
    rw [hc_def]
    push_cast
    ring
  rw [key, sub_self, zero_div]

/-- One period of the zero frequency: `∫_{-(1/2)}^{1/2} e 0 = 1`. -/
private lemma integral_period_e_zero :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      LeanLab.PNTPort.LargeSieve.e (((0 : ℕ) : ℝ) * α) = 1 := by
  have h : (fun α : ℝ => LeanLab.PNTPort.LargeSieve.e (((0 : ℕ) : ℝ) * α))
      = fun _ => (1 : ℂ) := by
    funext α
    unfold LeanLab.PNTPort.LargeSieve.e
    simp
  rw [h, intervalIntegral.integral_const]
  norm_num

/-- `T_H(N, H; α)` integrates to `0` over a full period whenever `H ≤ N`: only the
frequency `n = 0` survives, and its triangle weight is `H - |0 - N| = H - N = 0`. -/
private lemma integral_TH_period_eq_zero {N H : ℕ} (hHN : H ≤ N) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H α = 0 := by
  unfold TH
  rw [intervalIntegral.integral_finsetSum (s := (Icc (N - H) (N + H)).filter
      (fun n : ℕ => (n : ℝ) ≤ (N : ℝ) + (H : ℝ)))
    (f := fun (n : ℕ) (α : ℝ) =>
      (((H : ℝ) - |(n : ℝ) - (N : ℝ)| : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * α))
    (fun n _ => (continuous_const.mul (continuous_e_mul_freq n)).intervalIntegrable _ _)]
  set F : Finset ℕ := (Icc (N - H) (N + H)).filter
    (fun n : ℕ => (n : ℝ) ≤ (N : ℝ) + (H : ℝ)) with hF
  have hterm : ∀ n ∈ F,
      (∫ α in (-(1 / 2 : ℝ))..(1 / 2),
        ((((H : ℝ) - |(n : ℝ) - (N : ℝ)| : ℝ)) : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * α))
      = if n = 0 then (((H : ℝ) - (N : ℝ) : ℝ) : ℂ) else 0 := by
    intro n _
    rw [intervalIntegral.integral_const_mul]
    split_ifs with hn
    · subst hn
      rw [integral_period_e_zero, mul_one]
      have habs : |((0 : ℕ) : ℝ) - (N : ℝ)| = (N : ℝ) := by
        rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg N)]
      rw [habs]
    · rw [integral_period_e_ne_zero hn, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with h0
  · have hNH : N = H := by
      have h1 : N - H ≤ 0 := (Finset.mem_Icc.mp (Finset.mem_filter.mp h0).1).1
      omega
    subst hNH
    norm_num
  · rfl

/-- LEAF arXiv:1606.00869v2 page 2, integral of the product of T and wsum.

The integral is `0` for every `N`, `H` with `H ≤ N` (`integral_TH_period_eq_zero`
times the constant `wsum N H H`), so the bound holds with `K = 0`. -/
theorem integral_T_wsum_leaf : ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H α * (wsum N H H : ℂ)‖ ≤ K * (N * Real.log (2 * (N : ℝ) ^ 2 / H)) := by
  refine ⟨0, fun N H _ _ hHN => ?_⟩
  rw [intervalIntegral.integral_mul_const, integral_TH_period_eq_zero hHN, zero_mul, norm_zero]
  simp

/-- LEAF arXiv:1606.00869v2 page 2, bound for the partial sum over y. -/
theorem theorem2a_partial_sum_bound_leaf : ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N → ∀ y : ℝ, -(H : ℝ) ≤ y → y < H →
    |wsum N H y| ≤ K * N * Real.log N ^ 2 * Real.log (2 * H) := by sorry

/-- LEAF arXiv:1606.00869v2 page 2, theorem1 from theorem2b component. -/
theorem theorem1_from_theorem2b_leaf : ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K * (N * Real.log (2 * (N : ℝ) ^ 2 / H) + H * Real.log N ^ 2 * Real.log (2 * H)) := by sorry

/-- The exact Theorem1 Prop is conditionally dependent on Theorem2b and Sec5. -/
theorem lz_theorem1_decomp_assembly : RiemannHypothesis → Theorem1 := by
  intro _
  exact theorem1_from_theorem2b_leaf

end LeanLab.LZCesaroShort
