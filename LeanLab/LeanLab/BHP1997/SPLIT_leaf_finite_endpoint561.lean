/-
Independent split of the finite endpoint replacement step of the periodic
principal model. The complete period integral is replaced by the exact finite
convolution count, the truncated residue sum carries one uniform envelope, and
the squared count deviation over the even frequency set must save one arbitrary
power of the logarithm. That saving is the only arithmetic input of the split.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561m

namespace LeanLab.BHP1997.Decomp561m
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e

/-- LEAF. Exact finite convolution count on one complete period: the integral of
the integrand against a complete period of the additive character is the number
of pairs, one from the long support and one from the short support, whose sum is
the even frequency. There is no analytic input, and the short window is already a
complete period. -/
theorem leaf_endpoint_count_identity561 (ε x : ℝ) (N : ℕ) :
    (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        integrand512 ε x (fun _ => 1) (fun _ => 1) N t) =
      (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) : ℂ) := by
  sorry

/-- LEAF. Factorization of the endpoint difference: the complete period model and
the truncated main term carry the same prefactor and the same truncated residue
sum, so their difference is that prefactor times that residue sum times the
difference between the complete period integral and the short interval length.
Pure algebra, no estimate. -/
theorem leaf_endpoint_factorization561 (ε D x u v : ℝ) (N : ℕ) :
    completePrincipal561 ε D x u v N - truncatedMain512 ε D x u v N =
      ((u * v / (Real.log x * Real.log (length512 ε x)) : ℝ) : ℂ) *
        (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N) *
        ((∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        integrand512 ε x (fun _ => 1) (fun _ => 1) N t) -
          (length512 ε x : ℂ)) := by
  sorry

/-- LEAF. Uniform residue sum envelope: for a fixed exponent and a fixed arc
parameter the logarithm normalized prefactor times the truncated residue sum of
the principal model stays below one constant on the whole half line, uniformly in
the frequency and in the length. Only the trivial size of each residue term is
used, never any cancellation. -/
theorem leaf_endpoint_residue_envelope561 (ε D u v : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ N : ℕ,
      ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) ≤ C := by
  sorry

/-- LEAF. Power against logarithm threshold for the squared count deviation: on
the even frequency window the squared deviation of the exact convolution count
from the short interval length is at most one constant times the same scale as
the target, uniformly in the length, once the exponent stays below the fixed
positive threshold. This is the only arithmetic input of the split. -/
theorem leaf_endpoint_power_log_threshold561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ A : ℝ, 0 < A → ∀ D : ℝ,
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        (∑ N ∈ frequencies512 ε x,
            (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2) ≤ C * scale512 ε A x := by
  sorry

/-- The finite endpoint replacement step, assembled from the exact count
identity, the algebraic factorization, the uniform residue envelope and the power
against logarithm threshold. -/
theorem leaf_finite_endpoint561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∀ D : ℝ,
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          endpointError561 ε D x u v ≤ C * scale512 ε A x := by
  obtain ⟨ε₀, hε₀, hthr⟩ := leaf_endpoint_power_log_threshold561
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε' u v A hA D
  obtain ⟨C₁, hb₁⟩ := hthr ε hε hε' A hA D
  obtain ⟨C₂, hC₂, hb₂⟩ := leaf_endpoint_residue_envelope561 ε D u v
  refine ⟨max (max (C₂ * max C₁ 1) C₂) (max C₁ 3), ?_⟩
  intro x hx
  have hx3 : (3 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right C₁ 3) (le_max_right _ _)) hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hC₁le : C₁ ≤ max (max (C₂ * max C₁ 1) C₂) (max C₁ 3) :=
    le_trans (le_max_left C₁ 3) (le_max_right _ _)
  have hC₁x : C₁ ≤ x := le_trans hC₁le hx
  have hC₁C₂ : C₂ * C₁ ≤ max (max (C₂ * max C₁ 1) C₂) (max C₁ 3) := by
    refine le_trans (mul_le_mul_of_nonneg_left (le_max_left C₁ 1) hC₂.le) ?_
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hscale : 0 ≤ scale512 ε A x := by
    unfold scale512
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hx0 _) (sq_nonneg (length512 ε x)))
      (Real.rpow_nonneg hlog0 _)
  have hterm : ∀ N ∈ frequencies512 ε x,
      ‖completePrincipal561 ε D x u v N - truncatedMain512 ε D x u v N‖ ^ 2 =
        ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 := by
    intro N _
    rw [leaf_endpoint_factorization561 ε D x u v N,
      leaf_endpoint_count_identity561 ε x N]
    have hcast :
        ((((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) : ℂ) -
          ((length512 ε x : ℝ) : ℂ)) =
        (((((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) : ℝ) : ℂ) := by
      push_cast
      ring
    have hnormA : ‖((u * v / (Real.log x * Real.log (length512 ε x)) : ℝ) : ℂ)‖ ^ 2
        = (u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hnormD : ‖(((((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) : ℝ) : ℂ)‖ ^ 2 = (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hcast, norm_mul, norm_mul, mul_pow, mul_pow, hnormA, hnormD]
  have hmain : endpointError561 ε D x u v =
      ∑ N ∈ frequencies512 ε x, ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 := by
    unfold endpointError561
    exact Finset.sum_congr rfl hterm
  rw [hmain]
  calc ∑ N ∈ frequencies512 ε x, ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2
      ≤ ∑ N ∈ frequencies512 ε x, C₂ * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 :=
        Finset.sum_le_sum (fun N _ =>
          mul_le_mul_of_nonneg_right (hb₂ x hx3 N) (sq_nonneg _))
    _ = C₂ * (∑ N ∈ frequencies512 ε x, (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ C₂ * (C₁ * scale512 ε A x) :=
        mul_le_mul_of_nonneg_left (hb₁ x hC₁x) hC₂.le
    _ = (C₂ * C₁) * scale512 ε A x := by ring
    _ ≤ max (max (C₂ * max C₁ 1) C₂) (max C₁ 3) * scale512 ε A x :=
        mul_le_mul_of_nonneg_right hC₁C₂ hscale

end LeanLab.BHP1997.Decomp561m
