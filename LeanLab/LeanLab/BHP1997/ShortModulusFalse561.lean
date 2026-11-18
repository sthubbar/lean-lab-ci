/-
Refutation of the statement of leaf_short_modulus_decomposition561 in
LeanLab.BHP1997.SPLIT_leaf_short_prefix_replacement561, exactly as Lean parses it.
The body of the interval integral notation extends as far right as it can, so the
subtracted principal model term of the stated right hand side sits inside the first
integral over t and inside the sum over the reduced residues r, not outside as one
term per modulus.  The stated identity then fails.  Counterexample: epsilon equal to
-31/20, so the block length is 1/2 at x = 2; D = 0, u = v = 1, b = 0, N = 3.  Only the
modulus 1 occurs, the half width is 2, the left side is 4 / (log 2)^2 and the right
side is 16 / (log 2)^3.  The statement of the leaf is copied verbatim and is not
changed anywhere.  This refutes the statement as typed, not P0069 page 7.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_short_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- The statement of `leaf_short_modulus_decomposition561`, copied verbatim and
quantified over all its arguments, is false. -/
theorem leaf_short_modulus_decomposition561_false : ¬ (∀ (ε D x u v : ℝ) (b : ℕ → ℂ) (N : ℕ),
    longPrincipal561 ε D x b u N - principalArc512 ε D x u v N =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t)) := by
  intro h
  have h1 := h (-31/20) 0 2 1 1 (fun _ => 0) 3
  have hY : length512 (-31/20) 2 = 1/2 := by
    unfold length512; norm_num [Real.rpow_neg_one]
  have key : ∀ t : ℝ, (@fourier 1 ((2 : ℕ) : ℤ) (t : AddCircle (1 : ℝ))) *
      @fourier 1 ((1 : ℕ) : ℤ) (t : AddCircle (1 : ℝ)) *
      @fourier 1 (-((3 : ℕ) : ℤ)) (t : AddCircle (1 : ℝ)) = 1 := by
    intro t
    rw [← fourier_add, ← fourier_add]
    norm_num
  have hJ : ∀ t : ℝ, ((AddCircle.toCircle ((2 : ℕ) • (t : AddCircle (1 : ℝ))) : Circle) : ℂ) *
      ((AddCircle.toCircle (t : AddCircle (1 : ℝ)) : Circle) : ℂ) *
      (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * 3 * ↑t)) = 1 := by
    intro t
    have e : ((AddCircle.toCircle ((2 : ℕ) • (t : AddCircle (1 : ℝ))) : Circle) : ℂ) =
        @fourier 1 ((2 : ℕ) : ℤ) (t : AddCircle (1 : ℝ)) := by
      rw [fourier_apply, natCast_zsmul]
    rw [e]
    have := key t
    norm_num at this ⊢
    exact this
  unfold longPrincipal561 principalArc512 integrand512 ramanujan512 at h1
  rw [hY] at h1
  norm_num [polynomial512] at h1
  simp only [hJ] at h1
  norm_num at h1
  have hR : (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * 3)) ≠ 0 := by
    simp [Complex.exp_ne_zero]
  have hl2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hh : ((Real.log (1 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : Real.log (1 / 2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [this]; exact_mod_cast (neg_ne_zero.mpr hpos.ne')
  rw [hl2] at h1
  field_simp at h1
  have h2 : Real.log 2 * 4 = 16 := by
    have h3 := congrArg Complex.re h1
    simpa [Complex.log_re] using h3
  linarith

end LeanLab.BHP1997.Decomp561n
