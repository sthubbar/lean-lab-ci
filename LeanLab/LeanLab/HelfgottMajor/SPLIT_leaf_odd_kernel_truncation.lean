import LeanLab.HelfgottMajor.SPLIT_leaf_odd_case

/-!
Split of `leaf_odd_kernel_truncation`, the kernel step of the odd branch of the explicit
Polya-Vinogradov inequality, see the header of `SPLIT_leaf_odd_case.lean` and P0014, the explicit
Polya-Vinogradov input of the major arc chapter of Helfgott's ternary Goldbach book.

The parent asks, for every cutoff `H >= 1` at once, that each partial sum of an odd primitive
character modulo `q >= 8` be at most `f(H) = sqrt q / pi * (sum_{h <= H} 1/h) + (2/5) q log q / H`.
Being uniform in `H`, that is the same as a bound by the minimum of `f` over `H`, and the minimum
sits at `H` of size `(2/5) pi sqrt q log q`, where `f` is at least
`sqrt q / pi * (1/2 log q + log log q + 17/10)`. The split is therefore:

* `leaf_odd_sharp_bound_large`: the cutoff free sharp odd bound
  `||S(n)|| <= sqrt q / pi * (1/2 log q + log log q + 17/10)` for `q > 1200`, which is the range of
  the sharpened explicit odd Polya-Vinogradov bounds, Pomerance 2011 route with the refinements of
  Frolenkov and Soundararajan 2013 and Bordignon and Kerr, whose leading constants are at or below
  `1/(2 pi)`;
* `leaf_odd_sharp_bound_small`: the same bound on the finite range `8 <= q <= 1200`, a finite
  computation over the odd primitive characters of those moduli;
* `odd_kernel_cutoff_optimization`, proved here: for every `H >= 1`, the cutoff free bound is at
  most `f(H)`, from `sum_{h <= H} 1/h >= log H + 1/2`, which is `gamma > 1/2`, and
  `log H + c / H >= log c + 1`.

Numerical check, S95, numpy: over all odd characters of prime modulus `11 <= p < 4000`,
the ratio of the largest partial sum to the cutoff free bound is at most `0.754`, reached at `p = 11`.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- For a primitive character `χ` modulo `q`, the Gauss sum `∑ a, χ a * e^(2πi a/q)` has complex
norm `√q`. This follows from `gaussSum_mul_gaussSum_eq_card` together with
`star_gaussSum_eq`: `gaussSum χ stdAddChar * conj (gaussSum χ stdAddChar) = q`. -/
lemma gaussSum_abs_sqrt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) :
    ‖gaussSum χ stdAddChar‖ = Real.sqrt q := by
  have h₁ : (χ : MulChar (ZMod q) ℂ) ≠ 1 := by
    intro h
    have h₂ : χ ((-1 : ℤ) : ZMod q) = (1 : ℂ) := by
      rw [h]
      simp [MulChar.one_apply]
    have h₃ : χ ((-1 : ℤ) : ZMod q) ≠ (1 : ℂ) := by
      exact h_odd
    contradiction
  
  have h₂ : IsPrimitive (stdAddChar : AddChar (ZMod q) ℂ) := isPrimitive_stdAddChar
  
  have h₃ : gaussSum χ stdAddChar * gaussSum χ⁻¹ (stdAddChar⁻¹) = (q : ℂ) := by
    apply gaussSum_mul_gaussSum_eq_card
    <;> simp_all [IsDomain]
    <;> norm_num
    <;> try assumption
  
  have h₄ : star (gaussSum χ stdAddChar) = gaussSum χ⁻¹ (stdAddChar⁻¹) := by
    apply star_gaussSum_eq
  
  have h₅ : ‖gaussSum χ stdAddChar‖ ^ 2 = (q : ℝ) := by
    calc
      ‖gaussSum χ stdAddChar‖ ^ 2 = ‖gaussSum χ stdAddChar * star (gaussSum χ stdAddChar)‖ := by
        rw [← Complex.norm_mul]
        have h : ‖star (gaussSum χ stdAddChar)‖ = ‖gaussSum χ stdAddChar‖ := by
          rw [Complex.norm_conj]
        rw [h]
        <;> ring_nf
        <;> simp [Complex.norm_sq]
        <;> ring_nf
      _ = ‖(q : ℂ)‖ := by
        rw [h₃, h₄]
      _ = (q : ℝ) := by simp [Complex.norm_ofReal]
  
  have h₆ : ‖gaussSum χ stdAddChar‖ = Real.sqrt q := by
    rw [Real.sqrt_eq_iff_sq_eq (by positivity)]
    rw [h₅]
    <;> norm_cast
    <;> simp [Real.sqrt_eq_iff_sq_eq]
    <;> nlinarith
  
  exact h₆

/-- LEAF: sharpened explicit odd Polya-Vinogradov, large moduli. For an odd primitive character
modulo `q > 1200`, every partial sum is at most `sqrt q / pi * (1/2 log q + log log q + 17/10)`,
that is `1/(2 pi) sqrt q log q + 1/pi sqrt q log log q + 0.542 sqrt q`. This is the Polya Fourier
expansion of the odd sawtooth kernel with the Gauss sum of norm `sqrt q`, in the sharpened explicit
form of Pomerance 2011 and Frolenkov and Soundararajan 2013, and for large `q` it also follows from
the leading constant `3/(8 pi)` of Bordignon; the threshold `1200` has to be checked against the
explicit lower order terms of the cited source. HARD -/
theorem leaf_odd_sharp_bound_large {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq : 1200 < q) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  sorry

/-- LEAF: the same cutoff free odd bound on the finite range `8 <= q <= 1200`, a finite
computation: by periodicity only `n < q` matters, and for each modulus and each odd primitive
character the largest partial sum is compared with
`sqrt q / pi * (1/2 log q + log log q + 17/10)`. The S95 numerics give a ratio at most `0.754` on the
prime moduli. HARD, a large certified finite computation over characters. -/
theorem leaf_odd_sharp_bound_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q) (hq : q ≤ 1200) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
  sorry

/-- The optimization over the cutoff: for `q >= 8` and every `H >= 1`, the cutoff free bound is at
most `sqrt q / pi * sum_{h <= H} 1/h + (2/5) q log q / H`. With `c = (2/5) pi sqrt q log q`, this
is `sum_{h <= H} 1/h >= log H + 1/2`, which is `gamma > 1/2`, then `log H + c/H >= log c + 1`, and
`log c >= 1/2 log q + log log q + 1/5` because `log (2 pi / 5) >= 1 - 5/(2 pi) >= 1/5`. -/
theorem odd_kernel_cutoff_optimization {q : ℕ} (hq8 : 8 ≤ q) (H : ℕ) (hH : 1 ≤ H) :
    sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) ≤
      sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) := by
  have hqR : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq8
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : (0 : ℝ) < log (q : ℝ) := Real.log_pos (by linarith)
  have hsqpos : (0 : ℝ) < sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  have hπ : (0 : ℝ) < π := pi_pos
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  -- harmonic sum lower bound
  have heq : (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) = (harmonic H : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Rat.cast_inv, Rat.cast_natCast]
    simp [one_div]
  have hharm : log (H : ℝ) + 1 / 2 ≤ (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) := by
    rw [heq]
    have h1 := eulerMascheroniConstant_lt_eulerMascheroniSeq' H
    have h2 := one_half_lt_eulerMascheroniConstant
    have hH0 : H ≠ 0 := by omega
    simp only [eulerMascheroniSeq', hH0, ite_false] at h1
    linarith
  -- the constant c
  set c : ℝ := 2 / 5 * π * (sqrt (q : ℝ) * log (q : ℝ)) with hc
  have hcpos : 0 < c := by positivity
  have hlogc : log c = log (2 / 5 * π) + (1 / 2 * log (q : ℝ) + log (log (q : ℝ))) := by
    rw [hc, Real.log_mul (by positivity) (by positivity),
      Real.log_mul hsqpos.ne' hlogq.ne', Real.log_sqrt hqpos.le]
    ring
  have hlog25 : (1 : ℝ) / 5 ≤ log (2 / 5 * π) := by
    have hx : (5 : ℝ) / 4 ≤ 2 / 5 * π := by linarith [Real.pi_gt_d2]
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 / 5 * π by positivity)
    have hinv : (2 / 5 * π)⁻¹ ≤ 4 / 5 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    linarith
  -- log H + c / H >= log c + 1
  have hkey : log c + 1 ≤ log (H : ℝ) + c / (H : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < c / (H : ℝ) by positivity)
    rw [Real.log_div hcpos.ne' hHpos.ne'] at h
    linarith
  -- assemble
  have hmain : 1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10 ≤
      (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) + c / (H : ℝ) := by
    linarith
  have hu : (0 : ℝ) ≤ sqrt (q : ℝ) / π := by positivity
  have hstep := mul_le_mul_of_nonneg_left hmain hu
  have herr : sqrt (q : ℝ) / π * (c / (H : ℝ)) = 2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) := by
    have hqsq : sqrt (q : ℝ) * sqrt (q : ℝ) = (q : ℝ) := Real.mul_self_sqrt hqpos.le
    have h0 : sqrt (q : ℝ) / π * (c / (H : ℝ)) =
        2 / 5 * ((sqrt (q : ℝ) * sqrt (q : ℝ)) * log (q : ℝ)) / (H : ℝ) := by
      rw [hc]
      field_simp
    rw [h0, hqsq]
  have hsplit : sqrt (q : ℝ) / π * ((∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) + c / (H : ℝ)) =
      sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        sqrt (q : ℝ) / π * (c / (H : ℝ)) := mul_add _ _ _
  rw [hsplit, herr] at hstep
  exact hstep

/-- Assembly: `leaf_odd_kernel_truncation` from the two cutoff free leaves and the proved
optimization over the cutoff `H`. -/
theorem leaf_odd_kernel_truncation_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q)
    (H : ℕ) (hH : 1 ≤ H) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) := by
  -- `hq` is implied by `hq8` and is kept only to match the parent statement exactly
  clear hq
  have hfree : ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + 17 / 10) := by
    rcases le_or_gt q 1200 with hs | hl
    · exact leaf_odd_sharp_bound_small χ hχ h_odd hq8 hs n
    · exact leaf_odd_sharp_bound_large χ hχ h_odd hl n
  exact hfree.trans (odd_kernel_cutoff_optimization hq8 H hH)

end LeanLab.HelfgottMajor.PolyaVinogradov123
