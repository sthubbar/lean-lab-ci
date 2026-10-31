/-
J. Liu, K.-M. Tsang 2005, Small prime solutions of ternary linear equations, Acta Arith. 118,
79-100. Unit U-1533, run 20261026T0004Z-24325, type DECOMPOSE, file c of three.

Lemma 4.1, p. 86: with `Vⱼ(λ) = Σ_{M < |aⱼ| m ≤ N} e(aⱼ m λ)`,
(i)  `∫_{|λ| ≤ 1/(2|aⱼ|)} |Vⱼ(λ)|² dλ ≪ N/|aⱼ|²`,
(ii) `∫_{|λ| ≤ 1/2} |Vⱼ(λ)|² dλ ≪ N/|aⱼ|`.
Both follow from orthogonality: expanding the square, each off-diagonal term integrates to 0.
We write `a = |aⱼ|` as a positive natural number and sum over natural `m`; for negative `aⱼ`
the function `Vⱼ` is the complex conjugate of ours, so `|Vⱼ|` is unchanged. The bounds are
proved with the explicit constant 2 under `a ≤ N`.

AI-written Lean code, Claude, 2026-10-26. Ternary Goldbach is Helfgott 2013; binary Goldbach is
OPEN, nothing here is progress on it.
-/
import Mathlib

namespace LeanLab.LiuTsang2005.Decomp1533c
open Real Complex intervalIntegral

/-- `e(x) = exp(2πix)`. -/
noncomputable def eF (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- The index set `{m ∈ ℕ : M < a m ≤ N}`. -/
noncomputable def idx (a : ℕ) (M N : ℝ) : Finset ℕ :=
  (Finset.range (⌊N⌋₊ + 1)).filter fun m => M < (a : ℝ) * m ∧ (a : ℝ) * m ≤ N

/-- `V(λ) = Σ_{M < a m ≤ N} e(a m λ)`, p. 86. -/
noncomputable def V (a : ℕ) (M N lam : ℝ) : ℂ := ∑ m ∈ idx a M N, eF ((a : ℝ) * m * lam)

/-- LEAF. Unit U-1533. Expanding the square in the proof of Lemma 4.1, p. 86:
`|V(λ)|² = Σ_m Σ_{m'} e((a m - a m') λ)` as complex numbers. -/
theorem normSq_V_expand (a : ℕ) (M N lam : ℝ) :
    (((‖V a M N lam‖ ^ 2 : ℝ)) : ℂ) =
      ∑ m ∈ idx a M N, ∑ m' ∈ idx a M N, eF (((a : ℝ) * m - a * m') * lam) := by
  classical
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold V
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m' hm'
  unfold eF
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

/-- LEAF. Unit U-1533. Integral of a finite double sum of exponentials over `[u, v]` is the
double sum of the integrals, the interchange step in the proof of Lemma 4.1, p. 86. -/
theorem integral_double_sum (s : Finset ℕ) (c : ℕ → ℕ → ℝ) (u v : ℝ) :
    ∫ lam in u..v, ∑ m ∈ s, ∑ m' ∈ s, eF (c m m' * lam) =
      ∑ m ∈ s, ∑ m' ∈ s, ∫ lam in u..v, eF (c m m' * lam) := by
  have hcont : ∀ m m', Continuous (fun lam : ℝ => eF (c m m' * lam)) := by
    intros
    unfold eF
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun m hm =>
    Continuous.intervalIntegrable (by fun_prop) u v)]
  apply Finset.sum_congr rfl
  intro m hm
  exact intervalIntegral.integral_finsetSum (fun m' hm' => (hcont m m').intervalIntegrable u v)

/-- LEAF. Unit U-1533. Orthogonality on the short interval of Lemma 4.1 (i), p. 86: for
`a > 0`, `∫_{-1/(2a)}^{1/(2a)} e((a m - a m') λ) dλ` is `1/a` when `m = m'` and `0` otherwise. -/
theorem orth_short (a : ℕ) (ha : 0 < a) (m m' : ℕ) :
    ∫ lam in (-(1 / (2 * (a : ℝ))))..(1 / (2 * (a : ℝ))), eF (((a : ℝ) * m - a * m') * lam) =
      if m = m' then ((1 / (a : ℝ) : ℝ) : ℂ) else 0 := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  by_cases h : m = m'
  · subst m'
    simp [eF, sub_self, intervalIntegral.integral_const]
    push_cast
    field_simp
    ring
  · rw [if_neg h]
    have hd : (m : ℂ) - m' ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hc : 2 * (π : ℂ) * I * ((a : ℂ) * m - a * m') ≠ 0 := by
      rw [← mul_sub]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (mul_ne_zero haC hd)
    simp only [eF, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast]
    simp_rw [← mul_assoc]
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp (2 * (π : ℂ) * I * ((a : ℂ) * m - a * m') * (1 / (2 * (a : ℝ)) : ℝ)) =
        Complex.exp (2 * (π : ℂ) * I * ((a : ℂ) * m - a * m') * (-(1 / (2 * (a : ℝ))) : ℝ)) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨(m : ℤ) - m', ?_⟩
      push_cast
      field_simp
      <;> simp_all
      <;> ring
    rw [he, sub_self, zero_div]

/-- LEAF. Unit U-1533. Orthogonality on the long interval of Lemma 4.1 (ii), p. 86: for
`a > 0`, `∫_{-1/2}^{1/2} e((a m - a m') λ) dλ` is `1` when `m = m'` and `0` otherwise. -/
theorem orth_long (a : ℕ) (ha : 0 < a) (m m' : ℕ) :
    ∫ lam in (-(1 / 2 : ℝ))..(1 / 2), eF (((a : ℝ) * m - a * m') * lam) =
      if m = m' then 1 else 0 := by
  by_cases h : m = m'
  · subst m'
    norm_num [eF]
  · rw [if_neg h]
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hd : (m : ℂ) - m' ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hc : 2 * (π : ℂ) * I * ((a : ℂ) * m - a * m') ≠ 0 := by
      rw [← mul_sub]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (mul_ne_zero haC hd)
    simp only [eF, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast]
    simp_rw [← mul_assoc]
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp (2 * (π : ℂ) * I * ((a : ℂ) * m - a * m') * (1 / 2 : ℝ)) =
        Complex.exp (2 * (π : ℂ) * I * ((a : ℂ) * m - a * m') * (-(1 / 2 : ℝ))) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨(a : ℤ) * ((m : ℤ) - m'), ?_⟩
      push_cast
      ring
    rw [he]
    simp

/-- LEAF. Unit U-1533. Real and complex integrals of `|V|²` agree, the bookkeeping step that lets
the proof of Lemma 4.1, p. 86, compute in `ℂ`. -/
theorem integral_ofReal_normSq (a : ℕ) (M N u v : ℝ) :
    (((∫ lam in u..v, ‖V a M N lam‖ ^ 2 : ℝ)) : ℂ) =
      ∫ lam in u..v, (((‖V a M N lam‖ ^ 2 : ℝ)) : ℂ) := by
  exact intervalIntegral.integral_ofReal.symm

/-- LEAF. Unit U-1533. Counting step of Lemma 4.1, p. 86: for `a > 0` and `N ≥ 0`, the number of
natural `m` with `M < a m ≤ N` is at most `N/a + 1`. -/
theorem card_idx_le (a : ℕ) (ha : 0 < a) (M N : ℝ) (hN : 0 ≤ N) :
    ((idx a M N).card : ℝ) ≤ N / a + 1 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdiv : 0 ≤ N / (a : ℝ) := div_nonneg hN haR.le
  have hsub : idx a M N ⊆ Finset.range (⌊N / (a : ℝ)⌋₊ + 1) := by
    intro m hm
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply (Nat.le_floor_iff hdiv).mpr
    rw [le_div_iff₀ haR]
    simpa [mul_comm] using (Finset.mem_filter.mp hm).2.2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  calc ((idx a M N).card : ℝ) ≤ (⌊N / (a : ℝ)⌋₊ + 1 : ℕ) := by exact_mod_cast hcard
    _ ≤ N / a + 1 := by
      push_cast
      simpa [add_comm] using add_le_add_right (Nat.floor_le hdiv) 1

/-- LEAF. Unit U-1533. Constant check for Lemma 4.1, p. 86: for `0 < a ≤ N`,
`N/a + 1 ≤ 2N/a`. -/
theorem count_le_two (a N : ℝ) (ha : 0 < a) (haN : a ≤ N) : N / a + 1 ≤ 2 * N / a := by
  rw [div_add_one ha.ne', div_le_div_iff_of_pos_right ha]
  linarith

/-- The exact value of the short integral: `∫_{-1/(2a)}^{1/(2a)} |V|² = #idx / a`.
PROVED from the exponential expansion and short orthogonality; zero sorry. -/
theorem integral_short_eq (a : ℕ) (ha : 0 < a) (M N : ℝ) :
    ∫ lam in (-(1 / (2 * (a : ℝ))))..(1 / (2 * (a : ℝ))), ‖V a M N lam‖ ^ 2 =
      (idx a M N).card / (a : ℝ) := by
  have h := integral_ofReal_normSq a M N (-(1 / (2 * (a : ℝ)))) (1 / (2 * (a : ℝ)))
  simp_rw [normSq_V_expand] at h
  rw [integral_double_sum (idx a M N) (fun m m' => (a : ℝ) * m - a * m')] at h
  simp_rw [orth_short a ha, Finset.sum_ite_eq, Finset.sum_ite_mem, Finset.inter_self,
    Finset.sum_const, nsmul_eq_mul] at h
  apply Complex.ofReal_injective
  rw [h]; push_cast; ring

/-- The exact value of the long integral: `∫_{-1/2}^{1/2} |V|² = #idx`.
PROVED from the exponential expansion and long orthogonality; zero sorry. -/
theorem integral_long_eq (a : ℕ) (ha : 0 < a) (M N : ℝ) :
    ∫ lam in (-(1 / 2 : ℝ))..(1 / 2), ‖V a M N lam‖ ^ 2 = (idx a M N).card := by
  have h := integral_ofReal_normSq a M N (-(1 / 2 : ℝ)) (1 / 2)
  simp_rw [normSq_V_expand] at h
  rw [integral_double_sum (idx a M N) (fun m m' => (a : ℝ) * m - a * m')] at h
  simp_rw [orth_long a ha, Finset.sum_ite_eq, Finset.sum_ite_mem, Finset.inter_self,
    Finset.sum_const, nsmul_eq_mul, mul_one] at h
  apply Complex.ofReal_injective
  rw [h]; push_cast; ring

/-- **Lemma 4.1 (i), p. 86**, with constant 2: for `0 < a ≤ N`,
`∫_{|λ| ≤ 1/(2a)} |V(λ)|² ≤ 2N/a²`. PROVED from exact orthogonality and counting; zero sorry. -/
theorem lemma41_i (a : ℕ) (ha : 0 < a) (M N : ℝ) (haN : (a : ℝ) ≤ N) :
    ∫ lam in (-(1 / (2 * (a : ℝ))))..(1 / (2 * (a : ℝ))), ‖V a M N lam‖ ^ 2 ≤
      2 * N / (a : ℝ) ^ 2 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [integral_short_eq a ha]
  have h1 := card_idx_le a ha M N (by linarith)
  have h2 := count_le_two (a : ℝ) N ha' haN
  rw [div_le_iff₀ ha']
  calc ((idx a M N).card : ℝ) ≤ 2 * N / a := le_trans h1 h2
    _ = 2 * N / (a : ℝ) ^ 2 * a := by field_simp

/-- **Lemma 4.1 (ii), p. 86**, with constant 2: for `0 < a ≤ N`,
`∫_{|λ| ≤ 1/2} |V(λ)|² ≤ 2N/a`. PROVED from exact orthogonality and counting; zero sorry. -/
theorem lemma41_ii (a : ℕ) (ha : 0 < a) (M N : ℝ) (haN : (a : ℝ) ≤ N) :
    ∫ lam in (-(1 / 2 : ℝ))..(1 / 2), ‖V a M N lam‖ ^ 2 ≤ 2 * N / (a : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [integral_long_eq a ha]
  exact le_trans (card_idx_le a ha M N (by linarith)) (count_le_two (a : ℝ) N ha' haN)

end LeanLab.LiuTsang2005.Decomp1533c
