/-
Unit U-1536, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0026: J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I,
Acta Arith. 109.2 (2003), 169-194.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

The step decomposed by this unit and its two sibling files: Corollary 1 of Section 7, p. 185,
the large deviation bound for the power of two sum
  `G_L(x) = Σ_{j<L} e(2^j x)`,
namely `|G_L(x)| ≤ d L` outside a set `E ⊆ [0,1]` with `|E| = O(N^{-1/2} L^{-100})`.
It is used in (10.5) and (10.6), p. 191, the minor arc part of Lemma 13.

File a, Section 4 of the paper, pp. 172-177: Lemma 4 for `G_L` and the exponential Chebyshev step
of Section 7, p. 184.  The paper's Lemma 4 constant `c (1 + √A)` is replaced by the weaker
`11 (1 + A)`, using `4^j ≤ (2j+1) C(2j,j)` in place of Stirling; a polynomial factor in `L` is
harmless for Corollary 1.

Definitions: `Gpow`, `Spow = Re Gpow`, `EL L λ = ∫_0^1 exp(λ S_L)`, `devSet L d = {x ∈ [0,1] : |G_L x| > dL}`.
Assemblies, CONDITIONAL ON the leaves of this file: `lemma4_GL`, `devSet_le`.
-/
import Mathlib

namespace LeanLab.Linnik.Decomp1536a

open Real MeasureTheory Finset

/-- `G_L(x) = Σ_{j=0}^{L-1} e(2^j x)`, Section 4, p. 172, with `g = 2`. -/
noncomputable def Gpow (L : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range L, Complex.exp (2 * π * Complex.I * ((2 : ℂ) ^ j * x))

/-- `S_L(x) = Re G_L(x) = Σ_{j=0}^{L-1} cos(2π 2^j x)`, Section 4, p. 172. -/
noncomputable def Spow (L : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range L, Real.cos (2 * π * ((2 : ℝ) ^ j * x))

/-- `E_L = ∫_0^1 e^{λ S_L(x)} dx`, proof of Theorem 2, p. 173. -/
noncomputable def EL (L : ℕ) (lam : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (lam * Spow L x)

/-- The large deviation set `{x ∈ [0,1] : |G_L(x)| > dL}` of Section 7, p. 184. -/
def devSet (L : ℕ) (d : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ d * L < ‖Gpow L x‖}

/-- LEAF. Unit U-1536. `Re G_L(x) = S_L(x)`, the definition of `S_L` in Section 4, p. 172. -/
theorem re_GL (L : ℕ) (x : ℝ) : (Gpow L x).re = Spow L x := by
  simp only [Gpow, Spow]
  rw [Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  have h1 : 2 * π * Complex.I * ((2 : ℂ) ^ j * x) = (2 * π * ((2 : ℝ) ^ j * x) : ℝ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.exp_ofReal_mul_I_re]

/-- LEAF. Unit U-1536. The trivial bound `|G_L(x)| ≤ L`, used in the proof of Lemma 4 on p. 176
as `|G(x)| ≤ A`. -/
theorem norm_GL_le (L : ℕ) (x : ℝ) : ‖Gpow L x‖ ≤ L := by
  simp only [Gpow]
  apply le_trans (norm_sum_le _ _)
  have h1 : ∑ j ∈ range L, ‖Complex.exp (2 * π * Complex.I * ((2 : ℂ) ^ j * x))‖ = ∑ j ∈ range L, (1 : ℝ) := by
    apply sum_congr rfl
    intro j hj
    have h2 : 2 * π * Complex.I * ((2 : ℂ) ^ j * x) = (2 * π * ((2 : ℝ) ^ j * x) : ℝ) * Complex.I := by
      push_cast; ring
    rw [h2, Complex.norm_exp_ofReal_mul_I]
  rw [h1, sum_const, card_range, nsmul_eq_mul, mul_one]

/-- LEAF. Unit U-1536. `x ↦ |G_L(x)|` is continuous; a finite sum of exponentials. -/
theorem continuous_GL_norm (L : ℕ) : Continuous fun x : ℝ => ‖Gpow L x‖ := by
  have h1 : Continuous (Gpow L) := by
    unfold Gpow
    apply continuous_finsetSum
    intro j hj
    apply Continuous.comp Complex.continuous_exp
    exact continuous_const.mul (continuous_const.mul Complex.continuous_ofReal)
  exact Continuous.norm h1

/-- LEAF. Unit U-1536. `S_L` is continuous; a finite sum of cosines. -/
theorem continuous_SL (L : ℕ) : Continuous (Spow L) := by
  unfold Spow
  apply continuous_finsetSum
  intro j hj
  apply Continuous.comp continuous_cos
  exact continuous_const.mul (continuous_const.mul continuous_id')

/-- LEAF. Unit U-1536. Exponential Chebyshev inequality of Section 7, p. 184:
for `λ ≥ 0`, `∫_0^1 e^{λ|G_L|} ≥ Δ e^{λ d L}` where `Δ` is the measure of the large deviation
set, written as `Δ ≤ e^{-λ d L} ∫_0^1 e^{λ |G_L|}`. -/
theorem markov {L : ℕ} {d lam : ℝ} (hlam : 0 ≤ lam) :
    volume (devSet L d) ≤
      ENNReal.ofReal (Real.exp (-(lam * d * L)) * ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) := by
  sorry

/-- LEAF. Unit U-1536. The pointwise step (4.15) with the tail cut at `K` as in (4.17), p. 176:
for `0 ≤ r ≤ A` and `K = 2⌈A⌉ + 1`,
`e^r ≤ 2 Σ_{j<K} r^{2j}/(2j)! + 1`.
The paper writes `e^r ≤ e^r + e^{-r} = 2 Σ_j r^{2j}/(2j)!` and bounds the tail `j ≥ K` by an
absolute constant; with `2K ≥ 4A + 2` the tail is below `1/2`. -/
theorem exp_le_even_partial {A r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A) :
    Real.exp r ≤
      2 * ∑ j ∈ range (2 * ⌈A⌉₊ + 1), r ^ (2 * j) / ((2 * j).factorial : ℝ) + 1 := by
  sorry

/-- LEAF. Unit U-1536. The middle binomial term step before (4.16), p. 176, for `G = G_L`,
whose coefficients are all `1 ≥ 0`, so `G_0 = G`:
`∫_0^1 S_L^{2j} = 2^{-2j} Σ_ν C(2j,ν) ∫ G^ν Ḡ^{2j-ν} ≥ 2^{-2j} C(2j,j) ∫_0^1 |G_L|^{2j}`,
each integral being a nonnegative count of solutions of `Σ 2^{a_i} = Σ 2^{b_i}`. -/
theorem moment_binom (L j : ℕ) :
    (Nat.centralBinom j : ℝ) / 4 ^ j * ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j) := by
  sorry

/-- LEAF. Unit U-1536. `4^j ≤ (2j+1) C(2j,j)`, a weak form of the estimate behind (4.16), p. 176,
where the paper uses `4^j ≪ √(j+1) C(2j,j)`; Mathlib has
`Nat.four_pow_le_two_mul_self_mul_centralBinom`. -/
theorem four_pow_le (j : ℕ) : (4 : ℝ) ^ j ≤ (2 * j + 1) * Nat.centralBinom j := by
  rcases j with _ | j
  · simp
  · have h := Nat.four_pow_le_two_mul_self_mul_centralBinom (j+1) (by omega)
    have hc1 : (4 : ℝ) ^ (j + 1) = ((4 ^ (j + 1) : ℕ) : ℝ) := by norm_cast
    have hc2 : (((4 ^ (j + 1) : ℕ) : ℝ)) ≤ (((2 * (j + 1) * Nat.centralBinom (j + 1) : ℕ) : ℝ)) := by exact_mod_cast h
    rw [hc1]
    apply le_trans hc2
    push_cast
    have : (2 * (j + 1) : ℝ) ≤ 2 * (j + 1) + 1 := by linarith
    nlinarith

/-- LEAF. Unit U-1536. `∫_0^1 S_L(x)^n dx ≥ 0` for every `n`, p. 176, line after (4.17):
`S_L^n` is a cosine polynomial with nonnegative coefficients, so its mean is its constant
coefficient, which is `≥ 0`. -/
theorem moment_SL_nonneg (L n : ℕ) : 0 ≤ ∫ x in (0 : ℝ)..1, Spow L x ^ n := by
  sorry

/-- LEAF. Unit U-1536. The even partial sums of the exponential moment, p. 176, estimate of the
first term of (4.17): if `f` is continuous and every moment `∫_0^1 f^n` is `≥ 0`, then for
`λ ≥ 0`, `Σ_{j<K} λ^{2j}/(2j)! ∫_0^1 f^{2j} ≤ ∫_0^1 e^{λ f}`, since
`∫ e^{λ f} = Σ_n λ^n/n! ∫ f^n` with all terms nonnegative. -/
theorem even_partial_le_int_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hmom : ∀ n : ℕ, 0 ≤ ∫ x in (0 : ℝ)..1, f x ^ n) {lam : ℝ} (hlam : 0 ≤ lam) (K : ℕ) :
    ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ∫ x in (0 : ℝ)..1, f x ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Real.exp (lam * f x) := by
  sorry

/-! ### Assemblies, CONDITIONAL ON the leaves above -/

/-- `E_L(λ) ≥ 1` for `λ ≥ 0`. CONDITIONAL ON `continuous_SL`, `moment_SL_nonneg`,
`even_partial_le_int_exp`. -/
theorem one_le_EL (L : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) : 1 ≤ EL L lam := by
  have h := even_partial_le_int_exp (continuous_SL L) (moment_SL_nonneg L) hlam 1
  simpa [EL] using h

/-- `∫_0^1 |G_L|^{2j} ≤ (2j+1) ∫_0^1 S_L^{2j}`, (4.16) of p. 176 in the weak form.
CONDITIONAL ON `moment_binom`, `four_pow_le`, `moment_SL_nonneg`. -/
theorem moment_G_le (L j : ℕ) :
    ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤ (2 * j + 1) * ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j) := by
  have hb := moment_binom L j
  have h4 := four_pow_le j
  have hS := moment_SL_nonneg L (2 * j)
  have hc : (0 : ℝ) < Nat.centralBinom j := by exact_mod_cast Nat.centralBinom_pos j
  have h4p : (0 : ℝ) < 4 ^ j := by positivity
  set M := ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j)
  set T := ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j)
  have hM : M ≤ 4 ^ j / Nat.centralBinom j * T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have : (Nat.centralBinom j : ℝ) / 4 ^ j * M * 4 ^ j = Nat.centralBinom j * M := by
      field_simp
    nlinarith
  have hq : (4 : ℝ) ^ j / Nat.centralBinom j ≤ 2 * j + 1 := by
    rw [div_le_iff₀ hc]; linarith
  calc M ≤ 4 ^ j / Nat.centralBinom j * T := hM
    _ ≤ (2 * j + 1) * T := mul_le_mul_of_nonneg_right hq hS

/-- Lemma 4, (4.13) of p. 175, for `G = λ G_L`, in the weak form
`∫_0^1 e^{λ|G_L|} ≤ 11 (1 + λL) ∫_0^1 e^{λ S_L}` for `λ ≥ 0`.
CONDITIONAL ON the leaves of this file. -/
theorem lemma4_GL (L : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖) ≤ 11 * (1 + lam * L) * EL L lam := by
  set A := lam * L with hAdef
  set K := 2 * ⌈A⌉₊ + 1 with hK
  have hA : 0 ≤ A := mul_nonneg hlam (Nat.cast_nonneg _)
  have hcG := continuous_GL_norm L
  have hcS := continuous_SL L
  have hE1 := one_le_EL L hlam
  -- coefficients
  set c : ℕ → ℝ := fun j => lam ^ (2 * j) / ((2 * j).factorial : ℝ) with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by simp only [hc]; positivity
  set M : ℕ → ℝ := fun j => ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) with hM
  set T : ℕ → ℝ := fun j => ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j) with hT
  have hpt : ∀ x, Real.exp (lam * ‖Gpow L x‖) ≤
      2 * ∑ j ∈ range K, c j * ‖Gpow L x‖ ^ (2 * j) + 1 := by
    intro x
    have h := exp_le_even_partial (A := A) (mul_nonneg hlam (norm_nonneg (Gpow L x)))
      (mul_le_mul_of_nonneg_left (norm_GL_le L x) hlam)
    convert h using 3
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hc]; rw [mul_pow]; ring
  have hint1 : IntervalIntegrable (fun x => Real.exp (lam * ‖Gpow L x‖)) volume 0 1 :=
    (Real.continuous_exp.comp (continuous_const.mul hcG)).intervalIntegrable _ _
  have hcont_j : ∀ j, Continuous fun x => c j * ‖Gpow L x‖ ^ (2 * j) :=
    fun j => continuous_const.mul (hcG.pow _)
  have hcont_sum : Continuous fun x => 2 * ∑ j ∈ range K, c j * ‖Gpow L x‖ ^ (2 * j) + 1 :=
    (continuous_const.mul (continuous_finsetSum _ fun j _ => hcont_j j)).add continuous_const
  have h1 : ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖) ≤
      ∫ x in (0 : ℝ)..1, (2 * ∑ j ∈ range K, c j * ‖Gpow L x‖ ^ (2 * j) + 1) :=
    intervalIntegral.integral_mono_on (by norm_num) hint1 (hcont_sum.intervalIntegrable _ _)
      fun x _ => hpt x
  have h2 : ∫ x in (0 : ℝ)..1, (2 * ∑ j ∈ range K, c j * ‖Gpow L x‖ ^ (2 * j) + 1) =
      2 * ∑ j ∈ range K, c j * M j + 1 := by
    have hI1 : IntervalIntegrable
        (fun x => 2 * ∑ j ∈ range K, c j * ‖Gpow L x‖ ^ (2 * j)) volume 0 1 :=
      (continuous_const.mul (continuous_finsetSum _ fun j _ => hcont_j j)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun j _ => (hcont_j j).intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const_mul, hM]
    simp
  have h3 : ∑ j ∈ range K, c j * M j ≤ (2 * K - 1) * ∑ j ∈ range K, c j * T j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjK : (j : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.mp hj; exact_mod_cast this
    have hMj := moment_G_le L j
    have hTj : 0 ≤ T j := moment_SL_nonneg L (2 * j)
    calc c j * M j ≤ c j * ((2 * j + 1) * T j) := mul_le_mul_of_nonneg_left hMj (hc0 j)
      _ ≤ c j * ((2 * K - 1) * T j) := by
          apply mul_le_mul_of_nonneg_left _ (hc0 j)
          apply mul_le_mul_of_nonneg_right _ hTj
          linarith
      _ = (2 * K - 1) * (c j * T j) := by ring
  have h4 : ∑ j ∈ range K, c j * T j ≤ EL L lam :=
    even_partial_le_int_exp hcS (moment_SL_nonneg L) hlam K
  have hK1 : (1 : ℝ) ≤ K := by simp only [hK]; push_cast; have := Nat.cast_nonneg (α := ℝ) ⌈A⌉₊; linarith
  have hceil : (⌈A⌉₊ : ℝ) ≤ A + 1 := (Nat.ceil_lt_add_one hA).le
  have hKA : (4 * K - 1 : ℝ) ≤ 11 * (1 + A) := by
    simp only [hK]; push_cast; nlinarith
  have hEL0 : 0 ≤ EL L lam := by linarith
  calc ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)
      ≤ 2 * ∑ j ∈ range K, c j * M j + 1 := h1.trans h2.le
    _ ≤ 2 * ((2 * K - 1) * EL L lam) + EL L lam := by
        have := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 2 * K - 1)
        linarith
    _ = (4 * K - 1) * EL L lam := by ring
    _ ≤ 11 * (1 + A) * EL L lam := mul_le_mul_of_nonneg_right hKA hEL0

/-- The large deviation bound of Section 7, p. 184, before the numerical input:
`|{x ∈ [0,1] : |G_L(x)| > dL}| ≤ 11 (1 + λL) e^{-λ d L} E_L(λ)` for `λ ≥ 0`.
CONDITIONAL ON the leaves of this file. -/
theorem devSet_le (L : ℕ) (d : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    volume (devSet L d) ≤
      ENNReal.ofReal (11 * (1 + lam * L) * Real.exp (-(lam * d * L)) * EL L lam) := by
  refine (markov hlam).trans (ENNReal.ofReal_le_ofReal ?_)
  have := lemma4_GL L hlam
  have he := Real.exp_pos (-(lam * d * L))
  calc Real.exp (-(lam * d * L)) * ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)
      ≤ Real.exp (-(lam * d * L)) * (11 * (1 + lam * L) * EL L lam) :=
        mul_le_mul_of_nonneg_left this he.le
    _ = 11 * (1 + lam * L) * Real.exp (-(lam * d * L)) * EL L lam := by ring

end LeanLab.Linnik.Decomp1536a
