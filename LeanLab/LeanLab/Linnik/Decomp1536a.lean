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
import LeanLab.Ported.Prove2Me.Linnik1536a

namespace LeanLab.Linnik.Decomp1536a

open Real MeasureTheory Finset

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
  exact LeanLab.Ported.Prove2Me.Linnik1536a.markov hlam

/-- LEAF. Unit U-1536. The pointwise step (4.15) with the tail cut at `K` as in (4.17), p. 176:
for `0 ≤ r ≤ A` and `K = 2⌈A⌉ + 1`,
`e^r ≤ 2 Σ_{j<K} r^{2j}/(2j)! + 1`.
The paper writes `e^r ≤ e^r + e^{-r} = 2 Σ_j r^{2j}/(2j)!` and bounds the tail `j ≥ K` by an
absolute constant; with `2K ≥ 4A + 2` the tail is below `1/2`. -/
theorem exp_le_even_partial {A r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A) :
    Real.exp r ≤
      2 * ∑ j ∈ range (2 * ⌈A⌉₊ + 1), r ^ (2 * j) / ((2 * j).factorial : ℝ) + 1 := by
  exact LeanLab.Ported.Prove2Me.Linnik1536a.exp_le_even_partial hr hrA

/-- LEAF. Unit U-1536. The middle binomial term step before (4.16), p. 176, for `G = G_L`,
whose coefficients are all `1 ≥ 0`, so `G_0 = G`:
`∫_0^1 S_L^{2j} = 2^{-2j} Σ_ν C(2j,ν) ∫ G^ν Ḡ^{2j-ν} ≥ 2^{-2j} C(2j,j) ∫_0^1 |G_L|^{2j}`,
each integral being a nonnegative count of solutions of `Σ 2^{a_i} = Σ 2^{b_i}`. -/
theorem moment_binom (L j : ℕ) :
    (Nat.centralBinom j : ℝ) / 4 ^ j * ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j) := by
  exact LeanLab.Ported.Prove2Me.Linnik1536a.moment_binom L j

/-- LEAF. Unit U-1536. `4^j ≤ (2j+1) C(2j,j)`, a weak form of the estimate behind (4.16), p. 176,
where the paper uses `4^j ≪ √(j+1) C(2j,j)`; Mathlib has
`Nat.four_pow_le_two_mul_self_mul_centralBinom`. -/
theorem four_pow_le (j : ℕ) : (4 : ℝ) ^ j ≤ (2 * j + 1) * Nat.centralBinom j :=
  LeanLab.Ported.Prove2Me.Linnik1536a.four_pow_le j

/-- LEAF. Unit U-1536. `∫_0^1 S_L(x)^n dx ≥ 0` for every `n`, p. 176, line after (4.17):
`S_L^n` is a cosine polynomial with nonnegative coefficients, so its mean is its constant
coefficient, which is `≥ 0`. -/
theorem moment_SL_nonneg (L n : ℕ) : 0 ≤ ∫ x in (0 : ℝ)..1, Spow L x ^ n := by
  exact LeanLab.Ported.Prove2Me.Linnik1536a.moment_SL_nonneg L n

/-- LEAF. Unit U-1536. The even partial sums of the exponential moment, p. 176, estimate of the
first term of (4.17): if `f` is continuous and every moment `∫_0^1 f^n` is `≥ 0`, then for
`λ ≥ 0`, `Σ_{j<K} λ^{2j}/(2j)! ∫_0^1 f^{2j} ≤ ∫_0^1 e^{λ f}`, since
`∫ e^{λ f} = Σ_n λ^n/n! ∫ f^n` with all terms nonnegative. -/
theorem even_partial_le_int_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hmom : ∀ n : ℕ, 0 ≤ ∫ x in (0 : ℝ)..1, f x ^ n) {lam : ℝ} (hlam : 0 ≤ lam) (K : ℕ) :
    ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ∫ x in (0 : ℝ)..1, f x ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Real.exp (lam * f x) := by
  exact LeanLab.Ported.Prove2Me.Linnik1536a.even_partial_le_int_exp hf hmom hlam K

/-! ### Assemblies, CONDITIONAL ON the leaves above -/

/- The accepted port now proves all six leaves. The original dependency comments
are retained. These four assemblies have no remaining unproved input. -/

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

/-! ### Further estimates from the proof of Theorem 2 -/

open Filter
open scoped Topology

/-- Auxiliary square of the central binomial lower bound for p.176 display 4.16. -/
theorem centralBinom_sq_lower (j : ℕ) :
    (16 : ℝ) ^ j ≤ (4 * j + 1) * (Nat.centralBinom j : ℝ) ^ 2 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hc : ((j : ℝ) + 1) * (Nat.centralBinom (j + 1) : ℝ) =
        2 * (2 * j + 1) * Nat.centralBinom j := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ j
    have hpos : 0 < ((j : ℝ) + 1) ^ 2 := by positivity
    apply (mul_le_mul_iff_of_pos_right hpos).mp
    push_cast
    calc (16 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) ^ 2
        ≤ (4 * j + 1) * (Nat.centralBinom j : ℝ) ^ 2 * 16 * ((j : ℝ) + 1) ^ 2 := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ih (by norm_num)) hpos.le
      _ ≤ (4 * ((j : ℝ) + 1) + 1) * (2 * (2 * j + 1) * Nat.centralBinom j) ^ 2 := by
          nlinarith [sq_nonneg (Nat.centralBinom j : ℝ)]
      _ = (4 * ((j : ℝ) + 1) + 1) * (Nat.centralBinom (j + 1) : ℝ) ^ 2 * ((j : ℝ) + 1) ^ 2 := by
          rw [← hc]
          ring

/-- An explicit square root factor in p.176 display 4.16. -/
theorem four_pow_le_sqrt_mul_centralBinom (j : ℕ) :
    (4 : ℝ) ^ j ≤ Real.sqrt (4 * j + 1) * Nat.centralBinom j := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hp : ((4 : ℝ) ^ j) ^ 2 = (16 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [hp, mul_pow, Real.sq_sqrt (by positivity)]
  exact centralBinom_sq_lower j

/-- The square root comparison of moments in p.176 display 4.16. -/
theorem moment_G_le_sqrt (L j : ℕ) :
    ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤ (Real.sqrt (4 * j + 1)) * ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j) := by
  have hb := moment_binom L j
  have h4 := four_pow_le_sqrt_mul_centralBinom j
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
  have hq : (4 : ℝ) ^ j / Nat.centralBinom j ≤ Real.sqrt (4 * j + 1) := by
    rw [div_le_iff₀ hc]; linarith
  calc M ≤ 4 ^ j / Nat.centralBinom j * T := hM
    _ ≤ (Real.sqrt (4 * j + 1)) * T := mul_le_mul_of_nonneg_right hq hS

/-- An explicit constant in the square root version of p.175 display 4.13. -/
theorem lemma4_GL_sqrt (L : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖) ≤ 9 * (1 + Real.sqrt (lam * L)) * EL L lam := by
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
  have h3 : ∑ j ∈ range K, c j * M j ≤ (Real.sqrt (4 * K + 1)) * ∑ j ∈ range K, c j * T j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjK : (j : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.mp hj; exact_mod_cast this
    have hMj := moment_G_le_sqrt L j
    have hTj : 0 ≤ T j := moment_SL_nonneg L (2 * j)
    calc c j * M j ≤ c j * (Real.sqrt (4 * j + 1) * T j) := mul_le_mul_of_nonneg_left hMj (hc0 j)
      _ ≤ c j * ((Real.sqrt (4 * K + 1)) * T j) := by
          apply mul_le_mul_of_nonneg_left _ (hc0 j)
          apply mul_le_mul_of_nonneg_right _ hTj
          exact Real.sqrt_le_sqrt (by linarith)
      _ = (Real.sqrt (4 * K + 1)) * (c j * T j) := by ring
  have h4 : ∑ j ∈ range K, c j * T j ≤ EL L lam :=
    even_partial_le_int_exp hcS (moment_SL_nonneg L) hlam K
  have hceil : (⌈A⌉₊ : ℝ) ≤ A + 1 := (Nat.ceil_lt_add_one hA).le
  have hKA : 2 * Real.sqrt (4 * K + 1) + 1 ≤ 9 * (1 + Real.sqrt A) := by
    have hKle : (K : ℝ) ≤ 2 * A + 3 := by
      simp only [hK]
      push_cast
      linarith
    have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
    have hb : 4 * (K : ℝ) + 1 ≤ (3 * Real.sqrt A + 4) ^ 2 := by
      nlinarith [Real.sqrt_nonneg A]
    have hs := Real.sqrt_le_sqrt hb
    rw [Real.sqrt_sq (by positivity)] at hs
    nlinarith [Real.sqrt_nonneg A]
  have hEL0 : 0 ≤ EL L lam := by linarith
  calc ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)
      ≤ 2 * ∑ j ∈ range K, c j * M j + 1 := h1.trans h2.le
    _ ≤ 2 * ((Real.sqrt (4 * K + 1)) * EL L lam) + EL L lam := by
        have := mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg (4 * K + 1))
        linarith
    _ = (2 * Real.sqrt (4 * K + 1) + 1) * EL L lam := by ring
    _ ≤ 9 * (1 + Real.sqrt A) * EL L lam := mul_le_mul_of_nonneg_right hKA hEL0

/-- The lower comparison in the proof of Theorem 2c on p.175. -/
theorem EL_le_norm_moment (L : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    EL L lam ≤ ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖) := by
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_SL L))).intervalIntegrable _ _
  · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_GL_norm L))).intervalIntegrable _ _
  · intro x _
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam
    rw [← re_GL]
    exact Complex.re_le_norm _

/-- The logarithmic form of the two comparisons on p.175. -/
theorem log_norm_moment_gap (L : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) - Real.log (EL L lam) ∧
    Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) - Real.log (EL L lam) ≤
      Real.log (11 * (1 + lam * L)) := by
  have he : 0 < EL L lam := lt_of_lt_of_le zero_lt_one (one_le_EL L hlam)
  have hl := EL_le_norm_moment L hlam
  have hc : 0 < 11 * (1 + lam * L) := by positivity
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log he hl)
  · have h := Real.log_le_log (he.trans_le hl) (lemma4_GL L hlam)
    rw [Real.log_mul hc.ne' he.ne'] at h
    linarith

/-- The polynomial factor in the weak form of display 4.13 has zero exponential rate. -/
theorem log_prefactor_div_tendsto_zero {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun L : ℕ => Real.log (11 * (1 + lam * L)) / (L : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun L : ℕ => Real.log (11 * (1 + lam)) / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hlog : Tendsto (fun L : ℕ => Real.log ((L : ℝ) + 1) / (L : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 1 hn)
    simpa [Function.comp_def, add_assoc] using h
  apply squeeze_zero (g := fun L : ℕ => Real.log (11 * (1 + lam)) / (L : ℝ) +
    Real.log ((L : ℝ) + 1) / (L : ℝ))
  · intro L
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Real.log_nonneg
    have h : 0 ≤ lam * (L : ℝ) := by positivity
    linarith
  · intro L
    have hC : 0 < 11 * (1 + lam) := by positivity
    have hL : 0 < (L : ℝ) + 1 := by positivity
    have h : 11 * (1 + lam * L) ≤ (11 * (1 + lam)) * ((L : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) L]
    have hle := Real.log_le_log (by positivity : 0 < 11 * (1 + lam * L)) h
    rw [Real.log_mul hC.ne' hL.ne'] at hle
    simpa [add_div] using div_le_div_of_nonneg_right hle (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  · simpa using hc.add hlog

/-- The two logarithmic moments differ by a term of zero rate, from p.175 display 4.13. -/
theorem log_norm_moment_gap_div_tendsto_zero {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun L : ℕ =>
      (Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) - Real.log (EL L lam)) /
        (L : ℝ)) atTop (𝓝 0) := by
  exact squeeze_zero
    (fun L => div_nonneg (log_norm_moment_gap L hlam).1 (Nat.cast_nonneg _))
    (fun L => div_le_div_of_nonneg_right (log_norm_moment_gap L hlam).2 (Nat.cast_nonneg _))
    (log_prefactor_div_tendsto_zero hlam)

/-- Theorem 2c on p.172, CONDITIONAL ON the rate limit of Theorem 2a. -/
theorem norm_moment_rate_of_EL_rate {lam psi : ℝ} (hlam : 0 ≤ lam)
    (hEL : Tendsto (fun L : ℕ => Real.log (EL L lam) / (L : ℝ)) atTop (𝓝 psi)) :
    Tendsto (fun L : ℕ =>
      Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) / (L : ℝ)) atTop (𝓝 psi) := by
  have h := hEL.add (log_norm_moment_gap_div_tendsto_zero hlam)
  simpa only [add_zero, ← add_div, add_sub_cancel] using h

/-- Display 4.3 on p.172, CONDITIONAL ON the rate limit of Theorem 2a. -/
theorem norm_moment_exp_of_EL_rate {lam psi : ℝ} (hlam : 0 ≤ lam)
    (hEL : Tendsto (fun L : ℕ => Real.log (EL L lam) / (L : ℝ)) atTop (𝓝 psi)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ L : ℕ, 1 ≤ L →
      (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) =
        Real.exp ((L : ℝ) * (psi + err L)) := by
  refine ⟨fun L => Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) /
    (L : ℝ) - psi, ?_, ?_⟩
  · simpa using (norm_moment_rate_of_EL_rate hlam hEL).sub_const psi
  · intro L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    have hI : 0 < ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖) :=
      lt_of_lt_of_le zero_lt_one ((one_le_EL L hlam).trans (EL_le_norm_moment L hlam))
    rw [show (L : ℝ) * (psi +
      (Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) / (L : ℝ) - psi)) =
        Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) by field_simp; ring]
    exact (Real.exp_log hI).symm

/-- The finite block decomposition on p.173 before display 4.4. -/
theorem Spow_add (M N : ℕ) (x : ℝ) :
    Spow (M + N) x = Spow M x + Spow N ((2 : ℝ) ^ M * x) := by
  unfold Spow
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [pow_add]
  congr 1
  ring

/-- The period one property used on p.173 before display 4.5. -/
theorem Spow_periodic (L : ℕ) : Function.Periodic (Spow L) 1 := by
  intro x
  unfold Spow
  refine sum_congr rfl fun j _ => ?_
  rw [show 2 * π * ((2 : ℝ) ^ j * (x + 1)) =
    2 * π * ((2 : ℝ) ^ j * x) + (2 ^ j : ℕ) * (2 * π) by push_cast; ring]
  exact Real.cos_add_nat_mul_two_pi _ _

/-- The dyadic block distortion estimate on p.174 before displays 4.8 and 4.9. -/
theorem Spow_block_distortion (M : ℕ) (k x y : ℝ) :
    |Spow M ((x + k) / (2 : ℝ) ^ M) - Spow M ((y + k) / (2 : ℝ) ^ M)| ≤
      2 * π * |x - y| := by
  have ht (j : ℕ) :
      |Real.cos (2 * π * ((2 : ℝ) ^ j * ((x + k) / 2 ^ M))) -
        Real.cos (2 * π * ((2 : ℝ) ^ j * ((y + k) / 2 ^ M)))| ≤
        (2 * π * (2 : ℝ) ^ j / 2 ^ M) * |x - y| := by
    calc _ ≤ |2 * π * ((2 : ℝ) ^ j * ((x + k) / 2 ^ M)) -
        2 * π * ((2 : ℝ) ^ j * ((y + k) / 2 ^ M))| := Real.abs_cos_sub_cos_le _ _
      _ = _ := by
        rw [show 2 * π * ((2 : ℝ) ^ j * ((x + k) / 2 ^ M)) -
          2 * π * ((2 : ℝ) ^ j * ((y + k) / 2 ^ M)) =
          (2 * π * (2 : ℝ) ^ j / 2 ^ M) * (x - y) by ring]
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * (2 : ℝ) ^ j / 2 ^ M)]
  have hg : ∑ j ∈ range M, (2 : ℝ) ^ j = 2 ^ M - 1 := by
    have h := geom_sum_mul (2 : ℝ) M
    norm_num at h
    exact h
  unfold Spow
  rw [← sum_sub_distrib]
  calc _ ≤ ∑ j ∈ range M, |Real.cos (2 * π * ((2 : ℝ) ^ j * ((x + k) / 2 ^ M))) -
        Real.cos (2 * π * ((2 : ℝ) ^ j * ((y + k) / 2 ^ M)))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range M, (2 * π * (2 : ℝ) ^ j / 2 ^ M) * |x - y| :=
      sum_le_sum fun j _ => ht j
    _ = (2 * π / (2 : ℝ) ^ M * |x - y|) * ∑ j ∈ range M, (2 : ℝ) ^ j := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring
    _ ≤ 2 * π * |x - y| := by
      rw [hg]
      have hp : (0 : ℝ) < 2 ^ M := by positivity
      have hh : ((2 : ℝ) ^ M - 1) / 2 ^ M ≤ 1 := by rw [div_le_iff₀ hp]; linarith
      calc (2 * π / (2 : ℝ) ^ M * |x - y|) * (2 ^ M - 1)
          = (2 * π * |x - y|) * (((2 : ℝ) ^ M - 1) / 2 ^ M) := by ring
        _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * π) (abs_nonneg (x - y))]

/-- The equal interval partition and change of variables used in p.173 display 4.5. -/
theorem integral_unit_split {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..1, f x) = (1 / (n : ℝ)) *
      ∑ k ∈ range n, ∫ x in (0 : ℝ)..1, f ((x + k) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / n) (n := n) (μ := volume) (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_div, div_self hn0] at hsplit
  rw [← hsplit, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have h := intervalIntegral.inv_smul_integral_comp_div_add f (n : ℝ) ((k : ℝ) / n)
    (a := (0 : ℝ)) (b := 1)
  simpa only [smul_eq_mul, zero_div, zero_add, add_zero, Nat.cast_add, Nat.cast_one,
    add_div, one_div, add_comm] using h.symm

/-- The trivial absolute bound for S used in Section 4, pp.173 and 176. -/
theorem abs_Spow_le (L : ℕ) (x : ℝ) : |Spow L x| ≤ L := by
  rw [← re_GL]
  exact (Complex.abs_re_le_norm _).trans (norm_GL_le L x)

/-- The elementary exponential moment bounds from the Section 4 definitions. -/
theorem EL_exp_bounds (L : ℕ) (lam : ℝ) :
    Real.exp (-|lam| * L) ≤ EL L lam ∧ EL L lam ≤ Real.exp (|lam| * L) := by
  have hpt (x : ℝ) : -|lam| * L ≤ lam * Spow L x ∧ lam * Spow L x ≤ |lam| * L := by
    have h : |lam * Spow L x| ≤ |lam| * L := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_Spow_le L x) (abs_nonneg _)
    simpa only [neg_mul] using abs_le.mp h
  have hc : Continuous fun x => Real.exp (lam * Spow L x) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_SL L))
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (f := fun _ : ℝ => Real.exp (-|lam| * L)) intervalIntegrable_const
      (hc.intervalIntegrable _ _) (fun x _ => Real.exp_le_exp.mpr (hpt x).1)
    simpa [EL] using h
  · have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (g := fun _ : ℝ => Real.exp (|lam| * L)) (hc.intervalIntegrable _ _)
      intervalIntegrable_const (fun x _ => Real.exp_le_exp.mpr (hpt x).2)
    simpa [EL] using h

/-- Strict positivity of every real exponential moment, Section 4 p.173. -/
theorem EL_pos (L : ℕ) (lam : ℝ) : 0 < EL L lam :=
  (Real.exp_pos _).trans_le (EL_exp_bounds L lam).1

/-- The normalized logarithmic moments are bounded, Section 4 p.173. -/
theorem EL_log_bounds (L : ℕ) (lam : ℝ) :
    -|lam| * L ≤ Real.log (EL L lam) ∧ Real.log (EL L lam) ≤ |lam| * L := by
  have hl := Real.log_le_log (Real.exp_pos _) (EL_exp_bounds L lam).1
  have hu := Real.log_le_log (EL_pos L lam) (EL_exp_bounds L lam).2
  simpa only [Real.log_exp] using And.intro hl hu

/-- The dyadic sampling average in p.173 display 4.5. -/
noncomputable def blockAverage (M : ℕ) (lam x : ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ M) * ∑ k ∈ range ((2 : ℕ) ^ M),
    Real.exp (lam * Spow M ((x + k) / (2 : ℝ) ^ M))

/-- Continuity of the finite sampling average, p.173 display 4.5. -/
theorem blockAverage_continuous (M : ℕ) (lam : ℝ) : Continuous (blockAverage M lam) := by
  unfold blockAverage
  apply continuous_const.mul
  apply continuous_finsetSum
  intro k _
  exact Real.continuous_exp.comp (continuous_const.mul
    ((continuous_SL M).comp ((continuous_id.add continuous_const).div_const _)))

/-- Averaging the sampling average recovers E_M, p.173 display 4.5. -/
theorem blockAverage_mean (M : ℕ) (lam : ℝ) :
    (∫ x in (0 : ℝ)..1, blockAverage M lam x) = EL M lam := by
  have hc : Continuous fun x => Real.exp (lam * Spow M x) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_SL M))
  have h := integral_unit_split hc (n := (2 : ℕ) ^ M) (by positivity)
  unfold blockAverage
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · simpa only [Nat.cast_pow, Nat.cast_ofNat, EL] using h.symm
  · intro k _
    exact (hc.comp ((continuous_id.add continuous_const).div_const _)).intervalIntegrable _ _

/-- The block integral identity in p.173 display 4.5. -/
theorem EL_block_identity (M N : ℕ) (lam : ℝ) :
    EL (M + N) lam = ∫ x in (0 : ℝ)..1,
      Real.exp (lam * Spow N x) * blockAverage M lam x := by
  have hc : Continuous fun x => Real.exp (lam * Spow (M + N) x) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_SL (M + N)))
  have h := integral_unit_split hc (n := (2 : ℕ) ^ M) (by positivity)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  rw [EL, h, ← intervalIntegral.integral_finsetSum (s := range ((2 : ℕ) ^ M))
    (f := fun k x => Real.exp (lam * Spow (M + N) ((x + k) / (2 : ℝ) ^ M)))]
  · rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    have hpt : (∑ k ∈ range ((2 : ℕ) ^ M),
        Real.exp (lam * Spow (M + N) ((x + k) / (2 : ℝ) ^ M))) =
        Real.exp (lam * Spow N x) * ∑ k ∈ range ((2 : ℕ) ^ M),
          Real.exp (lam * Spow M ((x + k) / (2 : ℝ) ^ M)) := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [Spow_add]
      have hpow : (2 : ℝ) ^ M ≠ 0 := by positivity
      rw [show (2 : ℝ) ^ M * ((x + k) / (2 : ℝ) ^ M) = x + k by field_simp]
      have hper : Spow N (x + (k : ℝ)) = Spow N x := by
        simpa using (Spow_periodic N).nat_mul k x
      rw [hper, mul_add, Real.exp_add]
      ring
    unfold blockAverage
    rw [hpt]
    ring
  · intro k _
    exact (hc.comp ((continuous_id.add continuous_const).div_const _)).intervalIntegrable _ _

/-- The bounded distortion comparison behind p.174 displays 4.8 and 4.9.
The absolute value permits every real lambda. -/
theorem blockAverage_ratio (M : ℕ) (lam : ℝ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    blockAverage M lam x ≤ Real.exp (2 * π * |lam|) * blockAverage M lam y := by
  have hxy : |x - y| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hterm (k : ℕ) : Real.exp (lam * Spow M ((x + k) / (2 : ℝ) ^ M)) ≤
      Real.exp (2 * π * |lam|) * Real.exp (lam * Spow M ((y + k) / (2 : ℝ) ^ M)) := by
    have hS := (Spow_block_distortion M k x y).trans
      (mul_le_mul_of_nonneg_left hxy (by positivity : 0 ≤ 2 * π))
    have hl : lam * (Spow M ((x + k) / (2 : ℝ) ^ M) - Spow M ((y + k) / (2 : ℝ) ^ M)) ≤
        |lam| * (2 * π) := by
      calc _ ≤ |lam * (Spow M ((x + k) / (2 : ℝ) ^ M) -
          Spow M ((y + k) / (2 : ℝ) ^ M))| := le_abs_self _
        _ = |lam| * |Spow M ((x + k) / (2 : ℝ) ^ M) -
          Spow M ((y + k) / (2 : ℝ) ^ M)| := abs_mul _ _
        _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hS (abs_nonneg _)
    calc _ ≤ Real.exp (2 * π * |lam| + lam * Spow M ((y + k) / (2 : ℝ) ^ M)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_add _ _
  have hs : (∑ k ∈ range ((2 : ℕ) ^ M), Real.exp (lam * Spow M ((x + k) / (2 : ℝ) ^ M))) ≤
      Real.exp (2 * π * |lam|) *
        ∑ k ∈ range ((2 : ℕ) ^ M), Real.exp (lam * Spow M ((y + k) / (2 : ℝ) ^ M)) := by
    rw [mul_sum]
    exact sum_le_sum fun k _ => hterm k
  unfold blockAverage
  calc _ ≤ (1 / (2 : ℝ) ^ M) * (Real.exp (2 * π * |lam|) *
      ∑ k ∈ range ((2 : ℕ) ^ M), Real.exp (lam * Spow M ((y + k) / (2 : ℝ) ^ M))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Integrating the comparison in p.174 displays 4.8 and 4.9 gives a uniform bound. -/
theorem blockAverage_le_EL (M : ℕ) (lam : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    blockAverage M lam x ≤ Real.exp (2 * π * |lam|) * EL M lam := by
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (f := fun _ : ℝ => blockAverage M lam x)
    (g := fun y : ℝ => Real.exp (2 * π * |lam|) * blockAverage M lam y)
    intervalIntegrable_const ((continuous_const.mul (blockAverage_continuous M lam)).intervalIntegrable _ _)
    (fun y hy => blockAverage_ratio M lam hx hy)
  simpa [intervalIntegral.integral_const_mul, blockAverage_mean] using h

/-- Quasi multiplicativity from p.173 display 4.5 and p.174 bounded distortion. -/
theorem EL_add_le (M N : ℕ) (lam : ℝ) :
    EL (M + N) lam ≤ Real.exp (2 * π * |lam|) * EL M lam * EL N lam := by
  have hc : Continuous fun x => Real.exp (lam * Spow N x) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_SL N))
  rw [EL_block_identity]
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (f := fun x => Real.exp (lam * Spow N x) * blockAverage M lam x)
    (g := fun x => Real.exp (lam * Spow N x) * (Real.exp (2 * π * |lam|) * EL M lam))
    ((hc.mul (blockAverage_continuous M lam)).intervalIntegrable _ _)
    ((hc.mul continuous_const).intervalIntegrable _ _)
    (fun x hx => mul_le_mul_of_nonneg_left (blockAverage_le_EL M lam hx) (Real.exp_nonneg _))
  refine h.trans_eq ?_
  rw [intervalIntegral.integral_mul_const]
  change EL N lam * (Real.exp (2 * π * |lam|) * EL M lam) = _
  ring

/-- Theorem 2a on p.172, proved by the block argument of pp.173 and 174 and Fekete's lemma. -/
theorem EL_rate_exists (lam : ℝ) :
    ∃ psi : ℝ, Tendsto (fun L : ℕ => Real.log (EL L lam) / (L : ℝ)) atTop (𝓝 psi) := by
  let C : ℝ := 2 * π * |lam|
  let u : ℕ → ℝ := fun L => Real.log (EL L lam) + C
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : Subadditive u := by
    intro M N
    have h := Real.log_le_log (EL_pos (M + N) lam) (EL_add_le M N lam)
    rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (EL_pos M lam).ne') (EL_pos N lam).ne',
      Real.log_mul (Real.exp_ne_zero _) (EL_pos M lam).ne', Real.log_exp] at h
    dsimp [u, C]
    linarith
  have hb : BddBelow (Set.range fun L : ℕ => u L / (L : ℝ)) := by
    refine ⟨-|lam|, ?_⟩
    rintro _ ⟨L, rfl⟩
    by_cases hL : L = 0
    · simp [hL]
    · have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
      rw [le_div_iff₀ hLp]
      have h := (EL_log_bounds L lam).1
      dsimp [u]
      linarith
  have hc : Tendsto (fun L : ℕ => C / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨hs.lim, ?_⟩
  simpa only [u, add_div, add_sub_cancel_right, sub_zero] using (hs.tendsto_lim hb).sub hc

/-- Theorem 2c, p.172 display 4.3, with no cited rate input left. -/
theorem norm_moment_asymptotic {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ psi : ℝ, ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ L : ℕ, 1 ≤ L →
      (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) = Real.exp ((L : ℝ) * (psi + err L)) := by
  obtain ⟨psi, hpsi⟩ := EL_rate_exists lam
  obtain ⟨err, herr, hform⟩ := norm_moment_exp_of_EL_rate hlam hpsi
  exact ⟨psi, err, herr, hform⟩

/-- The exponential form of Theorem 2a on p.172 display 4.1. -/
theorem EL_asymptotic (lam : ℝ) :
    ∃ psi : ℝ, ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ L : ℕ, 1 ≤ L →
      EL L lam = Real.exp ((L : ℝ) * (psi + err L)) := by
  obtain ⟨psi, hpsi⟩ := EL_rate_exists lam
  refine ⟨psi, fun L => Real.log (EL L lam) / (L : ℝ) - psi, ?_, ?_⟩
  · simpa using hpsi.sub_const psi
  · intro L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    rw [show (L : ℝ) * (psi + (Real.log (EL L lam) / (L : ℝ) - psi)) = Real.log (EL L lam) by
      field_simp; ring]
    exact (Real.exp_log (EL_pos L lam)).symm

/-- Displays 4.1 and 4.3 on p.172 with one common exponential rate. -/
theorem exponential_moments_common_rate {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ psi : ℝ, ∃ errS errG : ℕ → ℝ,
      Tendsto errS atTop (𝓝 0) ∧ Tendsto errG atTop (𝓝 0) ∧ ∀ L : ℕ, 1 ≤ L →
        EL L lam = Real.exp ((L : ℝ) * (psi + errS L)) ∧
        (∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) =
          Real.exp ((L : ℝ) * (psi + errG L)) := by
  obtain ⟨psi, hpsi⟩ := EL_rate_exists lam
  obtain ⟨errG, herrG, hformG⟩ := norm_moment_exp_of_EL_rate hlam hpsi
  let errS : ℕ → ℝ := fun L => Real.log (EL L lam) / (L : ℝ) - psi
  have herrS : Tendsto errS atTop (𝓝 0) := by simpa [errS] using hpsi.sub_const psi
  refine ⟨psi, errS, errG, herrS, herrG, ?_⟩
  intro L hL
  refine ⟨?_, hformG L hL⟩
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  dsimp [errS]
  rw [show (L : ℝ) * (psi + (Real.log (EL L lam) / (L : ℝ) - psi)) = Real.log (EL L lam) by
    field_simp; ring]
  exact (Real.exp_log (EL_pos L lam)).symm

end LeanLab.Linnik.Decomp1536a
