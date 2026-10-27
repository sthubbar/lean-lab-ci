/-
Unit U-1546, run 20261026T0808Z-17522, STATE, track T1, paper P0097:
D. Zinoviev 1997, On Vinogradov's constant in Goldbach's ternary problem,
J. Number Theory 65, 334-358. Read from papers/P0097.pdf, page images of pp. 336 to 339.

Section 1 of the paper, the GRH inputs not yet stated anywhere in the lab:
* Lemma 1.2, p. 336, the zero weight sum `Σ 1.5/(2.25 + (T - γ)²) < 1 + 0.5 ln(qT)` and its
  case `T = 0`, p. 338, with the elementary steps (1.5), (1.6), (1.7), (1.8) and the closing
  arithmetic of p. 338 as separate leaves;
* Lemma 1.1, p. 336, the zero count in a window, PROVED from the weight bound of Lemma 1.2;
* Lemma 1.3, pp. 338 to 339, `|ψ(x, χ)| ≤ 0.83 √x ln² x`, with the two sum estimates and the
  closing arithmetic of p. 339 as separate leaves;
* Proposition 1.4, p. 339, `π(x; q, l) = Li(x)/φ(q) + 1.3 θ₁ √x ln x + θ₂ 10⁸`, with the
  integration by parts for `Li` from p. 341 as a leaf.
Lemma 1.5, Lemma 2.1, Lemmas 3.1 to 3.3 and Theorem 3.4 are already stated in this folder.

GRH is the lab's `LeanLab.DERZ1997.GRH`, zeros in the open strip. Zeros are counted without
multiplicity here: a finite set `Z` of distinct zeros, which is weaker than the paper's count
with multiplicity, so every statement below is implied by the paper's.

Change from the printed text, Lemma 1.1, second case: the paper prints `1.09(1 + 0.5 ln q)`
for `0 ≤ γ < 1`; its proof, "set T = 0", gives only `2.17(1 + 0.5 ln q)`, and that is the
form stated here, `lemma11_low`, for `|γ| ≤ 1`. Primitive characters are taken with modulus
`q ≥ 3`, so the principal character is excluded; Proposition 1.4 adds `(l, q) = 1` and
`q ≤ x^0.37`, the range of the paper's own proof through Lemma 1.3.

A `sorry` proves nothing. AI wrote the Lean code, Claude, 2026-10-26; checked only by the Lean
kernel. Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.DERZ1997.Statements

namespace LeanLab.Zinoviev1997.State1546
open Complex

/-! ### Definitions -/

/-- The nontrivial zeros of `L(s, χ)`, those in the open strip `0 < Re s < 1`. -/
def nontrivZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Set ℂ :=
  {s | DirichletCharacter.LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- The weight `1.5/(2.25 + (T - γ)²)` of a zero `ρ = β + iγ`, p. 336. -/
noncomputable def zeroWeight (T : ℝ) (ρ : ℂ) : ℝ :=
  1.5 / (2.25 + (T - ρ.im) ^ 2)

/-- The two bounds of Lemma 1.2 for a set `Zs` of zeros and a modulus `q`, p. 336 and p. 338:
every finite subset has weight sum below `1 + 0.5 ln(qT)` for `T ≥ 2`, and below
`1 + 0.5 ln q` at `T = 0`. -/
def ZeroWeightBounds (Zs : Set ℂ) (q : ℕ) : Prop :=
  (∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ, (↑Z : Set ℂ) ⊆ Zs →
      ∑ ρ ∈ Z, zeroWeight T ρ < 1 + 0.5 * Real.log (q * T)) ∧
  (∀ Z : Finset ℂ, (↑Z : Set ℂ) ⊆ Zs →
      ∑ ρ ∈ Z, zeroWeight 0 ρ < 1 + 0.5 * Real.log q)

/-- The twisted Chebyshev function `ψ(x, χ) = Σ_{n ≤ x} Λ(n) χ(n)`, p. 339. -/
noncomputable def psiChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- `π(x; q, l)`, the number of primes `p ≤ x` with `p ≡ l mod q`, p. 336 and p. 340. -/
noncomputable def piMod (x : ℝ) (q l : ℕ) : ℕ :=
  ((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = l % q)).card

/-- `Li(x) = ∫₂ˣ du/ln u`, p. 341. -/
noncomputable def zinLi (x : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..x, 1 / Real.log u

/-! ### Lemma 1.2, the elementary steps -/

/-- LEAF. Unit U-1546. Display (1.8), p. 338: for a zero with `β = 1/2` and `s = 2 + iT`,
`Re 1/(s - ρ) = (2 - β)/((2 - β)² + (T - γ)²) = 1.5/(2.25 + (T - γ)²)`. -/
theorem re_inv_sub_zero (T : ℝ) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    (1 / ((2 : ℂ) + T * I - ρ)).re = zeroWeight T ρ := by
  simp [one_div, Complex.inv_re, Complex.normSq_apply, State1546.zeroWeight, hρ,
    Complex.mul_re, Complex.mul_im]
  <;> ring

/-- LEAF. Unit U-1546. Display (1.5), p. 338: for `s = σ + iT` with `σ = 2 + d`,
`d ∈ {0, -1}`, so `1 ≤ σ ≤ 2`, and `T ≥ 2`, every partial sum of
`Re Σ_{n ≥ 1} (1/(2n) - 1/(s + 2n))` is below `1 + ½ ln T`. The terms are positive, so this
is the paper's bound on the full series. -/
theorem gamma_series_T {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 2 ≤ T) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re < 1 + 1 / 2 * Real.log T := by
  sorry

/-- LEAF. Unit U-1546. Display (1.6), p. 338: at `T = 0` and `1 ≤ σ ≤ 2`, every partial sum of
`Σ_{n ≥ 1} (1/(2n) - 1/(σ + 2n))` is below `1`. -/
theorem gamma_series_zero {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (1 / (2 * (n : ℝ)) - 1 / (σ + 2 * n)) < 1 := by
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      1 / (2 * (n : ℝ)) - 1 / (σ + 2 * n) ≤
        1 / (2 * (n : ℝ)) - 1 / (2 * ((n : ℝ) + 1)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    apply sub_le_sub_left
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have htel : ∑ n ∈ Finset.Icc 1 M,
      (1 / (2 * (n : ℝ)) - 1 / (2 * ((n : ℝ) + 1))) ≤ 1 / 2 := by
    by_cases hm : 1 ≤ M
    · have ht := Finset.sum_Icc_sub (M := ℝ) hm (fun n : ℕ => -(1 / (2 * (n : ℝ))))
      simp only [Nat.cast_add, Nat.cast_one, neg_sub_neg] at ht
      rw [ht]
      norm_num
      positivity
    · have : M = 0 := by omega
      simp [this]
  exact lt_of_le_of_lt ((Finset.sum_le_sum hterm).trans htel) (by norm_num)

/-- LEAF. Unit U-1546. Display (1.7), p. 338: `Σ_{n ≥ 1} Λ(n) n⁻² < 0.61`, every partial sum.
The true value is `-ζ'(2)/ζ(2) = 0.5699...`. -/
theorem vonMangoldt_sq_sum (M : ℕ) :
    ∑ n ∈ Finset.range M, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 < 0.61 := by
  sorry

/-- LEAF. Unit U-1546. The closing arithmetic of Lemma 1.2, p. 338:
`0.61 + ½ ln q - ½ ln π - γ/2 + 1 + ½ ln T < 1 + 0.5 ln(qT)`, `γ` Euler's constant, for
`q, T > 0`; at `T = 1` this is also the case `T = 0`, where (1.6) replaces `1 + ½ ln T` by 1. -/
theorem lemma12_arith {q T : ℝ} (hq : 0 < q) (hT : 0 < T) :
    0.61 + 1 / 2 * Real.log q - 1 / 2 * Real.log Real.pi - Real.eulerMascheroniConstant / 2
      + 1 + 1 / 2 * Real.log T < 1 + 0.5 * Real.log (q * T) := by
  have hp : 1 < Real.log Real.pi :=
    (by linarith [Real.log_three_gt_d9] : 1 < Real.log 3).trans_le
      (Real.log_le_log (by norm_num) (le_of_lt Real.pi_gt_three))
  have hg := Real.one_half_lt_eulerMascheroniConstant
  rw [Real.log_mul hq.ne' hT.ne']
  linarith

/-! ### Lemma 1.2 -/

/-- LEAF. Unit U-1546. Lemma 1.2, p. 336, for `T ≥ 2`: if GRH holds and `χ` is a primitive
character mod `q ≥ 3`, then for every finite set `Z` of distinct nontrivial zeros of
`L(s, χ)`, `Σ_{ρ ∈ Z} 1.5/(2.25 + (T - γ)²) < 1 + 0.5 ln(qT)`. The paper states `T > 2`; its
proof by (1.4), (1.5), (1.7), (1.8) at `s = 2 + iT` works at `T = 2` as well. -/
theorem lemma12_T (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, zeroWeight T ρ < 1 + 0.5 * Real.log (q * T) := by
  sorry

/-- LEAF. Unit U-1546. Lemma 1.2 at `T = 0`, p. 338: under GRH, for `χ` primitive mod `q ≥ 3`
and every finite set `Z` of distinct nontrivial zeros, `Σ_{ρ ∈ Z} 1.5/(2.25 + γ²) <
1 + 0.5 ln q`, by (1.4) at `s = 2` with (1.6) in place of (1.5). -/
theorem lemma12_zero (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, zeroWeight 0 ρ < 1 + 0.5 * Real.log q := by
  sorry

/-- Lemma 1.2 as one bundle, CONDITIONAL ON the leaves `lemma12_T` and `lemma12_zero`. -/
theorem lemma12 (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ZeroWeightBounds (nontrivZeros χ) q :=
  ⟨fun _ hT Z hZ => lemma12_T hG hq χ hχ hT Z hZ, fun Z hZ => lemma12_zero hG hq χ hχ Z hZ⟩

/-- Vacuity instance for `ZeroWeightBounds`: a single point `1/2 + 30i` with `q = 3`
satisfies both bounds, since every weight is at most `1.5/2.25 = 2/3 < 1`. PROVED. -/
theorem zeroWeightBounds_singleton :
    ZeroWeightBounds {(1 / 2 : ℂ) + 30 * I} 3 := by
  have hw : ∀ T : ℝ, zeroWeight T ((1 / 2 : ℂ) + 30 * I) ≤ 2 / 3 := by
    intro T
    unfold zeroWeight
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (T - ((1 / 2 : ℂ) + 30 * I).im)]
  have hsub : ∀ Z : Finset ℂ, (↑Z : Set ℂ) ⊆ {(1 / 2 : ℂ) + 30 * I} →
      ∀ T : ℝ, ∑ ρ ∈ Z, zeroWeight T ρ ≤ 2 / 3 := by
    intro Z hZ T
    have hZ' : Z ⊆ {(1 / 2 : ℂ) + 30 * I} := by
      rw [← Finset.coe_subset, Finset.coe_singleton]; exact hZ
    calc ∑ ρ ∈ Z, zeroWeight T ρ ≤ ∑ ρ ∈ {(1 / 2 : ℂ) + 30 * I}, zeroWeight T ρ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hZ'
          intro i _ _
          unfold zeroWeight
          positivity
      _ ≤ 2 / 3 := by rw [Finset.sum_singleton]; exact hw T
  have key : ∀ L : ℝ, 0 ≤ L → (2 / 3 : ℝ) < 1 + 0.5 * L := by
    intro L hL
    norm_num
    linarith
  refine ⟨fun T hT Z hZ => ?_, fun Z hZ => ?_⟩
  · refine lt_of_le_of_lt (hsub Z hZ T) (key _ (Real.log_nonneg ?_))
    push_cast
    linarith
  · refine lt_of_le_of_lt (hsub Z hZ 0) (key _ (Real.log_nonneg ?_))
    norm_num

/-! ### Lemma 1.1 -/

/-- Lemma 1.1, first case, p. 336 and its proof on p. 338, PROVED from the weight bound: if
`Zs` satisfies `ZeroWeightBounds Zs q` with `q ≥ 1` and `T ≥ 2`, then a finite set of
distinct points of `Zs` with `T - 1 ≤ γ < T + 1` has fewer than `2.17(1 + 0.5 ln(qT))`
elements, since each has weight at least `1.5/3.25`. -/
theorem lemma11_window_of_bounds {Zs : Set ℂ} {q : ℕ} (hq : 1 ≤ q)
    (h : ZeroWeightBounds Zs q) {T : ℝ} (hT : 2 ≤ T) (Z : Finset ℂ)
    (hZ : (↑Z : Set ℂ) ⊆ Zs) (hwin : ∀ ρ ∈ Z, T - 1 ≤ ρ.im ∧ ρ.im < T + 1) :
    (Z.card : ℝ) < 2.17 * (1 + 0.5 * Real.log (q * T)) := by
  have hterm : ∀ ρ ∈ Z, (1.5 / 3.25 : ℝ) ≤ zeroWeight T ρ := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hwin ρ hρ
    unfold zeroWeight
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hsum : (Z.card : ℝ) * (1.5 / 3.25) ≤ ∑ ρ ∈ Z, zeroWeight T ρ := by
    have := Finset.card_nsmul_le_sum Z (zeroWeight T) _ hterm
    simpa [nsmul_eq_mul] using this
  have hB := h.1 T hT Z hZ
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (q * T) := Real.log_nonneg (by nlinarith)
  linarith

/-- Lemma 1.1, second case, p. 336, in the form its proof gives, PROVED from the weight bound:
a finite set of distinct points of `Zs` with `|γ| ≤ 1` has fewer than `2.17(1 + 0.5 ln q)`
elements. The paper prints the constant 1.09 for `0 ≤ γ < 1`; see the file header. -/
theorem lemma11_low_of_bounds {Zs : Set ℂ} {q : ℕ} (hq : 1 ≤ q)
    (h : ZeroWeightBounds Zs q) (Z : Finset ℂ)
    (hZ : (↑Z : Set ℂ) ⊆ Zs) (hwin : ∀ ρ ∈ Z, |ρ.im| ≤ 1) :
    (Z.card : ℝ) < 2.17 * (1 + 0.5 * Real.log q) := by
  have hterm : ∀ ρ ∈ Z, (1.5 / 3.25 : ℝ) ≤ zeroWeight 0 ρ := by
    intro ρ hρ
    have h1 := hwin ρ hρ
    have h2 : (0 - ρ.im) ^ 2 ≤ 1 := by
      have := sq_abs ρ.im
      nlinarith [abs_nonneg ρ.im]
    unfold zeroWeight
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hsum : (Z.card : ℝ) * (1.5 / 3.25) ≤ ∑ ρ ∈ Z, zeroWeight 0 ρ := by
    have := Finset.card_nsmul_le_sum Z (zeroWeight 0) _ hterm
    simpa [nsmul_eq_mul] using this
  have hB := h.2 Z hZ
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq'
  linarith

/-- Lemma 1.1, first case, p. 336, for the zeros of `L(s, χ)`, CONDITIONAL ON the leaves
`lemma12_T` and `lemma12_zero`: under GRH, `χ` primitive mod `q ≥ 3`, `T ≥ 2`, fewer than
`2.17(1 + 0.5 ln(qT))` distinct zeros with `T - 1 ≤ γ < T + 1`. -/
theorem lemma11_window (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ)
    (hwin : ∀ ρ ∈ Z, T - 1 ≤ ρ.im ∧ ρ.im < T + 1) :
    (Z.card : ℝ) < 2.17 * (1 + 0.5 * Real.log (q * T)) :=
  lemma11_window_of_bounds (by omega) (lemma12 hG hq χ hχ) hT Z hZ hwin

/-- Lemma 1.1, second case, p. 336, with the constant its proof gives, CONDITIONAL ON the
leaves `lemma12_T` and `lemma12_zero`: under GRH, `χ` primitive mod `q ≥ 3`, fewer than
`2.17(1 + 0.5 ln q)` distinct zeros with `|γ| ≤ 1`. -/
theorem lemma11_low (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) (hwin : ∀ ρ ∈ Z, |ρ.im| ≤ 1) :
    (Z.card : ℝ) < 2.17 * (1 + 0.5 * Real.log q) :=
  lemma11_low_of_bounds (by omega) (lemma12 hG hq χ hχ) Z hZ hwin

/-! ### Lemma 1.3 -/

/-- LEAF. Unit U-1546. The first sum estimate in the proof of Lemma 1.3, p. 339:
`Σ_{t=1}^{M} 1/(t - 0.5) < 2.3 + ln M` for `M ≥ 1`. -/
theorem harmonic_half_sum (M : ℕ) (hM : 1 ≤ M) :
    ∑ t ∈ Finset.Icc 1 M, 1 / ((t : ℝ) - 0.5) < 2.3 + Real.log M := by
  by_cases hM2 : 2 ≤ M
  · have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM2
    have ha : AntitoneOn (fun u : ℝ => (u - (1 / 2))⁻¹) (Set.Icc 2 M) := by
      intro a ha b hb hab
      apply inv_anti₀ (by linarith [ha.1])
      linarith
    have hi := ha.sum_le_integral_Ico hM2
    have he : (∑ t ∈ Finset.Icc 3 M, 1 / ((t : ℝ) - (1 / 2))) =
        ∑ t ∈ Finset.Ico 2 M, (((t : ℝ) + 1) - (1 / 2))⁻¹ := by
      simpa only [Nat.reduceAdd, Finset.Ico_add_one_right_eq_Icc, Nat.cast_add,
        Nat.cast_one, one_div] using
        (Finset.sum_Ico_add' (fun t : ℕ => ((t : ℝ) - (1 / 2))⁻¹) 2 M 1).symm
    have hint : (∫ u in (2 : ℝ)..M, (u - (1 / 2))⁻¹) =
        Real.log ((M : ℝ) - (1 / 2)) - Real.log (3 / 2) := by
      rw [intervalIntegral.integral_comp_sub_right]
      rw [integral_inv]
      · norm_num
        rw [Real.log_div (by linarith : (M : ℝ) - 1 / 2 ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      · rw [Set.uIcc_of_le (by linarith : (2 : ℝ) - (1 / 2) ≤ (M : ℝ) - (1 / 2))]
        simp only [Set.mem_Icc, not_and_or, not_le]
        left
        norm_num
    have hlog : Real.log ((M : ℝ) - (1 / 2)) ≤ Real.log M :=
      Real.log_le_log (by linarith) (by linarith)
    have h15 : 0.4 < Real.log (3 / 2) := by
      have he : Real.log ((3 / 2) : ℝ) = Real.log 3 - Real.log 2 := by
        rw [← Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      rw [he]
      linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]
    simp only [Nat.cast_add, Nat.cast_one] at hi
    rw [← he] at hi
    norm_num only [Nat.cast_ofNat] at hi
    rw [hint] at hi
    have heq : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 M)) := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [heq, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    norm_num
    simp only [one_div] at hi
    linarith
  · have : M = 1 := by omega
    subst M
    norm_num

/-- LEAF. Unit U-1546. The second sum estimate in the proof of Lemma 1.3, p. 339:
`Σ_{t=1}^{M} ln t/(t - 0.5) < 0.5 ln² M + 0.16 ln M + 0.6` for `M ≥ 1`. -/
theorem log_half_sum (M : ℕ) (hM : 1 ≤ M) :
    ∑ t ∈ Finset.Icc 1 M, Real.log t / ((t : ℝ) - 0.5) <
      0.5 * Real.log M ^ 2 + 0.16 * Real.log M + 0.6 := by
  sorry

/-- LEAF. Unit U-1546. The closing arithmetic of Lemma 1.3, p. 339: for `x ≥ 10⁹`,
`1 ≤ q ≤ x^0.37` and `T = x^0.75`,
`√x (2.17(1 + 0.5 ln q) + 2.17(1 + 0.5 ln 2q)(1.7 + ln T) + 1.09(0.5 ln² T - 0.53 ln T + 0.6))
 + 4 x^0.25 ln² x ≤ 0.83 √x ln² x`. -/
theorem lemma13_arith {x q : ℝ} (hx : 10 ^ 9 ≤ x) (hq : 1 ≤ q) (hqx : q ≤ x ^ (0.37 : ℝ)) :
    Real.sqrt x * (2.17 * (1 + 0.5 * Real.log q)
        + 2.17 * (1 + 0.5 * Real.log (2 * q)) * (1.7 + Real.log (x ^ (0.75 : ℝ)))
        + 1.09 * (0.5 * Real.log (x ^ (0.75 : ℝ)) ^ 2 - 0.53 * Real.log (x ^ (0.75 : ℝ)) + 0.6))
      + 4 * x ^ (0.25 : ℝ) * Real.log x ^ 2 ≤ 0.83 * Real.sqrt x * Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL : 20 ≤ Real.log x := by
    have hh : Real.log ((10 : ℝ) ^ 9) ≤ Real.log x := Real.log_le_log (by positivity) hx
    rw [Real.log_pow, Real.log_ten_eq] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hqlog : Real.log q ≤ 0.37 * Real.log x := by
    have h := Real.log_le_log (by linarith : 0 < q) hqx
    rwa [Real.log_rpow hx0] at h
  have hqlog0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have h2q : Real.log (2 * q) ≤ 0.7 + 0.37 * Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : q ≠ 0)]
    linarith [Real.log_two_lt_d9]
  have hy : 0 < x ^ (0.25 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hy2 : (x ^ (0.25 : ℝ)) ^ 2 = Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]
    norm_num
  have hy4 : (x ^ (0.25 : ℝ)) ^ 4 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hy100 : 100 ≤ x ^ (0.25 : ℝ) := by
    by_contra h
    have hh : (x ^ (0.25 : ℝ)) ^ 4 < (100 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ (by linarith) hy.le (by norm_num)
    rw [hy4] at hh
    norm_num at hh
    linarith
  have hsmall : 4 * x ^ (0.25 : ℝ) ≤ 0.04 * Real.sqrt x := by
    rw [← hy2]
    nlinarith
  rw [Real.log_rpow hx0]
  have hprod : 2.17 * (1 + 0.5 * Real.log (2 * q)) * (1.7 + 0.75 * Real.log x) ≤
      2.17 * (1 + 0.5 * (0.7 + 0.37 * Real.log x)) * (1.7 + 0.75 * Real.log x) := by
    gcongr
  have hpoly : 2.17 * (1 + 0.5 * Real.log q)
        + 2.17 * (1 + 0.5 * Real.log (2 * q)) * (1.7 + 0.75 * Real.log x)
        + 1.09 * (0.5 * (0.75 * Real.log x) ^ 2 - 0.53 * (0.75 * Real.log x) + 0.6)
      ≤ 0.79 * Real.log x ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - 20)]
  have hm := mul_le_mul_of_nonneg_left hpoly (Real.sqrt_nonneg x)
  have hn := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (Real.log x))
  nlinarith

/-- LEAF. Unit U-1546. Lemma 1.3, pp. 338 to 339: under GRH, for `χ` primitive mod `k` with
`3 ≤ k ≤ x^0.37` and `x ≥ 10⁹`, `|ψ(x, χ)| ≤ 0.83 √x ln² x`. The paper's proof combines the
truncated explicit formula, Lemma 1 of its reference [3], with Lemma 1.1 and the three leaves
above. -/
theorem lemma13 (hG : LeanLab.DERZ1997.GRH) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (χ : DirichletCharacter ℂ k) (hχ : χ.IsPrimitive) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hkx : (k : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ‖psiChi χ x‖ ≤ 0.83 * Real.sqrt x * Real.log x ^ 2 := by
  sorry

/-! ### Proposition 1.4 -/

/-- LEAF. Unit U-1546. Integration by parts for `Li`, p. 341: for `x ≥ 2`,
`Li(x) = x/ln x - 2/ln 2 + ∫₂ˣ du/ln² u`. -/
theorem zinLi_by_parts {x : ℝ} (hx : 2 ≤ x) :
    zinLi x = x / Real.log x - 2 / Real.log 2 + ∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2 := by
  have hlog : ∀ u ∈ Set.uIcc (2 : ℝ) x, Real.log u ≠ 0 := by
    intro u hu
    rw [Set.uIcc_of_le hx] at hu
    exact ne_of_gt (Real.log_pos (by linarith [hu.1]))
  have hderiv : ∀ u ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => u / Real.log u) (1 / Real.log u - 1 / Real.log u ^ 2) u := by
    intro u hu
    have hu0 : u ≠ 0 := by
      rw [Set.uIcc_of_le hx] at hu
      linarith [hu.1]
    convert (hasDerivAt_id u).div (Real.hasDerivAt_log hu0) (hlog u hu) using 1
    · rfl
    · simp only [id_eq]
      field_simp [hu0, hlog u hu]

  have hc : ContinuousOn (fun u : ℝ => 1 / Real.log u) (Set.uIcc 2 x) :=
    continuousOn_const.div (Real.continuousOn_log.mono (by
      intro u hu
      rw [Set.uIcc_of_le hx] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hu.1])) hlog
  have hc2 : ContinuousOn (fun u : ℝ => 1 / Real.log u ^ 2) (Set.uIcc 2 x) :=
    continuousOn_const.div ((Real.continuousOn_log.mono (by
      intro u hu
      rw [Set.uIcc_of_le hx] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hu.1])).pow 2) (fun u hu => pow_ne_zero 2 (hlog u hu))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc.sub hc2).intervalIntegrable
  rw [intervalIntegral.integral_sub hc.intervalIntegrable hc2.intervalIntegrable] at hi
  unfold LeanLab.Zinoviev1997.State1546.zinLi
  linarith

/-- LEAF. Unit U-1546. Proposition 1.4, p. 339: under GRH, for `q ≥ 1`, `(l, q) = 1`,
`x ≥ 10⁹` and `q ≤ x^0.37`, there are `|θ₁| ≤ 1`, `|θ₂| ≤ 1` with
`π(x; q, l) = Li(x)/φ(q) + 1.3 θ₁ √x ln x + θ₂ 10⁸`. -/
theorem prop14 (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 1 ≤ q) (hl : Nat.Coprime l q)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ∃ θ₁ θ₂ : ℝ, |θ₁| ≤ 1 ∧ |θ₂| ≤ 1 ∧
      (piMod x q l : ℝ) = zinLi x / (Nat.totient q : ℝ)
        + 1.3 * θ₁ * Real.sqrt x * Real.log x + θ₂ * 10 ^ 8 := by
  sorry

end LeanLab.Zinoviev1997.State1546
