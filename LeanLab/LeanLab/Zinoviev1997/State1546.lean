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
open Complex MeasureTheory

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

/-- Supporting term comparison for display 1.5, pp. 337 to 338. -/
theorem gamma_term_bound {σ T u : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hu : 1 ≤ u) :
    (1 / (2 * (u : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * u)).re ≤
      (1 / (2*u) - 1 / (2*(u+1))) + T^2 / (2*u*(4*u^2+T^2)) := by
  have hu0 : 0 < u := by linarith
  have ha : 0 < σ + 2*u := by linarith
  have hd : 0 < (σ+2*u)^2+T^2 := by positivity
  have hd' : 0 < 4*u^2+T^2 := by positivity
  have he : (1 / (2 * (u : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * u)).re =
      (1/(2*u)-1/(σ+2*u)) + T^2/((σ+2*u)*((σ+2*u)^2+T^2)) := by
    simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    field_simp
    <;> ring
  rw [he]
  apply add_le_add
  · apply sub_le_sub_left
    apply one_div_le_one_div_of_le ha
    linarith
  · apply div_le_div_of_nonneg_left (sq_nonneg T) (by positivity)
    have h1 : 2*u ≤ σ+2*u := by linarith
    have h2 : 4*u^2+T^2 ≤ (σ+2*u)^2+T^2 := by nlinarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- The decreasing rational correction in display 1.5, p. 338. -/
theorem gamma_correction_sum {T : ℝ} (hT : 2 ≤ T) (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, T^2 / (2*(n : ℝ)*(4*(n : ℝ)^2+T^2)) <
      0.5 + 0.5 * Real.log T := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : AntitoneOn (fun u : ℝ => T^2 / (2*u*(4*u^2+T^2))) (Set.Icc 1 M) := by
    intro a ha b hb hab
    have ha0 : 0 < a := by linarith [ha.1]
    have hb0 : 0 < b := by linarith [hb.1]
    apply div_le_div_of_nonneg_left (sq_nonneg T) (by positivity)
    gcongr
  have hi := AntitoneOn.sum_le_integral_Ico (f := fun u : ℝ => T^2 / (2*u*(4*u^2+T^2))) hM
    (by simpa only [Nat.cast_one] using ha)
  have he : (∑ n ∈ Finset.Icc 2 M, T^2 / (2*(n : ℝ)*(4*(n : ℝ)^2+T^2))) =
      ∑ n ∈ Finset.Ico 1 M, T^2 / (2*((n : ℝ)+1)*(4*((n : ℝ)+1)^2+T^2)) := by
    simpa only [Nat.reduceAdd, Finset.Ico_add_one_right_eq_Icc, Nat.cast_add, Nat.cast_one] using
      (Finset.sum_Ico_add' (fun n : ℕ => T^2 / (2*(n : ℝ)*(4*(n : ℝ)^2+T^2))) 1 M 1).symm
  simp only [Nat.cast_add, Nat.cast_one] at hi
  rw [← he] at hi
  have hpos : ∀ u ∈ Set.uIcc (1 : ℝ) M, 0 < u := by
    intro u hu
    rw [Set.uIcc_of_le hm] at hu
    linarith [hu.1]
  have hc : ContinuousOn (fun u : ℝ => T^2 / (2*u*(4*u^2+T^2))) (Set.uIcc 1 M) := by
    apply continuousOn_const.div (by fun_prop)
    intro u hu
    have := hpos u hu
    positivity
  have hd : ∀ u ∈ Set.uIcc (1 : ℝ) M,
      HasDerivAt (fun u : ℝ => -(1/4) * Real.log (1+T^2/(4*u^2)))
        (T^2 / (2*u*(4*u^2+T^2))) u := by
    intro u hu
    have hu0 := hpos u hu
    have hn : 1+T^2/(4*u^2) ≠ 0 := by positivity
    convert (((hasDerivAt_const u (T^2)).div (((hasDerivAt_id u).pow 2).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu0.ne'))).const_add 1).log hn |>.const_mul (-(1/4 : ℝ)) using 1
    · funext v
      dsimp
    · dsimp
      field_simp
      <;> ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [hint] at hi
  have hnn : 0 ≤ Real.log (1+T^2/(4*(M : ℝ)^2)) := Real.log_nonneg (by have := div_nonneg (sq_nonneg T) (by positivity : 0 ≤ 4*(M : ℝ)^2); linarith)
  have hlog : Real.log (1+T^2/4) ≤ 2 * Real.log T := by
    have hh := Real.log_le_log (by positivity : 0 < 1+T^2/4)
      (show 1+T^2/4 ≤ T^2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hfirst : T^2/(2*(4+T^2)) < (1/2 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have heq : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [heq, Finset.sum_insert (by simp)]
  norm_num only [Nat.cast_one, one_pow, mul_one] at *
  linarith


/-- LEAF. Unit U-1546. Display (1.5), p. 338: for `s = σ + iT` with `σ = 2 + d`,
`d ∈ {0, -1}`, so `1 ≤ σ ≤ 2`, and `T ≥ 2`, every partial sum of
`Re Σ_{n ≥ 1} (1/(2n) - 1/(s + 2n))` is below `1 + ½ ln T`. The terms are positive, so this
is the paper's bound on the full series. -/
theorem gamma_series_T {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 2 ≤ T) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re < 1 + 1 / 2 * Real.log T := by
  by_cases hm : 1 ≤ M
  · have hterm : ∀ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n)).re ≤
          (1 / (2*(n : ℝ)) - 1 / (2*((n : ℝ)+1))) + T^2 / (2*(n : ℝ)*(4*(n : ℝ)^2+T^2)) := by
      intro n hn
      exact gamma_term_bound hσ1 hσ2 (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    have ht := Finset.sum_le_sum hterm
    have htel : ∑ n ∈ Finset.Icc 1 M, (1 / (2*(n : ℝ)) - 1 / (2*((n : ℝ)+1))) ≤ 1/2 := by
      have he := Finset.sum_Icc_sub (M := ℝ) hm (fun n : ℕ => -(1 / (2*(n : ℝ))))
      simp only [Nat.cast_add, Nat.cast_one, neg_sub_neg] at he
      rw [he]
      norm_num
      positivity
    rw [Finset.sum_add_distrib] at ht
    have hc := gamma_correction_sum hT M hm
    rw [show (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re =
        ∑ n ∈ Finset.Icc 1 M, (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n)).re by
      simp only [Complex.re_sum]]
    linarith
  · have : M = 0 := by omega
    subst M
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty, Complex.zero_re]
    have : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    linarith

/-- The infinite real-part series in display 1.5, p. 338, is summable.
This supporting form retains a nonstrict limiting bound from the finite partial sums. -/
theorem gamma_real_series_bound {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 2 ≤ T) :
    Summable (fun n : ℕ =>
      (1 / (2 * ((n+1 : ℕ) : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re) ∧
    (∑' n : ℕ,
      (1 / (2 * ((n+1 : ℕ) : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re) ≤
        1 + 1/2 * Real.log T := by
  let f : ℕ → ℝ := fun n =>
    (1 / (2 * ((n+1 : ℕ) : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re
  have hpos : ∀ n, 0 ≤ f n := by
    intro n
    have hu : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast (Nat.succ_pos n)
    have hu0 : 0 < (n+1 : ℕ) := Nat.succ_pos n
    have ha : 0 < σ + 2*((n+1 : ℕ) : ℝ) := by positivity
    have hd : 0 < (σ + 2*((n+1 : ℕ) : ℝ))^2 + T^2 := by positivity
    dsimp [f]
    simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    field_simp
    nlinarith [sq_nonneg T]
  have he : ∀ M : ℕ, (∑ n ∈ Finset.range M, f n) =
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), Complex.add_re, ih]
  have hb : ∀ M, (∑ n ∈ Finset.range M, f n) ≤ 1 + 1/2 * Real.log T := by
    intro M
    rw [he]
    exact (gamma_series_T hσ1 hσ2 hT M).le
  exact ⟨summable_of_sum_range_le hpos hb, Real.tsum_le_of_sum_range_le hpos hb⟩

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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- Finite certificate for display 1.7, p. 338, through n = 200. -/
theorem vonMangoldt_initial_bound : ∑ n ∈ Finset.range 201, ArithmeticFunction.vonMangoldt n / (n : ℝ)^2 < 0.578 := by
  have h2 : Real.log 2 < 0.694 := by linarith [Real.log_two_lt_d9]
  have h3 : Real.log 3 < 1.099 := by linarith [Real.log_three_lt_d9]
  have h5 : Real.log 5 < 1.610 := by linarith [Real.log_five_lt_d9]
  have h7 : Real.log (7 : ℝ) < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  have h11 : Real.log (11 : ℝ) ≤ 4 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 11) (by norm_num : (11 : ℝ) ≤ 2^4)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h13 : Real.log (13 : ℝ) ≤ 4 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 13) (by norm_num : (13 : ℝ) ≤ 2^4)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h17 : Real.log (17 : ℝ) ≤ 5 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 17) (by norm_num : (17 : ℝ) ≤ 2^5)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h19 : Real.log (19 : ℝ) ≤ 5 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 19) (by norm_num : (19 : ℝ) ≤ 2^5)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h23 : Real.log (23 : ℝ) ≤ 5 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 23) (by norm_num : (23 : ℝ) ≤ 2^5)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h29 : Real.log (29 : ℝ) ≤ 5 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 29) (by norm_num : (29 : ℝ) ≤ 2^5)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h31 : Real.log (31 : ℝ) ≤ 5 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 31) (by norm_num : (31 : ℝ) ≤ 2^5)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h37 : Real.log (37 : ℝ) ≤ 6 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 37) (by norm_num : (37 : ℝ) ≤ 2^6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h41 : Real.log (41 : ℝ) ≤ 6 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 41) (by norm_num : (41 : ℝ) ≤ 2^6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h43 : Real.log (43 : ℝ) ≤ 6 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 43) (by norm_num : (43 : ℝ) ≤ 2^6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h47 : Real.log (47 : ℝ) ≤ 6 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 47) (by norm_num : (47 : ℝ) ≤ 2^6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h53 : Real.log (53 : ℝ) ≤ 6 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 53) (by norm_num : (53 : ℝ) ≤ 2^6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h59 : Real.log (59 : ℝ) ≤ 6 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 59) (by norm_num : (59 : ℝ) ≤ 2^6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h61 : Real.log (61 : ℝ) ≤ 6 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 61) (by norm_num : (61 : ℝ) ≤ 2^6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h67 : Real.log (67 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 67) (by norm_num : (67 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h71 : Real.log (71 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 71) (by norm_num : (71 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h73 : Real.log (73 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 73) (by norm_num : (73 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h79 : Real.log (79 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 79) (by norm_num : (79 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h83 : Real.log (83 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 83) (by norm_num : (83 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h89 : Real.log (89 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 89) (by norm_num : (89 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h97 : Real.log (97 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 97) (by norm_num : (97 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h101 : Real.log (101 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 101) (by norm_num : (101 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h103 : Real.log (103 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 103) (by norm_num : (103 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h107 : Real.log (107 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 107) (by norm_num : (107 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h109 : Real.log (109 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 109) (by norm_num : (109 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h113 : Real.log (113 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 113) (by norm_num : (113 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h127 : Real.log (127 : ℝ) ≤ 7 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 127) (by norm_num : (127 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h131 : Real.log (131 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 131) (by norm_num : (131 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h137 : Real.log (137 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 137) (by norm_num : (137 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h139 : Real.log (139 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 139) (by norm_num : (139 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h149 : Real.log (149 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 149) (by norm_num : (149 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h151 : Real.log (151 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 151) (by norm_num : (151 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h157 : Real.log (157 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 157) (by norm_num : (157 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h163 : Real.log (163 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 163) (by norm_num : (163 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h167 : Real.log (167 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 167) (by norm_num : (167 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h173 : Real.log (173 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 173) (by norm_num : (173 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h179 : Real.log (179 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 179) (by norm_num : (179 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h181 : Real.log (181 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 181) (by norm_num : (181 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h191 : Real.log (191 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 191) (by norm_num : (191 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h193 : Real.log (193 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 193) (by norm_num : (193 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h197 : Real.log (197 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 197) (by norm_num : (197 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have h199 : Real.log (199 : ℝ) ≤ 8 * (0.694 : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 199) (by norm_num : (199 : ℝ) ≤ 2^8)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [ArithmeticFunction.vonMangoldt_apply,
    isPrimePow_iff_card_primeFactors_eq_one, Nat.primeFactors]
  linarith

/-- Integral tail supporting display 1.7, p. 338. -/
theorem log_sq_tail_bound (M : ℕ) (hM : 200 ≤ M) :
    ∑ n ∈ Finset.Icc 201 M, Real.log n / (n : ℝ)^2 ≤ 0.0315 := by
  have hm : (200 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : AntitoneOn (fun u : ℝ => Real.log u / u^2) (Set.Icc 200 M) := by
    intro a ha b hb hab
    have ha0 : 0 < a := by linarith [ha.1]
    have hb0 : 0 < b := by linarith [hb.1]
    have hl := Real.log_div_self_antitoneOn
      (show Real.exp 1 ≤ a by linarith [ha.1, Real.exp_one_lt_d9])
      (show Real.exp 1 ≤ b by linarith [hb.1, Real.exp_one_lt_d9]) hab
    have hinv := one_div_le_one_div_of_le ha0 hab
    have hp := mul_le_mul hl hinv (by positivity : 0 ≤ 1 / b)
      (div_nonneg (Real.log_nonneg (by linarith [ha.1])) ha0.le)
    convert hp using 1 <;> field_simp <;> ring
  have hi := ha.sum_le_integral_Ico hM
  have he : (∑ n ∈ Finset.Icc 201 M, Real.log n / (n : ℝ)^2) =
      ∑ n ∈ Finset.Ico 200 M, Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)^2 := by
    simpa only [Nat.reduceAdd, Finset.Ico_add_one_right_eq_Icc, Nat.cast_add, Nat.cast_one] using
      (Finset.sum_Ico_add' (fun n : ℕ => Real.log n / (n : ℝ)^2) 200 M 1).symm
  simp only [Nat.cast_add, Nat.cast_one] at hi
  rw [← he] at hi
  norm_num only [Nat.cast_ofNat] at hi
  have hpos : ∀ u ∈ Set.uIcc (200 : ℝ) M, 0 < u := by
    intro u hu
    rw [Set.uIcc_of_le hm] at hu
    linarith [hu.1]
  have hc : ContinuousOn (fun u : ℝ => Real.log u / u^2) (Set.uIcc 200 M) :=
    (continuousOn_id.log (fun u hu => (hpos u hu).ne')).div (continuousOn_id.pow 2)
      (fun u hu => pow_ne_zero 2 (hpos u hu).ne')
  have hd : ∀ u ∈ Set.uIcc (200 : ℝ) M,
      HasDerivAt (fun u : ℝ => -(Real.log u + 1) / u) (Real.log u / u^2) u := by
    intro u hu
    convert (((Real.hasDerivAt_log (hpos u hu).ne').add_const 1).neg.div (hasDerivAt_id u) (hpos u hu).ne') using 1
    · rfl
    · dsimp
      field_simp [(hpos u hu).ne']
      <;> ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [hint] at hi
  have h200 : Real.log (200 : ℝ) < 5.3 := by
    have he : Real.log (200 : ℝ) = 3 * Real.log 2 + 2 * Real.log 5 := by
      rw [show (200 : ℝ) = 2^3 * 5^2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      norm_num
    rw [he]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hnn : 0 ≤ (Real.log M + 1) / (M : ℝ) := by
    apply div_nonneg
    · linarith [Real.log_natCast_nonneg M]
    · positivity
  simp only [neg_div] at hi
  linarith


/-- LEAF. Unit U-1546. Display (1.7), p. 338: `Σ_{n ≥ 1} Λ(n) n⁻² < 0.61`, every partial sum.
The true value is `-ζ'(2)/ζ(2) = 0.5699...`. -/
theorem vonMangoldt_sq_sum (M : ℕ) :
    ∑ n ∈ Finset.range M, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 < 0.61 := by
  by_cases hm : M ≤ 201
  · have hh : ∑ n ∈ Finset.range M, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 ≤
        ∑ n ∈ Finset.range 201, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      intro n _ _
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)
    linarith [vonMangoldt_initial_bound]
  · have hm' : 201 ≤ M := by omega
    rw [← Finset.sum_range_add_sum_Ico (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ)^2) hm']
    have he : Finset.Ico 201 M = Finset.Icc 201 (M-1) := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    have htail : ∑ n ∈ Finset.Ico 201 M, ArithmeticFunction.vonMangoldt n / (n : ℝ)^2 ≤ 0.0315 := by
      calc
        _ ≤ ∑ n ∈ Finset.Ico 201 M, Real.log n / (n : ℝ)^2 := by
          apply Finset.sum_le_sum
          intro n _
          exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (sq_nonneg _)
        _ = ∑ n ∈ Finset.Icc 201 (M-1), Real.log n / (n : ℝ)^2 := by rw [he]
        _ ≤ _ := log_sq_tail_bound (M-1) (by omega)
    linarith [vonMangoldt_initial_bound]

/-- Display 1.7, p. 338, with the analytic L-function logarithmic derivative.
This bound uses no GRH and no primitivity assumption. -/
theorem log_derivative_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T*I) /
      DirichletCharacter.LFunction χ ((2 : ℂ) + T*I)‖ ≤ 0.61 := by
  have hbound := vonMangoldt_sq_sum
  let s : ℂ := 2 + T*I
  have hs : 1 < s.re := by simp [s]
  have hnonneg : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ)^2 :=
    fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ)^2) :=
    summable_of_sum_range_le hnonneg (fun M => (hbound M).le)
  have htsum : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ)^2 ≤ 0.61 :=
    Real.tsum_le_of_sum_range_le hnonneg (fun M => (hbound M).le)
  have ht : ∀ n : ℕ, ‖LSeries.term ((fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))) s n‖ ≤
      ArithmeticFunction.vonMangoldt n / (n : ℝ)^2 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [LSeries.norm_term_eq, ite_eq_right hn]
      simp only [Pi.mul_apply, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have he : (n : ℝ)^s.re = (n : ℝ)^2 := by simp [s]
      rw [he]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (χ.norm_le_one n)
        ArithmeticFunction.vonMangoldt_nonneg
  have hnormsum : Summable (fun n : ℕ => ‖LSeries.term ((fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))) s n‖) :=
    hsum.of_nonneg_of_le (fun n => norm_nonneg _) ht
  have hn : ‖LSeries ((fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))) s‖ ≤ 0.61 :=
    (norm_tsum_le_tsum_norm hnormsum).trans
      ((Summable.tsum_le_tsum ht hnormsum hsum).trans htsum)
  have he := χ.LSeries_twist_vonMangoldt_eq hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s = _ at he
  rw [he, neg_div, norm_neg] at hn
  change ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ 0.61
  rwa [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]

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

/-- A concrete domain instance for display 1.4 on p. 337.
A nontrivial primitive character modulo 3 exists and the height 2 gamma hypothesis holds.
This supplies no GRH instance and asserts no analytic zero density bound. -/
theorem primitive_three_gamma_instance : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ (2 : ZMod 3) ≠ 1 ∧
    ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + (2 : ℝ) * I + 2 * n))).re ≤
          1 + 1/2 * Real.log 2 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (by decide : (2 : ZMod 3) ≠ 1)
  have hu : IsUnit (2 : ZMod 3) := by norm_num [ZMod.isUnit_iff_coprime] <;> decide
  have hne : χ ≠ 1 := by
    intro he
    apply hχ
    rw [he]
    exact MulChar.one_apply hu
  have hc : χ.conductor = 3 := by
    obtain hc | hc := (Nat.dvd_prime Nat.prime_three).mp χ.conductor_dvd_level
    · exact False.elim (hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc))
    · exact hc
  refine ⟨χ, hc, hχ, ?_⟩
  intro σ hs1 hs2 M
  exact (gamma_series_T hs1 hs2 (by norm_num : (2 : ℝ) ≤ 2) M).le

/-- LEAF. The positive finite-subset consequence of display 1.4, p. 337.
The missing input is the Hadamard product and its real constant cancellation.
Source: Karatsuba, Basic Analytic Number Theory, reference 1, Chapter VIII, Sections 3 and 4,
as quoted on p. 337. The parity shift is covered by every sigma between 1 and 2.
The nonpositive reciprocal term in display 1.4 is discarded. No GRH is used here. -/
theorem zero_sum_hadamard_bound {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re ≤ A)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, (1 / ((2 : ℂ) + T * I - ρ)).re ≤
      (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T * I) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + T * I)).re
      + 1 / 2 * Real.log q - 1 / 2 * Real.log Real.pi
      - Real.eulerMascheroniConstant / 2 + A := by
  sorry

/-- LEAF. Unit U-1546. Lemma 1.2, p. 336, for `T ≥ 2`: if GRH holds and `χ` is a primitive
character mod `q ≥ 3`, then for every finite set `Z` of distinct nontrivial zeros of
`L(s, χ)`, `Σ_{ρ ∈ Z} 1.5/(2.25 + (T - γ)²) < 1 + 0.5 ln(qT)`. The paper states `T > 2`; its
proof by (1.4), (1.5), (1.7), (1.8) at `s = 2 + iT` works at `T = 2` as well. -/
theorem lemma12_T (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, zeroWeight T ρ < 1 + 0.5 * Real.log (q * T) := by
  have hf := zero_sum_hadamard_bound hq χ hχ T (1 + 1/2 * Real.log T)
    (fun σ hs1 hs2 M => (gamma_series_T hs1 hs2 hT M).le) Z hZ
  have he : (∑ ρ ∈ Z, (1 / ((2 : ℂ) + T * I - ρ)).re) =
      ∑ ρ ∈ Z, zeroWeight T ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hh := hZ hρ
    exact re_inv_sub_zero T (hG q χ ρ hh.1 hh.2.1 hh.2.2)
  rw [he] at hf
  have hr := (Complex.re_le_norm _).trans (log_derivative_norm_le χ T)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hn := lemma12_arith hq0 (by linarith : 0 < T)
  linarith

/-- LEAF. Unit U-1546. Lemma 1.2 at `T = 0`, p. 338: under GRH, for `χ` primitive mod `q ≥ 3`
and every finite set `Z` of distinct nontrivial zeros, `Σ_{ρ ∈ Z} 1.5/(2.25 + γ²) <
1 + 0.5 ln q`, by (1.4) at `s = 2` with (1.6) in place of (1.5). -/
theorem lemma12_zero (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, zeroWeight 0 ρ < 1 + 0.5 * Real.log q := by
  have hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + (0 : ℝ) * I + 2 * n))).re ≤ 1 := by
    intro σ hs1 hs2 M
    have he : (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + (0 : ℝ) * I + 2 * n))).re =
        ∑ n ∈ Finset.Icc 1 M, (1 / (2 * (n : ℝ)) - 1 / (σ + 2*n)) := by
      have ht (n : ℕ) : (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + (0 : ℝ) * I + 2 * n)) =
          ((1 / (2 * (n : ℝ)) - 1 / (σ + 2*n) : ℝ) : ℂ) := by
        push_cast
        simp
      simp only [Complex.re_sum, ht, Complex.ofReal_re]
    rw [he]
    exact (gamma_series_zero hs1 hs2 M).le
  have hf := zero_sum_hadamard_bound hq χ hχ 0 1 hA Z hZ
  have he : (∑ ρ ∈ Z, (1 / ((2 : ℂ) + (0 : ℝ) * I - ρ)).re) =
      ∑ ρ ∈ Z, zeroWeight 0 ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hh := hZ hρ
    exact re_inv_sub_zero 0 (hG q χ ρ hh.1 hh.2.1 hh.2.2)
  rw [he] at hf
  have hr := (Complex.re_le_norm _).trans (log_derivative_norm_le χ 0)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hn := lemma12_arith (q := (q : ℝ)) (T := 1) hq0 (by norm_num)
  norm_num only [Real.log_one, mul_one, mul_zero, add_zero] at hn
  linarith

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

/-- A diagnostic for the missing density input in display 1.4, p. 337.
Three abstract critical-line points need not satisfy the zero weight bounds.
These points are not asserted to be L-function zeros. -/
theorem critical_line_not_weight_bounds : ∃ Zs : Set ℂ, (∀ ρ ∈ Zs, ρ.re = 1/2) ∧ ¬ ZeroWeightBounds Zs 3 := by
  let Z : Finset ℂ := {(1/2 : ℂ), (1/2 : ℂ) + (1/2 : ℂ)*I, (1/2 : ℂ) - (1/2 : ℂ)*I}
  refine ⟨(Z : Set ℂ), ?_, ?_⟩
  · intro ρ hρ
    simp only [Z, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hρ
    rcases hρ with rfl | rfl | rfl <;> norm_num
  · intro h
    have hh := h.2 Z (by intro ρ hρ; exact hρ)
    norm_num [Z, zeroWeight, Complex.ext_iff] at hh
    linarith [Real.log_three_lt_d9]

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
  by_cases hM3 : 3 ≤ M
  · have hm : (3 : ℝ) ≤ M := by exact_mod_cast hM3
    have ha : AntitoneOn (fun u : ℝ => Real.log u / (u - 0.5)) (Set.Icc 3 M) := by
      intro a ha b hb hab
      have ha0 : 0 < a := by linarith [ha.1]
      have hb0 : 0 < b := by linarith [hb.1]
      have hla : 1 ≤ Real.log a := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ha.1
        linarith [Real.log_three_gt_d9]
      have hlab : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha0 hab)
      have hr := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
      rw [Real.log_div hb0.ne' ha0.ne'] at hr
      have hr' : a * (Real.log b - Real.log a) ≤ b - a := by
        have := (le_div_iff₀ ha0).mp (show Real.log b - Real.log a ≤ (b - a) / a by
          convert hr using 1 <;> field_simp <;> ring)
        nlinarith
      apply (div_le_div_iff₀ (by linarith [hb.1] : 0 < b - 0.5) (by linarith [ha.1] : 0 < a - 0.5)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hla)]
    have hi := ha.sum_le_integral_Ico hM3
    have he : (∑ t ∈ Finset.Icc 4 M, Real.log t / ((t : ℝ) - 0.5)) =
        ∑ t ∈ Finset.Ico 3 M, Real.log ((t : ℝ) + 1) / (((t : ℝ) + 1) - 0.5) := by
      simpa only [Nat.reduceAdd, Finset.Ico_add_one_right_eq_Icc, Nat.cast_add,
        Nat.cast_one] using
        (Finset.sum_Ico_add' (fun t : ℕ => Real.log t / ((t : ℝ) - 0.5)) 3 M 1).symm
    simp only [Nat.cast_add, Nat.cast_one] at hi
    rw [← he] at hi
    norm_num only [Nat.cast_ofNat] at hi
    have hpos : ∀ u ∈ Set.uIcc (3 : ℝ) M, 0 < u - 0.5 := by
      intro u hu
      rw [Set.uIcc_of_le hm] at hu
      linarith [hu.1]
    have hlogc : ContinuousOn (fun u : ℝ => Real.log (u - 0.5)) (Set.uIcc 3 M) :=
      (continuous_sub_right 0.5).continuousOn.log (fun u hu => (hpos u hu).ne')
    have hden : ContinuousOn (fun u : ℝ => u - 0.5) (Set.uIcc 3 M) :=
      (continuous_sub_right 0.5).continuousOn
    have hfc : ContinuousOn (fun u : ℝ => Real.log u / (u - 0.5)) (Set.uIcc 3 M) :=
      (continuousOn_id.log (fun u hu => by dsimp; linarith [hpos u hu])).div hden
        (fun u hu => (hpos u hu).ne')
    have hgc : ContinuousOn (fun u : ℝ => Real.log (u - 0.5) / (u - 0.5) + 0.5 / (u - 0.5)^2)
        (Set.uIcc 3 M) :=
      (hlogc.div hden (fun u hu => (hpos u hu).ne')).add
        (continuousOn_const.div (hden.pow 2) (fun u hu => pow_ne_zero 2 (hpos u hu).ne'))
    have hfg : ∀ u ∈ Set.Icc (3 : ℝ) M,
        Real.log u / (u - 0.5) ≤ Real.log (u - 0.5) / (u - 0.5) + 0.5 / (u - 0.5)^2 := by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hd : 0 < u - 0.5 := by linarith [hu.1]
      have hh := Real.log_le_sub_one_of_pos (div_pos hu0 hd)
      rw [Real.log_div hu0.ne' hd.ne'] at hh
      have hh' : Real.log u - Real.log (u - 0.5) ≤ 0.5 / (u - 0.5) := by
        convert hh using 1 <;> field_simp <;> ring
      have hh'' := (div_le_div_iff_of_pos_right hd).mpr hh'
      rw [sub_div] at hh''
      have he : 0.5 / (u - 0.5) / (u - 0.5) = 0.5 / (u - 0.5)^2 := by field_simp <;> ring
      rw [he] at hh''
      linarith only [hh'']
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hm hfc.intervalIntegrable hgc.intervalIntegrable hfg
    have hd : ∀ u ∈ Set.uIcc (3 : ℝ) M,
        HasDerivAt (fun u : ℝ => 0.5 * Real.log (u - 0.5)^2 - 0.5 / (u - 0.5))
          (Real.log (u - 0.5) / (u - 0.5) + 0.5 / (u - 0.5)^2) u := by
      intro u hu
      have hn := (hpos u hu).ne'
      convert ((((Real.hasDerivAt_log hn).comp u ((hasDerivAt_id u).sub_const 0.5)).pow 2).const_mul 0.5).sub
        ((hasDerivAt_const u (0.5 : ℝ)).div ((hasDerivAt_id u).sub_const 0.5) hn) using 1
      · funext v
        dsimp <;> ring
      · dsimp
        field_simp
        <;> ring
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hgc.intervalIntegrable
    rw [hint] at hmono
    have hlogs : 0 ≤ Real.log ((M : ℝ) - 0.5) ∧ Real.log ((M : ℝ) - 0.5) ≤ Real.log M :=
      ⟨Real.log_nonneg (by linarith), Real.log_le_log (by linarith) (by linarith)⟩
    have hconst : Real.log 2 / (2 - 0.5) + Real.log 3 / (3 - 0.5) -
        0.5 * Real.log (3 - 0.5)^2 + 0.5 / (3 - 0.5) < 0.75 := by
      have heq : Real.log (3 - 0.5 : ℝ) = Real.log 5 - Real.log 2 := by
        rw [← Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      rw [heq]
      norm_num
      nlinarith [Real.log_two_lt_d9, Real.log_two_gt_d9, Real.log_three_lt_d9,
        Real.log_five_gt_d9, sq_nonneg (Real.log 5 - Real.log 2 - 0.9)]
    have hlogM : 1 ≤ Real.log M := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hm
      linarith [Real.log_three_gt_d9]
    have heq : Finset.Icc 1 M = insert 1 (insert 2 (insert 3 (Finset.Icc 4 M))) := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [heq, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    norm_num only [Nat.cast_ofNat, Real.log_one, zero_div, zero_add]
    have hn : 0 ≤ 0.5 / ((M : ℝ) - 0.5) := div_nonneg (by norm_num) (by linarith)
    have hsq := mul_self_le_mul_self hlogs.1 hlogs.2
    norm_num only [show (0.5 : ℝ) = 1/2 by norm_num] at hmono hconst hn hsq
    nlinarith only [hi, hmono, hconst, hlogM, hn, hsq]
  · have hcases : M = 1 ∨ M = 2 := by omega
    rcases hcases with rfl | rfl
    · norm_num
    · norm_num [Finset.sum_Icc_succ_top]
      nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, sq_nonneg (Real.log 2)]

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

/-- LEAF. The analytic budget before the final scalar comparison in Lemma 1.3, p. 339.
The missing inputs are Chen and Wang 1993, reference 3, Lemma 1, as quoted on p. 339,
and the reciprocal zero sum estimate 1.9. The truncation height and zero multiplicities
must be justified inside this leaf. No simplicity of zeros is assumed. -/
theorem lemma13_explicit_budget (hG : LeanLab.DERZ1997.GRH) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (χ : DirichletCharacter ℂ k) (hχ : χ.IsPrimitive) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hkx : (k : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ‖psiChi χ x‖ ≤ Real.sqrt x * (2.17 * (1 + 0.5 * Real.log (k : ℝ))
        + 2.17 * (1 + 0.5 * Real.log (2 * (k : ℝ))) * (1.7 + Real.log (x ^ (0.75 : ℝ)))
        + 1.09 * (0.5 * Real.log (x ^ (0.75 : ℝ)) ^ 2 - 0.53 * Real.log (x ^ (0.75 : ℝ)) + 0.6))
      + 4 * x ^ (0.25 : ℝ) * Real.log x ^ 2 := by
  sorry

/-- LEAF. Unit U-1546. Lemma 1.3, pp. 338 to 339: under GRH, for `χ` primitive mod `k` with
`3 ≤ k ≤ x^0.37` and `x ≥ 10⁹`, `|ψ(x, χ)| ≤ 0.83 √x ln² x`. The paper's proof combines the
truncated explicit formula, Lemma 1 of its reference [3], with Lemma 1.1 and the three leaves
above. -/
theorem lemma13 (hG : LeanLab.DERZ1997.GRH) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (χ : DirichletCharacter ℂ k) (hχ : χ.IsPrimitive) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hkx : (k : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ‖psiChi χ x‖ ≤ 0.83 * Real.sqrt x * Real.log x ^ 2 := by
  exact (lemma13_explicit_budget hG hk χ hχ hx hkx).trans
    (lemma13_arith hx (by exact_mod_cast (by omega : 1 ≤ k)) hkx)

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

/-- LEAF. The absolute error form of Proposition 1.4, pp. 339 to 341.
The missing inputs are character orthogonality with explicit psi errors, Abel summation,
and the Schoenfeld 1976 estimates of reference 4 for the cases q = 1 and q = 2.
The modulus range must be checked throughout the integral, not only at its upper endpoint. -/
theorem prop14_error_bound (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 1 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  sorry

/-- LEAF. Unit U-1546. Proposition 1.4, p. 339: under GRH, for `q ≥ 1`, `(l, q) = 1`,
`x ≥ 10⁹` and `q ≤ x^0.37`, there are `|θ₁| ≤ 1`, `|θ₂| ≤ 1` with
`π(x; q, l) = Li(x)/φ(q) + 1.3 θ₁ √x ln x + θ₂ 10⁸`. -/
theorem prop14 (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 1 ≤ q) (hl : Nat.Coprime l q)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ∃ θ₁ θ₂ : ℝ, |θ₁| ≤ 1 ∧ |θ₂| ≤ 1 ∧
      (piMod x q l : ℝ) = zinLi x / (Nat.totient q : ℝ)
        + 1.3 * θ₁ * Real.sqrt x * Real.log x + θ₂ * 10 ^ 8 := by
  let E : ℝ := 1.3 * Real.sqrt x * Real.log x
  let F : ℝ := 10 ^ 8
  let r : ℝ := (piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)
  let θ : ℝ := r / (E + F)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hEF : 0 < E + F := by dsimp [E, F]; positivity
  have hr : |r| ≤ E + F := prop14_error_bound hG hq hl hx hqx
  have hθ : |θ| ≤ 1 := by
    dsimp [θ]
    rw [abs_div, abs_of_pos hEF, div_le_one hEF]
    exact hr
  have he : r = E*θ + F*θ := by
    dsimp [θ]
    field_simp [hEF.ne']
    <;> ring
  refine ⟨θ, θ, hθ, hθ, ?_⟩
  calc
    (piMod x q l : ℝ) = zinLi x / (Nat.totient q : ℝ) + r := by dsimp [r]; ring
    _ = zinLi x / (Nat.totient q : ℝ) + (E*θ + F*θ) := by rw [← he]
    _ = _ := by dsimp [E, F]; ring

end LeanLab.Zinoviev1997.State1546
