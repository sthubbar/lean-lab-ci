import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_lemma9_circles1122

/-!
A split of two MEDIUM leaves of the Iwaniec chain into standard facts, each small enough for one
prover: `iwaniec_display14_15_1122` of `SPLIT_iwaniec_no_zero_open_strip481_steps` and
`iwaniec_centre_lower1122` of `SPLIT_iwaniec_display16_17_1122`. Source: H. Iwaniec, On zeros
of Dirichlet's L series, Invent. Math. 23, 1974, pages 102 and 103, read on the page images of
`papers/Iwaniec1974.pdf`.

Display (14) with (15) of page 102 comes from the 3-4-1 inequality, the comparison of the
principal character with `ζ`, and the bound `|ζ'/ζ (σ) + 1/(σ - 1)| < 3` of page 102. The bound at
the centre on page 103 comes from the Euler product, `|L(σ + it, ψ)| ≥ ζ(2σ)/ζ(σ)`, and the size
of `ζ` near one. The assemblies prove the exact parent statements.

The leaf `iwaniec_lemma9_numeric1122` is not split here: it needs a bound of
`Σ_{p ∣ q} p^(η - 1)` in terms of `η log d` and a power of `l`, which is a real number theoretic
estimate, and it is reclassed HARD in the notes.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

section Helpers341
open Complex LSeries ArithmeticFunction
open scoped LSeries.notation

/-- Iwaniec 1974 page 102: `3 + 4 cos θ + cos 2θ ≥ 0`, as `Re (3 + 4u + u²) ≥ 0` for `|u| = 1`. -/
theorem comb_nonneg1122 (u : ℂ) (hu : ‖u‖ = 1) : 0 ≤ (3 + 4 * u + u ^ 2).re := by
  have h : u.re * u.re + u.im * u.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hu]; norm_num
  simp [pow_two]
  nlinarith [sq_nonneg (1 + u.re)]

/-- Iwaniec 1974 page 102, display (14): each Dirichlet series term of the 3-4-1 combination
has nonnegative real part. -/
theorem term_nonneg1122 {q : ℕ} (χ : DirichletCharacter ℂ q) (σ γ : ℝ) (_hσ : 1 < σ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re +
      4 * (term (↗χ * ↗Λ) ((σ : ℂ) + (γ : ℂ) * I) n).re +
      (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [term_of_ne_zero hn, Pi.mul_apply]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  set w : ℂ := (n : ℂ) ^ ((γ : ℂ) * I) with hw
  set p : ℂ := (n : ℂ) ^ (σ : ℂ) with hp
  have hw1 : ‖w‖ = 1 := by
    rw [hw, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw1; simp at hw1
  have h1 : (n : ℂ) ^ ((σ : ℂ) + (γ : ℂ) * I) = p * w := by
    rw [Complex.cpow_add _ _ hn0]
  have h2 : (n : ℂ) ^ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) = p * w * w := by
    rw [show (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I = (σ : ℂ) + (γ : ℂ) * I + (γ : ℂ) * I by
      push_cast; ring, Complex.cpow_add _ _ hn0, h1]
  have hpr : p = ((((n : ℝ) ^ σ : ℝ)) : ℂ) := by
    rw [hp, Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
  have hpos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ
  rw [h1, h2, MulChar.pow_apply' χ (by norm_num)]
  set r : ℝ := Λ n / (n : ℝ) ^ σ with hr
  have hr0 : 0 ≤ r := div_nonneg vonMangoldt_nonneg hpos.le
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    have hc : ‖χ n‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one χ hu.unit
      simpa using this
    have hp0 : p ≠ 0 := by rw [hpr]; exact_mod_cast hpos.ne'
    have key : 3 * ((1 : ℂ) * Λ n / p) + 4 * (χ n * Λ n / (p * w)) + χ n ^ 2 * Λ n / (p * w * w)
        = ((Λ n : ℂ) / p) * (3 + 4 * (χ n / w) + (χ n / w) ^ 2) := by
      field_simp
    have hrc : (Λ n : ℂ) / p = ((r : ℝ) : ℂ) := by rw [hr, hpr]; push_cast; rfl
    have hcomb := comb_nonneg1122 (χ n / w) (by rw [norm_div, hc, hw1]; norm_num)
    calc (0 : ℝ) ≤ r * (3 + 4 * (χ n / w) + (χ n / w) ^ 2).re := mul_nonneg hr0 hcomb
      _ = (((r : ℝ) : ℂ) * (3 + 4 * (χ n / w) + (χ n / w) ^ 2)).re := (Complex.re_ofReal_mul _ _).symm
      _ = _ := by
        rw [← hrc, ← key]; simp only [Complex.add_re]
        simp [Complex.mul_re]
  · simp [MulChar.map_nonunit _ hu]

/-- For `Re s > 1`, `L'/L (s, χ) = -Σ χ(n) Λ(n) n^(-s)`, Iwaniec 1974 page 102. -/
theorem logDeriv_Lfun481_eq1122 {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : logDeriv (Lfun481 χ) s = -LSeries (↗χ * ↗Λ) s := by
  haveI : NeZero q := ⟨by omega⟩
  have hfun : Lfun481 χ = DirichletCharacter.LFunction χ := by
    funext z; simp [Lfun481, show q ≠ 0 by omega]
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds s] LSeries (fun n => χ n) := by
    have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [hfun, logDeriv_apply, hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs]
  ring

end Helpers341

open scoped LSeries.notation in
/-- LEAF: Iwaniec 1974 page 102, display (14), the 3-4-1 inequality for log derivatives.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, display (14):
for `σ > 1`, `3 Re L'/L (σ, χ₀) + 4 Re L'/L (σ + it, χ) + Re L'/L (σ + 2it, χ²) ≤ 0`, from
`-L'/L (s, χ) = Σ Λ(n) χ(n) n^(-s)` and `3 + 4 cos θ + cos 2θ ≥ 0`, the inequality of Mertens. -/
theorem iwaniec_341_logDeriv1122 (q : ℕ) (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (σ γ : ℝ) (hσ : 1 < σ) :
    3 * (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re +
      4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤ 0 := by
  have h0 : 1 < (σ : ℂ).re := by simpa using hσ
  have h1 : 1 < ((σ : ℂ) + (γ : ℂ) * Complex.I).re := by simpa using hσ
  have h2 : 1 < ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I).re := by simpa using hσ
  have sA := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ q) h0
  have sB := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1
  have sC := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) h2
  rw [logDeriv_Lfun481_eq1122 hq _ h0, logDeriv_Lfun481_eq1122 hq _ h1, logDeriv_Lfun481_eq1122 hq _ h2]
  simp only [Complex.neg_re, LSeries]
  rw [Complex.re_tsum sA, Complex.re_tsum sB, Complex.re_tsum sC]
  have rA := Complex.reCLM.summable sA
  have rB := Complex.reCLM.summable sB
  have rC := Complex.reCLM.summable sC
  simp only [Complex.reCLM_apply] at rA rB rC
  have hnn : 0 ≤ ∑' n : ℕ, (3 * (LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗ArithmeticFunction.vonMangoldt) (σ : ℂ) n).re +
      4 * (LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) ((σ : ℂ) + (γ : ℂ) * Complex.I) n).re +
      (LSeries.term (↗(χ ^ 2) * ↗ArithmeticFunction.vonMangoldt) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) n).re) :=
    tsum_nonneg (term_nonneg1122 χ σ γ hσ)
  rw [Summable.tsum_add ((rA.mul_left 3).add (rB.mul_left 4)) rC,
    Summable.tsum_add (rA.mul_left 3) (rB.mul_left 4), tsum_mul_left, tsum_mul_left] at hnn
  linarith

/-- LEAF: Iwaniec 1974 page 102, the principal character against `ζ`, before display (15).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102:
`L'/L (s, χ₀) - ζ'/ζ (s) = Σ_{p ∣ q} log p / (p^s - 1)`, which is nonnegative at real `σ > 1`;
so `ζ'/ζ (σ) ≤ L'/L (σ, χ₀)`. -/
theorem iwaniec_principal_ge_zeta1122 (q : ℕ) (hq : 1 ≤ q) (σ : ℝ) (hσ : 1 < σ) :
    (logDeriv riemannZeta (σ : ℂ)).re ≤
      (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re := by
  sorry

/-- LEAF: Iwaniec 1974 page 102, the bound `|ζ'/ζ (s) + 1/(s - 1)| < 3` before display (15), at real `σ > 1`.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102: for real
`σ > 1`, `-ζ'/ζ (σ) ≤ 1/(σ - 1) + 3`. -/
theorem iwaniec_zeta_logDeriv_bound1122 (σ : ℝ) (hσ : 1 < σ) :
    -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 3 := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, the Euler product bound before display (16).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103:
`|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) = ζ(σ₀)/ζ(2σ₀)`, from the Euler product; stated as
`ζ(2σ)/ζ(σ) ≤ |L(σ + it, ψ)|` for every character and `σ > 1`. -/
theorem iwaniec_euler_lower1122 (q : ℕ) (hq : 1 ≤ q) (ψ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta ((2 * σ : ℝ) : ℂ)‖ / ‖riemannZeta (σ : ℂ)‖ ≤
      ‖Lfun481 ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, the size of `ζ` behind `Σ |μ(n)| n^(-σ₀) < 1/5θ`.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, before
display (16): `ζ(σ)/ζ(2σ) ≤ 1/(σ - 1)` near one, stated for `1 < σ ≤ 6/5`, where
`(σ - 1) ζ(σ) ≤ σ ≤ 6/5` and `ζ(2σ) ≥ ζ(12/5) > 6/5`. -/
theorem iwaniec_zeta_ratio1122 (σ : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    (σ - 1) * ‖riemannZeta (σ : ℂ)‖ ≤ ‖riemannZeta ((2 * σ : ℝ) : ℂ)‖ := by
  sorry

/-- The exact statement of the leaf `iwaniec_display14_15_1122`, from the 3-4-1 inequality, the
comparison with `ζ` and the bound for `ζ'/ζ`. -/
theorem iwaniec_display14_15_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (γ l σ : ℝ) (hl : l = Real.log ((q : ℝ) * (|γ| + 3))) (hσ : 1 < σ) :
    4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤
      3 / (σ - 1) + 6 * Real.log (5 * l) := by
  have h1 := iwaniec_341_logDeriv1122 q (by omega) χ σ γ hσ
  have h2 := iwaniec_principal_ge_zeta1122 q (by omega) σ hσ
  have h3 := iwaniec_zeta_logDeriv_bound1122 σ hσ
  have hq' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ht : 0 ≤ |γ| := abs_nonneg _
  have hbase : (9 : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by nlinarith
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : Real.exp 2 < 9 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hl2 : 2 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have h15 : (3 / 2 : ℝ) ≤ Real.log (5 * l) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp (3 / 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have h3' : 3 * (1 / (σ - 1)) = 3 / (σ - 1) := by ring
  linarith

/-- The exact statement of the leaf `iwaniec_centre_lower1122`, from the Euler product bound and
the size of `ζ` near one. -/
theorem iwaniec_centre_lower1122_split (q : ℕ) (hq : 1 ≤ q) (ψ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    σ - 1 ≤ ‖Lfun481 ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have h1 := iwaniec_euler_lower1122 q hq ψ σ t hσ
  have h2 := iwaniec_zeta_ratio1122 σ hσ hσ'
  have hz : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  have hpos : 0 < ‖riemannZeta (σ : ℂ)‖ := norm_pos_iff.mpr hz
  have h3 : σ - 1 ≤ ‖riemannZeta ((2 * σ : ℝ) : ℂ)‖ / ‖riemannZeta (σ : ℂ)‖ := by
    rw [le_div_iff₀ hpos]; exact h2
  linarith

end

end LeanLab.LPZ2007
