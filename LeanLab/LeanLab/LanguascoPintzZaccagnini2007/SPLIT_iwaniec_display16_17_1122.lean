import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_no_zero_open_strip481_steps

/-!
A further split of the two HARD leaves `iwaniec_display16_1122` and `iwaniec_display17_1122` of
`SPLIT_iwaniec_no_zero_open_strip481_steps`, along the two lines of page 103 of
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, 97 to 104, that derive
displays (16) and (17), read on the page image of `papers/Iwaniec1974.pdf`.

Each display comes from three inputs:
* Lemma 9, page 102: `|L(s, χ)| < M` in the circle about `s₀ = 1 + 5θ + iγ`, and the same for
  `χ²` about `s₁ = 1 + 5θ + 2iγ` with `2M`, as page 103 uses it;
* the lower bound at the centre, page 103: `|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / 5θ`;
* Lemma 10, page 102: the Landau type lower bound for `Re F'/F (s₀)`.

The assemblies below prove the exact statements of the two parent leaves from these four
leaves. The geometry, that the zero `ρ` lies in the circle of radius `η/2` about `s₀` because
`12θ < η`, that every zero of `L` has real part below one, and the algebra turning
`4 / (η/2)` into `8 / η`, is proved here.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 102, Lemma 10.
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, Lemma 10, a
consequence of the maximum principle: if `F` is regular in `|s - s₀| < r` and there
`|F(s)| ≤ B |F(s₀)|`, then `Re F'/F (s₀) ≥ -(4/r) log B + Σ_ρ Re 1/(s₀ - ρ)`, the sum over the
zeros in `|s - s₀| < r/2`. Stated here for any finite set `Z` of distinct zeros in that circle,
which is weaker than the printed sum since every omitted term `Re 1/(s₀ - ρ)` is nonnegative
under the hypothesis that the zeros in the circle have real part at most `re s₀`. -/
theorem iwaniec_lemma10_1122 (F : ℂ → ℂ) (s₀ : ℂ) (r B : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball s₀ r)) (hF0 : F s₀ ≠ 0)
    (hB : ∀ s ∈ Metric.ball s₀ r, ‖F s‖ ≤ B * ‖F s₀‖)
    (hzeros : ∀ z ∈ Metric.ball s₀ (r / 2), F z = 0 → z.re ≤ s₀.re)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.ball s₀ (r / 2) ∧ F ρ = 0) :
    -(4 / r) * Real.log B + ∑ ρ ∈ Z, (1 / (s₀ - ρ)).re ≤ (logDeriv F s₀).re := by
  sorry

/-- The classical size of `ζ` near one of page 103: `(σ - 1) ζ(σ) ≤ ζ(2σ)` for `1 < σ ≤ 6/5`,
from `(σ - 1) ζ(σ) ≤ σ` and `ζ(2σ) ≥ 1 + 2^(-2σ) + 3^(-2σ) > 6/5`.
Copied from the reduction in `SPLIT_iwaniec_medium_facts1122`. -/
private theorem iwaniec_zeta_ratio_aux1122 (σ : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    (σ - 1) * ‖riemannZeta (σ : ℂ)‖ ≤ ‖riemannZeta ((2 * σ : ℝ) : ℂ)‖ := by
  have hZ : ∀ s : ℝ, 1 < s →
      riemannZeta (s : ℂ) = ((∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s : ℝ) : ℂ) := by
    intro s hs
    rw [Complex.ofReal_tsum, zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    congr 1 with n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    norm_cast
  have hZnn : ∀ s : ℝ, 0 ≤ ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s :=
    fun s => tsum_nonneg (fun n => by positivity)
  -- upper bound at σ
  have hup : (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ) ≤ σ / (σ - 1) := by
    have h1 := ZetaAsymptotics.termTSum_of_lt hσ
    have h2 : 0 ≤ ZetaAsymptotics.termTSum σ :=
      tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) σ)
    rw [h1] at h2
    have hs0 : 0 < σ := by linarith
    have hs1 : 0 < σ - 1 := by linarith
    rw [le_div_iff₀ hs1]
    have h3 : 1 / σ * (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ) ≤ 1 / (σ - 1) := by linarith
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hs0 hs1, one_mul] at h3
    linarith
  -- lower bound at 2σ
  have h2σ : 1 < 2 * σ := by linarith
  have hsum : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ (2 * σ)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr h2σ)
    refine h.congr (fun n => ?_)
    push_cast
    rw [one_div]
  have hlow : 1 + 1 / (2 : ℝ) ^ (2 * σ) + 1 / (3 : ℝ) ^ (2 * σ) ≤
      ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (2 * σ) := by
    have h := hsum.sum_le_tsum (Finset.range 3) (fun n _ => by positivity)
    simp [Finset.sum_range_succ] at h
    norm_num at h ⊢
    linarith
  have hx2 : (2 : ℝ) ^ (2 * σ) ≤ 5.7 := by
    have h1 : (2 : ℝ) ^ (2 * σ) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : ((2 : ℝ) ^ (5 / 2 : ℝ)) ^ (2 : ℕ) = 32 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h3 : 0 ≤ (2 : ℝ) ^ (5 / 2 : ℝ) := by positivity
    nlinarith
  have hx3 : (3 : ℝ) ^ (2 * σ) ≤ 15.7 := by
    have h1 : (3 : ℝ) ^ (2 * σ) ≤ (3 : ℝ) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : ((3 : ℝ) ^ (5 / 2 : ℝ)) ^ (2 : ℕ) = 243 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h3 : 0 ≤ (3 : ℝ) ^ (5 / 2 : ℝ) := by positivity
    nlinarith
  have hp2 : 0 < (2 : ℝ) ^ (2 * σ) := by positivity
  have hp3 : 0 < (3 : ℝ) ^ (2 * σ) := by positivity
  have hi2 : 1 / 5.7 ≤ 1 / (2 : ℝ) ^ (2 * σ) := one_div_le_one_div_of_le hp2 hx2
  have hi3 : 1 / 15.7 ≤ 1 / (3 : ℝ) ^ (2 * σ) := one_div_le_one_div_of_le hp3 hx3
  rw [hZ σ hσ, hZ (2 * σ) h2σ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (hZnn σ), abs_of_nonneg (hZnn (2 * σ))]
  have hs1 : 0 < σ - 1 := by linarith
  have h4 : (σ - 1) * (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ) ≤ σ := by
    have := mul_le_mul_of_nonneg_left hup hs1.le
    rw [mul_div_cancel₀ _ hs1.ne'] at this
    exact this
  have hnum : (1 : ℝ) / 5 ≤ 1 / 5.7 + 1 / 15.7 := by norm_num
  linarith

/-- Page 103, the Euler product bound `ζ(2σ)/ζ(σ) ≤ |L(σ + it, ψ)|` for every character `ψ`
modulo `q ≥ 1` and every `σ > 1`, from the Euler products of `ζ` and of `L(s, ψ)` and the
pointwise bound `|1 - ψ(p) p^{-s}| ≤ 1 + p^{-σ}`. -/
private theorem iwaniec_euler_lower_aux1122 {q : ℕ} (hq : q ≠ 0) (ψ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta ((2 * σ : ℝ) : ℂ)‖ / ‖riemannZeta (σ : ℂ)‖ ≤
      ‖Lfun481 ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  haveI : NeZero q := ⟨hq⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hs : 1 < s.re := by
    rw [hs_def]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    linarith
  have h1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h2 : 1 < (((2 * σ : ℝ)) : ℂ).re := by simpa using (show (1:ℝ) < 2 * σ by linarith)
  have mpχ : Multipliable (fun p : Nat.Primes => (1 - ψ p * (p : ℂ) ^ (-s))⁻¹) :=
    ⟨_, DirichletCharacter.LSeries_eulerProduct_hasProd ψ hs⟩
  have mp1 : Multipliable (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹) :=
    ⟨_, riemannZeta_eulerProduct_hasProd h1⟩
  have mp2 : Multipliable (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ)))⁻¹) :=
    ⟨_, riemannZeta_eulerProduct_hasProd h2⟩
  have hLval : Lfun481 ψ s = LSeries (fun n => ψ ↑n) s := by
    rw [show Lfun481 ψ s = DirichletCharacter.LFunction ψ s from by
      simp only [Lfun481, dif_neg hq]]
    exact DirichletCharacter.LFunction_eq_LSeries ψ hs
  rw [hLval, ← norm_div]
  suffices h : ‖riemannZeta ((2 * σ : ℝ) : ℂ) / riemannZeta (σ : ℂ)‖₊ ≤
      ‖LSeries (fun n => ψ ↑n) s‖₊ by exact_mod_cast h
  have hzσ : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1
  rw [nnnorm_div, div_le_iff₀ (nnnorm_pos.mpr hzσ),
    ← riemannZeta_eulerProduct_tprod h1, ← riemannZeta_eulerProduct_tprod h2,
    ← DirichletCharacter.LSeries_eulerProduct_tprod ψ hs,
    mp1.nnnorm_tprod, mp2.nnnorm_tprod, mpχ.nnnorm_tprod,
    ← mpχ.nnnorm.tprod_mul mp1.nnnorm]
  refine mp2.nnnorm.tprod_le_tprod (fun p => ?_) (mpχ.nnnorm.mul mp1.nnnorm)
  have hne1 : (1 - (p : ℂ) ^ (-(σ : ℂ))) ≠ 0 := Complex.one_sub_prime_cpow_ne_zero p.2 h1
  have hne2 : (1 - (p : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ))) ≠ 0 :=
    Complex.one_sub_prime_cpow_ne_zero p.2 h2
  have hneχ : (1 - ψ p * (p : ℂ) ^ (-s)) ≠ 0 := by
    have hlt : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos]
      have hsre : (-s).re = -σ := by
        rw [hs_def]; simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          ]; ring
      rw [hsre, Real.rpow_neg (by positivity)]
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
      have hpσ : (1 : ℝ) < (p : ℝ) ^ σ := Real.one_lt_rpow hp1 (by linarith)
      have hinv : ((p : ℝ) ^ σ)⁻¹ < 1 := by
        rw [inv_lt_one_iff₀]
        exact Or.inr hpσ
      calc ‖ψ ↑↑p‖ * (↑↑p ^ σ)⁻¹ ≤ 1 * (↑↑p ^ σ)⁻¹ :=
            mul_le_mul_of_nonneg_right (ψ.norm_le_one p) (by positivity)
        _ = (↑↑p ^ σ)⁻¹ := one_mul _
        _ < 1 := hinv
    intro hzero
    rw [sub_eq_zero] at hzero
    rw [hzero.symm, norm_one] at hlt
    exact lt_irrefl 1 hlt
  simp only [nnnorm_inv, ← mul_inv]
  have hfact : ‖1 - (p : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ))‖₊ =
      ‖1 + (p : ℂ) ^ (-(σ : ℂ))‖₊ * ‖1 - (p : ℂ) ^ (-(σ : ℂ))‖₊ := by
    rw [← nnnorm_mul]
    congr 1
    have hh : (p : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ)) = ((p : ℂ) ^ (-(σ : ℂ))) ^ 2 := by
      convert Complex.cpow_nat_mul (p : ℂ) 2 (-(σ : ℂ)) using 2 <;> push_cast <;> ring
    calc
      1 - (p : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ)) = 1 - ((p : ℂ) ^ (-(σ : ℂ))) ^ 2 := by rw [hh]
      _ = (1 + (p : ℂ) ^ (-(σ : ℂ))) * (1 - (p : ℂ) ^ (-(σ : ℂ))) := by ring
  rw [inv_le_inv₀, hfact]
  · apply _root_.mul_le_mul_left
    rw [← norm_toNNReal, ← norm_toNNReal]
    apply Real.toNNReal_le_toNNReal
    calc
      ‖1 - ψ p * (p : ℂ) ^ (-s)‖ ≤ 1 + ‖ψ p * (p : ℂ) ^ (-s)‖ := by
        simpa using norm_sub_le (1 : ℂ) (ψ p * (p : ℂ) ^ (-s))
      _ ≤ 1 + ‖(p : ℂ) ^ (-s)‖ := by
        rw [norm_mul]
        nlinarith [ψ.norm_le_one p, norm_nonneg ((p : ℂ) ^ (-s))]
      _ = ‖1 + (p : ℂ) ^ (-(σ : ℂ))‖ := by
        have hpnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-σ) := by
          rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
          have hsre : (-s).re = -σ := by
            rw [hs_def]; simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
              Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
              ]; ring
          rw [hsre]
        rw [hpnorm]
        have hpos : 0 ≤ 1 + (p : ℝ) ^ (-σ) := by positivity
        rw [← Real.norm_of_nonneg hpos, ← Complex.norm_real, Complex.ofReal_add,
          Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
        norm_cast
  · exact nnnorm_pos.mpr hne2
  · exact mul_pos (nnnorm_pos.mpr hneχ) (nnnorm_pos.mpr hne1)

/-- LEAF: Iwaniec 1974 page 103, the bound at the centre used for displays (16) and (17).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the line before
display (16): `|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / (σ₀ - 1)`, from the Euler product, with
`σ₀ = 1 + 5θ`. Stated for every character and `1 < σ ≤ 6/5`; on that range
`ζ(σ) / ζ(2σ) ≤ 1 / (σ - 1)`. -/
theorem iwaniec_centre_lower1122 (q : ℕ) (hq : 1 ≤ q) (ψ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    σ - 1 ≤ ‖Lfun481 ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have h1 := iwaniec_euler_lower_aux1122 (by omega) ψ hσ t
  have h2 := iwaniec_zeta_ratio_aux1122 σ hσ hσ'
  have hz : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  have hpos : 0 < ‖riemannZeta (σ : ℂ)‖ := norm_pos_iff.mpr hz
  have h3 : σ - 1 ≤ ‖riemannZeta ((2 * σ : ℝ) : ℂ)‖ / ‖riemannZeta (σ : ℂ)‖ := by
    rw [le_div_iff₀ hpos]; exact h2
  linarith

/-- LEAF: Iwaniec 1974 page 102, Lemma 9, as page 103 applies it before display (16).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102, Lemma 9, from
Theorem 1 of page 97: for a nonprincipal `χ` modulo `q ≥ 3`, `|L(s, χ)| < M` where
`Re s > 1 - η`. Page 103 uses it in the circle `|s - s₀| < η`, `s₀ = 1 + 5θ + iγ`, with `l`, `η`,
`M` taken at the height `γ`; see the QUESTION in the notes on this choice of height. -/
theorem iwaniec_lemma9_circle16_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) η) :
    ‖Lfun481 χ s‖ ≤ M := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, Lemma 9 as applied before display (17).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the sentence
before display (17): for a nonprincipal `ψ`, here `χ²`, `L(s, ψ)` satisfies
`|L(s, ψ)| ≤ 2M` in the circle `|s - s₁| < η/2`, `s₁ = 1 + 5θ + 2iγ`, with `l`, `η`, `M` taken at
the height `γ`. From Lemma 9 of page 102; see the QUESTION in the notes on the factor `2`. -/
theorem iwaniec_lemma9_circle17_1122 (q : ℕ) (hq : 3 ≤ q) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (s : ℂ) (hs : s ∈ Metric.ball (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) (η / 2)) :
    ‖Lfun481 ψ s‖ ≤ 2 * M := by
  sorry

/-- The size facts of page 102 for the parameters: `0 < θ ≤ 1/25`, `0 < η` and `12 θ < η`,
the last because `θ = η / (400 log M)` and `log M ≥ 100`. -/
theorem iwaniec_params1122 (q : ℕ) (hq : 3 ≤ q) (γ l η θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    0 < θ ∧ θ ≤ 1 / 25 ∧ 0 < η ∧ 12 * θ < η := by
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
  have hL1 : 1 ≤ Real.log (2 * l) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  set L := Real.log (2 * l) with hL
  have hd : (1 : ℝ) ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hlogd : 0 ≤ Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := Real.log_nonneg hd
  set D := Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) with hD
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hsplit : (l * L) ^ (3 / 4 : ℝ) = l ^ (3 / 4 : ℝ) * L ^ (3 / 4 : ℝ) :=
    Real.mul_rpow hl0 hL0
  have hlpow : l ^ (1 / 2 : ℝ) ≤ l ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsqrt : Real.sqrt l = l ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow l
  have hLpow : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlhalf : 1 ≤ l ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hl34 : 1 ≤ l ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hP : 1 ≤ (l * L) ^ (3 / 4 : ℝ) := by
    rw [hsplit]; exact one_le_mul_of_one_le_of_one_le hl34 hLpow
  have hden : 1 ≤ D + (l * L) ^ (3 / 4 : ℝ) := by linarith
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθle : θ ≤ 1 / 25 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set E := l ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) with hE
  have hEpos : 1 ≤ E := by rw [hE]; exact one_le_mul_of_one_le_of_one_le hlhalf hLpow
  have hηE : η = 1 / E := by rw [hη, hsqrt, hE]; exact (one_div _).symm
  have hηpos : 0 < η := by rw [hηE]; positivity
  have hEle : E ≤ (l * L) ^ (3 / 4 : ℝ) := by
    rw [hsplit, hE]
    exact mul_le_mul_of_nonneg_right hlpow (by linarith)
  refine ⟨hθpos, hθle, hηpos, ?_⟩
  rw [hθ, hηE, mul_one_div, div_lt_div_iff₀ (by positivity) (by linarith)]
  linarith

/-- `Lfun481` agrees with Mathlib's `LFunction` for a positive modulus. -/
theorem iwaniec_Lfun_eq1122 {q : ℕ} (hq : q ≠ 0) (ψ : DirichletCharacter ℂ q) :
    Lfun481 ψ = (haveI : NeZero q := ⟨hq⟩; DirichletCharacter.LFunction ψ) := by
  funext s
  simp only [Lfun481, dif_neg hq]

/-- For a nonprincipal character the zeros of `Lfun481` have real part below one, and the
function is differentiable everywhere. -/
theorem iwaniec_Lfun_facts1122 {q : ℕ} (hq : q ≠ 0) (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) :
    Differentiable ℂ (Lfun481 ψ) ∧ ∀ z : ℂ, Lfun481 ψ z = 0 → z.re < 1 := by
  haveI : NeZero q := ⟨hq⟩
  rw [iwaniec_Lfun_eq1122 hq ψ]
  refine ⟨DirichletCharacter.differentiable_LFunction hψ, ?_⟩
  intro z hz
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp h) hz

/-- A character with a nonreal value is nonprincipal. -/
theorem iwaniec_ne_one_of_nonreal1122 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) : χ ≠ 1 := by
  rintro rfl
  obtain ⟨a, ha⟩ := hnonreal
  apply ha
  by_cases hu : IsUnit a
  · simp [MulChar.one_apply hu]
  · simp [MulChar.map_nonunit _ hu]

/-- Display (16) of page 103, the exact statement of `iwaniec_display16_1122`, from Lemma 9 in
the circle about `s₀`, the bound at the centre, and Lemma 10 with the zero `ρ = s`. -/
theorem iwaniec_display16_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (s : ℂ) (l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|s.im| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (hzero : Lfun481 χ s = 0) (hreg : 1 - θ < s.re) (hlt : s.re < 1) :
    -(4 / η) * Real.log (M / (5 * θ)) + 1 / (1 + 5 * θ - s.re) ≤
      (logDeriv (Lfun481 χ) (((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)).re := by
  obtain ⟨hθpos, hθle, hηpos, h12⟩ := iwaniec_params1122 q hq s.im l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hχ := iwaniec_ne_one_of_nonreal1122 χ hnonreal
  obtain ⟨hdiff, hre⟩ := iwaniec_Lfun_facts1122 hq0 χ hχ
  set s₀ : ℂ := ((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I with hs₀
  have hc := iwaniec_centre_lower1122 q (by omega) χ (1 + 5 * θ) s.im (by linarith)
    (by linarith)
  have hc' : 5 * θ ≤ ‖Lfun481 χ s₀‖ := by
    have : (1 + 5 * θ) - 1 = 5 * θ := by ring
    rw [this] at hc; exact hc
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hF0 : Lfun481 χ s₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc'; linarith
  have hB : ∀ z ∈ Metric.ball s₀ η, ‖Lfun481 χ z‖ ≤ M / (5 * θ) * ‖Lfun481 χ s₀‖ := by
    intro z hz
    have h1 := iwaniec_lemma9_circle16_1122 q hq χ hχ s.im l η M θ hl hη hM hθ z hz
    have h2 : M ≤ M / (5 * θ) * ‖Lfun481 χ s₀‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hc' hMnn
    linarith
  have hdiffS : s₀ - s = (((1 + 5 * θ - s.re : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [hs₀]
  have hsball : s ∈ Metric.ball s₀ (η / 2) := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, hdiffS, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hzeros : ∀ z ∈ Metric.ball s₀ (η / 2), Lfun481 χ z = 0 → z.re ≤ s₀.re := by
    intro z _ hz
    have := hre z hz
    have : s₀.re = 1 + 5 * θ := by simp [hs₀]
    linarith
  have key := iwaniec_lemma10_1122 (Lfun481 χ) s₀ η (M / (5 * θ)) hηpos
    hdiff.differentiableOn hF0 hB hzeros {s} (by
      intro ρ hρ
      rw [Finset.mem_singleton] at hρ
      subst hρ
      exact ⟨hsball, hzero⟩)
  rw [Finset.sum_singleton, hdiffS] at key
  have hre1 : (1 / (((1 + 5 * θ - s.re : ℝ)) : ℂ)).re = 1 / (1 + 5 * θ - s.re) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre1] at key
  exact key

/-- Display (17) of page 103, the exact statement of `iwaniec_display17_1122`, from Lemma 9 in
the circle about `s₁` for `χ²`, the bound at the centre, and Lemma 10 with no zero. -/
theorem iwaniec_display17_1122_split (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    -(8 / η) * Real.log (2 * M / (5 * θ)) ≤
      (logDeriv (Lfun481 (χ ^ 2)) (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re := by
  obtain ⟨hθpos, hθle, hηpos, _⟩ := iwaniec_params1122 q hq γ l η θ hl hη hθ
  have hq0 : q ≠ 0 := by omega
  have hψ := iwaniec_sq_ne_one_of_nonreal1122 χ hnonreal
  obtain ⟨hdiff, hre⟩ := iwaniec_Lfun_facts1122 hq0 (χ ^ 2) hψ
  set s₁ : ℂ := ((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I with hs₁
  have hc := iwaniec_centre_lower1122 q (by omega) (χ ^ 2) (1 + 5 * θ) (2 * γ) (by linarith)
    (by linarith)
  have hc' : 5 * θ ≤ ‖Lfun481 (χ ^ 2) s₁‖ := by
    have : (1 + 5 * θ) - 1 = 5 * θ := by ring
    rw [this] at hc; exact hc
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hF0 : Lfun481 (χ ^ 2) s₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hc'; linarith
  have hB : ∀ z ∈ Metric.ball s₁ (η / 2),
      ‖Lfun481 (χ ^ 2) z‖ ≤ 2 * M / (5 * θ) * ‖Lfun481 (χ ^ 2) s₁‖ := by
    intro z hz
    have h1 := iwaniec_lemma9_circle17_1122 q hq (χ ^ 2) hψ γ l η M θ hl hη hM hθ z hz
    have h2 : 2 * M ≤ 2 * M / (5 * θ) * ‖Lfun481 (χ ^ 2) s₁‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hc' (by linarith)
    linarith
  have hzeros : ∀ z ∈ Metric.ball s₁ (η / 2 / 2), Lfun481 (χ ^ 2) z = 0 → z.re ≤ s₁.re := by
    intro z _ hz
    have := hre z hz
    have : s₁.re = 1 + 5 * θ := by simp [hs₁]
    linarith
  have key := iwaniec_lemma10_1122 (Lfun481 (χ ^ 2)) s₁ (η / 2) (2 * M / (5 * θ))
    (by linarith) hdiff.differentiableOn hF0 hB hzeros ∅ (by simp)
  rw [Finset.sum_empty, add_zero] at key
  have h48 : 4 / (η / 2) = 8 / η := by field_simp; ring
  rw [h48] at key
  exact key

end

end LeanLab.LPZ2007
