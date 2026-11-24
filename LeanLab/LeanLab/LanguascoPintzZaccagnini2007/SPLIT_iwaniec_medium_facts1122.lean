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
  sorry

/-- LEAF: Iwaniec 1974 page 102, the principal character against `ζ`, before display (15).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102:
`L'/L (s, χ₀) - ζ'/ζ (s) = Σ_{p ∣ q} log p / (p^s - 1)`, which is nonnegative at real `σ > 1`;
so `ζ'/ζ (σ) ≤ L'/L (σ, χ₀)`. -/
theorem iwaniec_principal_ge_zeta1122 (q : ℕ) (hq : 1 ≤ q) (σ : ℝ) (hσ : 1 < σ) :
    (logDeriv riemannZeta (σ : ℂ)).re ≤
      (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re := by
  have hq0 : q ≠ 0 := by omega
  haveI : NeZero q := ⟨hq0⟩
  have hσ1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set P : ℂ → ℂ := fun s => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) with hP
  have hev : Lfun481 (1 : DirichletCharacter ℂ q) =ᶠ[nhds (σ : ℂ)] (P * riemannZeta) := by
    have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds (by simpa using hσ1)] with s hs
    have hs' : s ≠ 1 := by simpa using hs
    simp only [Lfun481, dif_neg hq0, Pi.mul_apply, hP]
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs'
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  have hre : 1 < (σ : ℂ).re := by simpa using hσ
  have hz : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  -- each factor at a real point
  have hfac : ∀ p ∈ q.primeFactors,
      HasDerivAt (fun s : ℂ => 1 - (p : ℂ) ^ (-s))
        (((p : ℝ) ^ (-σ) * Real.log p : ℝ) : ℂ) (σ : ℂ) ∧
      (1 : ℂ) - (p : ℂ) ^ (-(σ : ℂ)) = ((1 - (p : ℝ) ^ (-σ) : ℝ) : ℂ) ∧
      0 < (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) < 1 ∧ 0 ≤ Real.log p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    have hcp : ((p : ℝ) ^ (-σ) : ℝ) = ((p : ℂ) ^ (-(σ : ℂ))) := by
      rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf
    have hlog : ((Real.log p : ℝ) : ℂ) = Complex.log (p : ℂ) := by
      rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
    refine ⟨?_, ?_, Real.rpow_pos_of_pos (by linarith) _, ?_, Real.log_nonneg hp1.le⟩
    · have h1 : HasDerivAt (fun s : ℂ => -s) (-1) (σ : ℂ) := (hasDerivAt_id _).neg
      have h2 := h1.const_cpow (c := (p : ℂ)) (Or.inl hc)
      have h3 := h2.const_sub 1
      convert h3 using 1
      push_cast
      rw [hcp]
      ring
    · push_cast; rw [hcp]
    · exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hPne : ∀ p ∈ q.primeFactors, (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ) ≠ 0 := by
    intro p hp
    obtain ⟨_, h2, _, h4, _⟩ := hfac p hp
    simp only [h2]; exact_mod_cast (by linarith : (1 : ℝ) - (p : ℝ) ^ (-σ) ≠ 0)
  have hPd : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ) :=
    fun p hp => (hfac p hp).1.differentiableAt
  have hP0 : P (σ : ℂ) ≠ 0 := by
    simp only [hP]; exact Finset.prod_ne_zero_iff.mpr hPne
  have hPdiff : DifferentiableAt ℂ P (σ : ℂ) := by
    simp only [hP]; exact DifferentiableAt.fun_finsetProd hPd
  have hzd : DifferentiableAt ℂ riemannZeta (σ : ℂ) := differentiableAt_riemannZeta hσ1
  rw [logDeriv_mul (σ : ℂ) hP0 hz hPdiff hzd, Complex.add_re]
  have hPeq : logDeriv P (σ : ℂ) =
      ∑ p ∈ q.primeFactors, logDeriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ) := by
    simp only [hP]; exact logDeriv_fun_prod hPne hPd
  have hnn : 0 ≤ (logDeriv P (σ : ℂ)).re := by
    rw [hPeq, Complex.re_sum]
    apply Finset.sum_nonneg
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hfac p hp
    rw [logDeriv_apply, h1.deriv, h2, ← Complex.ofReal_div, Complex.ofReal_re]
    apply div_nonneg (mul_nonneg h3.le h5) (by linarith)
  linarith

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
