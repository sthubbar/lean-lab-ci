/-
AI wrote this Lean code. Codex task394, 2026-11-05.
Supporting steps and a supply decomposition of page 337, display 1.4.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.DecompJ1130
import LeanLab.Zinoviev1997.Decomp394b

open Complex Filter Topology

namespace LeanLab.Zinoviev1997.Decomp394a

/-- Supporting nonnegative summands for display 1.4 on p. 337. -/
theorem gamma_summand_nonneg {σ T : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    0 ≤ (1 / (2 * ((n+1 : ℕ) : ℂ)) -
      1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re := by
  have hu : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have ha : 0 < σ + 2*((n+1 : ℕ) : ℝ) := by positivity
  have hd : 0 < (σ + 2*((n+1 : ℕ) : ℝ))^2 + T^2 := by positivity
  simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  field_simp
  nlinarith [sq_nonneg T]

/-- Supporting reindexing for display 1.4 on p. 337. -/
theorem gamma_sum_range_eq (σ T : ℝ) (M : ℕ) :
    (∑ n ∈ Finset.range M,
      (1 / (2 * ((n+1 : ℕ) : ℂ)) -
        1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re) =
    (∑ n ∈ Finset.Icc 1 M,
      (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), Complex.add_re, ih]

/-- Supporting limit passage for display 1.4 on p. 337. -/
theorem gamma_series_of_partial_bounds {σ T A : ℝ} (hσ : 0 ≤ σ)
    (hA : ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re ≤ A) :
    Summable (fun n : ℕ =>
      (1 / (2 * ((n+1 : ℕ) : ℂ)) -
        1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re) ∧
    (∑' n : ℕ,
      (1 / (2 * ((n+1 : ℕ) : ℂ)) -
        1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re) ≤ A := by
  have hn := gamma_summand_nonneg (T := T) hσ
  have hb : ∀ M, (∑ n ∈ Finset.range M,
      (1 / (2 * ((n+1 : ℕ) : ℂ)) -
        1 / ((σ : ℂ) + T*I + 2*(n+1 : ℕ))).re) ≤ A := by
    intro M
    rw [gamma_sum_range_eq]
    exact hA M
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

/-- Supporting kernel positivity for display 1.4 on p. 337. -/
theorem zero_kernel_pos (T : ℝ) {ρ : ℂ} (hρ : ρ.re < 1) :
    0 < (1 / ((2 : ℂ) + T*I - ρ)).re := by
  have hr : 0 < 2 - ρ.re := by linarith
  have hd : 0 < (2 - ρ.re)^2 + (T - ρ.im)^2 := by positivity
  simpa [one_div, Complex.inv_re, Complex.normSq_apply, pow_two] using div_pos hr hd

/-- Supporting finite subset comparison for display 1.4 on p. 337. -/
theorem finite_sum_le_weighted_tsum {α : Type*} (S : Set α) (Z : Finset α)
    (hZ : (↑Z : Set α) ⊆ S) (f : α → ℝ) (hf : ∀ x ∈ S, 0 ≤ f x)
    (m : S → ℕ) (hm : ∀ x, 0 < m x)
    (hs : Summable (fun x : S => (m x : ℝ) * f x)) :
    ∑ x ∈ Z, f x ≤ ∑' x : S, (m x : ℝ) * f x := by
  classical
  let g : Z → S := fun x => ⟨x, hZ x.property⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : S => (x : α)) hab
  calc
    _ ≤ ∑ x : Z, (m (g x) : ℝ) * f x := by
      rw [← Finset.sum_attach]
      apply Finset.sum_le_sum
      intro x hx
      have hm1 : (1 : ℝ) ≤ m (g x) := by exact_mod_cast hm (g x)
      nlinarith [hf x (hZ x.property)]
    _ = ∑ x ∈ (Finset.univ.map ⟨g, hg⟩), (m x : ℝ) * f x := by
      simp
      rfl
    _ ≤ _ := hs.sum_le_tsum _ (fun x hx => mul_nonneg (Nat.cast_nonneg _) (hf x x.property))

/-- Supporting finite gamma budget for display 1.4 on p. 337. -/
theorem gamma_budget_ge_third {T A : ℝ}
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re ≤ A) :
    (1 : ℝ) / 3 ≤ A := by
  have ha := hA 2 (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_Icc_succ_top, one_div, Complex.inv_re, Complex.normSq_apply] at ha
  have h1 : 4 / (16 + T*T) ≤ (1 : ℝ)/4 := by
    rw [div_le_iff₀ (by nlinarith [sq_nonneg T] : 0 < 16 + T*T)]
    nlinarith [sq_nonneg T]
  have h2 : 6 / (36 + T*T) ≤ (1 : ℝ)/6 := by
    rw [div_le_iff₀ (by nlinarith [sq_nonneg T] : 0 < 36 + T*T)]
    nlinarith [sq_nonneg T]
  linarith

/-- Supporting differentiation of the archimedean factor in display 1.1 on p. 337. -/
theorem gammaR_logDeriv {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -Complex.log Real.pi / 2 +
      (1/2 : ℂ) * Complex.digamma (s/2) := by
  have hpole : ∀ m : ℕ, s/2 ≠ -(m : ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hr
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hpnez : (Real.pi : ℂ) ^ (-s/2) ≠ 0 :=
    by simp [Complex.cpow_eq_zero_iff, Real.pi_ne_zero]
  have hpow := ((hasDerivAt_id s).neg.div_const 2).const_cpow
    (c := (Real.pi : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hg := ((hasDerivAt_id s).div_const 2).logDeriv_Gamma hpole
  simp only [id_eq] at hg
  simp only [Pi.neg_apply, id_eq] at hpow
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z/2) * Complex.Gamma (z/2)) s = _
  rw [logDeriv_fun_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z/2))
    (g := fun z : ℂ => Complex.Gamma (z/2)) s hpnez
    (Complex.Gamma_ne_zero hpole) hpow.differentiableAt
    ((Complex.differentiableAt_Gamma _ hpole).comp s (by fun_prop)), hg]
  rw [logDeriv_apply, hpow.deriv]
  field_simp

/-- Supporting nonvanishing of the archimedean factor in display 1.1 on p. 337. -/
theorem gammaFactor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using (show 0 < s.re + 1 by linarith))

/-- Supporting differentiation of display 1.1 on p. 337 in Mathlib's normalization. -/
theorem completed_logDeriv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
  classical
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hs
  have hgam := gammaFactor_ne_zero χ (by linarith : 0 < s.re)
  have hL := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hgdiff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
    have hd {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Complex.Gammaℝ z := by
      have hi := (Complex.differentiable_Gammaℝ_inv z).inv
        (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz))
      change DifferentiableAt ℂ (fun w : ℂ => ((Complex.Gammaℝ w)⁻¹)⁻¹) z at hi
      simpa only [inv_inv] using hi
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact hd (by linarith)
    · exact (hd (by simpa using (show 0 < s.re + 1 by linarith))).comp s (by fun_prop)
  have he : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      (fun z => DirichletCharacter.LFunction χ z * DirichletCharacter.gammaFactor χ z) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    have hz0 : z ≠ 0 := by intro he; norm_num [he] at hz
    have hg := gammaFactor_ne_zero χ (by linarith : 0 < z.re)
    exact ((eq_div_iff hg).mp
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0))).symm
  rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds, ← logDeriv_apply,
    logDeriv_fun_mul _ hL hgam
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs1)) hgdiff]

/-- Supporting real derivative of the gamma factor in display 1.1 on p. 337. -/
theorem gammaR_real_logDeriv {s : ℂ} (hs : 0 < s.re) :
    (logDeriv Complex.Gammaℝ s).re = -Real.log Real.pi / 2 +
      (1/2 : ℝ) * (Complex.digamma (s/2)).re := by
  rw [gammaR_logDeriv hs]
  simp [Complex.log_re, Complex.norm_real, abs_of_pos Real.pi_pos]

/-- The gamma part of display 1.4 on p. 337, The Gamma Euler limit is proved without a cited input. -/
theorem gammaFactor_budget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re ≤ A) :
    (logDeriv (DirichletCharacter.gammaFactor χ) ((2 : ℂ) + T*I)).re ≤
      -Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 + A := by
  classical
  by_cases hev : χ.Even
  · have hf : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      ext z
      simp [DirichletCharacter.gammaFactor, hev]
    rw [hf, gammaR_real_logDeriv (by norm_num)]
    have hseries := gamma_series_of_partial_bounds (T := T) (by norm_num : (0 : ℝ) ≤ 2)
      (hA 2 (by norm_num) (by norm_num))
    have hid := LeanLab.Zinoviev1997.Decomp394b.digamma_real_series_of_summable
      (σ := 2) (T := T) (by norm_num) hseries.1
    have hsum := hseries.2
    have hinv : 0 ≤ (1 / ((2 : ℂ) + T*I)).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg (by norm_num) (Complex.normSq_nonneg _)
    norm_num only [Complex.ofReal_ofNat] at hid hsum
    linarith
  · have hf : DirichletCharacter.gammaFactor χ =
        (fun z : ℂ => Complex.Gammaℝ (z+1)) := by
      ext z
      simp [DirichletCharacter.gammaFactor, hev]
    rw [hf, logDeriv_apply, deriv_comp_add_const]
    change (logDeriv Complex.Gammaℝ (((2 : ℂ) + T*I)+1)).re ≤ _
    rw [gammaR_real_logDeriv (by norm_num)]
    have hseries := gamma_series_of_partial_bounds (T := T) (by norm_num : (0 : ℝ) ≤ 1)
      (hA 1 (by norm_num) (by norm_num))
    have hid := LeanLab.Zinoviev1997.Decomp394b.digamma_real_series_of_summable
      (σ := 1) (T := T) (by norm_num) hseries.1
    have hsum := hseries.2
    have hpole : ∀ m : ℕ, ((1 : ℂ) + T*I)/2 ≠ -(m : ℂ) := by
      intro m he
      have hr := congrArg Complex.re he
      simp at hr
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    have hd := Complex.digamma_apply_add_one (((1 : ℂ) + T*I)/2) hpole
    have hc : (1/2 : ℝ) * ((((1 : ℂ) + T*I)/2)⁻¹).re =
        (1 / ((1 : ℂ) + T*I)).re := by
      rw [inv_div]
      simp [div_eq_mul_inv, Complex.mul_re]
    have he : (((2 : ℂ) + T*I)+1)/2 = ((1 : ℂ) + T*I)/2 + 1 := by ring
    rw [he, hd, Complex.add_re]
    norm_num only [Complex.ofReal_one] at hid hsum
    linarith

/-- Supporting one term lower bound for display 1.4 on p. 337. -/
theorem gamma_two_term_lower (T : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    1 / (2*(n : ℝ)) - 1 / (2*((n : ℝ)+1)) ≤
      (1 / (2*(n : ℂ)) - 1 / ((2 : ℂ) + T*I + 2*n)).re := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (2 + 2*(n : ℝ))^2 + T^2 := by positivity
  have hden : 0 < 2 + 2*(n : ℝ) := by positivity
  have hh : (2 + 2*(n : ℝ)) / ((2+2*(n : ℝ))^2 + T^2) ≤
      1 / (2+2*(n : ℝ)) := by
    rw [div_le_div_iff₀ hd hden]
    nlinarith [sq_nonneg T]
  simpa [one_div, Complex.inv_re, Complex.normSq_apply, pow_two,
    mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
    sub_le_sub_left hh (1 / (2*(n : ℝ)))

/-- Supporting telescoping lower bound for display 1.4 on p. 337. -/
theorem gamma_partial_lower (T : ℝ) (M : ℕ) :
    (1 : ℝ)/2 - 1/(2*((M : ℝ)+1)) ≤
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2*(n : ℂ)) - 1 / ((2 : ℂ) + T*I + 2*n))).re := by
  by_cases hM : 1 ≤ M
  · have ht := Finset.sum_Icc_sub (M := ℝ) hM
      (fun n : ℕ => -(1 / (2*(n : ℝ))))
    push_cast at ht
    have he : (∑ n ∈ Finset.Icc 1 M,
        (1 / (2*(n : ℝ)) - 1 / (2*((n : ℝ)+1)))) =
        (1 : ℝ)/2 - 1/(2*((M : ℝ)+1)) := by
      simpa only [neg_sub_neg, neg_neg, div_one, mul_one, sub_eq_add_neg, add_comm] using ht
    rw [← he]
    change (∑ n ∈ Finset.Icc 1 M, _) ≤ Complex.reAddGroupHom _
    rw [map_sum]
    exact Finset.sum_le_sum fun n hn => gamma_two_term_lower T (Finset.mem_Icc.mp hn).1
  · have : M = 0 := by omega
    norm_num [this]

/-- Supporting sharp minimum gamma budget for displays 1.4 and 1.6 on pp. 337 to 338. -/
theorem gamma_budget_ge_half {T A : ℝ}
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re ≤ A) :
    (1 : ℝ)/2 ≤ A := by
  have hi := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have ht : Tendsto (fun M : ℕ => (1 : ℝ)/2 - 1/(2*((M : ℝ)+1)))
      atTop (nhds ((1 : ℝ)/2)) := by
    convert (tendsto_const_nhds (x := (1 : ℝ)/2)).sub hi using 1
    · ext M
      field_simp
    · norm_num
  apply le_of_tendsto ht
  filter_upwards [] with M
  exact (gamma_partial_lower T M).trans (hA 2 (by norm_num) (by norm_num) M)

/-- A supporting scalar range of displays 1.4 and 1.7 on pp. 337 to 338. -/
theorem large_modulus_scalar {q d A : ℝ} (hq : 8 ≤ q)
    (hd : -(0.61 : ℝ) ≤ d) (hA : (1 : ℝ)/2 ≤ A) :
    0 < d + 1/2 * Real.log q - 1/2 * Real.log Real.pi -
      Real.eulerMascheroniConstant / 2 + A := by
  have hlogq := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hq
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  rw [h8] at hlogq
  have hlogpi : Real.log Real.pi < 1.15 := by
    rw [Real.log_lt_iff_lt_exp Real.pi_pos]
    have hx := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.15)
    have he1 := Real.exp_one_gt_d9
    have he : Real.exp 1 * Real.exp 0.15 = Real.exp 1.15 := by
      rw [← Real.exp_add]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hx (Real.exp_pos 1).le
    have hnum : Real.pi < Real.exp 1 * (1 + 0.15 + 0.15^2/2) := by
      nlinarith [Real.pi_lt_d2]
    rw [he] at hh
    exact hnum.trans_le hh
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have h2 := Real.log_two_gt_d9
  linarith

/-- Supporting negative diagnostic for the norm-only route to display 1.4 on p. 337.
This is a scalar budget failure and asserts no counterexample to a paper theorem. -/
theorem norm_only_budget_negative :
    -(0.61 : ℝ) + 1/2 * Real.log 3 - 1/2 * Real.log Real.pi -
      Real.eulerMascheroniConstant / 2 + 1/2 < 0 := by
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) Real.pi_gt_three
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  linarith

/-- The gamma budget in display 1.4 on p. 337 after differentiating display 1.1.
The Gamma Euler limit is proved without a cited input. No information about zeros is used. -/
theorem completed_budget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re ≤ A) :
    (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + T*I)).re +
      1/2 * Real.log q ≤
      (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T*I) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + T*I)).re +
        1/2 * Real.log q - 1/2 * Real.log Real.pi -
        Real.eulerMascheroniConstant / 2 + A := by
  have he := congrArg Complex.re (completed_logDeriv_eq χ (s := (2 : ℂ) + T*I)
    (by norm_num))
  simp only [Complex.add_re, logDeriv_apply] at he
  have hb := gammaFactor_budget χ T A hA
  simp only [logDeriv_apply] at hb ⊢
  linarith

/-- A supporting range of display 1.4 on p. 337 from display 1.7 on p. 338.
For q at least 8 this positivity needs no canonical product and no primitivity. -/
theorem large_modulus_budget {q : ℕ} [NeZero q] (hq : 8 ≤ q)
    (χ : DirichletCharacter ℂ q) (T A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T*I + 2*n))).re ≤ A) :
    0 < (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T*I) /
      DirichletCharacter.LFunction χ ((2 : ℂ) + T*I)).re +
      1/2 * Real.log q - 1/2 * Real.log Real.pi -
      Real.eulerMascheroniConstant / 2 + A := by
  have hn := LeanLab.Zinoviev1997.State1546.log_derivative_norm_le χ T
  have hd := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
  exact large_modulus_scalar (by exact_mod_cast hq) hd (gamma_budget_ge_half hA)

/-- Supporting negative diagnostic for the exponential factor in display 1.2 on p. 337.
Entireness and an empty zero set alone do not force a nonnegative real logarithmic derivative. -/
theorem zero_free_entire_negative_logDeriv :
    Differentiable ℂ (fun s : ℂ => Complex.exp (-s)) ∧
      (∀ s : ℂ, Complex.exp (-s) ≠ 0) ∧
      ∀ s : ℂ, (logDeriv (fun z : ℂ => Complex.exp (-z)) s).re = -1 := by
  refine ⟨by fun_prop, fun s => Complex.exp_ne_zero _, ?_⟩
  intro s
  change (logDeriv (Complex.exp ∘ fun z : ℂ => -z) s).re = -1
  rw [logDeriv_comp (by fun_prop) (by fun_prop), Complex.logDeriv_exp]
  simp

/-- LEAF. Page 337, displays 1.2 through 1.4 and the cited constant cancellation.
The positive multiplicities and the real canonical product identity concern only
Mathlib's completed L function. The archimedean series is a separate leaf. -/
theorem canonical_zero_series {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) :
    ∃ m : _root_.nontrivZeros χ → ℕ,
      (∀ ρ, 0 < m ρ) ∧
      Summable (fun ρ : _root_.nontrivZeros χ =>
        (m ρ : ℝ) * (1 / ((2 : ℂ) + T*I - ρ)).re) ∧
      (∑' ρ : _root_.nontrivZeros χ,
        (m ρ : ℝ) * (1 / ((2 : ℂ) + T*I - ρ)).re) =
        (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + T*I)).re +
          1/2 * Real.log q := by
  sorry

/-- The first sealed target's exact statement, supplied from two smaller analytic leaves.
CONDITIONAL ON canonical_zero_series. -/
theorem logarithmic_derivative_L_bound {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re ≤ A) :
    (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T * I) /
      DirichletCharacter.LFunction χ ((2 : ℂ) + T * I)).re +
      1 / 2 * Real.log q - 1 / 2 * Real.log Real.pi -
      Real.eulerMascheroniConstant / 2 + A ≥ 0 := by
  by_cases hlarge : 8 ≤ q
  · exact (large_modulus_budget hlarge χ T A hA).le
  · obtain ⟨m, _, _, he⟩ := canonical_zero_series hq χ hχ T
    have hp : 0 ≤ ∑' ρ : _root_.nontrivZeros χ,
        (m ρ : ℝ) * (1 / ((2 : ℂ) + T*I - ρ)).re := by
      apply tsum_nonneg
      intro ρ
      exact mul_nonneg (Nat.cast_nonneg _) (zero_kernel_pos T ρ.property.2.2).le
    rw [he] at hp
    exact hp.trans (completed_budget χ T A hA)

/-- The second sealed target's exact statement, supplied from the same smaller leaves.
CONDITIONAL ON canonical_zero_series. -/
theorem real_part_logarithmic_derivative_bound {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re ≤ A)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, (1 / ((2 : ℂ) + T * I - ρ)).re ≤
      (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T * I) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + T * I)).re
      + 1 / 2 * Real.log q - 1 / 2 * Real.log Real.pi
      - Real.eulerMascheroniConstant / 2 + A := by
  obtain ⟨m, hm, hs, he⟩ := canonical_zero_series hq χ hχ T
  have hfinite := finite_sum_le_weighted_tsum (_root_.nontrivZeros χ) Z hZ
    (fun ρ : ℂ => (1 / ((2 : ℂ) + T*I - ρ)).re)
    (fun ρ hρ => (zero_kernel_pos T hρ.2.2).le) m hm hs
  rw [he] at hfinite
  exact hfinite.trans (completed_budget χ T A hA)

end LeanLab.Zinoviev1997.Decomp394a
