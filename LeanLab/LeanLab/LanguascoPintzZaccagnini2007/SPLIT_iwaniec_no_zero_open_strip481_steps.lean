import LeanLab.LanguascoPintzZaccagnini2007.IwaniecCells1122

/-!
A split of the open strip step `iwaniec_no_zero_open_strip481` of
`SPLIT_iwaniec_zero_free481`, and with it of the four parameter cells of
`SPLIT_iwaniec_no_zero_open_strip481`, along the PROOF of Iwaniec 1974, Lemma 11, step (i),
pages 102 and 103 of papers/Iwaniec1974.pdf, read on the page images. The cells cut the
parameter range; this file cuts the argument instead.

Source: H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, 97 to 104.
Page 97: `q ≥ 3`, `d = ∏_{p ∣ q} p`, `l = log q (|t| + 3)`, `η⁻¹ = √l (log 2l) ^ (3/4)`.
Page 102, Lemma 9: `M = (d ^ η exp l ^ (1/4)) ^ 100`. Lemma 11: `θ = η / (400 log M)`, which
equals the printed `1 / (4·10⁴ (log d + (l log 2l) ^ (3/4)))` of page 97, proved as
`iwaniec_theta_identity1122`; the leaves below use the printed page 97 form of `θ`.

Step (i) of Lemma 11 for a character with `χ² ≠ χ₀`, which every character with a nonreal
value has, `iwaniec_sq_ne_one_of_nonreal1122`. A zero `ρ = β + iγ` with `β > 1 - θ`, the
points `σ₀ = 1 + 5θ`, `s₀ = σ₀ + iγ`, `s₁ = σ₀ + 2iγ`:
* display (16), page 103, from Lemma 9 and Lemma 10 for `L(s, χ)` around `s₀`;
* display (17), page 103, from Lemma 9 and Lemma 10 for `L(s, χ²)` around `s₁`;
* displays (14) and (15), page 102, the 3-4-1 inequality with the principal character term
  bounded below;
* the closing numerical inequality of page 103, `... ≤ 1 / (15 θ)`.
The assembly `iwaniec_printed_nonreal_split1122` combines the four by real algebra alone:
`4 / (σ₀ - β) ≤ 3 / (5θ) + 1 / (15θ)`, so `σ₀ - β ≥ 6θ` and `β ≤ 1 - θ`. Points with real part
at least one are handled by Mathlib's `LFunction_ne_zero_of_one_le_re`. The lab statement then
follows from `iwaniecStatement481_of_printed1122`, and the open strip step and each of the four
cells follow from it.

Lemma 9 itself, which holds the Vinogradov input Lemmas 4 and 5, sits inside the leaves for
displays (16) and (17).

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

open MeasureTheory Filter
open scoped Topology

private theorem steps_Lfun481_eq {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (s : ℂ) :
    Lfun481 χ s = DirichletCharacter.LFunction χ s := by
  simp only [Lfun481, dif_neg (NeZero.ne r)]

private theorem steps_logDeriv_eq {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (s : ℂ) :
    logDeriv (Lfun481 χ) s = logDeriv (DirichletCharacter.LFunction χ) s := by
  have h : Lfun481 χ = DirichletCharacter.LFunction χ :=
    funext fun z => steps_Lfun481_eq χ z
  rw [h]

private theorem steps_341 {q : ℕ} [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (σ γ : ℝ) (hσ : 1 < σ) :
    3 * (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re +
      4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤ 0 := by
  have h := LeanLab.PNTPort.DirichletZF.three_four_one (N := q) χ hσ γ
  push_cast at h
  simp only [logDeriv_apply, neg_div, Complex.neg_re] at h
  have e1 : (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re
      = (deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ) /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ : ℂ)).re := by
    rw [steps_logDeriv_eq, logDeriv_apply]
  have e2 : (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
      = (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (γ : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
    rw [steps_logDeriv_eq, logDeriv_apply]
  have e3 : (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re
      = (deriv (DirichletCharacter.LFunction (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) /
          DirichletCharacter.LFunction (χ ^ 2) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re := by
    rw [steps_logDeriv_eq, logDeriv_apply]
  rw [e1, e2, e3]
  push_cast
  linarith

private theorem steps_zeta_ofReal_tsum (σ : ℝ) (hσ : 1 < σ) :
    riemannZeta (σ : ℂ) = ((∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum, zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hσ)]
  congr 1 with n
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
  norm_cast

private theorem steps_zeta_ge_inv (σ : ℝ) (hσ : 1 < σ) :
    1 / (σ - 1) ≤ ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ := by
  have hs1 : (0 : ℝ) < σ - 1 := by linarith
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (n + 1 : ℝ) ^ σ := fun n => by positivity
  have hsummable : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ σ) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hσ)
    refine h.congr (fun n => ?_)
    push_cast
    rw [one_div]
  have hanti : ∀ N : ℕ, AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc 1 (1 + (N : ℝ))) := by
    intro N x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hy0 : (0 : ℝ) < y := by linarith [hy.1]
    show y ^ (-σ) ≤ x ^ (-σ)
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx0 σ) (Real.rpow_le_rpow hx0.le hxy (by linarith))
  have hpoint : ∀ N : ℕ, ∫ x in (1 : ℝ)..(1 + (N : ℝ)), x ^ (-σ) ≤
      ∑ i ∈ Finset.range N, 1 / (i + 1 : ℝ) ^ σ := by
    intro N
    have h1 := AntitoneOn.integral_le_sum (hanti N)
    have h2 : ∑ i ∈ Finset.range N, ((1 : ℝ) + i) ^ (-σ) =
        ∑ i ∈ Finset.range N, 1 / (i + 1 : ℝ) ^ σ := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show ((1 : ℝ) + i) = (i + 1 : ℝ) by ring, Real.rpow_neg (by positivity), one_div]
    rw [h2] at h1
    exact h1
  have hInt : ∀ N : ℕ, ∫ x in (1 : ℝ)..(1 + (N : ℝ)), x ^ (-σ) =
      (1 - (1 + (N : ℝ)) ^ (1 - σ)) / (σ - 1) := by
    intro N
    have hne1 : -σ ≠ (-1 : ℝ) := by linarith
    have hne2 : (0:ℝ) ∉ Set.uIcc (1:ℝ) (1 + (N:ℝ)) := by
      intro h
      rw [Set.mem_uIcc] at h
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact absurd ha (by norm_num)
      · have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        linarith
    rw [integral_rpow (Or.inr ⟨hne1, hne2⟩)]
    have h1 : -σ + 1 = 1 - σ := by ring
    rw [h1, Real.one_rpow]
    rw [div_eq_div_iff (by linarith : (1 - σ) ≠ 0) (by linarith : (σ - 1) ≠ 0)]
    ring
  have hb : Tendsto (fun N : ℕ => (1 + (N : ℝ)) ^ (1 - σ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => (1 + (N : ℝ))) atTop atTop :=
      by simpa [add_comm] using (tendsto_atTop_add_const_right (Filter.atTop) (1:ℝ) tendsto_natCast_atTop_atTop)
    have h3 : Tendsto (fun x : ℝ => x ^ (-(σ - 1))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hs1
    refine (h3.comp h2).congr (fun N => ?_)
    simp only [Function.comp_apply]
    congr 1
    ring
  have hlim : Tendsto (fun N : ℕ => (1 - (1 + (N:ℝ)) ^ (1 - σ)) / (σ - 1)) atTop
      (𝓝 (1 / (σ - 1))) := by
    have hsub : Tendsto (fun N : ℕ => 1 - (1 + (N:ℝ)) ^ (1 - σ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hb
    simpa using hsub.div_const (σ - 1)
  have htend1 : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(1 + (N : ℝ)), x ^ (-σ)) atTop
      (𝓝 (1 / (σ - 1))) :=
    Tendsto.congr' (Eventually.of_forall (fun N => (hInt N).symm)) hlim
  have htend2 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, 1 / (i + 1 : ℝ) ^ σ) atTop
      (𝓝 (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ)) := hsummable.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto htend1 htend2 (Eventually.of_forall hpoint)

private theorem steps_logMul_one_eq (n : ℕ) :
    LSeries.logMul (1 : ℕ → ℂ) n = Complex.log (n : ℂ) := by
  rw [LSeries.logMul]; simp

private theorem steps_LSeries_log_one (σ : ℝ) :
    LSeries (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ) =
      ((∑' n : ℕ, Real.log n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with h0 | hn
  · subst h0; simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, steps_logMul_one_eq]
    have h1 : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, Complex.ofReal_log (Nat.cast_nonneg n)]
    have h2 : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp only [h1, h2, ← Complex.ofReal_div, Complex.reCLM_apply, Complex.ofReal_re]

private theorem steps_deriv_zeta (σ : ℝ) (hσ : 1 < σ) :
    deriv riemannZeta (σ : ℂ) = -(((∑' n : ℕ, Real.log n / (n : ℝ) ^ σ : ℝ)) : ℂ) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hderiveq : deriv (LSeries (1 : ℕ → ℂ)) (σ : ℂ) = deriv riemannZeta (σ : ℂ) := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact LSeries_one_eq_riemannZeta hz
  have hab : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (σ : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    have h : ((1:ℝ) : EReal) < ((σ:ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr hσ
    simpa using h
  rw [← hderiveq, LSeries_deriv hab, steps_LSeries_log_one]

private theorem steps_log_tsum_bound (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ σ) ≤ 1 / (σ - 1) ^ (2:ℕ) + 1.1 := by
  have hs1 : (0 : ℝ) < σ - 1 := by linarith
  have hsummable : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ σ) := by
    have ha : (0:ℝ) < (σ - 1) / 2 := by linarith
    have hp : (1:ℝ) < (σ + 1) / 2 := by linarith
    have hb : Summable (fun n : ℕ => ((n:ℝ) ^ ((σ + 1)/2))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr hp
    have hb2 : Summable (fun n : ℕ => (2/(σ-1)) * ((n:ℝ) ^ ((σ + 1)/2))⁻¹) :=
      hb.mul_left _
    refine Summable.of_nonneg_of_le (fun n => div_nonneg (Real.log_natCast_nonneg n) (by positivity)) (fun n => ?_) hb2
    rcases eq_or_ne n 0 with h0 | hn
    · subst h0
      have hp0 : ((σ + 1)/2 : ℝ) ≠ 0 := by positivity
      simp [Real.zero_rpow hp0]
    · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hlog : Real.log (n:ℝ) ≤ (n:ℝ) ^ ((σ-1)/2) / ((σ-1)/2) :=
        Real.log_le_rpow_div hn0.le ha
      have hden : 0 < (n:ℝ) ^ σ := Real.rpow_pos_of_pos hn0 σ
      have hAB : (n:ℝ) ^ ((σ-1)/2) / (n:ℝ)^σ = ((n:ℝ) ^ ((σ+1)/2))⁻¹ := by
        rw [← Real.rpow_sub hn0, show (σ-1)/2 - σ = -((σ+1)/2) by ring, Real.rpow_neg hn0.le]
      calc Real.log (n:ℝ) / (n:ℝ) ^ σ
          ≤ ((n:ℝ) ^ ((σ-1)/2) / ((σ-1)/2)) / (n:ℝ)^σ :=
            div_le_div_of_nonneg_right hlog hden.le
        _ = ((n:ℝ) ^ ((σ-1)/2) / (n:ℝ)^σ) / ((σ-1)/2) := by
            field_simp
        _ = ((n:ℝ) ^ ((σ+1)/2))⁻¹ / ((σ-1)/2) := by rw [hAB]
        _ = (2/(σ-1)) * ((n:ℝ) ^ ((σ+1)/2))⁻¹ := by
            field_simp

  have hIntval : ∫ x in Set.Ioi (1 : ℝ), Real.log x * x ^ (-σ) = 1 / (σ - 1) ^ (2:ℕ) := by
    have hsub := integral_comp_log_Ioi (g := fun y : ℝ => y * Real.exp (-(σ - 1) * y)) (a := 1)
      (by norm_num)
    have h1 : ∫ x in Set.Ioi (1 : ℝ), Real.log x * x ^ (-σ) =
        ∫ x in Set.Ioi (1 : ℝ), x⁻¹ • (Real.log x * Real.exp (-(σ - 1) * Real.log x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [Set.mem_Ioi] at hx
      have hx0 : (0 : ℝ) < x := by linarith
      have e1 : Real.exp (-(σ - 1) * Real.log x) = x ^ (-(σ - 1)) := by
        rw [Real.rpow_def_of_pos hx0]; ring_nf
      rw [e1, smul_eq_mul]
      have key : x ^ (-1 : ℝ) * x ^ (-(σ - 1)) = x ^ (-σ) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      rw [← key, ← Real.rpow_neg_one]
      ring
    have h3 : ∫ y : ℝ in Set.Ioi 0, y * Real.exp (-(σ - 1) * y) =
        ∫ t : ℝ in Set.Ioi 0, t ^ ((2 : ℝ) - 1) * Real.exp (-((σ - 1) * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      have e : ((2 : ℝ) - 1) = 1 := by norm_num
      rw [e, Real.rpow_one]
      ring_nf
    have h2 : ∫ t : ℝ in Set.Ioi 0, t ^ ((2 : ℝ) - 1) * Real.exp (-((σ - 1) * t)) =
        1 / (σ - 1) ^ (2:ℕ) := by
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := σ - 1) (by norm_num) hs1
      rw [Real.Gamma_two, mul_one] at h
      rw [h]
      have e : (1 / (σ - 1)) ^ (2:ℝ) = (1 / (σ - 1)) ^ (2:ℕ) := Real.rpow_natCast _ 2
      rw [e, div_pow, one_pow]
    rw [h1, hsub, Real.log_one]
    exact h3.trans h2
  have hanti : ∀ a : ℕ, AntitoneOn (fun t : ℝ => Real.log t * t ^ (-σ)) (Set.Icc 3 (3 + (a : ℝ))) := by
    intro a
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · refine Real.continuousOn_log.mono ?_
        intro x hx
        simp only [Set.mem_Icc] at hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        linarith [hx.1]
      · refine ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl ?_)
        simp only [Set.mem_Icc] at hx
        exact (by linarith [hx.1] : (0:ℝ) < x).ne'
    · refine DifferentiableOn.mul ?_ ?_
      · refine DifferentiableOn.log ?_ (fun x hx => ?_)
        · fun_prop
        · rw [interior_Icc] at hx; linarith [hx.1]
      · refine DifferentiableOn.rpow_const differentiableOn_id (fun x hx => Or.inl ?_)
        rw [interior_Icc] at hx; linarith [hx.1]
    · intro x hx
      have hx3 : 3 < x := by
        rw [interior_Icc] at hx; linarith [hx.1]
      have hx0 : (0 : ℝ) < x := by linarith
      have hderiv : HasDerivAt (fun t : ℝ => Real.log t * t ^ (-σ))
          (1 / x * x ^ (-σ) + Real.log x * (-σ * x ^ (-σ - 1))) x := by
        have h1 : HasDerivAt (fun t : ℝ => Real.log t) (1 / x) x := by
          simpa [one_div] using Real.hasDerivAt_log hx0.ne'
        have h2 : HasDerivAt (fun t : ℝ => t ^ (-σ)) (-σ * x ^ (-σ - 1)) x := by
          simpa using Real.hasDerivAt_rpow_const (x := x) (p := -σ) (Or.inl hx0.ne')
        have hmul := h1.mul h2
        convert hmul using 1
      rw [hderiv.deriv]
      have hl3 : 1 < Real.log x := by
        rw [Real.lt_log_iff_exp_lt hx0]
        calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          _ < 3 := by norm_num
          _ < x := hx3
      have hpos : 0 < x ^ (-σ - 1) := Real.rpow_pos_of_pos hx0 _
      have hfac : 1 / x * x ^ (-σ) + Real.log x * (-σ * x ^ (-σ - 1)) =
          x ^ (-σ - 1) * (1 - σ * Real.log x) := by
        rw [show (1 / x : ℝ) = x ^ (-1 : ℝ) by rw [one_div, Real.rpow_neg_one]]
        rw [← Real.rpow_add hx0]
        rw [show (-1:ℝ) + -σ = -σ - 1 by ring]
        ring
      rw [hfac]
      have : 1 - σ * Real.log x < 0 := by nlinarith
      nlinarith
  have hlog2le : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hlog3le : Real.log 3 ≤ 1.5 := by
    have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    rw [h4] at h34; nlinarith
  have hg2 : Real.log 2 / (2 : ℝ) ^ σ ≤ 0.4 := by
    have h2 : (2 : ℝ) ^ σ ≥ 2 := by
      calc (2:ℝ) ^ σ ≥ (2:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ.le
        _ = 2 := Real.rpow_one 2
    have hpos : 0 < (2 : ℝ) ^ σ := by positivity
    rw [div_le_iff₀ hpos]; nlinarith
  have hg3 : Real.log 3 / (3 : ℝ) ^ σ ≤ 0.5 := by
    have h3 : (3 : ℝ) ^ σ ≥ 3 := by
      calc (3:ℝ) ^ σ ≥ (3:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ.le
        _ = 3 := Real.rpow_one 3
    have hpos : 0 < (3 : ℝ) ^ σ := by positivity
    rw [div_le_iff₀ hpos]; nlinarith
  have hsmall : ∑ n ∈ Finset.range 4, Real.log n / (n : ℝ) ^ σ ≤ 0.9 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty, zero_add]
    have h0 : Real.log (↑(0:ℕ) : ℝ) / (↑(0:ℕ) : ℝ) ^ σ = 0 := by simp
    have h1 : Real.log (↑(1:ℕ) : ℝ) / (↑(1:ℕ) : ℝ) ^ σ = 0 := by simp
    rw [h0, h1]
    linarith [hg2, hg3]
  have hnonneg : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ σ := fun n =>
    div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  have htail : ∀ N : ℕ, ∑ i ∈ Finset.range N, Real.log (((4 + i : ℕ)) : ℝ) / (((4 + i : ℕ)) : ℝ) ^ σ ≤
      1 / (σ - 1) ^ (2:ℕ) := by
    intro N
    have hstep := AntitoneOn.sum_le_integral (x₀ := 3) (a := N) (hanti N)
    have hcongr : ∑ i ∈ Finset.range N, (fun t : ℝ => Real.log t * t ^ (-σ))
        (3 + ((i : ℕ) + 1 : ℕ)) =
        ∑ i ∈ Finset.range N, Real.log (((4 + i : ℕ)) : ℝ) / (((4 + i : ℕ)) : ℝ) ^ σ := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have e1 : (3 + ((i : ℕ) + 1 : ℕ) : ℝ) = ((4 + i : ℕ) : ℝ) := by push_cast; ring
      rw [e1]
      dsimp only
      rw [Real.rpow_neg (Nat.cast_nonneg (4 + i)), div_eq_mul_inv]
    rw [hcongr] at hstep
    have hint : IntegrableOn (fun x : ℝ => Real.log x * x ^ (-σ)) (Set.Ioi (1:ℝ)) := by
      by_contra hcon
      rw [MeasureTheory.integral_undef hcon] at hIntval
      have hpos : (0:ℝ) < 1 / (σ - 1) ^ (2:ℕ) := by positivity
      linarith
    have hmono : ∫ x in (3 : ℝ)..(3 + (N : ℝ)), Real.log x * x ^ (-σ) ≤
        ∫ x in Set.Ioi (1 : ℝ), Real.log x * x ^ (-σ) := by
      have hsub : Set.Ioc (3:ℝ) (3 + (N:ℝ)) ⊆ Set.Ioi (1:ℝ) := by
        intro x hx
        simp only [Set.mem_Ioc, Set.mem_Ioi] at hx ⊢
        linarith [hx.1]
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun x : ℝ => Real.log x * x ^ (-σ)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        rw [Set.mem_Ioi] at hx
        have hx0 : (0:ℝ) < x := by linarith
        exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg hx0.le _)
      have h2 := setIntegral_mono_set (s := Set.Ioc (3:ℝ) (3 + (N:ℝ))) (t := Set.Ioi (1:ℝ))
        (f := fun x : ℝ => Real.log x * x ^ (-σ)) hint hnn (Filter.Eventually.of_forall hsub)
      rw [intervalIntegral.integral_of_le (by have h : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N; linarith)]
      exact h2
    linarith [hstep, hmono, hIntval]
  have hpoint : ∀ N : ℕ, ∑ n ∈ Finset.range N, Real.log n / (n : ℝ) ^ σ ≤
      1 / (σ - 1) ^ (2:ℕ) + 1.1 := by
    intro N
    have hsplit : ∑ n ∈ Finset.range (4 + N), Real.log n / (n : ℝ) ^ σ =
        (∑ n ∈ Finset.range 4, Real.log n / (n : ℝ) ^ σ) +
        ∑ i ∈ Finset.range N, Real.log (((4 + i : ℕ)) : ℝ) / (((4 + i : ℕ)) : ℝ) ^ σ :=
      Finset.sum_range_add (fun n => Real.log n / (n : ℝ) ^ σ) 4 N
    have hsub : ∑ n ∈ Finset.range N, Real.log n / (n : ℝ) ^ σ ≤
        ∑ n ∈ Finset.range (4 + N), Real.log n / (n : ℝ) ^ σ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hnonneg i)
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have := htail N
    linarith
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, Real.log n / (n : ℝ) ^ σ) atTop
      (𝓝 (∑' n : ℕ, Real.log n / (n : ℝ) ^ σ)) := hsummable.hasSum.tendsto_sum_nat
  exact le_of_tendsto htend (Eventually.of_forall hpoint)


private theorem steps_zeta_logDeriv_bound (σ : ℝ) (hσ : 1 < σ) :
    -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 3 := by
  have hs1 : (0 : ℝ) < σ - 1 := by linarith
  set Z : ℝ := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ with hZ
  set T : ℝ := ∑' n : ℕ, Real.log n / (n : ℝ) ^ σ with hT
  have hZlow : 1 / (σ - 1) ≤ Z := by rw [hZ]; exact steps_zeta_ge_inv σ hσ
  have hTup : T ≤ 1 / (σ - 1) ^ (2:ℕ) + 1.1 := by rw [hT]; exact steps_log_tsum_bound σ hσ
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZlow
  have hzeta : riemannZeta (σ : ℂ) = ((Z : ℝ) : ℂ) := by
    rw [hZ]; exact steps_zeta_ofReal_tsum σ hσ
  have hderiv : deriv riemannZeta (σ : ℂ) = -((T : ℝ) : ℂ) := by
    rw [hT]; exact steps_deriv_zeta σ hσ
  have hmain : -(logDeriv riemannZeta (σ : ℂ)).re = T / Z := by
    have e : logDeriv riemannZeta (σ : ℂ) = -((T : ℂ) / (Z : ℂ)) := by
      rw [logDeriv_apply, hzeta, hderiv, neg_div]
    rw [e]
    simp only [Complex.neg_re, neg_neg, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hmain]
  have hZone : 1 ≤ Z := by
    rw [hZ]
    have hsummable : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ σ) := by
      have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hσ)
      refine h.congr (fun n => ?_)
      push_cast
      rw [one_div]
    have h1 : ∑ n ∈ Finset.range 1, 1 / (n + 1 : ℝ) ^ σ ≤
        ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ :=
      Summable.sum_le_tsum (Finset.range 1) (fun i _ => by positivity) hsummable
    simpa using h1
  have hTZ : T ≤ Z * (1 / (σ - 1) + 3) := by
    have hZnn : (0:ℝ) ≤ 1 / (σ - 1) := by positivity
    have h1 : (1 / (σ - 1)) * (1 / (σ - 1)) ≤ Z * (1 / (σ - 1)) :=
      mul_le_mul_of_nonneg_right hZlow hZnn
    have e1 : (1 / (σ - 1)) * (1 / (σ - 1)) = 1 / (σ - 1) ^ (2:ℕ) := by
      field_simp
    have h2 : (3:ℝ) ≤ 3 * Z := by linarith
    have e2 : Z * (1 / (σ - 1) + 3) = Z * (1 / (σ - 1)) + 3 * Z := by ring
    nlinarith [h1, e1, h2, e2, hTup]
  rw [div_le_iff₀ hZpos]
  linarith [hTZ]

private theorem steps_prin {q : ℕ} [NeZero q] (σ : ℝ) (hσ : 1 < σ) :
    (logDeriv riemannZeta (σ : ℂ)).re ≤
      (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  -- zeta side
  have hzeta : logDeriv riemannZeta (σ : ℂ) =
      - LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) := by
    have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq (s := (σ : ℂ)) hs
    have h2 : LSeries (1 : ℕ → ℂ) (σ : ℂ) = riemannZeta (σ : ℂ) :=
      LSeries_one_eq_riemannZeta hs
    have h3 : deriv (LSeries (1 : ℕ → ℂ)) (σ : ℂ) = deriv riemannZeta (σ : ℂ) := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
      exact LSeries_one_eq_riemannZeta hz
    rw [logDeriv_apply, ← h3, ← h2, h1]
    simp only [neg_div, neg_neg]
  -- character side
  have hchar : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ) =
      - LSeries ((fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) *
          fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) := by
    have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ q) hs
    have h2 : LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) (σ : ℂ) =
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ : ℂ) :=
      (DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ q) hs).symm
    have h3 : deriv (LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q))) (σ : ℂ) =
        deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ) := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
      exact (DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ q) hz).symm
    rw [logDeriv_apply, ← h3, ← h2, h1]
    simp only [neg_div, neg_neg]
  have hLfun : logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ) =
      logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ) := by
    have h : Lfun481 (1 : DirichletCharacter ℂ q) = DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) :=
      funext fun z => by simp only [Lfun481, dif_neg (NeZero.ne q)]
    rw [h]
  have hs1 : Summable (fun n : ℕ => LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) *
      fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ q) hs
  have hs2 : Summable (fun n : ℕ => LSeries.term
      (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hA : (logDeriv riemannZeta (σ : ℂ)).re =
      -∑' n, (LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n).re := by
    rw [hzeta, Complex.neg_re, LSeries, Complex.re_tsum hs2]
  have hB : (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re =
      -∑' n, (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) *
        fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n).re := by
    rw [hLfun, hchar, Complex.neg_re, LSeries, Complex.re_tsum hs1]
  rw [hA, hB]
  have hkey : ∑' n, (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) *
        fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n).re ≤
      ∑' n, (LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        (σ : ℂ) n).re := by
    refine Summable.tsum_le_tsum (f := fun n => (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) * fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n).re)
      ?_ (Complex.reCLM.summable hs1) (Complex.reCLM.summable hs2)
    intro n
    rcases eq_or_ne n 0 with h0 | hn
    · subst h0
      have hp0 : ((σ + 1)/2 : ℝ) ≠ 0 := by positivity
      simp [Real.zero_rpow hp0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      simp only [Pi.mul_apply]
      have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have ea : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast n, Complex.ofReal_cpow hn0.le]
      set A : ℝ := (n : ℝ) ^ σ with hA
      have hA0 : 0 < A := Real.rpow_pos_of_pos hn0 σ
      have hLnn : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hleft : ((1 : DirichletCharacter ℂ q) (n : ZMod q) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (A : ℂ)).re =
          ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re *
            (ArithmeticFunction.vonMangoldt n / A) := by
        have hsplit : ((1 : DirichletCharacter ℂ q) (n : ZMod q) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (A : ℂ)) =
            (1 : DirichletCharacter ℂ q) (n : ZMod q) *
              ((ArithmeticFunction.vonMangoldt n / A : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hsplit, Complex.mul_re]
        simp
      have hright : ((((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (A : ℂ))).re =
          ArithmeticFunction.vonMangoldt n / A := by
        rw [← Complex.ofReal_div, Complex.ofReal_re]
      rw [ea, hleft, hright]
      have hre_le : ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re ≤ 1 := by
        by_cases hu : IsUnit (n : ZMod q)
        · rw [MulChar.one_apply hu]; simp
        · rw [MulChar.map_nonunit _ hu]; simp
      have hLa : 0 ≤ ArithmeticFunction.vonMangoldt n / A := div_nonneg hLnn hA0.le
      nlinarith
  exact neg_le_neg hkey

/-- LEAF: Iwaniec 1974 page 103, Lemma 11 step (i), display (16).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, display (16),
from Lemma 9 page 102 and Lemma 10 page 102. For `χ ≠ χ₀` modulo `q ≥ 3`, a zero `ρ = s` of
`L(s, χ)` with `β > 1 - θ`, `σ₀ = 1 + 5θ`, `s₀ = σ₀ + iγ`:
`Re L'/L (s₀, χ) ≥ -(4/η) log (M / 5θ) + 1 / (σ₀ - β)`. -/
theorem iwaniec_display16_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (s : ℂ) (l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|s.im| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))))
    (hzero : Lfun481 χ s = 0) (hreg : 1 - θ < s.re) (hlt : s.re < 1) :
    -(4 / η) * Real.log (M / (5 * θ)) + 1 / (1 + 5 * θ - s.re) ≤
      (logDeriv (Lfun481 χ) (((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)).re := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, Lemma 11 step (i), display (17).
Class: HARD.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, display (17),
from Lemma 9 page 102 applied to `χ²`, nonprincipal since `χ` has a nonreal value, and
Lemma 10 page 102. With `σ₀ = 1 + 5θ`, `s₁ = σ₀ + 2iγ`:
`Re L'/L (s₁, χ²) ≥ -(8/η) log (2M / 5θ)`. The paper uses `M` at the height `γ` of the zero
also around `s₁`; see the QUESTION in the notes. -/
theorem iwaniec_display17_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    -(8 / η) * Real.log (2 * M / (5 * θ)) ≤
      (logDeriv (Lfun481 (χ ^ 2)) (((1 + 5 * θ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re := by
  sorry

/-- LEAF: Iwaniec 1974 page 102, displays (14) and (15) of the proof of Lemma 11.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 102: display (14),
`3 Re L'/L (σ, χ₀) + 4 Re L'/L (σ + it, χ) + Re L'/L (σ + 2it, χ²) ≤ 0` for `σ > 1`, and
display (15) at the real point `σ`, `Re L'/L (σ, χ₀) ≥ -1/(σ - 1) - 2 log 5l`, from
`|ζ'/ζ (σ) + 1/(σ - 1)| < 3` and `|L'/L (σ, χ₀) - ζ'/ζ (σ)| < 2 log log 3d`. Here `l` is taken at
any height `γ`, since `log 3d ≤ l` for every `γ`. -/
theorem iwaniec_display14_15_1122 (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (γ l σ : ℝ) (hl : l = Real.log ((q : ℝ) * (|γ| + 3))) (hσ : 1 < σ) :
    4 * (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re +
      (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re ≤
      3 / (σ - 1) + 6 * Real.log (5 * l) := by
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  have h341 := steps_341 hq χ σ γ hσ
  have hprin := steps_prin (q := q) σ hσ
  have hz := steps_zeta_logDeriv_bound σ hσ
  set A1 := (logDeriv (Lfun481 (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re with hA1
  set B1 := (logDeriv (Lfun481 χ) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re with hB1
  set C1 := (logDeriv (Lfun481 (χ ^ 2)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re with hC1
  set Z1 := (logDeriv riemannZeta (σ : ℂ)).re with hZ1
  have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have ht : (0:ℝ) ≤ |γ| := abs_nonneg γ
  have hbase : (9:ℝ) ≤ (q:ℝ) * (|γ| + 3) := by nlinarith
  have he2 : Real.exp 2 < 9 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hl2 : 2 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have h15 : (3/2 : ℝ) ≤ Real.log (5 * l) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 : Real.exp (3/2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hD : 3 / (σ - 1) = 3 * (1 / (σ - 1)) := by ring
  rw [hD]
  nlinarith [h341, hprin, hz, h15]


/-- LEAF: Iwaniec 1974 page 103, the closing numerical step of Lemma 11 step (i).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103, the line after
display (17): `6 log 5l + (16/η) log (M / 5θ) + (8/η) log (2M / 5θ) ≤ 1 / (15 θ)`, with
`θ = η / (400 log M)` of page 102 in its printed page 97 form, `iwaniec_theta_identity1122`.
A floating point check over `log d` up to `10⁵` and `l` from `log 9` to `10⁸` gives a ratio of
left to right side at most about `0.96`. -/
theorem iwaniec_closing_numeric1122 (q : ℕ) (hq : 3 ≤ q) (γ l η M θ : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100)
    (hθ : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (l * Real.log (2 * l)) ^ (3 / 4 : ℝ)))) :
    6 * Real.log (5 * l) + (16 / η) * Real.log (M / (5 * θ)) +
      (8 / η) * Real.log (2 * M / (5 * θ)) ≤ 1 / (15 * θ) := by
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
  have hl0 : 0 < l := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (2 * l) := ⟨_, rfl⟩
  rw [← hL] at hη hθ
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    linarith
  obtain ⟨D, hD⟩ : ∃ D, D = Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hD] at hθ
  have hd : (1 : ℝ) ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.log_nonneg hd
  obtain ⟨u, hu⟩ : ∃ u, u = l ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_rpow (by linarith) (by norm_num)
  obtain ⟨E, hE⟩ : ∃ E, E = Real.sqrt l * L ^ (3 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hE] at hη
  have hsqrt1 : 1 ≤ Real.sqrt l := by
    rw [Real.le_sqrt (by norm_num) hl0.le]; linarith
  have hLp : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hE1 : 1 ≤ E := by rw [hE]; exact one_le_mul_of_one_le_of_one_le hsqrt1 hLp
  have hE0 : 0 < E := by linarith
  have hηE : η * E = 1 := by rw [hη]; field_simp
  -- P = E u
  have hP : (l * L) ^ (3 / 4 : ℝ) = E * u := by
    rw [Real.mul_rpow hl0.le (by linarith), hE, hu, Real.sqrt_eq_rpow]
    have : l ^ (3 / 4 : ℝ) = l ^ (1 / 2 : ℝ) * l ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hl0]; norm_num
    rw [this]; ring
  rw [hP] at hθ
  obtain ⟨X, hX⟩ : ∃ X, X = D + E * u := ⟨_, rfl⟩
  rw [← hX] at hθ
  have hEu : 1 ≤ E * u := one_le_mul_of_one_le_of_one_le hE1 hu1
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have hθpos : 0 < θ := by rw [hθ]; positivity
  -- log M
  have hdpos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by linarith
  have hMpos : 0 < M := by rw [hM]; positivity
  have hlogM : Real.log M = 100 * (η * D + u) := by
    rw [hM, Real.log_pow, Real.log_mul (Real.rpow_pos_of_pos hdpos _).ne' (Real.exp_pos _).ne',
      Real.log_rpow hdpos, Real.log_exp, ← hD, ← hu]
    push_cast; ring
  have h5θ : 5 * θ = 1 / (8000 * X) := by rw [hθ]; field_simp; ring
  have hlog5θ : Real.log (5 * θ) = -Real.log (8000 * X) := by
    rw [h5θ, one_div, Real.log_inv]
  have hA : Real.log (M / (5 * θ)) = Real.log M + Real.log (8000 * X) := by
    rw [Real.log_div hMpos.ne' (by positivity), hlog5θ]; ring
  have hB : Real.log (2 * M / (5 * θ)) = Real.log 2 + Real.log M + Real.log (8000 * X) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hMpos.ne',
      hlog5θ]; ring
  have h16 : 16 / η = 16 * E := by rw [hη]; field_simp
  have h8 : 8 / η = 8 * E := by rw [hη]; field_simp
  have hR : 1 / (15 * θ) = 40000 * X / 15 := by rw [hθ]; field_simp; ring
  have hEM : E * Real.log M = 100 * X := by
    rw [hlogM, hX]
    have : E * (100 * (η * D + u)) = 100 * ((η * E) * D + E * u) := by ring
    rw [this, hηE]; ring
  -- scalar bounds
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog5 : Real.log 5 ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog8000 : Real.log 8000 ≤ 13 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlu : Real.log u = (1 / 4) * Real.log l := by rw [hu, Real.log_rpow hl0]
  have hlu' : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hll : Real.log l ≤ 4 * (u - 1) := by linarith
  have hLL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hLeq : L = Real.log 2 + Real.log l := by rw [hL, Real.log_mul (by norm_num) hl0.ne']
  have h5l : Real.log (5 * l) = Real.log 5 + Real.log l := Real.log_mul (by norm_num) hl0.ne'
  have h5l0 : 0 ≤ Real.log (5 * l) := Real.log_nonneg (by linarith)
  have hlogP : Real.log (E * u) = (3 / 4) * (Real.log l + Real.log L) := by
    rw [← hP, Real.log_rpow (by positivity), Real.log_mul hl0.ne' (by positivity)]
  have hS : 6 * Real.log (5 * l) + 24 * (Real.log 8000 + Real.log (E * u)) + 8 * Real.log 2 ≤
      (800 / 3) * u := by
    rw [h5l, hlogP]; linarith
  have hlam : Real.log (8000 * X) = Real.log 8000 + Real.log X :=
    Real.log_mul (by norm_num) hX0.ne'
  have hXP : Real.log X - Real.log (E * u) ≤ X / (E * u) - 1 := by
    rw [← Real.log_div hX0.ne' (by positivity)]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hEX : E * (X / (E * u) - 1) ≤ D := by
    have : E * (X / (E * u) - 1) = D / u := by
      rw [hX]; field_simp; ring
    rw [this]; exact div_le_self hD0 hu1
  have hK : 6 * Real.log (5 * l) + 24 * E * Real.log (8000 * X) + 8 * E * Real.log 2 ≤
      (800 / 3) * X := by
    have h1 := mul_le_mul_of_nonneg_left hS hE0.le
    have h2 : E * (Real.log X - Real.log (E * u)) ≤ E * (X / (E * u) - 1) :=
      mul_le_mul_of_nonneg_left hXP hE0.le
    have h3 : 6 * Real.log (5 * l) ≤ E * (6 * Real.log (5 * l)) := by
      have := mul_le_mul_of_nonneg_right hE1 (by linarith : (0:ℝ) ≤ 6 * Real.log (5 * l))
      linarith
    rw [hlam]
    linarith [h1, h2, hEX, h3, hX]
  rw [hA, hB, h16, h8, hR]
  have : 6 * Real.log (5 * l) + 16 * E * (Real.log M + Real.log (8000 * X)) +
      8 * E * (Real.log 2 + Real.log M + Real.log (8000 * X)) =
      6 * Real.log (5 * l) + 24 * E * Real.log (8000 * X) + 8 * E * Real.log 2 +
        24 * (E * Real.log M) := by ring
  rw [this, hEM]
  linarith

/-- The printed denominator of page 97 is positive for `q ≥ 3`. -/
theorem iwaniec_printed_theta_pos1122 (q : ℕ) (hq : 3 ≤ q) (γ : ℝ) :
    0 < 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (Real.log ((q : ℝ) * (|γ| + 3)) *
        Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3)))) ^ (3 / 4 : ℝ))) := by
  have hq' : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ht : 0 ≤ |γ| := abs_nonneg _
  have hbase : (3 : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by nlinarith
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hl1 : 1 < Real.log ((q : ℝ) * (|γ| + 3)) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  have hl2 : 0 < Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3))) :=
    Real.log_pos (by linarith)
  have hpow : 0 < (Real.log ((q : ℝ) * (|γ| + 3)) *
      Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3)))) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by linarith) hl2) _
  have hd : (1 : ℝ) ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hlogd : 0 ≤ Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := Real.log_nonneg hd
  have : 0 < Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) +
      (Real.log ((q : ℝ) * (|γ| + 3)) *
        Real.log (2 * Real.log ((q : ℝ) * (|γ| + 3)))) ^ (3 / 4 : ℝ) := by linarith
  positivity

/-- The printed Theorem 2 of page 97 for characters with a nonreal value, assembled from the
four steps of Lemma 11 step (i): displays (16), (17), (14) with (15), and the closing
numerical inequality. -/
theorem iwaniec_printed_nonreal_split1122 (r : ℕ) (hr : 3 ≤ r) (χ : DirichletCharacter ℂ r)
    (hnonreal : ∃ a, (χ a).im ≠ 0) (s : ℂ)
    (hs : 1 - 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (Real.log ((r : ℝ) * (|s.im| + 3)) *
          Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ))) < s.re) :
    Lfun481 χ s ≠ 0 := by
  have hr0 : r ≠ 0 := by omega
  rcases le_or_gt 1 s.re with hge | hlt
  · haveI : NeZero r := ⟨hr0⟩
    have hne : χ ≠ 1 := by
      rintro rfl
      obtain ⟨a, ha⟩ := hnonreal
      apply ha
      by_cases hu : IsUnit a
      · simp [MulChar.one_apply hu]
      · simp [MulChar.map_nonunit _ hu]
    have hL : Lfun481 χ s = DirichletCharacter.LFunction χ s := by
      simp only [Lfun481, dif_neg hr0]
    rw [hL]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hge
  · intro hzero
    have hθpos := iwaniec_printed_theta_pos1122 r hr s.im
    obtain ⟨l, hl⟩ : ∃ l, l = Real.log ((r : ℝ) * (|s.im| + 3)) := ⟨_, rfl⟩
    obtain ⟨η, hη⟩ : ∃ η, η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹ := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M, M = (((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) ^ η *
        Real.exp (l ^ (1 / 4 : ℝ))) ^ 100 := ⟨_, rfl⟩
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (l * Real.log (2 * l)) ^ (3 / 4 : ℝ))) := ⟨_, rfl⟩
    have hθ' : θ = 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
        (Real.log ((r : ℝ) * (|s.im| + 3)) *
          Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ))) := by
      rw [hθ, hl]
    rw [← hθ'] at hs hθpos
    have hA := iwaniec_display16_1122 r hr χ hnonreal s l η M θ hl hη hM hθ hzero hs hlt
    have hB := iwaniec_display17_1122 r hr χ hnonreal s.im l η M θ hl hη hM hθ
    have hC := iwaniec_display14_15_1122 r hr χ s.im l (1 + 5 * θ) hl (by linarith)
    have hD := iwaniec_closing_numeric1122 r hr s.im l η M θ hl hη hM hθ
    have hC' : 4 * (logDeriv (Lfun481 χ) (((1 + 5 * θ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)).re +
        (logDeriv (Lfun481 (χ ^ 2))
          (((1 + 5 * θ : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I)).re ≤
        3 / (5 * θ) + 6 * Real.log (5 * l) := by
      have h5 : (1 + 5 * θ) - 1 = 5 * θ := by ring
      rw [h5] at hC
      exact hC
    set x := 1 + 5 * θ - s.re with hx
    have hxpos : 0 < x := by rw [hx]; linarith
    have hkey : 4 / x ≤ 3 / (5 * θ) + 1 / (15 * θ) := by
      have h4 : 4 * (1 / x) = 4 / x := by ring
      have hm : 4 * ((4 / η) * Real.log (M / (5 * θ))) =
          (16 / η) * Real.log (M / (5 * θ)) := by ring
      linarith [hA, hB, hC', hD, hm, h4]
    have hsum : 3 / (5 * θ) + 1 / (15 * θ) = 2 / (3 * θ) := by
      field_simp
      ring
    rw [hsum, div_le_div_iff₀ hxpos (by positivity)] at hkey
    have : 6 * θ ≤ x := by linarith
    rw [hx] at this
    linarith

/-- The lab statement `IwaniecStatement481` from the four steps of Lemma 11 step (i). -/
theorem iwaniecStatement481_steps1122 : IwaniecStatement481 :=
  iwaniecStatement481_of_printed1122 (fun r hr χ hnonreal s hs =>
    iwaniec_printed_nonreal_split1122 r hr χ hnonreal s hs)

/-- The exact statement of `iwaniec_no_zero_open_strip481` of `SPLIT_iwaniec_zero_free481`,
assembled from the four steps. -/
theorem iwaniec_no_zero_open_strip481_steps (r : ℕ) (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hnonreal : ∃ a, (χ a).im ≠ 0)
    {s : ℂ} (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_small_modulus_bounded_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_small_modulus_bounded_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : r ≤ 10 ^ 4)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : |s.im| ≤ 2) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_large_modulus_bounded_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_large_modulus_bounded_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : 10 ^ 4 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : |s.im| ≤ 2) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_small_modulus_large_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_small_modulus_large_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : r ≤ 10 ^ 4)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : 2 ≤ |s.im|) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

/-- The exact statement of the cell `iwaniec_no_zero_strip_large_modulus_large_height481`
of `SPLIT_iwaniec_no_zero_open_strip481`, from the four steps. -/
theorem iwaniec_no_zero_strip_large_modulus_large_height481_steps
    (r : ℕ) (hr : 1 ≤ r) (hmod : 10 ^ 4 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hnonreal : ∃ a, (χ a).im ≠ 0) {s : ℂ}
    (hlt : s.re < 1) (hpos : 0 < s.re)
    (hreg : 1 - 1 / iwaniecDenom481 r s.im < s.re)
    (hheight : 2 ≤ |s.im|) : Lfun481 χ s ≠ 0 :=
  iwaniecStatement481_steps1122 r hr χ hprim hnonreal s hreg

end

end LeanLab.LPZ2007
