import LeanLab.ChirreHagen2025.Statements

/-!
Decomposition of P0075 Lemma 2.1, pages 2 and 3.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp122b

/-- P0075 page 3, the bound obtained by adding the four terms of equation 2.1. -/
noncomputable def backlundRhs (u N : ℝ) : ℝ :=
  Real.log (N - 1) +
    1.001 * u * (Real.log N ^ 2 + 4 * Real.log N + 8) / (4 * Real.pi * Real.sqrt N) -
    Real.eulerMascheroniConstant + 1.3 / Real.log (N - 1) ^ 2 + 1 / u +
    Real.log N ^ 2 / (8 * Real.pi * Real.sqrt N)

/-- LEAF. P0075 page 3, equation 2.1 and the next five displays.
Uses reference 11, Lemma 10 and reference 19, Theorem 10.
At integer prime powers the boundary term is interpreted by its left limit. -/
theorem backlund_reduction (hRH : RiemannHypothesis) (σ t : ℝ)
    (hσ : 1 < σ) (hσtop : σ < 2) (ht : 100 ≤ |t|)
    (N : ℕ) (hN : 74 ≤ N) :
    ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      backlundRhs |t| N := by
  sorry

/-- LEAF. P0075 page 3, choose N = floor of |t| to the fourth power plus one. -/
theorem backlund_numeric (u : ℝ) (hu : 100 ≤ u) :
    74 ≤ ⌊u ^ 4⌋₊ + 1 ∧ backlundRhs u ((⌊u ^ 4⌋₊ + 1 : ℕ) : ℝ) ≤ 4 * Real.log u := by
  have hu0 : 0 < u := by linarith
  let N : ℝ := ((⌊u ^ 4⌋₊ + 1 : ℕ) : ℝ)
  have hNlo : u ^ 4 ≤ N := by
    dsimp [N]
    push_cast
    exact (Nat.lt_floor_add_one (u ^ 4)).le
  have hNhi : N ≤ u ^ 4 + 1 := by
    dsimp [N]
    push_cast
    linarith [Nat.floor_le (show 0 ≤ u ^ 4 by positivity)]
  have hu4 : (100 : ℝ) ^ 4 ≤ u ^ 4 := by gcongr
  have hNpos : 0 < N := by linarith
  have hNm : 1 < N - 1 := by norm_num at hu4; linarith
  have hNnat : 74 ≤ ⌊u ^ 4⌋₊ + 1 := by
    have : (74 : ℝ) ≤ N := by norm_num at hu4; linarith
    dsimp [N] at this
    exact_mod_cast this
  refine ⟨hNnat, ?_⟩
  change backlundRhs u N ≤ 4 * Real.log u
  have hL0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogNm : Real.log (N - 1) ≤ 4 * Real.log u := by
    calc Real.log (N - 1) ≤ Real.log (u ^ 4) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = 4 * Real.log u := by rw [Real.log_pow]; norm_num
  have hlog2 : 2 * Real.log 2 ≤ Real.log u := by
    calc 2 * Real.log 2 = Real.log ((2 : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log u := Real.log_le_log (by norm_num) (by norm_num; linarith)
  have hlogN : Real.log N ≤ 4.5 * Real.log u := by
    have hpow : 1 ≤ u ^ 4 := by norm_num at hu4; linarith
    calc Real.log N ≤ Real.log (2 * u ^ 4) :=
          Real.log_le_log hNpos (by linarith)
      _ = Real.log 2 + 4 * Real.log u := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 4.5 * Real.log u := by linarith
  have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have he2 : Real.exp 2 ≤ 100 := by
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    nlinarith [Real.exp_pos 1]
  have hl100 : Real.log 100 ≤ 4.7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : Real.exp (4.7 : ℝ) = Real.exp 1 ^ 4 * Real.exp (7 / 30 : ℝ) ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
    rw [he]
    calc (100 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 * (37 / 30 : ℝ) ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 4 * Real.exp (7 / 30 : ℝ) ^ 3 := by
        gcongr
        · exact Real.exp_one_gt_d9.le
        · linarith [Real.add_one_le_exp (7 / 30 : ℝ)]
  have hratio := Real.log_div_sqrt_antitoneOn
    (show Real.exp 2 ≤ 100 from he2) (he2.trans hu) hu
  have hratio0 : 0 ≤ Real.log u / Real.sqrt u := by positivity
  have hratio' : Real.log u / Real.sqrt u ≤ 0.47 := by
    have hs : Real.sqrt (100 : ℝ) = 10 := by norm_num
    change Real.log u / Real.sqrt u ≤ Real.log 100 / Real.sqrt 100 at hratio
    rw [hs] at hratio
    linarith
  have hsq := pow_le_pow_left₀ hratio0 hratio' 2
  rw [div_pow, Real.sq_sqrt hu0.le] at hsq
  have hLsq : Real.log u ^ 2 ≤ 0.2209 * u := by
    exact (div_le_iff₀ hu0).mp (by norm_num at hsq ⊢; exact hsq)
  have hratio1 := Real.log_div_self_antitoneOn
    (show Real.exp 1 ≤ 100 from he1.trans (by norm_num))
    (show Real.exp 1 ≤ u from he1.trans (by linarith)) hu
  have hL : Real.log u ≤ 0.047 * u := by
    have : Real.log u / u ≤ 0.047 := by
      change Real.log u / u ≤ Real.log 100 / 100 at hratio1
      linarith
    exact (div_le_iff₀ hu0).mp this
  have hNsq : Real.log N ^ 2 ≤ 4.473225 * u := by
    have h := pow_le_pow_left₀ hlogN0 hlogN 2
    nlinarith
  have hNlog : Real.log N ≤ 0.2115 * u := by linarith
  have hsqrt : u ^ 2 ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt hNlo
    have he : Real.sqrt (u ^ 4) = u ^ 2 := by
      convert Real.sqrt_sq (sq_nonneg u) using 1 <;> ring
    rwa [he] at h
  have hden4 : 12 * u ^ 2 ≤ 4 * Real.pi * Real.sqrt N := by
    have hp := Real.pi_gt_three.le
    nlinarith [Real.sqrt_nonneg N]
  have hden8 : 24 * u ^ 2 ≤ 8 * Real.pi * Real.sqrt N := by linarith
  have hd4 : 0 < 4 * Real.pi * Real.sqrt N := by positivity
  have hd8 : 0 < 8 * Real.pi * Real.sqrt N := by positivity
  have hbig : 1.001 * u * (Real.log N ^ 2 + 4 * Real.log N + 8) /
      (4 * Real.pi * Real.sqrt N) ≤ 0.451 := by
    apply (div_le_iff₀ hd4).2
    have hsum : Real.log N ^ 2 + 4 * Real.log N + 8 ≤ 5.399225 * u := by linarith
    have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1.001 * u by positivity)
    nlinarith [sq_nonneg u]
  have hsmall : Real.log N ^ 2 / (8 * Real.pi * Real.sqrt N) ≤ 0.002 := by
    apply (div_le_iff₀ hd8).2
    have huu : 100 * u ≤ u ^ 2 := by nlinarith
    nlinarith
  have hlogNm10 : 10 ≤ Real.log (N - 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc Real.exp 1 ^ 10 ≤ (3 : ℝ) ^ 10 := by gcongr
      _ ≤ N - 1 := by norm_num at hu4 ⊢; linarith
  have hrec : 1.3 / Real.log (N - 1) ^ 2 ≤ 0.013 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.log (N - 1) ^ 2)).2
    nlinarith
  have huinv : 1 / u ≤ 0.01 := by apply (div_le_iff₀ hu0).2; linarith
  have hgamma := Real.one_half_lt_eulerMascheroniConstant
  unfold backlundRhs
  linarith


/-- LEAF. P0075 page 3, the last sentence extends the interior bound by continuity. -/
theorem boundary_extension (t : ℝ) (ht : 100 ≤ |t|) (C : ℝ)
    (h : ∀ σ : ℝ, 1 < σ → σ < 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ C) :
    ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ C := by
  have ht0 : t ≠ 0 := by intro he; norm_num [he] at ht
  have hcont : ContinuousOn (fun σ : ℝ =>
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖)
      (Set.Icc 1 2) := by
    intro σ hσ
    have hs : (σ : ℂ) + t * Complex.I ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      exact ht0 hi
    have harg : ContinuousAt (fun x : ℝ => (x : ℂ) + t * Complex.I) σ := by
      fun_prop
    have hz : ContinuousAt (fun x : ℝ => riemannZeta ((x : ℂ) + t * Complex.I)) σ :=
      ContinuousAt.comp (g := riemannZeta) (f := fun x : ℝ => (x : ℂ) + t * Complex.I)
        (differentiableAt_riemannZeta hs).continuousAt harg
    have hd : ContinuousAt (fun x : ℝ => deriv riemannZeta ((x : ℂ) + t * Complex.I)) σ :=
      ContinuousAt.comp (g := deriv riemannZeta) (f := fun x : ℝ => (x : ℂ) + t * Complex.I)
        (analyticOn_riemannZeta.deriv.continuousOn.continuousAt
          (isOpen_compl_singleton.mem_nhds hs)) harg
    have hn : riemannZeta ((σ : ℂ) + t * Complex.I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simpa using hσ.1)
    exact (hd.div hz hn).norm.continuousWithinAt
  have hcl : closure (Set.Ioo (1 : ℝ) 2) = Set.Icc 1 2 :=
    closure_Ioo (by norm_num)
  intro σ hσ hσtop
  exact le_on_closure (fun x hx => h x hx.1 hx.2)
    (hcl.symm ▸ hcont) continuousOn_const (hcl.symm ▸ ⟨hσ, hσtop⟩)

/-- P0075 Lemma 2.1, assembled with exactly the lab's cited Prop as conclusion.
CONDITIONAL ON backlund_reduction until its published analytic inputs are formalized. -/
theorem lemma2_1_assembled : lemma2_1 := by
  intro hRH σ t hσ hσtop ht
  apply boundary_extension t ht (4 * Real.log |t|) ?_ σ hσ hσtop
  intro s hs hstop
  obtain ⟨hN, hnum⟩ := backlund_numeric |t| ht
  exact (backlund_reduction hRH s t hs hstop ht _ hN).trans hnum

end LeanLab.ChirreHagen2025.Decomp122b
