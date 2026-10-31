/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5793, paper P0097.

# Zinoviev 1997, Theorem 3.4, assembled, CONDITIONAL ON the GRH arc input only

`ArcInput N` is exactly what Zinoviev's GRH lemmas give for one `N`, in the lab's convention
`SZ(α) = S(-α)`, so the arcs are the paper's reflected through `α ↦ -α` mod 1:

* a measurable set `E`, the major arcs `E₁'`, with `|S(α)| ≤ 0.18 N/ln N` on `(0, 1] \ E`,
  Lemma 2.1, p. 343, which covers `E₁'' ∪ E₂`;
* `∫_{(0,1] ∩ E} S³ e(-Nα) = (σ/e)(N²/2 + 8θN) + c` with `σ > 1.21`, `|θ| ≤ 1`, `|c| ≤ 0.04 N²`,
  Lemma 3.2 with the `0.04` its proof gives, Lemma 3.3 with the `1/e` its proof gives, F-5027, and
  `σ > 12/π² > 1.21` for odd `N`, p. 357.

`zinoviev_of_arcs`: for every natural `N ≥ 10^20`, `ArcInput N` implies that `N` is a sum of three
primes. Everything else is PROVED here: the identity (0.4) through `SZ_cube_tendsto` and the prime
power bound `T3_le` with Mathlib's `ψ - θ ≤ 2√x log x`; the mean square (3.17) through
`SZ_sq_le`, which uses Parseval and Lemma 1.5; the closing arithmetic of p. 357. CONDITIONAL ON
`ArcInput`, the GRH content of Lemmas 2.1 and 3.2. Binary Goldbach is OPEN.
-/
import LeanLab.Zinoviev1997.PrimePowers
import LeanLab.Zinoviev1997.Arith
import LeanLab.ChebyshevExplicit.Psi30Upper

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology ArithmeticFunction LeanLab.CircleOrth MeasureTheory

/-- The GRH arc input of Zinoviev's Lemmas 2.1, 3.2 and 3.3 for one `N`. -/
def ArcInput (N : ℕ) : Prop :=
  ∃ E : Set ℝ, MeasurableSet E ∧
    (∀ α ∈ Set.Ioc (0 : ℝ) 1 \ E, ‖SZ N α‖ ≤ 0.18 * N / Real.log N) ∧
    ∃ σ θ₁ : ℝ, 1.21 < σ ∧ |θ₁| ≤ 1 ∧
      ‖(∫ α in Set.Ioc (0 : ℝ) 1 ∩ E, SZ N α ^ 3 * ee (-((N : ℤ) * α))) -
        ((σ / Real.exp 1 * ((N : ℝ) ^ 2 / 2 + 8 * θ₁ * N) : ℝ) : ℂ)‖ ≤ 0.04 * (N : ℝ) ^ 2

/-- **Zinoviev 1997, Theorem 3.4**, CONDITIONAL ON `ArcInput N`. -/
theorem zinoviev_of_arcs (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (h : ArcInput N) : IsTernarySum N := by
  by_contra hT
  obtain ⟨E, hE, hminor, σ, θ₁, hσ, hθ, hmaj⟩ := h
  have hNR : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have hN0 : 0 < N := by exact_mod_cast hNR
  set L := Real.log N with hLdef
  have hL : 46 ≤ L := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  set f : ℝ → ℂ := fun α => SZ N α ^ 3 * ee (-((N : ℤ) * α)) with hf
  have hfc : Continuous f :=
    ((continuous_SZ hN0).pow 3).mul (continuous_ee.comp (continuous_const.mul continuous_id).neg)
  set I := ∫ α in (0 : ℝ)..1, f α with hIdef
  have hsplit : I = (∫ α in Set.Ioc (0 : ℝ) 1 ∩ E, f α) + ∫ α in Set.Ioc (0 : ℝ) 1 \ E, f α := by
    rw [hIdef, intervalIntegral.integral_of_le zero_le_one,
      integral_inter_add_sdiff hE (hfc.integrableOn_Ioc)]
  -- the minor arcs
  set c := 0.18 * (N : ℝ) / L
  have hc0 : 0 ≤ c := by positivity
  have hg : Continuous fun α => ‖SZ N α‖ ^ 2 := (continuous_SZ hN0).norm.pow 2
  have hA : MeasurableSet (Set.Ioc (0 : ℝ) 1 \ E) := measurableSet_Ioc.diff hE
  have hrest : ‖∫ α in Set.Ioc (0 : ℝ) 1 \ E, f α‖ ≤ 0.1728 * (N : ℝ) ^ 2 := by
    calc ‖∫ α in Set.Ioc (0 : ℝ) 1 \ E, f α‖ ≤ ∫ α in Set.Ioc (0 : ℝ) 1 \ E, ‖f α‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ α in Set.Ioc (0 : ℝ) 1 \ E, c * ‖SZ N α‖ ^ 2 := by
          refine setIntegral_mono_on (hfc.norm.integrableOn_Ioc.mono_set Set.diff_subset)
            ((hg.const_mul c).integrableOn_Ioc.mono_set Set.diff_subset) hA fun α hα => ?_
          rw [hf]; simp only
          rw [norm_mul, norm_ee, mul_one, norm_pow, pow_succ]
          have := hminor α hα
          have h0 : 0 ≤ ‖SZ N α‖ ^ 2 := sq_nonneg _
          calc ‖SZ N α‖ ^ 2 * ‖SZ N α‖ ≤ ‖SZ N α‖ ^ 2 * c := mul_le_mul_of_nonneg_left this h0
            _ = c * ‖SZ N α‖ ^ 2 := by ring
      _ ≤ ∫ α in Set.Ioc (0 : ℝ) 1, c * ‖SZ N α‖ ^ 2 := by
          refine setIntegral_mono_set (hg.const_mul c).integrableOn_Ioc
            (ae_of_all _ fun α => by positivity) Set.diff_subset.eventuallyLE
      _ = c * ∫ α in (0 : ℝ)..1, ‖SZ N α‖ ^ 2 := by
          rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
      _ ≤ c * (0.96 * N * L) := mul_le_mul_of_nonneg_left (SZ_sq_le N hN) hc0
      _ = 0.1728 * (N : ℝ) ^ 2 := by
          have hL0 : L ≠ 0 := by linarith
          simp only [c]; field_simp; ring
  -- the major arcs
  have hse : 0.444 < σ / Real.exp 1 := by
    rw [lt_div_iff₀ (Real.exp_pos 1)]; nlinarith [Real.exp_one_lt_d9]
  have hθl := (abs_le.mp hθ).1
  have hmain : 0.444 * ((N : ℝ) ^ 2 / 2 - 8 * N) ≤ σ / Real.exp 1 * ((N : ℝ) ^ 2 / 2 + 8 * θ₁ * N) := by
    have hA1 : (N : ℝ) ^ 2 / 2 - 8 * N ≤ (N : ℝ) ^ 2 / 2 + 8 * θ₁ * N := by nlinarith
    have hA0 : 0 ≤ (N : ℝ) ^ 2 / 2 - 8 * N := by nlinarith
    exact mul_le_mul hse.le hA1 hA0 (by linarith)
  have hre_maj : σ / Real.exp 1 * ((N : ℝ) ^ 2 / 2 + 8 * θ₁ * N) - 0.04 * (N : ℝ) ^ 2 ≤
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ E, f α).re := by
    have := Complex.abs_re_le_norm ((∫ α in Set.Ioc (0 : ℝ) 1 ∩ E, f α) -
      ((σ / Real.exp 1 * ((N : ℝ) ^ 2 / 2 + 8 * θ₁ * N) : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at this
    have := (abs_le.mp (this.trans hmaj)).1
    linarith
  have hre_min : -(0.1728 * (N : ℝ) ^ 2) ≤ (∫ α in Set.Ioc (0 : ℝ) 1 \ E, f α).re := by
    have := Complex.abs_re_le_norm (∫ α in Set.Ioc (0 : ℝ) 1 \ E, f α)
    have := (abs_le.mp (this.trans hrest)).1
    linarith
  have hlow : 0.009 * (N : ℝ) ^ 2 ≤ I.re := by
    rw [hsplit, Complex.add_re]
    nlinarith
  -- the upper bound from the prime powers
  set U := 3 * Real.exp (-1) *
    ((Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * L) with hU
  have hup : I.re ≤ U := by
    have ht := (Complex.continuous_re.tendsto _).comp (SZ_cube_tendsto hN0)
    refine le_of_tendsto ht (Eventually.of_forall fun M => ?_)
    simp only [Function.comp, Complex.ofReal_re]
    exact T3_le hN0 hT M
  -- U is tiny
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hpt := Chebyshev.psi_sub_theta_le hN1
  have hpt0 : 0 ≤ Chebyshev.psi N - Chebyshev.theta N := by
    linarith [Chebyshev.theta_le_psi (N : ℝ)]
  have hpsi := LeanLab.ChebyshevExplicit.psi_le_11062 N
  have hsm := logN_small N hN
  have hpsi' : Chebyshev.psi N ≤ 1.2 * N := by nlinarith
  have hpsi0 : 0 ≤ Chebyshev.psi N := Chebyshev.psi_nonneg _
  have hc3 := cube_lt_exp L hL
  have hsq : Real.exp (L / 2) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNR]; congr 1; ring
  rw [hsq] at hc3
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNR.le
  have hL2 : L ^ 2 ≤ 0.0000587 * Real.sqrt N := by nlinarith
  have he1 := exp_neg_one_lt
  have hU1 : U ≤ 3 * 0.36788 * ((2 * Real.sqrt N * L) * (1.2 * N) * L) := by
    rw [hU]
    have hL0 : 0 ≤ L := by linarith
    have h1 : (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * L ≤
        (2 * Real.sqrt N * L) * (1.2 * N) * L := by
      apply mul_le_mul_of_nonneg_right _ hL0
      exact mul_le_mul hpt hpsi' hpsi0 (by positivity)
    have h2 : 0 ≤ (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * L := by positivity
    nlinarith [Real.exp_pos (-1)]
  have hU2 : 3 * 0.36788 * ((2 * Real.sqrt N * L) * (1.2 * N) * L) ≤ 0.0002 * (N : ℝ) ^ 2 := by
    have : (2 * Real.sqrt N * L) * (1.2 * N) * L = 2.4 * N * (Real.sqrt N * L ^ 2) := by ring
    rw [this]
    have h3 : Real.sqrt N * L ^ 2 ≤ 0.0000587 * N := by
      calc Real.sqrt N * L ^ 2 ≤ Real.sqrt N * (0.0000587 * Real.sqrt N) :=
            mul_le_mul_of_nonneg_left hL2 hs0.le
        _ = 0.0000587 * N := by linear_combination (0.0000587 : ℝ) * hss
    nlinarith
  have hN2 : 0 < (N : ℝ) ^ 2 := by positivity
  linarith

end LeanLab.Zinoviev1997
