/-
P0068 Zhan 1991, page 263 display (3.3) and page 264 display (3.4): Perron's truncated formula
on `Re s = c = 1 + 1/L` for the dyadic sums of (3.4), split into two cited LEAF steps:
`perron_single_leaf_pt`, Davenport chapter 17, and `perron_sum_leaf_pt`, the divisor bound
summation. The expansion of `Vline_pt` over tuples and the reduction are PROVED.
Source: papers/P0068.pdf. AI-written Lean code, Claude. Binary Goldbach is OPEN.

Falsity check: the statement is believed TRUE. The jump terms at `n₁⋯n₂₀ = u` or `= N - A`
cost `1/2` per tuple, the number of tuples with a given product is `≤ d₂₀(m) ≪ N^{ε/2}`,
`|aⱼ| ≤ log N`, and `T ≤ N` puts this `N^ε` inside `K N^{1+ε}/T`.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122
import LeanLab.PNTPort.ExplicitPsi1.Residues

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-- The partial sum (3.2), page 263: `Σ_{N-A<n≤u} Λ(n) χ(n)`. -/
def Psum_pt {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (Λ n : ℂ) * χ n

/-- The `j`-th term of Heath-Brown's identity with `k = 10`, `X = N^{1/10}`, page 263, summed
against `χ` over `N - A < n ≤ u`: `Σ (log * ζ^{j-1} * M_X^j)(n) χ(n)`. -/
def HBsum_pt {q : ℕ} (j : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n),
    (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) *
      muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) * χ n

/-- The dyadic sum of (3.4) before Perron's formula, page 264:
`Σ_{n_j ∈ I_j, N-A < n₁⋯n₂₀ ≤ u} a₁(n₁)χ(n₁)⋯a₂₀(n₂₀)χ(n₂₀)`, `I_j = (N_j, 2N_j]`. -/
def Dsum_pt {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Fintype.piFinset fun j : Fin 20 => dyad (Nv j)).filter
      (fun n => (N : ℝ) - A < ∏ j, (n j : ℝ) ∧ ∏ j, (n j : ℝ) ≤ u),
    ∏ j : Fin 20, aj (j.val + 1) (n j) * χ (n j)

/-- The line integral of (3.4), page 264, on `Re s = σ`, written in `t` with `s = σ + it`:
`(1/2πi) ∫_{σ-iT}^{σ+iT} F(s,χ) (u^s - (N-A)^s) s⁻¹ ds`. -/
def Vline_pt {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A σ T u : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fprod Nv χ ((σ : ℂ) + t * Complex.I) *
    (((u : ℂ) ^ ((σ : ℂ) + t * Complex.I) - (((N : ℝ) - A : ℝ) : ℂ) ^ ((σ : ℂ) + t * Complex.I))
      / ((σ : ℂ) + t * Complex.I))

/-- Perron's summation formula (3.3), (3.4) with `c = 1 + L⁻¹`, error `O(T⁻¹ N^{1+ε})`. -/
def PerronTrunc_pt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ‖Dsum_pt Nv χ N A u - Vline_pt Nv χ N A (1 + 1 / Real.log N) T u‖ ≤ K * (N : ℝ) ^ (1 + ε) / T

/-! ### The split -/

/-- The coefficient `a₁(n₁)χ(n₁)⋯a₂₀(n₂₀)χ(n₂₀)` of one tuple, page 264. -/
def coef_pt {q : ℕ} (χ : DirichletCharacter ℂ q) (n : Fin 20 → ℕ) : ℂ :=
  ∏ j : Fin 20, aj (j.val + 1) (n j) * χ (n j)

/-- The product `n₁⋯n₂₀` of one tuple. -/
def Pn_pt (n : Fin 20 → ℕ) : ℝ := ∏ j, (n j : ℝ)

/-- The single term Perron integral `(1/2πi) ∫_{c-iT}^{c+iT} y^s s⁻¹ ds`, written in `t`. -/
def Jint_pt (c T y : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)

/-- The step function `1` for `y ≥ 1`, `0` for `y < 1`, the limit of `Jint_pt` off `y = 1`. -/
def Hstep_pt (y : ℝ) : ℂ := if 1 ≤ y then 1 else 0

lemma Pn_pos_pt {Nv : Fin 20 → ℝ} {n : Fin 20 → ℕ}
    (hn : n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))) : 0 < Pn_pt n := by
  unfold Pn_pt
  apply Finset.prod_pos
  intro j _
  have h := Fintype.mem_piFinset.mp hn j
  unfold dyad at h
  have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).1
  exact_mod_cast h1

lemma prod_cpow_pt {ι : Type*} (t : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (r : ℂ) :
    ∏ i ∈ t, (x i : ℂ) ^ r = (((∏ i ∈ t, x i : ℝ)) : ℂ) ^ r := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hx a) (Finset.prod_nonneg fun i _ => hx i)]

lemma jint_integrable_pt (c T y : ℝ) (hc : 0 < c) (hy : 0 < y) :
    IntervalIntegrable (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
      ((c : ℂ) + t * Complex.I)) MeasureTheory.volume (-T) T := by
  apply Continuous.intervalIntegrable
  have hcont : Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I) := by fun_prop
  apply Continuous.div (Continuous.const_cpow hcont (Or.inl (by exact_mod_cast hy.ne'))) hcont
  intro t h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- PROVED: page 264 display (3.4), the termwise expansion behind (3.3): multiplying out
`F(s,χ) = Π f_j(s,χ)` of display (3.6) as a finite sum over tuples and using
`u^s (n₁⋯n₂₀)^{-s} = (u/n₁⋯n₂₀)^s` for positive reals, the line integral is the sum over tuples
of the coefficient times the difference of two single term Perron integrals. -/
theorem vline_expand_pt : ∀ (N : ℕ) (A T u : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Nv : Fin 20 → ℝ), 0 < (N : ℝ) - A → (N : ℝ) - A ≤ u → 0 < T →
    Vline_pt Nv χ N A (1 + 1 / Real.log N) T u =
      ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
        coef_pt χ n * (Jint_pt (1 + 1 / Real.log N) T (u / Pn_pt n) -
          Jint_pt (1 + 1 / Real.log N) T (((N : ℝ) - A) / Pn_pt n)) := by
  intro N A T u q χ Nv hNA hu hT
  set c : ℝ := 1 + 1 / Real.log N with hcdef
  have hc : 0 < c := by
    have : 0 ≤ 1 / Real.log N := by
      apply div_nonneg zero_le_one; exact Real.log_natCast_nonneg N
    linarith
  have hu0 : 0 < u := lt_of_lt_of_le hNA hu
  have hF : ∀ s : ℂ, Fprod Nv χ s = ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      coef_pt χ n * ((Pn_pt n : ℝ) : ℂ) ^ (-s) := by
    intro s
    unfold Fprod fj
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.prod_mul_distrib, coef_pt, Pn_pt]
    congr 1
    rw [← prod_cpow_pt Finset.univ (fun j => (n j : ℝ)) (fun j => Nat.cast_nonneg _)]
    simp
  have hterm : ∀ (n : Fin 20 → ℕ), 0 < Pn_pt n → ∀ t : ℝ,
      coef_pt χ n * ((Pn_pt n : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
        (((u : ℂ) ^ ((c : ℂ) + t * Complex.I) -
          (((N : ℝ) - A : ℝ) : ℂ) ^ ((c : ℂ) + t * Complex.I)) / ((c : ℂ) + t * Complex.I))
      = coef_pt χ n * (((u / Pn_pt n : ℝ) : ℂ) ^ ((c : ℂ) + t * Complex.I) /
            ((c : ℂ) + t * Complex.I) -
          (((((N : ℝ) - A) / Pn_pt n : ℝ)) : ℂ) ^ ((c : ℂ) + t * Complex.I) /
            ((c : ℂ) + t * Complex.I)) := by
    intro n hP t
    rw [Complex.ofReal_div, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hu0.le hP.le,
      Complex.div_cpow_ofReal_nonneg hNA.le hP.le, Complex.cpow_neg]
    ring
  unfold Vline_pt Jint_pt
  simp_rw [hF, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hP := Pn_pos_pt hn
    rw [intervalIntegral.integral_congr (fun t _ => hterm n hP t), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (jint_integrable_pt c T _ hc (div_pos hu0 hP))
        (jint_integrable_pt c T _ hc (div_pos hNA hP))]
    ring
  · intro n hn
    have hP := Pn_pos_pt hn
    convert ((jint_integrable_pt c T _ hc (div_pos hu0 hP)).sub
      (jint_integrable_pt c T _ hc (div_pos hNA hP))).const_mul (coef_pt χ n) using 1
    funext t
    exact hterm n hP t

/-- The single term error bound of Davenport chapter 17: `1/2 + c/T` at `y = 1`, and
`2 y^c min(1, 1/(T|log y|))` otherwise; the factor 2 is a safety margin over Davenport's 1. -/
def Bterm_pt (c T y : ℝ) : ℝ :=
  if y = 1 then 1 / 2 + c / T else 2 * y ^ c * min 1 (1 / (T * |Real.log y|))

section PerronKernelHelpers

open Complex Filter Topology Set MeasureTheory

private theorem jint_bound_two (y : ℝ) (hy : 0 < y) (hy1 : y ≠ 1) (T : ℝ) (hT : 0 < T) :
    ‖Jint_pt 2 T y - (if 1 < y then 1 else 0)‖ ≤ y ^ 2 / (Real.pi * T * |Real.log y|) := by
  let F : ℂ → ℂ := fun s => (y : ℂ) ^ s / s
  let H : ℝ → ℝ → ℝ → ℂ := fun a b v => ∫ σ in a..b, F ((σ : ℂ) + v * I)
  let V : ℝ → ℂ := fun a => ∫ t in (-T)..T, F ((a : ℂ) + t * I)
  have hF : ∀ s : ℂ, s ≠ 0 → AnalyticAt ℂ F s := by
    intro s hs
    exact (LeanLab.PNTPort.ExplicitPsi1.analyticAt_xpow hy s).div analyticAt_id hs
  have hn : ∀ σ v : ℝ, |v| = T → ‖F ((σ : ℂ) + v * I)‖ ≤ y ^ σ / T := by
    intro σ v hv
    dsimp [F]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hd : T ≤ ‖(σ : ℂ) + v * I‖ := by
      have hh := Complex.abs_im_le_norm ((σ : ℂ) + v * I)
      simpa [hv] using hh
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) hT hd
  have hnear : (F - fun s : ℂ => 1 / (s - 0)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    have hd := (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl (ofReal_ne_zero.mpr hy.ne'))
    have hh := hd.tendsto_slope_zero
    simp only [id_eq, zero_add, cpow_zero, mul_one, one_mul, smul_eq_mul] at hh
    have he : (F - fun s : ℂ => 1 / (s - 0)) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun s => s⁻¹ * ((y : ℂ) ^ s - 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      dsimp [F]
      field_simp
      ring
    exact (hh.congr' he.symm).isBigO_one ℂ
  have hrectL : ∀ a : ℝ, a < 0 → RectangleIntegral' F ⟨a, -T⟩ ⟨2, T⟩ = 1 := by
    intro a ha
    apply ResidueTheoremOnRectangleWithSimplePole' (p := 0) (A := 1)
    · simp; linarith
    · simp; linarith
    · rw [rectangle_mem_nhds_iff]
      simp only [mem_reProdIm, zero_re, zero_im, uIoo_of_le (by linarith : a ≤ 2),
        uIoo_of_le (by linarith : -T ≤ T), Set.mem_Ioo]
      exact ⟨⟨ha, by norm_num⟩, by linarith, hT⟩
    · intro s hs
      exact (hF s hs.2).differentiableAt.differentiableWithinAt
    · exact hnear
  have hrectR : ∀ b : ℝ, 2 ≤ b → RectangleIntegral' F ⟨2, -T⟩ ⟨b, T⟩ = 0 := by
    intro b hb
    have hf : HolomorphicOn F (Rectangle (⟨2, -T⟩ : ℂ) ⟨b, T⟩) := by
      intro s hs
      apply (hF s ?_).differentiableAt.differentiableWithinAt
      intro hz
      simp only [Rectangle, mem_reProdIm, uIcc_of_le (by linarith : (2 : ℝ) ≤ b)] at hs
      have hh := hs.1.1
      rw [hz] at hh
      norm_num at hh
    simp only [RectangleIntegral', hf.vanishesOnRectangle (by rfl), smul_zero]
  have hhl : ∀ a : ℝ, a ≤ 2 → 1 < y → ∀ v : ℝ, |v| = T →
      ‖H a 2 v‖ ≤ y ^ 2 / (T * Real.log y) := by
    intro a ha hyy v hv
    have hdom : IntegrableOn (fun σ : ℝ => y ^ σ / T) (Iic 2) := by
      have hh := (integrableOn_exp_mul_Iic (Real.log_pos hyy) 2).div_const T
      simpa [IntegrableOn, Real.rpow_def_of_pos hy, mul_comm] using hh
    have hsub : Ioc a (2 : ℝ) ⊆ Iic 2 := fun _ h => h.2
    have hh := norm_integral_le_of_norm_le (hdom.mono_set hsub) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with σ hσ
      exact hn σ v hv)
    have hh' := setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun σ => by dsimp; positivity))
      (Filter.Eventually.of_forall hsub)
    have he : (∫ σ in Iic (2 : ℝ), y ^ σ / T) = y ^ 2 / (T * Real.log y) := by
      simp_rw [Real.rpow_def_of_pos hy]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const]
      have he : (fun σ : ℝ => Real.exp (Real.log y * σ)) = (fun σ : ℝ => Real.exp (σ * Real.log y)) := by funext σ; rw [mul_comm]
      rw [integral_exp_mul_Iic (Real.log_pos hyy)]
      rw [← Real.rpow_def_of_pos hy, Real.rpow_two]
      ring
    have hh0 : ‖H a 2 v‖ ≤ ∫ σ in Ioc a 2, y ^ σ / T := by simpa [H, intervalIntegral.integral_of_le ha] using hh
    exact hh0.trans (hh'.trans_eq he)
  have hhr : ∀ b : ℝ, 2 ≤ b → y < 1 → ∀ v : ℝ, |v| = T →
      ‖H 2 b v‖ ≤ y ^ 2 / (T * -Real.log y) := by
    intro b hb hyy v hv
    have hl : Real.log y < 0 := Real.log_neg hy hyy
    have hdom : IntegrableOn (fun σ : ℝ => y ^ σ / T) (Ioi 2) := by
      have hh := (integrableOn_exp_mul_Ioi hl 2).div_const T
      simpa [IntegrableOn, Real.rpow_def_of_pos hy, mul_comm] using hh
    have hsub : Ioc (2 : ℝ) b ⊆ Ioi 2 := fun _ h => h.1
    have hh := norm_integral_le_of_norm_le (hdom.mono_set hsub) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with σ hσ
      exact hn σ v hv)
    have hh' := setIntegral_mono_set hdom (Filter.Eventually.of_forall (fun σ => by dsimp; positivity))
      (Filter.Eventually.of_forall hsub)
    have he : (∫ σ in Ioi (2 : ℝ), y ^ σ / T) = y ^ 2 / (T * -Real.log y) := by
      simp_rw [Real.rpow_def_of_pos hy]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const]
      have he : (fun σ : ℝ => Real.exp (Real.log y * σ)) = (fun σ : ℝ => Real.exp (σ * Real.log y)) := by funext σ; rw [mul_comm]
      rw [integral_exp_mul_Ioi hl]
      rw [← Real.rpow_def_of_pos hy, Real.rpow_two]
      ring
    have hh0 : ‖H 2 b v‖ ≤ ∫ σ in Ioc 2 b, y ^ σ / T := by simpa [H, intervalIntegral.integral_of_le hb] using hh
    exact hh0.trans (hh'.trans_eq he)
  have hV : ∀ a : ℝ, 1 ≤ |a| → ‖V a‖ ≤ 2 * T * y ^ a := by
    intro a ha
    have hh : ∀ t ∈ Set.uIoc (-T) T, ‖F ((a : ℂ) + t * I)‖ ≤ y ^ a := by
      intro t _
      have hd : 1 ≤ ‖(a : ℂ) + t * I‖ := by
        have h := Complex.abs_re_le_norm ((a : ℂ) + t * I)
        have hre : ((a : ℂ) + t * I).re = a := by simp
        rw [hre] at h
        exact ha.trans h
      dsimp [F]
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact div_le_self (Real.rpow_nonneg hy.le _) hd
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hh
    have he : |T - -T| = 2 * T := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
    rw [he] at h
    exact h.trans_eq (by ring)
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have hcI : c * I = ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    dsimp [c]
    push_cast
    field_simp
  have hcn : ‖c‖ = 1 / (2 * Real.pi) := by
    simp [c, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_div]
  have hpK : Jint_pt 2 T y = c * I * V 2 := by
    have hX : (∫ t in (-T)..T, (y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) /
        (((2 : ℝ) : ℂ) + t * I)) = V 2 := by
      simp only [V]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [F]
    rw [hcI, Jint_pt, hX, one_div]
    push_cast
    try ring
  let D : ℝ := y ^ 2 / (T * |Real.log y|)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  rcases lt_or_gt_of_ne hy1 with hyy | hyy
  · simp only [not_lt.mpr hyy.le, ↓reduceIte, sub_zero]
    have hl : Real.log y < 0 := Real.log_neg hy hyy
    have hhs : ∀ b : ℝ, 2 ≤ b → ∀ v : ℝ, |v| = T → ‖H 2 b v‖ ≤ D := by
      intro b hb v hv
      simpa [D, abs_of_neg hl] using hhr b hb hyy v hv
    have hbound : ∀ n : ℕ, ‖Jint_pt 2 T y‖ ≤ (2 * T * y ^ ((n : ℝ) + 3) + 2 * D) / (2 * Real.pi) := by
      intro n
      let b : ℝ := n + 3
      have hb : 2 ≤ b := by dsimp [b]; have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hId := hrectR b hb
      have hId : c * (H 2 b (-T) - H 2 b T + I * V b - I * V 2) = 0 := by
        simpa only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
          smul_eq_mul, one_div, c, H, V] using hId
      have he : Jint_pt 2 T y = c * (H 2 b (-T) - H 2 b T + I * V b) := by
        rw [hpK]
        linear_combination -hId
      have hnorm : ‖H 2 b (-T) - H 2 b T + I * V b‖ ≤ ‖H 2 b (-T)‖ + ‖H 2 b T‖ + ‖V b‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (by simp))
      have hv := hV b (by rw [abs_of_nonneg (by linarith)]; linarith)
      have hh1 := hhs b hb (-T) (by rw [abs_neg, abs_of_pos hT])
      have hh2 := hhs b hb T (abs_of_pos hT)
      rw [he, norm_mul, hcn]
      calc
        _ ≤ (1 / (2 * Real.pi)) * (D + D + 2 * T * y ^ b) := by gcongr; linarith
        _ = _ := by dsimp [b]; ring
    have hp : Tendsto (fun n : ℕ => y ^ ((n : ℝ) + 3)) atTop (𝓝 0) := by
      have he : ∀ n : ℕ, y ^ ((n : ℝ) + 3) = y ^ n * y ^ (3 : ℕ) := by
        intro n
        rw [Real.rpow_add hy, Real.rpow_natCast]
        norm_cast
      simp_rw [he]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hy.le hyy).mul_const (y ^ 3)
    have hh := ((hp.const_mul (2 * T)).add_const (2 * D)).div_const (2 * Real.pi)
    have hfinal : (0 + 2 * D) / (2 * Real.pi) = y ^ 2 / (Real.pi * T * |Real.log y|) := by
      dsimp [D]
      field_simp
      ring
    simp only [mul_zero] at hh
    rw [hfinal] at hh
    exact ge_of_tendsto' hh hbound
  · simp only [hyy, ↓reduceIte]
    have hl : 0 < Real.log y := Real.log_pos hyy
    have hhs : ∀ a : ℝ, a ≤ 2 → ∀ v : ℝ, |v| = T → ‖H a 2 v‖ ≤ D := by
      intro a ha v hv
      simpa [D, abs_of_pos hl] using hhl a ha hyy v hv
    have hbound : ∀ n : ℕ, ‖Jint_pt 2 T y - 1‖ ≤ (2 * T * y ^ (-((n : ℝ) + 1)) + 2 * D) / (2 * Real.pi) := by
      intro n
      let a : ℝ := -((n : ℝ) + 1)
      have ha : a < 0 := by dsimp [a]; have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hId := hrectL a ha
      have hId : c * (H a 2 (-T) - H a 2 T + I * V 2 - I * V a) = 1 := by
        simpa only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
          smul_eq_mul, one_div, c, H, V] using hId
      have he : Jint_pt 2 T y - 1 = c * (I * V a - H a 2 (-T) + H a 2 T) := by
        rw [hpK]
        linear_combination hId
      have hnorm : ‖I * V a - H a 2 (-T) + H a 2 T‖ ≤ ‖V a‖ + ‖H a 2 (-T)‖ + ‖H a 2 T‖ := by
        exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (by simp)) le_rfl)
      have hv := hV a (by rw [abs_of_neg ha]; dsimp [a]; have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hh1 := hhs a (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT])
      have hh2 := hhs a (by linarith) T (abs_of_pos hT)
      rw [he, norm_mul, hcn]
      calc
        _ ≤ (1 / (2 * Real.pi)) * (2 * T * y ^ a + D + D) := by gcongr; linarith
        _ = _ := by dsimp [a]; ring
    have hp : Tendsto (fun n : ℕ => y ^ (-((n : ℝ) + 1))) atTop (𝓝 0) := by
      have he : ∀ n : ℕ, y ^ (-((n : ℝ) + 1)) = (y⁻¹) ^ n * y⁻¹ := by
        intro n
        rw [Real.rpow_neg hy.le, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_one,
          mul_inv, inv_pow]
      simp_rw [he]
      have hiy : y⁻¹ < 1 := (inv_lt_one₀ hy).mpr hyy
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hy.le) hiy).mul_const y⁻¹
    have hh := ((hp.const_mul (2 * T)).add_const (2 * D)).div_const (2 * Real.pi)
    have hfinal : (0 + 2 * D) / (2 * Real.pi) = y ^ 2 / (Real.pi * T * |Real.log y|) := by
      dsimp [D]
      field_simp
      ring
    simp only [mul_zero] at hh
    rw [hfinal] at hh
    exact ge_of_tendsto' hh hbound


/-! ### The classical Perron estimates, re-derived from the rectangle residue theorem -/

private theorem jint_rescale {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Jint_pt c T y = Jint_pt 2 (T / (c / 2)) (y ^ (c / 2)) := by
  let a : ℝ := c / 2
  let z : ℝ := y ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hy a
  have hpower (u : ℝ) :
      (y : ℂ) ^ ((c : ℂ) + ((a * u : ℝ) : ℂ) * I) =
        (z : ℂ) ^ ((2 : ℂ) + u * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne')]
    rw [← Complex.ofReal_log hy.le, ← Complex.ofReal_log hz.le]
    dsimp [z]
    rw [Real.log_rpow hy]
    push_cast
    congr 1
    dsimp [a]
    push_cast
    ring
  have hden (u : ℝ) : (c : ℂ) + ((a * u : ℝ) : ℂ) * I =
      (a : ℂ) * ((2 : ℂ) + u * I) := by
    dsimp [a]
    push_cast
    ring
  have hterm (u : ℝ) : (a : ℂ) *
      ((y : ℂ) ^ ((c : ℂ) + ((a * u : ℝ) : ℂ) * I) /
        ((c : ℂ) + ((a * u : ℝ) : ℂ) * I)) =
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I) := by
    rw [hpower, hden, ← mul_div_assoc]
    exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr ha.ne')
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  have hs := intervalIntegral.smul_integral_comp_mul_left (a := -T / a) (b := T / a) f a
  have hl : a * (-T / a) = -T := by field_simp
  have hr : a * (T / a) = T := by field_simp
  rw [hl, hr] at hs
  have heq : (∫ u : ℝ in (-T / a)..(T / a),
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I)) =
      ∫ t : ℝ in (-T)..T, f t := by
    calc
      _ = ∫ u : ℝ in (-T / a)..(T / a), (a : ℂ) * f (a * u) := by
        apply intervalIntegral.integral_congr
        intro u _
        exact (hterm u).symm
      _ = (a : ℂ) * ∫ u : ℝ in (-T / a)..(T / a), f (a * u) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [← Complex.real_smul]; exact hs
  unfold Jint_pt
  change (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, f t) =
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ in (-(T / a))..(T / a),
      (z : ℂ) ^ ((2 : ℂ) + u * I) / ((2 : ℂ) + u * I)
  rw [← neg_div, heq]

private theorem jint_remainder_bound {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c)
    (hT : 0 < T) :
    ‖Jint_pt c T y - (if 1 < y then 1 else 0)‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  have hscale : Jint_pt c T y = Jint_pt 2 (T / (c / 2)) (y ^ (c / 2)) := jint_rescale hy hc
  let a : ℝ := c / 2
  let z : ℝ := y ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hy a
  have hlog : Real.log z = a * Real.log y := Real.log_rpow hy a
  have hbranch : (1 < z) ↔ (1 < y) := by
    rw [Real.one_lt_rpow_iff_of_pos hy]
    simp [ha, ha.not_gt]
  have hz1 : z ≠ 1 := by
    intro h
    have hh := congrArg Real.log h
    rw [hlog, Real.log_one] at hh
    exact (mul_ne_zero ha.ne' (Real.log_ne_zero_of_pos_of_ne_one hy hy1)) hh
  have h := jint_bound_two z hz hz1 (T / a) (div_pos hT ha)
  rw [hscale]
  have hpow : z ^ 2 = y ^ c := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    congr 1
    dsimp [a]
    ring
  simp only [hbranch, hpow, hlog, abs_mul, abs_of_pos ha] at h
  have hden : Real.pi * (T / a) * (a * |Real.log y|) = Real.pi * T * |Real.log y| := by
    field_simp
  rw [hden] at h
  exact h


private theorem jint_at_one {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖Jint_pt c T 1 - 1 / 2‖ ≤ c / T := by
  have hn : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous (fun t : ℝ => (1 : ℂ) / ((c : ℂ) + t * I)) := by
    exact continuous_const.div (by fun_prop) hn
  have hint : IntervalIntegrable (fun t : ℝ => (1 : ℂ) / ((c : ℂ) + t * I))
      MeasureTheory.volume (-T) T := hcont.intervalIntegrable (-T) T
  have hre : (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I)).re =
      2 * Real.arctan (T / c) := by
    calc
      _ = ∫ t : ℝ in (-T)..T, ((1 : ℂ) / ((c : ℂ) + t * I)).re :=
        (Complex.reCLM.intervalIntegral_comp_comm hint).symm
      _ = ∫ t : ℝ in (-T)..T, c / (c ^ 2 + t ^ 2) := by
        congr 1
        funext t
        simp [Complex.div_re, Complex.normSq_apply, pow_two]
      _ = _ := by rw [integral_div_sq_add_sq, neg_div, Real.arctan_neg]; ring
  have him : (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I)).im = 0 := by
    calc
      _ = ∫ t : ℝ in (-T)..T, ((1 : ℂ) / ((c : ℂ) + t * I)).im :=
        (Complex.imCLM.intervalIntegral_comp_comm hint).symm
      _ = ∫ t : ℝ in (-T)..T, -(t / (c ^ 2 + t ^ 2)) := by
        congr 1
        funext t
        simp [Complex.div_im, Complex.normSq_apply, pow_two, neg_div]
      _ = _ := by
        rw [intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc.ne']
        simp
  have hval : Jint_pt c T 1 = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
    unfold Jint_pt
    simp only [Complex.ofReal_one, Complex.one_cpow]
    have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
    rw [hfac]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero, hre]
      ring
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, add_zero, him]
  have hdiff : Jint_pt c T 1 - 1 / 2 = ((Real.arctan (T / c) / Real.pi - 1 / 2 : ℝ) : ℂ) := by
    rw [hval]
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
  have hupper : Real.arctan (T / c) / Real.pi ≤ 1 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  rw [abs_of_nonpos (by linarith)]
  have hinv : Real.arctan (c / T) = Real.pi / 2 - Real.arctan (T / c) := by
    simpa only [inv_div] using Real.arctan_inv_of_pos (div_pos hT hc)
  have heq : -(Real.arctan (T / c) / Real.pi - 1 / 2) = Real.arctan (c / T) / Real.pi := by
    rw [hinv]
    field_simp
    ring
  rw [heq]
  exact (div_le_div_of_nonneg_right (Real.arctan_le_self (by positivity))
    Real.pi_pos.le).trans (div_le_self (by positivity) (by linarith [Real.pi_gt_three]))


private theorem jint_gt_one_large {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (hlarge : 1 ≤ T * Real.log y) :
    ‖Jint_pt c T y - 1‖ ≤ y ^ c * min 1 (1 / (T * Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hd : 0 < T * Real.log y := mul_pos hT hlog
  have h := jint_remainder_bound (c := c) (T := T) hy0 (ne_of_gt hy) hc hT
  simp only [hy, ite_true, abs_of_pos hlog] at h
  refine h.trans ?_
  rw [min_eq_right ((div_le_one hd).mpr hlarge)]
  calc
    y ^ c / (Real.pi * T * Real.log y) = (y ^ c / (T * Real.log y)) / Real.pi := by ring
    _ ≤ y ^ c / (T * Real.log y) := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    _ = _ := by ring

private theorem jint_lt_one_large {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c)
    (hT : 0 < T) (hlarge : 1 ≤ T * |Real.log y|) :
    ‖Jint_pt c T y‖ ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := by
  have hlog : 0 < |Real.log y| := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy0 (ne_of_lt hy))
  have hd : 0 < T * |Real.log y| := mul_pos hT hlog
  have h := jint_remainder_bound (c := c) (T := T) hy0 (ne_of_lt hy) hc hT
  simp only [not_lt_of_ge hy.le, ite_false, sub_zero] at h
  refine h.trans ?_
  rw [min_eq_right ((div_le_one hd).mpr hlarge)]
  calc
    y ^ c / (Real.pi * T * |Real.log y|) = (y ^ c / (T * |Real.log y|)) / Real.pi := by ring
    _ ≤ y ^ c / (T * |Real.log y|) := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    _ = _ := by ring

private theorem jint_norm_small {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hsmall : T * |Real.log y| ≤ 1) : ‖Jint_pt c T y‖ ≤ y ^ c := by
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  let A : ℝ → ℝ := fun t => (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) / (c ^ 2 + t ^ 2)
  let B : ℝ → ℝ := fun t => (c * Real.sin (t * Real.log y) - t * Real.cos (t * Real.log y)) / (c ^ 2 + t ^ 2)
  have hyp : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hpow (t : ℝ) : (y : ℂ) ^ ((c : ℂ) + t * I) =
      ((y ^ c : ℝ) : ℂ) * ((Real.cos (t * Real.log y) : ℂ) + (Real.sin (t * Real.log y) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.ofReal_log hy.le]
    have he : ((Real.log y : ℝ) : ℂ) * ((c : ℂ) + t * I) =
        ((Real.log y * c : ℝ) : ℂ) + ((t * Real.log y : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.rpow_def_of_pos hy]
  have hre (t : ℝ) : (f t).re = y ^ c * A t := by
    dsimp [f, A]
    rw [hpow]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have him (t : ℝ) : (f t).im = y ^ c * B t := by
    dsimp [f, B]
    rw [hpow]
    simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have hodd (t : ℝ) : (f (-t)).im = -(f t).im := by
    rw [him, him]
    dsimp [B]
    simp only [neg_mul, Real.sin_neg, Real.cos_neg, neg_sq]
    ring
  have hi0 : (∫ t : ℝ in (-T)..T, (f t).im) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t => (f t).im)
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at h
    linarith
  have hn (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous f := by
    dsimp [f]
    apply Continuous.div ?_ (by fun_prop) hn
    simp_rw [hpow]
    fun_prop
  have hint : IntervalIntegrable f MeasureTheory.volume (-T) T :=
    hcont.intervalIntegrable (-T) T
  have hJI : (∫ t in (-T)..T, f t).im = 0 := by
    calc
      _ = ∫ t : ℝ in (-T)..T, (f t).im := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
      _ = 0 := hi0
  have hpoint (t : ℝ) : |(f t).re| ≤ y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|) := by
    rw [hre, abs_mul, abs_of_pos hyp]
    apply mul_le_mul_of_nonneg_left _ hyp.le
    dsimp [A]
    rw [abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
    have hcos : |c * Real.cos (t * Real.log y)| ≤ c := by
      rw [abs_mul, abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hc.le).trans_eq (mul_one c)
    have hsin : |t * Real.sin (t * Real.log y)| ≤ t ^ 2 * |Real.log y| := by
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := t * Real.log y)) (abs_nonneg t)
      rw [abs_mul] at h
      nlinarith [sq_abs t]
    have htri := abs_add_le (c * Real.cos (t * Real.log y)) (t * Real.sin (t * Real.log y))
    have hcancel : c / (c ^ 2 + t ^ 2) * (c ^ 2 + t ^ 2) = c := div_mul_cancel₀ _ (hden t).ne'
    nlinarith [mul_nonneg (sq_nonneg c) (abs_nonneg (Real.log y))]
  have hquot : Continuous (fun t : ℝ => c / (c ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t => (hden t).ne')
  have hg : Continuous (fun t : ℝ => y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|)) :=
    continuous_const.mul (hquot.add continuous_const)
  have hbound : |∫ t in (-T)..T, (f t).re| ≤
      ∫ t in (-T)..T, y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|) := by
    calc
      _ ≤ ∫ t in (-T)..T, |(f t).re| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun t => (f t).re) (by linarith : -T ≤ T)
      _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
        ((Complex.continuous_re.comp hcont).abs.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
        (fun t _ => hpoint t)
  have heval : (∫ t in (-T)..T, y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|)) =
      y ^ c * (2 * Real.arctan (T / c) + 2 * T * |Real.log y|) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hquot.intervalIntegrable _ _) intervalIntegrable_const,
      integral_div_sq_add_sq]
    simp only [neg_div, Real.arctan_neg, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [heval] at hbound
  have hR : |∫ t in (-T)..T, (f t).re| ≤ y ^ c * (Real.pi + 2) := by
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hyp.le)
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  have hJ : (∫ t in (-T)..T, f t) = ((∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    apply Complex.ext
    · exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm
    · simpa only [Complex.ofReal_im] using hJI
  have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  unfold Jint_pt
  change ‖(1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, f t‖ ≤ _
  rw [hJ, hfac, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (show 0 < (1 / (2 * Real.pi) : ℝ) by positivity)]
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  exact hR.trans (mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) hyp.le)

private theorem jint_gt_one_small {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (hsmall : T * Real.log y ≤ 1) : ‖Jint_pt c T y - 1‖ ≤ y ^ c := by
  have hy0 : 0 < y := by linarith
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  let A : ℝ → ℝ := fun t => (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) / (c ^ 2 + t ^ 2)
  let B : ℝ → ℝ := fun t => (c * Real.sin (t * Real.log y) - t * Real.cos (t * Real.log y)) / (c ^ 2 + t ^ 2)
  have hyp : 0 < y ^ c := Real.rpow_pos_of_pos hy0 c
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hpow (t : ℝ) : (y : ℂ) ^ ((c : ℂ) + t * I) =
      ((y ^ c : ℝ) : ℂ) * ((Real.cos (t * Real.log y) : ℂ) + (Real.sin (t * Real.log y) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy0.ne'), ← Complex.ofReal_log hy0.le]
    have he : ((Real.log y : ℝ) : ℂ) * ((c : ℂ) + t * I) =
        ((Real.log y * c : ℝ) : ℂ) + ((t * Real.log y : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.rpow_def_of_pos hy0]
  have hre (t : ℝ) : (f t).re = y ^ c * A t := by
    dsimp [f, A]
    rw [hpow]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have him (t : ℝ) : (f t).im = y ^ c * B t := by
    dsimp [f, B]
    rw [hpow]
    simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have hodd (t : ℝ) : (f (-t)).im = -(f t).im := by
    rw [him, him]
    dsimp [B]
    simp only [neg_mul, Real.sin_neg, Real.cos_neg, neg_sq]
    ring
  have hi0 : (∫ t : ℝ in (-T)..T, (f t).im) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t => (f t).im)
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at h
    linarith
  have hn (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous f := by
    dsimp [f]
    apply Continuous.div ?_ (by fun_prop) hn
    simp_rw [hpow]
    fun_prop
  have hint : IntervalIntegrable f MeasureTheory.volume (-T) T :=
    hcont.intervalIntegrable (-T) T
  have hJI : (∫ t in (-T)..T, f t).im = 0 := by
    calc
      _ = ∫ t : ℝ in (-T)..T, (f t).im := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
      _ = 0 := hi0
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hnonneg : 0 ≤ ∫ t in (-T)..T, (f t).re := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have hat : |t| ≤ T := abs_le.mpr ht
    have hphase : |t * Real.log y| ≤ 1 := by
      rw [abs_mul, abs_of_pos hlog]
      exact (mul_le_mul_of_nonneg_right hat hlog.le).trans hsmall
    have hcos : 0 ≤ Real.cos (t * Real.log y) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp hphase).1, Real.pi_gt_three],
        by linarith [(abs_le.mp hphase).2, Real.pi_gt_three]⟩
    have hsin : 0 ≤ t * Real.sin (t * Real.log y) := by
      rcases le_or_gt 0 t with ht0 | ht0
      · exact mul_nonneg ht0 (Real.sin_nonneg_of_nonneg_of_le_pi
          (mul_nonneg ht0 hlog.le) (by linarith [(abs_le.mp hphase).2, Real.pi_gt_three]))
      · exact mul_nonneg_of_nonpos_of_nonpos ht0.le
          (Real.sin_nonpos_of_nonpos_of_neg_pi_le
            (mul_nonpos_of_nonpos_of_nonneg ht0.le hlog.le)
            (by linarith [(abs_le.mp hphase).1, Real.pi_gt_three]))
    rw [hre]
    apply mul_nonneg hyp.le
    dsimp [A]
    exact div_nonneg (add_nonneg (mul_nonneg hc.le hcos) hsin) (hden t).le
  have hJ : (∫ t in (-T)..T, f t) = ((∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    apply Complex.ext
    · exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm
    · simpa only [Complex.ofReal_im] using hJI
  have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  have hval : Jint_pt c T y = (((1 / (2 * Real.pi)) * ∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    unfold Jint_pt
    change (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, f t) = _
    rw [hJ, hfac, Complex.ofReal_mul]
  let R : ℝ := (1 / (2 * Real.pi)) * ∫ t in (-T)..T, (f t).re
  have hR0 : 0 ≤ R := mul_nonneg (by positivity) hnonneg
  have hnorm := jint_norm_small hy0 hc hT (by simpa only [abs_of_pos hlog] using hsmall)
  have hR : R ≤ y ^ c := by
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0] at hnorm
    exact hnorm
  have hy1 : 1 ≤ y ^ c := Real.one_le_rpow hy.le hc.le
  have hdiff : Jint_pt c T y - 1 = ((R - 1 : ℝ) : ℂ) := by
    rw [hval]
    dsimp [R]
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

private theorem jint_gt_one {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖Jint_pt c T y - 1‖ ≤ y ^ c * min 1 (1 / (T * Real.log y)) := by
  by_cases hlarge : 1 ≤ T * Real.log y
  · exact jint_gt_one_large hy hc hT hlarge
  · have hs : T * Real.log y ≤ 1 := (lt_of_not_ge hlarge).le
    have hd : 0 < T * Real.log y := mul_pos hT (Real.log_pos hy)
    rw [min_eq_left ((one_le_div hd).mpr hs), mul_one]
    exact jint_gt_one_small hy hc hT hs

private theorem jint_lt_one {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖Jint_pt c T y‖ ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := by
  by_cases hlarge : 1 ≤ T * |Real.log y|
  · exact jint_lt_one_large hy0 hy hc hT hlarge
  · have hs : T * |Real.log y| ≤ 1 := (lt_of_not_ge hlarge).le
    have hd : 0 < T * |Real.log y| := mul_pos hT
      (abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy0 (ne_of_lt hy)))
    rw [min_eq_left ((one_le_div hd).mpr hs), mul_one]
    exact jint_norm_small hy0 hc hT hs

/-- LEAF: the single term Perron estimate used for page 263 display (3.3): for `c > 0`, `T > 0`,
`y > 0`, `|(1/2πi)∫_{c-iT}^{c+iT} y^s s⁻¹ ds - δ(y)| < y^c min(1, 1/(T|log y|))` for `y ≠ 1`,
and `|(1/2πi)∫ s⁻¹ ds - 1/2| < c/T` at `y = 1`, Davenport, Multiplicative Number Theory,
chapter 17, the lemma; Titchmarsh, Theory of Functions, 3.12. Class MEDIUM. -/
theorem perron_single_leaf_pt : ∀ c T y : ℝ, 0 < c → 0 < T → 0 < y →
    ‖Hstep_pt y - Jint_pt c T y‖ ≤ Bterm_pt c T y := by
  intro c T y hc hT hy
  rw [norm_sub_rev]
  rcases lt_trichotomy y 1 with hy1 | hy1 | hy1
  · have hHs : Hstep_pt y = 0 := by
      unfold Hstep_pt
      rw [if_neg (not_le.mpr hy1)]
    have hB : Bterm_pt c T y = 2 * y ^ c * min 1 (1 / (T * |Real.log y|)) := by
      unfold Bterm_pt
      rw [if_neg (ne_of_lt hy1)]
    rw [hHs, hB, sub_zero]
    refine (jint_lt_one hy hy1 hc hT).trans ?_
    have hmin : 0 ≤ min 1 (1 / (T * |Real.log y|)) :=
      le_min zero_le_one (by positivity)
    have hyc : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
    have h0 : 0 ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := mul_nonneg hyc hmin
    nlinarith [h0]
  · subst hy1
    have hHs : Hstep_pt 1 = 1 := by
      unfold Hstep_pt
      rw [if_pos le_rfl]
    have hB : Bterm_pt c T 1 = 1 / 2 + c / T := by
      unfold Bterm_pt
      rw [if_pos rfl]
    rw [hHs, hB]
    have h1 := jint_at_one hc hT
    have he : Jint_pt c T 1 - 1 = (Jint_pt c T 1 - 1 / 2) + ((1 / 2 : ℂ) - 1) := by ring
    rw [he]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖((1 / 2 : ℂ) - 1)‖ = 1 / 2 := by
      rw [show (1 / 2 : ℂ) - 1 = -((1 / 2 : ℝ) : ℂ) by push_cast; ring, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [h2]
    linarith
  · have hHs : Hstep_pt y = 1 := by
      unfold Hstep_pt
      rw [if_pos hy1.le]
    have hlog : 0 < Real.log y := Real.log_pos hy1
    have hB : Bterm_pt c T y = 2 * y ^ c * min 1 (1 / (T * Real.log y)) := by
      unfold Bterm_pt
      rw [if_neg (ne_of_gt hy1), abs_of_pos hlog]
    rw [hHs, hB]
    refine (jint_gt_one hy1 hc hT).trans ?_
    have hmin : 0 ≤ min 1 (1 / (T * Real.log y)) :=
      le_min zero_le_one (by positivity)
    have hyc : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
    have h0 : 0 ≤ y ^ c * min 1 (1 / (T * Real.log y)) := mul_nonneg hyc hmin
    nlinarith [h0]


end PerronKernelHelpers

/-- LEAF: page 263 display (3.3), the summation of the single term errors over the tuples of
(3.4), with `|a₁(n₁)⋯a₂₀(n₂₀)| ≤ log (2N) ≪ N^{ε/2}`, the divisor bound
`d₂₀(m) ≪ N^{ε/2}` for the tuples with product at or near `u` or `N - A`, the harmonic sum
`Σ 1/|u - m| ≪ log N` for the rest, and `T ≤ N` so the lattice point terms `N^ε` are
`≤ N^{1+ε}/T`. Class MEDIUM. -/
theorem perron_sum_leaf_pt : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      ‖coef_pt χ n‖ * (Bterm_pt (1 + 1 / Real.log N) T (u / Pn_pt n) +
        Bterm_pt (1 + 1 / Real.log N) T (((N : ℝ) - A) / Pn_pt n))
      ≤ K * (N : ℝ) ^ (1 + ε) / T := by
  sorry

/-- PROVED from the two LEAF steps above: the error of Perron's formula (3.3), page 263. -/
theorem perron_error_pt : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      ‖coef_pt χ n‖ * (‖Hstep_pt (u / Pn_pt n) - Jint_pt (1 + 1 / Real.log N) T (u / Pn_pt n)‖ +
        ‖Hstep_pt (((N : ℝ) - A) / Pn_pt n) -
          Jint_pt (1 + 1 / Real.log N) T (((N : ℝ) - A) / Pn_pt n)‖)
      ≤ K * (N : ℝ) ^ (1 + ε) / T := by
  intro ε hε
  obtain ⟨K, N₀, hK, hS⟩ := perron_sum_leaf_pt ε hε
  refine ⟨K, max N₀ 2, hK, ?_⟩
  intro N A T u q χ Nv hN hA hA2 hC hT2 hTN hu1 hu2
  have hN0 : N₀ ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hNA : 0 < (N : ℝ) - A := by
    have : (N : ℝ) ^ (2 / 3 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hc : 0 < 1 + 1 / Real.log N := by
    have : 0 ≤ 1 / Real.log N := by
      apply div_nonneg zero_le_one; exact Real.log_natCast_nonneg N
    linarith
  refine le_trans ?_ (hS N A T u q χ Nv hN0 hA hA2 hC hT2 hTN hu1 hu2)
  apply Finset.sum_le_sum
  intro n hn
  have hP := Pn_pos_pt hn
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact add_le_add
    (perron_single_leaf_pt _ T _ hc (by linarith) (div_pos (lt_of_lt_of_le hNA hu1) hP))
    (perron_single_leaf_pt _ T _ hc (by linarith) (div_pos hNA hP))

/-- PROVED: the dyadic sum is the sum over tuples of the coefficient times the step difference. -/
lemma dsum_eq_step_pt {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ)
    (hu : (N : ℝ) - A ≤ u) :
    Dsum_pt Nv χ N A u = ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      coef_pt χ n * (Hstep_pt (u / Pn_pt n) - Hstep_pt (((N : ℝ) - A) / Pn_pt n)) := by
  unfold Dsum_pt
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hP := Pn_pos_pt hn
  have e1 : (1 ≤ u / Pn_pt n) ↔ Pn_pt n ≤ u := by rw [le_div_iff₀ hP, one_mul]
  have e2 : (1 ≤ ((N : ℝ) - A) / Pn_pt n) ↔ Pn_pt n ≤ (N : ℝ) - A := by
    rw [le_div_iff₀ hP, one_mul]
  unfold Hstep_pt coef_pt
  rw [show (∏ j, (n j : ℝ)) = Pn_pt n from rfl]
  simp only [e1, e2]
  by_cases h1 : (N : ℝ) - A < Pn_pt n
  · have h3 : ¬ Pn_pt n ≤ (N : ℝ) - A := not_le.mpr h1
    by_cases h2 : Pn_pt n ≤ u
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
  · have h1' : Pn_pt n ≤ (N : ℝ) - A := not_lt.mp h1
    have h2 : Pn_pt n ≤ u := le_trans h1' hu
    simp [h1, h2, h1']

/-- PROVED from the two LEAF steps: Perron's truncated formula (3.3), (3.4), page 263. -/
theorem perronTrunc_split_pt : PerronTrunc_pt := by
  intro ε hε
  obtain ⟨K, N₀, hK, hB⟩ := perron_error_pt ε hε
  refine ⟨K, max N₀ 2, hK, ?_⟩
  intro N A T u q χ Nv hN hA hA2 hC hT2 hTN hu1 hu2
  have hN0 : N₀ ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hNA : 0 < (N : ℝ) - A := by
    have : (N : ℝ) ^ (2 / 3 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  rw [dsum_eq_step_pt Nv χ N A u hu1,
    vline_expand_pt N A T u q χ Nv hNA hu1 (by linarith), ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) (le_trans ?_ (hB N A T u q χ Nv hN0 hA hA2 hC hT2 hTN hu1 hu2))
  apply Finset.sum_le_sum
  intro n _
  rw [← mul_sub, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  set c : ℝ := 1 + 1 / Real.log N
  calc ‖Hstep_pt (u / Pn_pt n) - Hstep_pt (((N : ℝ) - A) / Pn_pt n) -
        (Jint_pt c T (u / Pn_pt n) - Jint_pt c T (((N : ℝ) - A) / Pn_pt n))‖
      = ‖(Hstep_pt (u / Pn_pt n) - Jint_pt c T (u / Pn_pt n)) -
          (Hstep_pt (((N : ℝ) - A) / Pn_pt n) - Jint_pt c T (((N : ℝ) - A) / Pn_pt n))‖ := by
        congr 1; ring
    _ ≤ _ := norm_sub_le _ _

end

end LeanLab.Zhan1991
