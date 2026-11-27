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

/-! ### Helpers for the summation leaf -/

section PerronSumHelpers

private lemma dyad_one_le_pt {x : ℝ} {n : ℕ} (h : n ∈ dyad x) : 1 ≤ n := by
  unfold dyad at h
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).1

private lemma dyad_mem_pt {x : ℝ} {n : ℕ} (h : n ∈ dyad x) : x < n ∧ (n : ℝ) ≤ 2 * x := by
  unfold dyad at h
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
  obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp h1
  have hx0 : 0 ≤ x := by
    by_contra hx
    push_neg at hx
    have h20 : ⌊2 * x⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
    rw [h20] at h4
    omega
  refine ⟨by exact_mod_cast h2, ?_⟩
  have h5 : (n : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) := by exact_mod_cast h4
  have h6 : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
  linarith

private lemma prod_erase_ge_pt {Nv : Fin 20 → ℝ} (j : Fin 20)
    (h : ∀ i, (1 / 2 : ℝ) ≤ Nv i) :
    (1 / 2 : ℝ) ^ 19 ≤ ∏ i ∈ Finset.univ.erase j, Nv i := by
  calc (1 / 2 : ℝ) ^ 19 = ∏ i ∈ Finset.univ.erase j, (1 / 2 : ℝ) := by
        rw [Finset.prod_const]
        congr 1
        rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i ∈ Finset.univ.erase j, Nv i :=
        Finset.prod_le_prod₀ (fun i _ => by norm_num) (fun i _ => h i)

private lemma Nv_le_pt {N : ℕ} {Nv : Fin 20 → ℝ} (hC : Cond35 N Nv) (j : Fin 20) :
    Nv j ≤ 2 ^ 19 * (N : ℝ) := by
  have hprod_le : ∏ i, Nv i ≤ (N : ℝ) := hC.2.2.1
  have hsplit : (1 / 2 : ℝ) ^ 19 * Nv j ≤ ∏ i, Nv i := by
    rw [← Finset.prod_erase_mul Finset.univ Nv (Finset.mem_univ j)]
    exact mul_le_mul_of_nonneg_right (prod_erase_ge_pt j hC.1)
      (le_trans (by norm_num : (0:ℝ) ≤ 1/2) (hC.1 j))
  have h2 : (0:ℝ) < (2:ℝ) ^ 19 := by norm_num
  have h3 : (2:ℝ) ^ 19 * (1 / 2 : ℝ) ^ 19 = 1 := by norm_num
  nlinarith [hsplit, hprod_le, h2, h3]

private lemma Pn_le_pt {N : ℕ} {Nv : Fin 20 → ℝ} (hC : Cond35 N Nv) {n : Fin 20 → ℕ}
    (hn : n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))) :
    Pn_pt n ≤ 2 ^ 20 * (N : ℝ) := by
  have hfac : ∀ j : Fin 20, (n j : ℝ) ≤ 2 * Nv j :=
    fun j => (dyad_mem_pt (Fintype.mem_piFinset.mp hn j)).2
  unfold Pn_pt
  calc ∏ j, (n j : ℝ) ≤ ∏ j : Fin 20, (2 * Nv j) :=
        Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hfac j)
    _ = 2 ^ 20 * ∏ j, Nv j := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ 2 ^ 20 * (N : ℝ) := by
        have h := hC.2.2.1
        have h2 : (0:ℝ) < (2:ℝ) ^ 20 := by norm_num
        nlinarith [h, h2]

private lemma Pn_one_le_pt {Nv : Fin 20 → ℝ} {n : Fin 20 → ℕ}
    (hn : n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))) : 1 ≤ Pn_pt n := by
  unfold Pn_pt
  rw [show (1:ℝ) = ∏ _j : Fin 20, (1:ℝ) from by simp]
  exact Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => by
    have h := dyad_one_le_pt (Fintype.mem_piFinset.mp hn j)
    exact_mod_cast h)

/-- Each coefficient `a_j(n_j)χ(n_j)` has norm at most `21 log (2N)`. -/
private lemma coef_norm_le_pt {q : ℕ} (χ : DirichletCharacter ℂ q) {N : ℕ} {Nv : Fin 20 → ℝ}
    (hC : Cond35 N Nv) (hN : 2 ≤ N) {n : Fin 20 → ℕ}
    (hn : n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))) :
    ‖coef_pt χ n‖ ≤ (21 * Real.log (2 * N)) ^ 20 := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNR : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlog : 0 < Real.log (2 * (N:ℝ)) := Real.log_pos (by linarith)
  have hlog1 : 1 ≤ 21 * Real.log (2 * (N:ℝ)) := by
    have h4 : Real.log 4 ≤ Real.log (2 * (N:ℝ)) := by
      apply Real.log_le_log (by norm_num)
      nlinarith
    have h42 : (1:ℝ) < Real.log 4 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_gt_d9]
    nlinarith
  have hfac : ∀ j : Fin 20, ‖aj (j.val + 1) (n j) * χ (n j)‖ ≤ 21 * Real.log (2 * N) := by
    intro j
    have hmem : n j ∈ dyad (Nv j) := Fintype.mem_piFinset.mp hn j
    have h1 : 1 ≤ n j := dyad_one_le_pt hmem
    have h2 : (n j : ℝ) ≤ 2 * Nv j := (dyad_mem_pt hmem).2
    have h3 : Nv j ≤ 2 ^ 19 * (N:ℝ) := Nv_le_pt hC j
    have hn2 : (n j : ℝ) ≤ 2 ^ 20 * (N:ℝ) := by
      have : (2:ℝ) * (2^19 * (N:ℝ)) = 2^20 * (N:ℝ) := by ring
      nlinarith [h2, h3]
    have hlog2 : Real.log (n j) ≤ 20 * Real.log 2 + Real.log (N:ℝ) := by
      have := Real.log_le_log (by exact_mod_cast h1 : (0:ℝ) < n j) hn2
      rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    have hlt : 20 * Real.log 2 + Real.log (N:ℝ) ≤ 21 * Real.log (2 * (N:ℝ)) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2), Real.log_pos (by linarith : (1:ℝ) < (N:ℝ))]
    have hb : ‖aj (j.val + 1) (n j)‖ ≤ max (Real.log (n j)) 1 := by
      unfold aj
      by_cases h1' : j.val + 1 = 1
      · rw [if_pos h1', Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by exact_mod_cast h1))]
        exact le_max_left _ _
      · rw [if_neg h1']
        by_cases h2' : j.val + 1 ≤ 10
        · rw [if_pos h2']; simp only [norm_one]; exact le_max_right _ _
        · rw [if_neg h2']
          have hmob : ‖((μ (n j) : ℤ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]
            have h := ArithmeticFunction.abs_moebius_le_one (n := n j)
            exact_mod_cast h
          exact hmob.trans (le_max_right _ _)
    have hmax : max (Real.log (n j)) 1 ≤ 21 * Real.log (2 * (N:ℝ)) :=
      max_le (le_trans hlog2 hlt) hlog1
    rw [norm_mul]
    have hχ : ‖χ (n j)‖ ≤ 1 := DirichletCharacter.norm_le_one (χ := χ) _
    calc ‖aj (j.val + 1) (n j)‖ * ‖χ (n j)‖ ≤ (21 * Real.log (2 * N)) * 1 :=
          mul_le_mul (hb.trans hmax) hχ (norm_nonneg _) (by linarith)
      _ = 21 * Real.log (2 * N) := by ring
  unfold coef_pt
  rw [show (∏ j : Fin 20, (aj (j.val + 1) (n j) * χ (n j)))
      = ∏ j ∈ (Finset.univ : Finset (Fin 20)), (aj (j.val + 1) (n j) * χ (n j)) from rfl,
    norm_prod]
  calc ∏ j : Fin 20, ‖aj (j.val + 1) (n j) * χ (n j)‖
      ≤ ∏ _j : Fin 20, (21 * Real.log (2 * N)) :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hfac j)
    _ = (21 * Real.log (2 * N)) ^ 20 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PerronSumHelpers

section PerronSumHelpers2

/-- `|log y| ≥ |y-1|/(1+y)`. -/
private lemma abs_log_ge_pt {y : ℝ} (hy : 0 < y) : |y - 1| / (1 + y) ≤ |Real.log y| := by
  have h1 : 0 < 1 + y := by linarith
  rcases le_or_gt 1 y with h | h
  · have hlog : 0 ≤ Real.log y := Real.log_nonneg h
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y - 1), abs_of_nonneg hlog]
    have hb : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hy
    have hdiv : 1 - y⁻¹ = (y - 1) / y := by field_simp
    rw [hdiv] at hb
    have hmono : (y - 1) / (1 + y) ≤ (y - 1) / y :=
      div_le_div_of_nonneg_left (by linarith) hy (by linarith)
    linarith
  · have hlog : Real.log y ≤ 0 := Real.log_nonpos hy.le h.le
    have h1y : y - 1 = -(1 - y) := by ring
    rw [h1y, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - y), abs_of_nonpos hlog]
    have hb : 1 - (y⁻¹)⁻¹ ≤ Real.log y⁻¹ :=
      Real.one_sub_inv_le_log_of_pos (by positivity : (0:ℝ) < y⁻¹)
    rw [inv_inv, Real.log_inv] at hb
    have hle : (1 - y) / (1 + y) ≤ 1 - y := by
      rw [div_le_iff₀ h1]; nlinarith
    linarith

/-- `y^c ≤ 3(1+y)` for `y ≤ N` and `c = 1 + 1/log N`. -/
private lemma rpow_c_le_pt {N : ℕ} (hN : 2 ≤ N) {y : ℝ} (hy : 0 < y) (hyN : y ≤ N) :
    y ^ (1 + 1 / Real.log N) ≤ 3 * (1 + y) := by
  have hNR : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos (by linarith)
  rcases le_or_gt y 1 with hy1 | hy1
  · have hle1 : y ^ (1 + 1 / Real.log N) ≤ 1 :=
      Real.rpow_le_one hy.le hy1 (by positivity)
    linarith
  · have hsplit : y ^ (1 + 1 / Real.log N) = y * y ^ (1 / Real.log N) := by
      rw [Real.rpow_add hy, Real.rpow_one]
    rw [hsplit]
    have hb : y ^ (1 / Real.log N) ≤ 3 := by
      rw [Real.rpow_def_of_pos hy]
      have hlogle : Real.log y ≤ Real.log (N:ℝ) := Real.log_le_log hy hyN
      have hexp : Real.log y * (1 / Real.log N) ≤ 1 := by
        rw [mul_one_div, div_le_one hL]; exact hlogle
      calc Real.exp (Real.log y * (1 / Real.log N)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hexp
        _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith [hb, hy1.le]

/-- `min 1 (K/h) ≤ 2K/(K+h)` for `K > 0`, `h ≥ 0`. -/
private lemma min_one_div_le_pt {K h : ℝ} (hK : 0 < K) (hh : 0 ≤ h) :
    min 1 (K / h) ≤ 2 * K / (K + h) := by
  have hden : 0 < K + h := by linarith
  rcases eq_or_lt_of_le hh with h0 | hpos
  · rw [← h0, div_zero, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    positivity
  · rcases le_or_gt h K with hle | hlt
    · have hge : 1 ≤ K / h := by rw [le_div_iff₀ hpos]; linarith
      rw [min_eq_left hge, le_div_iff₀ hden]; linarith
    · have hlt1 : K / h < 1 := by rw [div_lt_one hpos]; exact hlt
      rw [min_eq_right hlt1.le, le_div_iff₀ hden, div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith

/-- `min 1 (1/(T|log y|)) ≤ 2(1+y)/(1+y+T|y-1|)`. -/
private lemma min_log_bound_pt {y T : ℝ} (hy : 0 < y) (hT : 0 < T) :
    min 1 (1 / (T * |Real.log y|)) ≤ 2 * (1 + y) / (1 + y + T * |y - 1|) := by
  have hge : |y - 1| / (1 + y) ≤ |Real.log y| := abs_log_ge_pt hy
  have hstep : 1 / (T * |Real.log y|) ≤ ((1 + y) / T) / |y - 1| := by
    rcases eq_or_lt_of_le (abs_nonneg (y - 1) : (0:ℝ) ≤ |y - 1|) with h0 | hpos
    · have hy1 : y = 1 := by
        have hz : |y - 1| = 0 := by rw [← h0]
        exact sub_eq_zero.mp (abs_eq_zero.mp hz)
      subst hy1
      rw [Real.log_one, abs_zero, mul_zero, one_div, inv_zero, sub_self, abs_zero, div_zero]
    · have h1 : 0 < T * (|y - 1| / (1 + y)) := by positivity
      have h2 : T * (|y - 1| / (1 + y)) ≤ T * |Real.log y| :=
        mul_le_mul_of_nonneg_left hge hT.le
      have h4 := one_div_le_one_div_of_le h1 h2
      have h5 : 1 / (T * (|y - 1| / (1 + y))) = ((1 + y) / T) / |y - 1| := by
        field_simp
      rwa [h5] at h4
  have hmin := min_one_div_le_pt (K := (1 + y) / T) (h := |y - 1|)
    (by positivity) (abs_nonneg _)
  refine le_trans (min_le_min_left _ hstep) ?_
  have hEq : 2 * ((1 + y) / T) / ((1 + y) / T + |y - 1|) = 2 * (1 + y) / (1 + y + T * |y - 1|) := by
    field_simp
  rw [hEq] at hmin
  exact hmin

end PerronSumHelpers2

section PerronSumHelpers3

/-- The single-term Perron error at `v/m` for a positive integer `m`, in closed form. -/
private lemma Bterm_v_bound_pt {N : ℕ} (hN : 2 ≤ N) {T v : ℝ} (hT : 2 ≤ T)
    (hv : 0 < v) (hvN : v ≤ N) {m : ℕ} (hm : 1 ≤ m) :
    Bterm_pt (1 + 1 / Real.log N) T (v / m) ≤
      12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) := by
  have hNR : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hT0 : 0 < T := by linarith
  have hy : 0 < v / m := by positivity
  have hyN : v / m ≤ N := by
    rw [div_le_iff₀ hm0]
    have h1 : (N:ℝ) * 1 ≤ (N:ℝ) * (m:ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hm) (by positivity)
    nlinarith
  have hc3 : 1 + 1 / Real.log N ≤ 3 := by
    have h2 : (1:ℝ) / Real.log N ≤ 2 := by
      rw [div_le_iff₀ hL]
      have hle : Real.log 2 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) hNR
      linarith [Real.log_two_gt_d9, hle]
    linarith
  have hc0 : (0:ℝ) < 1 + 1 / Real.log N := by
    have : (0:ℝ) ≤ 1 / Real.log N := by positivity
    linarith
  have habs : |v/m - 1| = |v - (m:ℝ)| / (m:ℝ) := by
    have h1 : v/(m:ℝ) - 1 = (v - m)/(m:ℝ) := by field_simp
    rw [h1, abs_div, abs_of_nonneg (le_of_lt hm0)]
  have hkey : 2 * (3 * (1 + v/m)) * (2 * (1 + v/m) / (1 + v/m + T * |v/m - 1|))
      = 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) := by
    rw [habs]
    field_simp
    ring
  rw [Bterm_pt]
  by_cases hy1 : v/m = 1
  · rw [if_pos hy1]
    have hvmeq : v = (m:ℝ) := by
      rw [div_eq_iff (ne_of_gt hm0)] at hy1
      linarith
    have hR : 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) = 24 := by
      rw [hvmeq, sub_self, abs_zero, mul_zero, add_zero]
      field_simp
      ring
    rw [hR]
    have h2 : (1 + 1 / Real.log N) / T ≤ 3/2 := by
      rw [div_le_iff₀ hT0]; linarith
    linarith
  · rw [if_neg hy1]
    have h1 : (v/m) ^ (1 + 1 / Real.log N) ≤ 3 * (1 + v/m) := rpow_c_le_pt hN hy hyN
    have h2 : min 1 (1 / (T * |Real.log (v/m)|)) ≤ 2 * (1 + v/m) / (1 + v/m + T * |v/m - 1|) :=
      min_log_bound_pt hy hT0
    have hB : (0:ℝ) ≤ min 1 (1 / (T * |Real.log (v/m)|)) :=
      le_min zero_le_one (by positivity)
    have hD : (0:ℝ) ≤ 2 * (1 + v/m) / (1 + v/m + T * |v/m - 1|) := by positivity
    have hA : (0:ℝ) ≤ 2 * (3 * (1 + v/m)) := by positivity
    calc 2 * (v/m) ^ (1 + 1 / Real.log N) * min 1 (1 / (T * |Real.log (v/m)|))
        ≤ (2 * (3 * (1 + v/m))) * (2 * (1 + v/m) / (1 + v/m + T * |v/m - 1|)) :=
          mul_le_mul (by nlinarith [h1]) h2 hB hA
      _ = 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) := hkey

end PerronSumHelpers3

section PerronSumHelpers4

/-- The harmonic bound `Σ_{k=1}^{M} 1/k ≤ 1 + log M`. -/
private lemma sum_inv_Icc_le_pt (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1:ℝ)/k ≤ 1 + Real.log M := by
  induction M with
  | zero => simp
  | succ n ih =>
    have hcast0 : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
    have htop : ∑ k ∈ Finset.Icc 1 (n+1), (1:ℝ)/k
        = ∑ k ∈ Finset.Icc 1 n, (1:ℝ)/k + 1/((n:ℝ)+1) := by
      rw [← hcast0]
      exact Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega) (fun k => (1:ℝ)/k)
    rw [htop]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast h
      have hlog : (1:ℝ)/((n:ℝ)+1) ≤ Real.log ((n:ℝ)+1) - Real.log (n:ℝ) := by
        have hb := Real.one_sub_inv_le_log_of_pos
          (show (0:ℝ) < ((n:ℝ)+1)/(n:ℝ) by positivity)
        rw [inv_div, Real.log_div (by positivity) (ne_of_gt hn)] at hb
        have he : 1 - (n:ℝ)/((n:ℝ)+1) = 1/((n:ℝ)+1) := by field_simp; ring
        rwa [he] at hb
      rw [hcast0]
      linarith

/-- `Σ_{m=1}^{V-1} 1/(V-m) ≤ 1 + log V`. -/
private lemma sum_sub_inv_pt {V : ℕ} (hV : 1 ≤ V) :
    ∑ m ∈ Finset.Icc 1 (V-1), (1:ℝ)/((V:ℝ) - m) ≤ 1 + Real.log V := by
  have hterm : ∀ m ∈ Finset.Icc 1 (V-1), (1:ℝ)/((V:ℝ) - m) = (1:ℝ)/(((V - m : ℕ)) : ℝ) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    rw [Nat.cast_sub (by omega : m ≤ V)]
  have hstep : ∑ m ∈ Finset.Icc 1 (V-1), (1:ℝ)/((V:ℝ) - m)
      ≤ ∑ k ∈ Finset.Icc 1 (V-1), (1:ℝ)/k := by
    rw [Finset.sum_congr rfl hterm]
    have hinj : Set.InjOn (fun m : ℕ => V - m) ↑(Finset.Icc 1 (V-1)) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
      simp only [] at hab
      have ha' : a ≤ V := by omega
      have hb' : b ≤ V := by omega
      have h1 : V - a + a = V - b + a := by rw [hab]
      have h2 : V - b + b = V := Nat.sub_add_cancel hb'
      have h3 : V - b + a = V := by rw [← h1]; exact Nat.sub_add_cancel ha'
      have h4 : V - b + a = V - b + b := by rw [h3, h2]
      exact Nat.add_left_cancel h4
    have himg : Finset.image (fun m : ℕ => V - m) (Finset.Icc 1 (V-1)) = Finset.Icc 1 (V-1) := by
      ext k
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; omega
      · intro hk
        exact ⟨V - k, ⟨by omega, by omega⟩, by omega⟩
    have hsi := Finset.sum_image (s := Finset.Icc 1 (V-1))
      (g := fun m : ℕ => V - m) (f := fun k : ℕ => (1:ℝ)/k) hinj
    rw [himg] at hsi
    rw [← hsi]
  refine hstep.trans ?_
  rcases eq_or_lt_of_le hV with h | h
  · subst h; simp
  · have h2 : 2 ≤ V := h
    have h0 : (0:ℝ) < ((V-1:ℕ):ℝ) := by
      have : 0 < V - 1 := by omega
      exact_mod_cast this
    have hcast : ((V-1:ℕ):ℝ) ≤ (V:ℝ) := by
      have : V - 1 ≤ V := by omega
      exact_mod_cast this
    have := sum_inv_Icc_le_pt (V-1)
    linarith [Real.log_le_log h0 hcast]

/-- `Σ_{m=V+2}^{M} 1/(m-V) ≤ 1 + log M`. -/
private lemma sum_sub_inv_high_pt (V M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc (V+1) M, (1:ℝ)/((m:ℝ) - V) ≤ 1 + Real.log M := by
  have hterm : ∀ m ∈ Finset.Icc (V+1) M, (1:ℝ)/((m:ℝ) - V) = (1:ℝ)/(((m - V : ℕ)) : ℝ) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    rw [Nat.cast_sub (by omega : V ≤ m)]
  have hstep : ∑ m ∈ Finset.Icc (V+1) M, (1:ℝ)/((m:ℝ) - V)
      ≤ ∑ k ∈ Finset.Icc 1 M, (1:ℝ)/k := by
    rw [Finset.sum_congr rfl hterm]
    have hinj : Set.InjOn (fun m : ℕ => m - V) ↑(Finset.Icc (V+1) M) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
      simp only [] at hab
      have ha' : V ≤ a := by omega
      have hb' : V ≤ b := by omega
      have h1 : a - V + V = b - V + V := by rw [hab]
      have h2 : a - V + V = a := Nat.sub_add_cancel ha'
      have h3 : b - V + V = b := Nat.sub_add_cancel hb'
      rw [h3] at h1
      rw [h2] at h1
      exact h1
    rw [← Finset.sum_image (s := Finset.Icc (V+1) M) (g := fun m : ℕ => m - V)
      (f := fun k : ℕ => (1:ℝ)/k) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_image, Finset.mem_Icc] at hk ⊢
      obtain ⟨m, ⟨h1, h2⟩, rfl⟩ := hk
      omega
    · intro k _ _; positivity
  exact hstep.trans (sum_inv_Icc_le_pt M)

/-- The partial-fraction sum `Σ_{m=1}^{V-1} 1/(m(V-m)) ≤ 2(1+log V)/V`. -/
private lemma sum_pf_pt {V : ℕ} (hV : 1 ≤ V) :
    ∑ m ∈ Finset.Icc 1 (V-1), (1:ℝ)/((m:ℝ) * ((V:ℝ) - m)) ≤ 2 * (1 + Real.log V) / V := by
  have hVpos : (0:ℝ) < V := by exact_mod_cast hV
  have hterm : ∀ m ∈ Finset.Icc 1 (V-1), (1:ℝ)/((m:ℝ) * ((V:ℝ) - m))
      = (1/(V:ℝ)) * ((1:ℝ)/m + (1:ℝ)/((V:ℝ) - m)) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have hm0 : (m:ℝ) ≠ 0 := by
      have : 0 < m := by omega
      exact_mod_cast ne_of_gt this
    have hVm : (V:ℝ) - m ≠ 0 := by
      have hlt : m < V := by omega
      have : (m:ℝ) < V := by exact_mod_cast hlt
      linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib]
  have h1 : ∑ x ∈ Finset.Icc 1 (V-1), (1:ℝ)/x ≤ 1 + Real.log V := by
    refine (sum_inv_Icc_le_pt (V-1)).trans ?_
    rcases eq_or_lt_of_le hV with h | h
    · subst h; simp
    · have h0 : (0:ℝ) < ((V-1:ℕ):ℝ) := by
        have : 0 < V - 1 := by omega
        exact_mod_cast this
      have hcast : ((V-1:ℕ):ℝ) ≤ (V:ℝ) := by
        have : V - 1 ≤ V := by omega
        exact_mod_cast this
      linarith [Real.log_le_log h0 hcast]
  have h2 : ∑ x ∈ Finset.Icc 1 (V-1), (1:ℝ)/((V:ℝ) - x) ≤ 1 + Real.log V :=
    sum_sub_inv_pt hV
  have hsum : (1/(V:ℝ)) * (∑ x ∈ Finset.Icc 1 (V-1), (1:ℝ)/x
      + ∑ x ∈ Finset.Icc 1 (V-1), (1:ℝ)/((V:ℝ) - x)) ≤ (1/(V:ℝ)) * (2 * (1 + Real.log V)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  refine hsum.trans (le_of_eq ?_)
  field_simp

end PerronSumHelpers4

section PerronSumHelpers5

open Filter Topology

/-- The divisor bound, re-derived so that no import beyond the file's own is needed. -/
private theorem exists_pow_le_two_pow_pt (k : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ℕ, ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) one_lt_two
  have ht' : Tendsto (fun a : ℕ => ((a + 1 : ℕ) : ℝ) ^ k / 2 ^ (a + 1)) atTop (𝓝 0) :=
    ht.comp (tendsto_add_atTop_nat 1)
  obtain ⟨S, hS⟩ := ht'.bddAbove_range
  refine ⟨max 1 (2 * S), le_max_left _ _, fun a => ?_⟩
  have h1 : ((a + 1 : ℕ) : ℝ) ^ k / 2 ^ (a + 1) ≤ S := hS ⟨a, rfl⟩
  have h2 : (0 : ℝ) < 2 ^ (a + 1) := by positivity
  rw [div_le_iff₀ h2] at h1
  push_cast at h1
  have h3 : (0 : ℝ) < 2 ^ a := by positivity
  calc ((a : ℝ) + 1) ^ k ≤ S * 2 ^ (a + 1) := h1
    _ = (2 * S) * 2 ^ a := by ring
    _ ≤ max 1 (2 * S) * 2 ^ a := by gcongr; exact le_max_right _ _

private theorem prime_pow_factor_le_pt (k : ℕ) (M : ℝ) (hM1 : 1 ≤ M)
    (hM : ∀ a : ℕ, ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a) (p a : ℕ) (hp : 2 ≤ p) :
    ((a : ℝ) + 1) ^ k ≤ (if p < 2 ^ k then M else 1) * (p : ℝ) ^ a := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  split_ifs with h
  · calc ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a := hM a
      _ ≤ M * (p : ℝ) ^ a := by gcongr
  · push Not at h
    have ha : (a : ℝ) + 1 ≤ 2 ^ a := by
      have := Nat.lt_two_pow_self (n := a)
      exact_mod_cast this
    have hpk : ((2 : ℝ) ^ k) ≤ p := by exact_mod_cast h
    calc ((a : ℝ) + 1) ^ k ≤ ((2 : ℝ) ^ a) ^ k := by gcongr
      _ = ((2 : ℝ) ^ k) ^ a := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (p : ℝ) ^ a := by gcongr
      _ = 1 * (p : ℝ) ^ a := by ring

private theorem card_divisors_pow_le_pt (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ^ k ≤ C * n := by
  obtain ⟨M, hM1, hM⟩ := exists_pow_le_two_pow_pt k
  refine ⟨M ^ (2 ^ k), one_le_pow₀ hM1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors hn0]
  push_cast
  rw [← prod_pow]
  have hg : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ k ≤
      (if p < 2 ^ k then M else 1) * (p : ℝ) ^ n.factorization p := by
    intro p hp
    exact prime_pow_factor_le_pt k M hM1 hM p _ (Nat.prime_of_mem_primeFactors hp).two_le
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ k
      ≤ ∏ p ∈ n.primeFactors, ((if p < 2 ^ k then M else 1) * (p : ℝ) ^ n.factorization p) :=
        prod_le_prod₀ (fun p _ => by positivity) hg
    _ = (∏ p ∈ n.primeFactors, (if p < 2 ^ k then M else 1)) *
          ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := prod_mul_distrib
    _ ≤ M ^ (2 ^ k) * n := by
        have hn' : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
          conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
          push_cast; rfl
        rw [← hn']
        gcongr
        rw [← prod_filter, prod_const]
        apply pow_le_pow_right₀ hM1
        calc (n.primeFactors.filter (· < 2 ^ k)).card ≤ (Finset.range (2 ^ k)).card := by
              apply Finset.card_le_card
              intro p hp
              simp only [Finset.mem_filter] at hp
              simpa using hp.2
          _ = 2 ^ k := Finset.card_range _

private theorem card_divisors_le_rpow_pt (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  obtain ⟨C, hC1, hC⟩ := card_divisors_pow_le_pt k
  refine ⟨C ^ ((k : ℝ)⁻¹), by positivity, fun n hn => ?_⟩
  have hk0 : k ≠ 0 := by omega
  have hd0 : (0 : ℝ) ≤ n.divisors.card := by positivity
  calc (n.divisors.card : ℝ) = ((n.divisors.card : ℝ) ^ k) ^ ((k : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hd0 hk0).symm
    _ ≤ (C * n) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) (hC n hn) (by positivity)
    _ = C ^ ((k : ℝ)⁻¹) * (n : ℝ) ^ ((k : ℝ)⁻¹) :=
        Real.mul_rpow (by linarith) (by positivity)

end PerronSumHelpers5

section PerronSumHelpers6

/-- A countable bound: a set of naturals inside a real interval `[a,b]` has at most `b-a+1`
elements. -/
private lemma card_le_of_mem_Icc_pt {s : Finset ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ m ∈ s, a ≤ (m:ℝ) ∧ (m:ℝ) ≤ b) : (s.card : ℝ) ≤ b - a + 1 := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have hsub : s ⊆ Finset.Icc (Nat.ceil a) (Nat.floor b) := by
    intro m hm
    obtain ⟨h1, h2⟩ := h m hm
    simp only [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
  have h1 : (s.card : ℝ) ≤ ((Finset.Icc (Nat.ceil a) (Nat.floor b)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : ((Nat.floor b : ℕ) : ℝ) ≤ b := Nat.floor_le hb0
  have h3 : a ≤ ((Nat.ceil a : ℕ) : ℝ) := Nat.le_ceil a
  rcases le_or_gt (Nat.ceil a) (Nat.floor b + 1) with hcase | hcase
  · rw [Nat.cast_sub hcase] at h1
    push_cast at h1
    linarith
  · have hz : Nat.floor b + 1 - Nat.ceil a = 0 := by omega
    rw [hz] at h1
    push_cast at h1
    linarith

end PerronSumHelpers6

section PerronSumHelpers7

/-- The near part of the tuple sum: the integers `m` with `T|v-m| ≤ m+v` or `|v-m| ≤ 1`. -/
private lemma near_card_pt {v T : ℝ} (hv : 0 < v) (hT : 2 ≤ T) (M : ℕ) :
    ((Finset.Icc 1 M).filter
      (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1)).card ≤ 8*v/T + 5 := by
  classical
  have hTpos : 0 < T := by linarith
  have hT1 : (0:ℝ) < T - 1 := by linarith
  have hT2 : (0:ℝ) < T + 1 := by linarith
  have hsub1 : ((Finset.Icc 1 M).filter
      (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v)).card ≤ 8*v/T + 2 := by
    have hmem : ∀ m ∈ (Finset.Icc 1 M).filter
        (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v),
        v*(T-1)/(T+1) ≤ (m:ℝ) ∧ (m:ℝ) ≤ v*(T+1)/(T-1) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hm2⟩, hcond⟩ := hm
      have hmr : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      constructor
      · rcases le_or_gt (m:ℝ) v with h | h
        · have h2 : T*(v - (m:ℝ)) ≤ (m:ℝ) + v := by
            rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - m)] at hcond
          exact (div_le_iff₀ hT2).mpr (by nlinarith)
        · have h2 : v*(T-1)/(T+1) ≤ v := (div_le_iff₀ hT2).mpr (by nlinarith)
          linarith
      · rcases le_or_gt (m:ℝ) v with h | h
        · have h3 : v*(T-1) ≤ v*(T+1) :=
            mul_le_mul_of_nonneg_left (by linarith : T-1 ≤ T+1) (le_of_lt hv)
          have h2 : v ≤ v*(T+1)/(T-1) := (le_div_iff₀ hT1).mpr h3
          linarith
        · have h1 : T*((m:ℝ) - v) ≤ (m:ℝ) + v := by
            rwa [abs_of_neg (by linarith : v - m < 0), neg_sub] at hcond
          exact (le_div_iff₀ hT1).mpr (by nlinarith)
    have hT2m1 : (0:ℝ) < T^2 - 1 := by nlinarith
    have e : v*(T+1)/(T-1) - v*(T-1)/(T+1) = v * (4*T/(T^2-1)) := by
      have h1 : (T:ℝ) - 1 ≠ 0 := ne_of_gt hT1
      have h2 : (T:ℝ) + 1 ≠ 0 := ne_of_gt hT2
      have h3 : (T:ℝ)^2 - 1 ≠ 0 := ne_of_gt hT2m1
      field_simp
      ring
    have hnn : 0 ≤ v*(T+1)/(T-1) - v*(T-1)/(T+1) := by
      rw [e]
      have : (0:ℝ) < 4*T/(T^2-1) := by positivity
      nlinarith
    have h1 : (((Finset.Icc 1 M).filter
        (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v)).card : ℝ)
        ≤ v*(T+1)/(T-1) - v*(T-1)/(T+1) + 1 := by
      apply card_le_of_mem_Icc_pt (a := v*(T-1)/(T+1)) (b := v*(T+1)/(T-1))
      · positivity
      · linarith
      · exact hmem
    have h2 : v*(T+1)/(T-1) - v*(T-1)/(T+1) + 1 ≤ 8*v/T + 2 := by
      rw [e]
      have h4 : 4*T/(T^2-1) ≤ 8/T := by
        rw [div_le_iff₀ (by nlinarith : (0:ℝ) < T^2 - 1)]
        rw [div_mul_eq_mul_div, le_div_iff₀ hTpos]
        nlinarith
      have h5 : v * (4*T/(T^2-1)) ≤ v * (8/T) := mul_le_mul_of_nonneg_left h4 (le_of_lt hv)
      have h6 : v * (8/T) = 8*v/T := by ring
      rw [h6] at h5
      linarith
    linarith
  have hsub2 : (((Finset.Icc 1 M).filter
      (fun m : ℕ => |v - (m:ℝ)| ≤ 1)).card : ℝ) ≤ 3 := by
    have hmem : ∀ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => |v - (m:ℝ)| ≤ 1),
        v - 1 ≤ (m:ℝ) ∧ (m:ℝ) ≤ v + 1 := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      have hle := abs_le.mp hm.2
      constructor <;> linarith [hle.1, hle.2]
    have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a + 1 ≤ 3 →
        (∀ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => |v - (m:ℝ)| ≤ 1),
          a ≤ (m:ℝ) ∧ (m:ℝ) ≤ b) →
        (((Finset.Icc 1 M).filter (fun m : ℕ => |v - (m:ℝ)| ≤ 1)).card : ℝ) ≤ 3 := by
      intro a b ha hab hba hmem'
      exact le_trans (card_le_of_mem_Icc_pt (s := (Finset.Icc 1 M).filter
        (fun m : ℕ => |v - (m:ℝ)| ≤ 1)) ha hab hmem') hba
    have h1r : (((Finset.Icc 1 M).filter (fun m : ℕ => |v - (m:ℝ)| ≤ 1)).card : ℝ) ≤ 3 := by
      rcases le_or_gt v 1 with hv1 | hv1
      · refine key 0 (v+1) le_rfl (by linarith) (by linarith) ?_
        intro m hm
        have := hmem m hm
        constructor
        · have : (1:ℝ) ≤ (m:ℝ) := by
            have := (Finset.mem_filter.mp hm).1
            simp only [Finset.mem_Icc] at this
            exact_mod_cast this.1
          linarith
        · exact this.2
      · refine key (v-1) (v+1) (by linarith) (by linarith) (by linarith) ?_
        intro m hm
        exact hmem m hm
    exact h1r
  have hunion : ((Finset.Icc 1 M).filter
      (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1))
      ⊆ (Finset.Icc 1 M).filter (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v) ∪
        (Finset.Icc 1 M).filter (fun m : ℕ => |v - (m:ℝ)| ≤ 1) := by
    intro m hm
    simp only [Finset.mem_filter] at hm
    rcases hm.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm.1, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm.1, h⟩)
  calc (((Finset.Icc 1 M).filter
        (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1)).card : ℝ)
      ≤ (((Finset.Icc 1 M).filter (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v) ∪
          (Finset.Icc 1 M).filter (fun m : ℕ => |v - (m:ℝ)| ≤ 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hunion
    _ ≤ (((Finset.Icc 1 M).filter (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v)).card : ℝ) +
          (((Finset.Icc 1 M).filter (fun m : ℕ => |v - (m:ℝ)| ≤ 1)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ 8*v/T + 2 + 3 := by linarith
    _ = 8*v/T + 5 := by ring

end PerronSumHelpers7

section PerronSumHelpers8

/-- Pointwise bound on the far-below part (`m ≤ v-1`). -/
private lemma Sfun_low_pt {v T : ℝ} (hv : 0 < v) (hT : 0 < T) {m V : ℕ} (hm : 1 ≤ m)
    (hmv : (m:ℝ) ≤ v - 1) (hmV : m ≤ V - 1) (hVle : (V:ℝ) ≤ v) :
    12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
      ≤ 48 * v^2 / (T * ((m:ℝ) * ((V:ℝ) - (m:ℝ)))) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hvm : (0:ℝ) < v - (m:ℝ) := by linarith
  have habs : |v - (m:ℝ)| = v - (m:ℝ) := abs_of_pos hvm
  have hmVr : (m:ℝ) ≤ (V:ℝ) - 1 := by
    have h1 : ((V-1 : ℕ) : ℝ) = (V:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ V)]; push_cast; ring
    have h2 : (m:ℝ) ≤ ((V-1 : ℕ) : ℝ) := by exact_mod_cast hmV
    linarith
  have hV0 : (0:ℝ) < (V:ℝ) - (m:ℝ) := by linarith
  have hD1 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + v + T * (v - (m:ℝ))) := by positivity
  have hb : (0:ℝ) < (m:ℝ) * (T * (v - (m:ℝ))) := by positivity
  have hb' : (0:ℝ) < (m:ℝ) * (T * ((V:ℝ) - (m:ℝ))) := by positivity
  have hD2 : (m:ℝ) * (T * (v - (m:ℝ))) ≤ (m:ℝ) * ((m:ℝ) + v + T * (v - (m:ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hm0)
    linarith
  have hD3 : (m:ℝ) * (T * ((V:ℝ) - (m:ℝ))) ≤ (m:ℝ) * (T * (v - (m:ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hm0)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hT)
    linarith
  have hnum : 12 * ((m:ℝ) + v) ^ 2 ≤ 12 * (2*v)^2 := by
    have h1 : (m:ℝ) + v ≤ 2*v := by linarith
    have h2 : (0:ℝ) ≤ (m:ℝ) + v := by linarith
    have h3 := pow_le_pow_left₀ h2 h1 2
    linarith
  rw [habs]
  refine le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hD1)) ?_
  refine le_trans (div_le_div_of_nonneg_left (by positivity) hb hD2) ?_
  refine le_trans (div_le_div_of_nonneg_left (by positivity) hb' hD3) ?_
  have hfin : 12 * (2*v)^2 = 48 * v^2 := by ring
  have hden : (m:ℝ) * (T * ((V:ℝ) - (m:ℝ))) = T * ((m:ℝ) * ((V:ℝ) - (m:ℝ))) := by ring
  rw [hfin, hden]

/-- Pointwise bound on the far-above part (`v+1 ≤ m`). -/
private lemma Sfun_high_pt {v T : ℝ} (hv : 0 < v) (hT : 0 < T) {m V : ℕ} (hm : 1 ≤ m)
    (hmv : v + 1 ≤ (m:ℝ)) (hmV : V + 1 ≤ m) (hVle : v ≤ (V:ℝ)) :
    12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
      ≤ 48 / T * (1 + v / ((m:ℝ) - (V:ℝ))) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hvm : (0:ℝ) < (m:ℝ) - v := by linarith
  have habs : |v - (m:ℝ)| = (m:ℝ) - v := by
    rw [abs_of_neg (by linarith : v - (m:ℝ) < 0)]; ring
  have hV0 : (0:ℝ) < (m:ℝ) - (V:ℝ) := by
    have : (V:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hmV
    linarith
  have hD1 : (0:ℝ) < (m:ℝ) * ((m:ℝ) + v + T * ((m:ℝ) - v)) := by positivity
  have hb : (0:ℝ) < (m:ℝ) * (T * ((m:ℝ) - v)) := by positivity
  have hD2 : (m:ℝ) * (T * ((m:ℝ) - v)) ≤ (m:ℝ) * ((m:ℝ) + v + T * ((m:ℝ) - v)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hm0)
    linarith
  have hnum : 12 * ((m:ℝ) + v) ^ 2 ≤ 12 * (2*(m:ℝ))^2 := by
    have h1 : (m:ℝ) + v ≤ 2*(m:ℝ) := by linarith
    have h2 : (0:ℝ) ≤ (m:ℝ) + v := by linarith
    have h3 := pow_le_pow_left₀ h2 h1 2
    linarith
  rw [habs]
  refine le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hD1)) ?_
  refine le_trans (div_le_div_of_nonneg_left (by positivity) hb hD2) ?_
  have hkey : 12 * (2*(m:ℝ))^2 / ((m:ℝ) * (T * ((m:ℝ) - v)))
      = 48 / T * ((m:ℝ) / ((m:ℝ) - v)) := by
    field_simp
    ring
  rw [hkey]
  have hsplit : (m:ℝ) / ((m:ℝ) - v) = 1 + v / ((m:ℝ) - v) := by
    field_simp
    ring
  rw [hsplit]
  have hle : v / ((m:ℝ) - v) ≤ v / ((m:ℝ) - (V:ℝ)) := by
    apply div_le_div_of_nonneg_left (le_of_lt hv) hV0
    linarith
  have h1 : (0:ℝ) ≤ 48 / T := by positivity
  have h2 := mul_le_mul_of_nonneg_left (by linarith : 1 + v/((m:ℝ)-v) ≤ 1 + v/((m:ℝ)-(V:ℝ))) h1
  linarith

end PerronSumHelpers8

section PerronSumHelpers9

/-- Pointwise bound on the near part. -/
private lemma Sfun_near_pt {v T : ℝ} (hv : 0 < v) (hT : 2 ≤ T) {m : ℕ} (hm : 1 ≤ m)
    (h : T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1) :
    12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) ≤ 48 := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have habs : (0:ℝ) ≤ |v - (m:ℝ)| := abs_nonneg _
  have hbase : 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
      ≤ 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v)) := by
    apply div_le_div_of_nonneg_left (by positivity)
    · exact mul_pos hm0 (by linarith)
    · apply mul_le_mul_of_nonneg_left _ (le_of_lt hm0)
      have hT0 : (0:ℝ) < T := by linarith
      have := mul_nonneg (le_of_lt hT0) habs
      linarith
  have halg : 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v)) = 12 * (1 + v/(m:ℝ)) := by
    field_simp <;> ring
  have hratio : v/(m:ℝ) ≤ 3 := by
    rcases h with h | h
    · rcases le_or_gt v (m:ℝ) with hmv | hmv
      · rw [div_le_iff₀ hm0]; linarith
      · have h2 : T * (v - (m:ℝ)) ≤ (m:ℝ) + v := by
          rwa [abs_of_pos (by linarith : (0:ℝ) < v - m)] at h
        have h3 : v*(T-1) ≤ (m:ℝ)*(T+1) := by nlinarith
        have h4 : (0:ℝ) < T - 1 := by linarith
        have h6 : (m:ℝ) * (T+1) ≤ 3 * (m:ℝ) * (T-1) := by nlinarith
        have h7 : v * (T-1) ≤ 3 * (m:ℝ) * (T-1) := le_trans h3 h6
        have h8 : v ≤ 3 * (m:ℝ) := le_of_mul_le_mul_right h7 h4
        rw [div_le_iff₀ hm0]; linarith
    · have h2 : v ≤ (m:ℝ) + 1 := by linarith [abs_le.mp h]
      rw [div_le_iff₀ hm0]
      linarith
  rw [halg] at hbase
  nlinarith

/-- The sum over the integers `m ≤ M` of the single-term expression. -/
private lemma sum_S_bound_pt {v T : ℝ} (hv : 1 ≤ v) (hT : 2 ≤ T) (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
      ≤ 48 * (8*v/T + 5) + 384 * v * (1 + Real.log v) / T
        + 96 * (M:ℝ)/T + 96 * v * (1 + Real.log M)/T := by
  classical
  have hv0 : 0 < v := by linarith
  have hT0 : 0 < T := by linarith
  set V := ⌊v⌋₊ with hVdef
  set Vc := ⌈v⌉₊ with hVcdef
  have hV1 : 1 ≤ V := by rw [hVdef]; exact Nat.le_floor (show ((1:ℕ):ℝ) ≤ v by exact_mod_cast hv)
  have hVle : (V:ℝ) ≤ v := by rw [hVdef]; exact Nat.floor_le (by linarith)
  have hVcle : v ≤ (Vc:ℝ) := by rw [hVcdef]; exact Nat.le_ceil v
  have hVclt : (Vc:ℝ) < v + 1 := by rw [hVcdef]; exact Nat.ceil_lt_add_one (by linarith)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M)
    (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1)
    (f := fun m => 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)))
  rw [← hsplit]
  -- near part
  have hnear : ∑ m ∈ (Finset.Icc 1 M).filter
      (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1),
      12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) ≤ 48 * (8*v/T + 5) := by
    have hpt : ∀ m ∈ (Finset.Icc 1 M).filter
        (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1),
        12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) ≤ 48 := by
      intro m hm'
      have hm1' : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm').1).1
      exact Sfun_near_pt hv0 hT hm1' (Finset.mem_filter.mp hm').2
    calc ∑ m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1),
          12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
        ≤ ∑ _m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1), (48:ℝ) :=
          Finset.sum_le_sum hpt
      _ = 48 * (((Finset.Icc 1 M).filter
          (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 48 * (8*v/T + 5) := by
          have hc : (((Finset.Icc 1 M).filter
              (fun m : ℕ => T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1)).card : ℝ)
              ≤ 8*v/T + 5 := by
            exact_mod_cast near_card_pt hv0 hT M
          nlinarith
  -- far part
  have hfar : ∑ m ∈ (Finset.Icc 1 M).filter
      (fun m : ℕ => ¬ (T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1)),
      12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
      ≤ 384 * v * (1 + Real.log v) / T + (96 * (M:ℝ)/T + 96 * v * (1 + Real.log M)/T) := by
    set sF := (Finset.Icc 1 M).filter
      (fun m : ℕ => ¬ (T * |v - (m:ℝ)| ≤ (m:ℝ) + v ∨ |v - (m:ℝ)| ≤ 1)) with hsF
    have hsub : sF ⊆ (Finset.Icc 1 M).filter
        (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|) ∪
        (Finset.Icc 1 M).filter (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|) := by
      intro m hm'
      have hmI : m ∈ Finset.Icc 1 M := (Finset.mem_filter.mp hm').1
      have hnot := (Finset.mem_filter.mp hm').2
      have h2 : (1:ℝ) < |v - (m:ℝ)| := not_le.mp (fun hc => hnot (Or.inr hc))
      have hlt := lt_abs.mp h2
      rcases hlt with hgl | hgr
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmI, ⟨by linarith, h2⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmI, ⟨by linarith, h2⟩⟩)
    have hdisj : Disjoint ((Finset.Icc 1 M).filter
          (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|))
        ((Finset.Icc 1 M).filter (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|)) := by
      apply Finset.disjoint_filter.mpr
      intro m _ h1 h2
      linarith [h1.1, h2.1]
    have hstep : ∑ m ∈ sF, 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
        ≤ ∑ m ∈ ((Finset.Icc 1 M).filter
            (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|)) ∪
          ((Finset.Icc 1 M).filter (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|)),
          12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i _ _
      positivity
    rw [Finset.sum_union hdisj] at hstep
    refine hstep.trans ?_
    have hlowb : ∑ m ∈ (Finset.Icc 1 M).filter
        (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|),
        12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
        ≤ 384 * v * (1 + Real.log v) / T := by
      have hMV : ∀ m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|), m ≤ V - 1 := by
        intro m hm'
        obtain ⟨hmI, hmv, -⟩ := Finset.mem_filter.mp hm'
        have h1 : m + 1 ≤ V := Nat.le_floor (a := v) (n := m+1) (by push_cast; linarith)
        omega
      have hpt : ∀ m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|),
          12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
          ≤ 48 * v^2 / (T * ((m:ℝ) * ((V:ℝ) - (m:ℝ)))) := by
        intro m hm'
        obtain ⟨hmI, hmv, -⟩ := Finset.mem_filter.mp hm'
        have hm1' : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
        exact Sfun_low_pt hv0 hT0 hm1' hmv (hMV m hm') hVle
      have hsub2 : (Finset.Icc 1 M).filter (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|)
          ⊆ Finset.Icc 1 (V-1) := by
        intro m hm'
        obtain ⟨hmI, hmv, -⟩ := Finset.mem_filter.mp hm'
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hmI).1, hMV m hm'⟩
      have hsum2 : ∑ m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|),
          (1:ℝ) / ((m:ℝ) * ((V:ℝ) - (m:ℝ))) ≤ 2 * (1 + Real.log V) / V := by
        refine le_trans ?_ (sum_pf_pt hV1)
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub2
        intro i hi _
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hiV : i ≤ V - 1 := (Finset.mem_Icc.mp hi).2
        have h1 : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi1
        have h2 : (0:ℝ) < (V:ℝ) - (i:ℝ) := by
          have h3 : ((V-1:ℕ):ℝ) = (V:ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ V)]; push_cast; ring
          have h4 : (i:ℝ) ≤ ((V-1:ℕ):ℝ) := by exact_mod_cast hiV
          rw [h3] at h4; linarith
        exact le_of_lt (div_pos one_pos (mul_pos h1 h2))
      calc ∑ m ∈ (Finset.Icc 1 M).filter
            (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|),
            12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
          ≤ ∑ m ∈ (Finset.Icc 1 M).filter
              (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|),
              48 * v^2 / (T * ((m:ℝ) * ((V:ℝ) - (m:ℝ)))) := Finset.sum_le_sum hpt
        _ = (48 * v^2 / T) * ∑ m ∈ (Finset.Icc 1 M).filter
              (fun m : ℕ => (m:ℝ) ≤ v - 1 ∧ 1 < |v - (m:ℝ)|),
              (1:ℝ) / ((m:ℝ) * ((V:ℝ) - (m:ℝ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            field_simp <;> ring
        _ ≤ (48 * v^2 / T) * (2 * (1 + Real.log V) / V) := by
            apply mul_le_mul_of_nonneg_left hsum2 (by positivity)
        _ ≤ 384 * v * (1 + Real.log v) / T := by
            have hVpos : (0:ℝ) < V := by exact_mod_cast hV1
            have hlogv0 : (0:ℝ) ≤ Real.log v := Real.log_nonneg hv
            have hlogV0 : (0:ℝ) ≤ Real.log (V:ℝ) := Real.log_nonneg (by exact_mod_cast hV1)
            have hvV2 : v ≤ 2 * (V:ℝ) := by
              have h1 : v < (V:ℝ) + 1 := by rw [hVdef]; exact Nat.lt_floor_add_one v
              have h2 : (1:ℝ) ≤ (V:ℝ) := by exact_mod_cast hV1
              linarith
            have hlogV : Real.log (V:ℝ) ≤ Real.log v := Real.log_le_log hVpos hVle
            have e1 : (48 * v^2 / T) * (2 * (1 + Real.log (V:ℝ)) / V)
                = 96 * (v/T) * ((v/(V:ℝ)) * (1 + Real.log (V:ℝ))) := by
              field_simp <;> ring
            have e2 : 384 * v * (1 + Real.log v) / T = 96 * (v/T) * (4 * (1 + Real.log v)) := by
              field_simp <;> ring
            rw [e1, e2]
            apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 96 * (v/T))
            have h2 : v/(V:ℝ) ≤ 2 := by rw [div_le_iff₀ hVpos]; linarith
            have h3 : (0:ℝ) ≤ v/(V:ℝ) := by positivity
            have h4 : (1:ℝ) + Real.log (V:ℝ) ≤ 2 * (1 + Real.log v) := by linarith
            have h5 : (0:ℝ) ≤ 1 + Real.log (V:ℝ) := by linarith
            nlinarith [h2, h3, h4, h5]
    have hhighb : ∑ m ∈ (Finset.Icc 1 M).filter
        (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|),
        12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
        ≤ 96 * (M:ℝ)/T + 96 * v * (1 + Real.log M)/T := by
      have hMV : ∀ m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|), Vc + 1 ≤ m := by
        intro m hm'
        obtain ⟨hmI, hmv, -⟩ := Finset.mem_filter.mp hm'
        have hVc1 : (Vc:ℝ) ≤ v + 1 := le_of_lt hVclt
        have h1 : (Vc:ℝ) < (m:ℝ) := by linarith
        have h2 : Vc < m := by exact_mod_cast h1
        omega
      have hpt : ∀ m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|),
          12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
          ≤ 48 / T * (1 + v / ((m:ℝ) - (Vc:ℝ))) := by
        intro m hm'
        obtain ⟨hmI, hmv, -⟩ := Finset.mem_filter.mp hm'
        have hm1' : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
        exact Sfun_high_pt hv0 hT0 hm1' hmv (hMV m hm') hVcle
      have hsub3 : (Finset.Icc 1 M).filter (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|)
          ⊆ Finset.Icc (Vc+1) M := by
        intro m hm'
        obtain ⟨hmI, hmv, -⟩ := Finset.mem_filter.mp hm'
        exact Finset.mem_Icc.mpr ⟨hMV m hm', (Finset.mem_Icc.mp hmI).2⟩
      have hsum3 : ∑ m ∈ (Finset.Icc 1 M).filter
          (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|),
          (1:ℝ) / ((m:ℝ) - (Vc:ℝ)) ≤ 1 + Real.log M := by
        refine le_trans ?_ (sum_sub_inv_high_pt Vc M hM)
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub3
        intro i hi _
        have hi1 : Vc + 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have h1 : (Vc:ℝ) + 1 ≤ (i:ℝ) := by exact_mod_cast hi1
        have h2 : (0:ℝ) < (i:ℝ) - (Vc:ℝ) := by linarith
        exact le_of_lt (div_pos one_pos h2)
      have hcount : (((Finset.Icc 1 M).filter
          (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|)).card : ℝ) ≤ M := by
        have hc : ((Finset.Icc 1 M).filter
            (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|)).card ≤ (Finset.Icc 1 M).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have hc2 : (Finset.Icc 1 M).card = M := by
          rw [Nat.card_Icc]; omega
        rw [hc2] at hc
        exact_mod_cast hc
      calc ∑ m ∈ (Finset.Icc 1 M).filter
            (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|),
            12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
          ≤ ∑ m ∈ (Finset.Icc 1 M).filter
              (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|),
              48 / T * (1 + v / ((m:ℝ) - (Vc:ℝ))) := Finset.sum_le_sum hpt
        _ ≤ 96 * (M:ℝ)/T + 96 * v * (1 + Real.log M)/T := by
            set S := (Finset.Icc 1 M).filter
              (fun m : ℕ => v + 1 ≤ (m:ℝ) ∧ 1 < |v - (m:ℝ)|) with hSdef
            rw [← Finset.mul_sum]
            have hterm : ∀ m ∈ S, (1 + v / ((m:ℝ) - (Vc:ℝ)))
                = 1 + v * (1 / ((m:ℝ) - (Vc:ℝ))) := by
              intro m _; ring
            rw [Finset.sum_congr rfl hterm]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            have hcard : ((S.card : ℝ)) ≤ M := hcount
            have hsum3' : ∑ m ∈ S, (1:ℝ) / ((m:ℝ) - (Vc:ℝ)) ≤ 1 + Real.log M := hsum3
            have hA : ∑ _m ∈ S, (1:ℝ) ≤ M := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
              exact hcard
            have hB : ∑ m ∈ S, (1:ℝ) / ((m:ℝ) - (Vc:ℝ)) ≤ 1 + Real.log M := hsum3'
            have hv0' : (0:ℝ) ≤ v := le_of_lt hv0
            have hpos : (0:ℝ) ≤ 48 / T := by positivity
            have h1 : (48 / T) * (∑ _m ∈ S, (1:ℝ) + v * ∑ m ∈ S, (1:ℝ) / ((m:ℝ) - (Vc:ℝ)))
                ≤ (48 / T) * (M + v * (1 + Real.log M)) := by
              apply mul_le_mul_of_nonneg_left _ hpos
              have := mul_le_mul_of_nonneg_left hB hv0'
              linarith
            have h2 : (48 / T) * (M + v * (1 + Real.log M))
                = 48 * (M:ℝ)/T + 48 * v * (1 + Real.log M)/T := by
              field_simp <;> ring
            have h3 : (0:ℝ) ≤ 48 * (M:ℝ)/T := by positivity
            have h4 : (0:ℝ) ≤ 48 * v * (1 + Real.log M)/T := by positivity
            calc (48 / T) * (∑ _m ∈ S, (1:ℝ) + v * ∑ m ∈ S, (1:ℝ) / ((m:ℝ) - (Vc:ℝ)))
                ≤ (48 / T) * (M + v * (1 + Real.log M)) := h1
              _ = 48 * (M:ℝ)/T + 48 * v * (1 + Real.log M)/T := h2
              _ ≤ 96 * (M:ℝ)/T + 96 * v * (1 + Real.log M)/T := by
                have e1 : (96:ℝ) * (M:ℝ)/T = 2 * (48 * (M:ℝ)/T) := by ring
                have e2 : (96:ℝ) * v * (1 + Real.log M)/T
                    = 2 * (48 * v * (1 + Real.log M)/T) := by ring
                rw [e1, e2]; linarith
    linarith
  linarith

end PerronSumHelpers9

section PerronSumHelpers10

/-- Number of tuples with a given product is at most `d(m)^20`. -/
private lemma fiber_card_le_pt (m : ℕ) {Nv : Fin 20 → ℝ} :
    (((Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))).filter
      (fun n => (∏ j, n j) = m))).card ≤ (m.divisors.card) ^ 20 := by
  classical
  set T := Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)) with hT
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hempty : T.filter (fun n => (∏ j, n j) = 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn hprod
      have hpos : (0:ℝ) < Pn_pt n := Pn_pos_pt (Nv := Nv) hn
      have hcastn : ((∏ j, n j : ℕ) : ℝ) = Pn_pt n := by rw [Nat.cast_prod]; rfl
      rw [hprod] at hcastn
      simp only [Nat.cast_zero] at hcastn
      linarith
    rw [hempty]; simp
  · have hsub : T.filter (fun n => (∏ j, n j) = m)
        ⊆ Fintype.piFinset (fun _ : Fin 20 => m.divisors) := by
      intro n hn
      have hmem : n ∈ T := (Finset.mem_filter.mp hn).1
      have hprod : (∏ j, n j) = m := (Finset.mem_filter.mp hn).2
      rw [Fintype.mem_piFinset]
      intro j
      have hdiv : n j ∣ m := by
        rw [← hprod]
        exact Finset.dvd_prod_of_mem (f := fun i : Fin 20 => n i) (Finset.mem_univ j)
      exact Nat.mem_divisors.mpr ⟨hdiv, by omega⟩
    calc (T.filter (fun n => (∏ j, n j) = m)).card
        ≤ (Fintype.piFinset (fun _ : Fin 20 => m.divisors)).card := Finset.card_le_card hsub
      _ = (m.divisors.card) ^ 20 := by
          rw [Fintype.card_piFinset]
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The tuple sum, grouped by the product and bounded with the divisor bound. -/
private lemma sum_coef_le_pt {q : ℕ} (χ : DirichletCharacter ℂ q) {N : ℕ} {Nv : Fin 20 → ℝ}
    (hC : Cond35 N Nv) (hN : 2 ≤ N) {Cc Adiv : ℝ} (hCc0 : 0 ≤ Cc) (hAdiv0 : 0 ≤ Adiv)
    (hCc : ∀ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ ≤ Cc)
    (hAdiv : ∀ m : ℕ, 1 ≤ m → m ≤ 2 ^ 20 * N + 1 → ((m.divisors.card : ℝ)) ^ 20 ≤ Adiv)
    (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ * F (∏ j, n j)
      ≤ Cc * Adiv * ∑ m ∈ Finset.Icc 1 (2 ^ 20 * N + 1), F m := by
  classical
  set T := Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)) with hT
  set M₀ := 2 ^ 20 * N + 1 with hM₀
  have hmaps : ∀ i ∈ T, (∏ j, i j) ∈ Finset.image (fun n => ∏ j, n j) T :=
    fun i hi => Finset.mem_image_of_mem _ hi
  have hcast : ∀ n : Fin 20 → ℕ, ((∏ j, n j : ℕ) : ℝ) = Pn_pt n := by
    intro n
    rw [Nat.cast_prod]
    rfl
  -- step 1: replace the coefficient norms by Cc
  have h1 : ∑ n ∈ T, ‖coef_pt χ n‖ * F (∏ j, n j) ≤ ∑ n ∈ T, Cc * F (∏ j, n j) := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (hCc n hn) (hF _)
  have h2 : ∑ n ∈ T, Cc * F (∏ j, n j) = Cc * ∑ n ∈ T, F (∏ j, n j) := by
    rw [Finset.mul_sum]
  -- step 2: reindex by the product
  have h3 : ∑ n ∈ T, F (∏ j, n j)
      = ∑ m ∈ Finset.image (fun n => ∏ j, n j) T,
          ∑ n ∈ T.filter (fun n => (∏ j, n j) = m), F (∏ j, n j) := by
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  -- step 3: bound each fiber
  have h4 : ∑ m ∈ Finset.image (fun n => ∏ j, n j) T,
      ∑ n ∈ T.filter (fun n => (∏ j, n j) = m), F (∏ j, n j)
      ≤ ∑ m ∈ Finset.image (fun n => ∏ j, n j) T, Adiv * F m := by
    apply Finset.sum_le_sum
    intro m hm
    have hcard : ((T.filter (fun n => (∏ j, n j) = m)).card : ℝ) ≤ Adiv := by
      obtain ⟨n₀, hn₀, hmn⟩ := Finset.mem_image.mp hm
      subst hmn
      have hm1 : (1:ℝ) ≤ ((∏ j, n₀ j : ℕ) : ℝ) := by
        rw [hcast n₀]; exact Pn_one_le_pt hn₀
      have hmM : ((∏ j, n₀ j : ℕ) : ℝ) ≤ ((2 ^ 20 * N + 1 : ℕ) : ℝ) := by
        have h1 : Pn_pt n₀ ≤ 2 ^ 20 * (N:ℝ) := Pn_le_pt hC hn₀
        have h2 : ((∏ j, n₀ j : ℕ) : ℝ) = Pn_pt n₀ := hcast n₀
        rw [h2]; push_cast; linarith
      refine le_trans (by exact_mod_cast fiber_card_le_pt (∏ j, n₀ j))
        (hAdiv (∏ j, n₀ j) (by exact_mod_cast hm1) (by exact_mod_cast hmM))
    calc ∑ n ∈ T.filter (fun n => (∏ j, n j) = m), F (∏ j, n j)
        = ∑ n ∈ T.filter (fun n => (∏ j, n j) = m), F m := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [(Finset.mem_filter.mp hn).2]
      _ = ((T.filter (fun n => (∏ j, n j) = m)).card : ℝ) * F m := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Adiv * F m := mul_le_mul_of_nonneg_right hcard (hF m)
  -- step 4: extend to the interval
  have hsub : Finset.image (fun n => ∏ j, n j) T ⊆ Finset.Icc 1 M₀ := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    have hpos : 1 ≤ ∏ j, n j := by
      have h1 : (1:ℝ) ≤ ((∏ j, n j : ℕ) : ℝ) := by
        rw [hcast n]; exact Pn_one_le_pt hn
      exact_mod_cast h1
    have hle : (∏ j, n j) ≤ M₀ := by
      have h1 : Pn_pt n ≤ 2 ^ 20 * (N:ℝ) := Pn_le_pt hC hn
      have h2 : ((∏ j, n j : ℕ) : ℝ) = Pn_pt n := hcast n
      have : ((∏ j, n j : ℕ) : ℝ) ≤ ((2 ^ 20 * N : ℕ) : ℝ) := by
        rw [h2]; push_cast; linarith
      have := Nat.cast_le.mp this
      rw [hM₀]; omega
    exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
  have h5 : ∑ m ∈ Finset.image (fun n => ∏ j, n j) T, Adiv * F m
      ≤ ∑ m ∈ Finset.Icc 1 M₀, Adiv * F m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    exact mul_nonneg hAdiv0 (hF i)
  have h6 : ∑ m ∈ Finset.Icc 1 M₀, Adiv * F m = Adiv * ∑ m ∈ Finset.Icc 1 M₀, F m := by
    rw [Finset.mul_sum]
  calc ∑ n ∈ T, ‖coef_pt χ n‖ * F (∏ j, n j)
      ≤ ∑ n ∈ T, Cc * F (∏ j, n j) := h1
    _ = Cc * ∑ n ∈ T, F (∏ j, n j) := h2
    _ = Cc * ∑ m ∈ Finset.image (fun n => ∏ j, n j) T,
          ∑ n ∈ T.filter (fun n => (∏ j, n j) = m), F (∏ j, n j) := by rw [h3]
    _ ≤ Cc * ∑ m ∈ Finset.image (fun n => ∏ j, n j) T, Adiv * F m := by
        apply mul_le_mul_of_nonneg_left h4 hCc0
    _ ≤ Cc * ∑ m ∈ Finset.Icc 1 M₀, Adiv * F m := by
        apply mul_le_mul_of_nonneg_left h5 hCc0
    _ = Cc * Adiv * ∑ m ∈ Finset.Icc 1 M₀, F m := by rw [h6]; ring

end PerronSumHelpers10

section PerronSumHelpers11

/-- The clean form of the integer sum bound: `1200 M (1 + log M) / T`. -/
private lemma sum_S_bound2_pt {v T : ℝ} (hv : 1 ≤ v) (hT : 2 ≤ T) (M : ℕ) (hM : 1 ≤ M)
    (hTM : T ≤ (M:ℝ)) (hvM : v ≤ (M:ℝ)) :
    ∑ m ∈ Finset.Icc 1 M, 12 * ((m:ℝ) + v) ^ 2 / ((m:ℝ) * ((m:ℝ) + v + T * |v - (m:ℝ)|))
      ≤ 1200 * (M:ℝ) * (1 + Real.log M) / T := by
  have hT0 : 0 < T := by linarith
  have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hlogM : (0:ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hlogv : (0:ℝ) ≤ Real.log v := Real.log_nonneg hv
  have hlogvM : Real.log v ≤ Real.log M := Real.log_le_log (by linarith) hvM
  have base := sum_S_bound_pt hv hT M hM
  have h1 : 48 * (8*v/T + 5) ≤ 624 * ((M:ℝ) * (1 + Real.log M) / T) := by
    have e : 48 * (8*v/T + 5) = 384*v/T + 240 := by ring
    rw [e]
    have ha : 384*v/T ≤ 384 * ((M:ℝ) * (1 + Real.log M) / T) := by
      have e2 : 384 * ((M:ℝ) * (1 + Real.log M) / T) = 384*((M:ℝ)*(1 + Real.log M))/T := by ring
      rw [e2]
      apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
      nlinarith
    have hb : (240:ℝ) ≤ 240 * ((M:ℝ) * (1 + Real.log M) / T) := by
      have e2 : 240 * ((M:ℝ) * (1 + Real.log M) / T) = 240*((M:ℝ)*(1 + Real.log M))/T := by ring
      rw [e2, le_div_iff₀ hT0]
      nlinarith
    linarith
  have h2 : 384 * v * (1 + Real.log v)/T ≤ 384 * ((M:ℝ) * (1 + Real.log M) / T) := by
    have e2 : 384 * ((M:ℝ) * (1 + Real.log M) / T) = 384*((M:ℝ)*(1 + Real.log M))/T := by ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
    nlinarith
  have h3 : 96 * (M:ℝ)/T ≤ 96 * ((M:ℝ) * (1 + Real.log M) / T) := by
    have e2 : 96 * ((M:ℝ) * (1 + Real.log M) / T) = 96*((M:ℝ)*(1 + Real.log M))/T := by ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
    nlinarith
  have h4 : 96 * v * (1 + Real.log M)/T ≤ 96 * ((M:ℝ) * (1 + Real.log M) / T) := by
    have e2 : 96 * ((M:ℝ) * (1 + Real.log M) / T) = 96*((M:ℝ)*(1 + Real.log M))/T := by ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
    nlinarith
  have hsum : 624 * ((M:ℝ) * (1 + Real.log M) / T) + 384 * ((M:ℝ) * (1 + Real.log M) / T)
      + 96 * ((M:ℝ) * (1 + Real.log M) / T) + 96 * ((M:ℝ) * (1 + Real.log M) / T)
      = 1200 * (M:ℝ) * (1 + Real.log M) / T := by
    field_simp
    ring
  linarith [base, h1, h2, h3, h4, hsum]

end PerronSumHelpers11

set_option maxHeartbeats 2000000 in
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
  intro ε hε
  set k : ℕ := ⌈80/ε⌉₊ + 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
  obtain ⟨Cdiv, hCdivpos, hCdiv⟩ := card_divisors_le_rpow_pt k hk1
  have hkbound : 20 * ((k:ℝ)⁻¹) ≤ ε/4 := by
    have h1 : (80:ℝ)/ε ≤ (k:ℝ) := by
      have ha : ((⌈80/ε⌉₊ : ℕ) : ℝ) ≤ (k:ℝ) := by
        have : ⌈80/ε⌉₊ ≤ k := by omega
        exact_mod_cast this
      have hb : (80:ℝ)/ε ≤ ((⌈80/ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      linarith
    have h2 : (k:ℝ)⁻¹ ≤ ε/80 := by
      have h3 : (1:ℝ) ≤ (ε/80) * (k:ℝ) := by
        have h4 : (0:ℝ) < ε/80 := by positivity
        have h6 : (ε/80) * ((80:ℝ)/ε) ≤ (ε/80) * (k:ℝ) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt h4)
        have h7 : (ε/80) * ((80:ℝ)/ε) = 1 := by field_simp
        linarith
      have h5 : (k:ℝ)⁻¹ = 1/(k:ℝ) := (one_div (k:ℝ)).symm
      rw [h5]
      exact (div_le_iff₀ hkR).mpr (by linarith)
    have h8 : 20 * (k:ℝ)⁻¹ ≤ 20 * (ε/80) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h9 : 20 * (ε/80) = ε/4 := by ring
    linarith
  set Kc : ℝ := 2400 * Cdiv^20 * (2:ℝ)^(21*ε/4) * 2^21 * 24 * 42^20 with hKc
  have hKcpos : (0:ℝ) < Kc := by
    rw [hKc]
    have h1 : (0:ℝ) < Cdiv^20 := by positivity
    have h2 : (0:ℝ) < (2:ℝ)^(21*ε/4) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨Kc, max (max 8 (((2:ℝ)^21 / (ε/168)^21)^(8/ε))) 2, hKcpos, ?_⟩
  intro N A T u q χ Nv hN hA hA2 hC hT2 hTN hu1 hu2
  set X : ℝ := Kc * (N:ℝ)^(1+ε) / T with hX
  have hN₀8 : (8:ℝ) ≤ (N:ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₀X : ((2:ℝ)^21 / (ε/168)^21)^(8/ε) ≤ (N:ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₀2 : (2:ℝ) ≤ (N:ℝ) := le_trans (le_max_right _ _) hN
  have hN2 : 2 ≤ N := by exact_mod_cast hN₀2
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hδpos : (0:ℝ) < ε/168 := by positivity
  -- the coefficient bound
  have hcoefpow : (2:ℝ)^21 / (ε/168)^21 ≤ (N:ℝ)^(ε/8) := by
    have hx : (((2:ℝ)^21 / (ε/168)^21)^(8/ε))^(ε/8) = (2:ℝ)^21 / (ε/168)^21 := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^21 / (ε/168)^21)]
      have : (8/ε)*(ε/8) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [← hx]
    exact Real.rpow_le_rpow (by positivity) hN₀X (by linarith)
  -- the logarithmic gain
  have hlogkey : (1 + Real.log (N:ℝ))^21 ≤ (N:ℝ)^(ε/4) := by
    have hlog3 : (1:ℝ) < Real.log (3:ℝ) := by
      have h1 : Real.exp 1 < (3:ℝ) := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.log (Real.exp 1) < Real.log (3:ℝ) := Real.log_lt_log (Real.exp_pos 1) h1
      rwa [Real.log_exp] at h2
    have hlogN1 : (1:ℝ) ≤ Real.log (N:ℝ) := by
      have h2 : Real.log (3:ℝ) ≤ Real.log (N:ℝ) :=
        Real.log_le_log (by norm_num) (by linarith : (3:ℝ) ≤ (N:ℝ))
      linarith
    have hlogNpos : (0:ℝ) < Real.log (N:ℝ) := by linarith
    have hb : Real.log (N:ℝ) ≤ (N:ℝ)^(ε/168)/(ε/168) :=
      Real.log_le_rpow_div (by linarith) hδpos
    have e1 : (1 + Real.log (N:ℝ))^21 ≤ (2 * ((N:ℝ)^(ε/168)/(ε/168)))^21 := by
      apply pow_le_pow_left₀ (by linarith)
      linarith
    have e2 : (2 * ((N:ℝ)^(ε/168)/(ε/168)))^21
        = ((2:ℝ)^21 / (ε/168)^21) * ((N:ℝ)^(ε/168))^21 := by
      rw [mul_pow, div_pow]
      ring
    have e3 : ((N:ℝ)^(ε/168))^21 = (N:ℝ)^(ε/8) := by
      rw [← Real.rpow_natCast ((N:ℝ)^(ε/168)) 21, ← Real.rpow_mul (by linarith)]
      congr 1
      ring
    have eqt : (2 * ((N:ℝ)^(ε/168)/(ε/168)))^21
        = ((2:ℝ)^21 / (ε/168)^21) * (N:ℝ)^(ε/8) := by
      rw [e2, e3]
    have hp1 : ((2:ℝ)^21 / (ε/168)^21) * (N:ℝ)^(ε/8) ≤ (N:ℝ)^(ε/8) * ((N:ℝ)^(ε/8)) := by
      apply mul_le_mul_of_nonneg_right hcoefpow (by positivity)
    have e5 : (N:ℝ)^(ε/8) * ((N:ℝ)^(ε/8)) = (N:ℝ)^(ε/4) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
    calc (1 + Real.log (N:ℝ))^21 ≤ (2 * ((N:ℝ)^(ε/168)/(ε/168)))^21 := e1
      _ = ((2:ℝ)^21 / (ε/168)^21) * (N:ℝ)^(ε/8) := eqt
      _ ≤ (N:ℝ)^(ε/8) * ((N:ℝ)^(ε/8)) := hp1
      _ = (N:ℝ)^(ε/4) := e5
  -- per tuple bound
  have hcast : ∀ n : Fin 20 → ℕ, ((∏ j, n j : ℕ) : ℝ) = Pn_pt n := by
    intro n
    rw [Nat.cast_prod]
    rfl
  have hNA : (0:ℝ) < (N:ℝ) - A := by
    have h1 : (N:ℝ) ^ (2/3:ℝ) < (N:ℝ) ^ (1:ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_one] at h1
    linarith
  have hcbrt : (2:ℝ) ≤ (N:ℝ)^(1/3:ℝ) := by
    have h1 : ((2:ℝ))^3 ≤ (N:ℝ) := by
      have h9 : (8:ℝ) ≤ (N:ℝ) := hN₀8
      have h10 : ((2:ℝ))^3 = 8 := by norm_num
      linarith
    have hexp : (2:ℝ) = ((2:ℝ)^3)^(1/3:ℝ) := by
      rw [← Real.rpow_natCast (2:ℝ) 3, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      exact (show (2:ℝ)^(((3:ℕ):ℝ) * (1/3:ℝ)) = (2:ℝ) from by
        rw [show ((3:ℕ):ℝ) * (1/3:ℝ) = (1:ℝ) by norm_num, Real.rpow_one]).symm
    rw [hexp]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h23 : (N:ℝ)^(2/3:ℝ) ≤ (N:ℝ)/2 := by
    have h1 : (N:ℝ)^(2/3:ℝ) = (N:ℝ)^(1/3:ℝ) * (N:ℝ)^(1/3:ℝ) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
    have h3 : (N:ℝ)^(1/3:ℝ) * (N:ℝ)^(1/3:ℝ) * (N:ℝ)^(1/3:ℝ) = (N:ℝ) := by
      rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
      rw [show (1/3:ℝ) + 1/3 + 1/3 = 1 by ring, Real.rpow_one]
    have h4 : (0:ℝ) ≤ (N:ℝ)^(1/3:ℝ) := by positivity
    have h5 : (N:ℝ)^(1/3:ℝ) * (N:ℝ)^(1/3:ℝ) * 2
        ≤ (N:ℝ)^(1/3:ℝ) * (N:ℝ)^(1/3:ℝ) * (N:ℝ)^(1/3:ℝ) := by
      have h6 : (0:ℝ) ≤ (N:ℝ)^(1/3:ℝ) * (N:ℝ)^(1/3:ℝ) := by positivity
      nlinarith
    rw [h1, h3] at *
    linarith
  have hu1 : 1 ≤ u := by linarith
  have hu'1 : 1 ≤ (N:ℝ) - A := by linarith
  have hu0 : 0 < u := by linarith
  have huN : u ≤ N := hu2
  have hu'0 : 0 < (N:ℝ) - A := by linarith
  have hu'N : (N:ℝ) - A ≤ (N:ℝ) := by linarith
  set S1 : ℕ → ℝ := fun m => 12 * ((m:ℝ) + u) ^ 2 /
    ((m:ℝ) * ((m:ℝ) + u + T * |u - (m:ℝ)|)) with hS1
  set S2 : ℕ → ℝ := fun m => 12 * ((m:ℝ) + ((N:ℝ) - A)) ^ 2 /
    ((m:ℝ) * ((m:ℝ) + ((N:ℝ) - A) + T * |((N:ℝ) - A) - (m:ℝ)|)) with hS2
  have hS1nn : ∀ m, 0 ≤ S1 m := by
    intro m; rw [hS1]; positivity
  have hS2nn : ∀ m, 0 ≤ S2 m := by
    intro m; rw [hS2]; positivity
  have hper : ∀ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      ‖coef_pt χ n‖ * (Bterm_pt (1 + 1 / Real.log N) T (u / Pn_pt n) +
        Bterm_pt (1 + 1 / Real.log N) T (((N : ℝ) - A) / Pn_pt n))
      ≤ ‖coef_pt χ n‖ * (S1 (∏ j, n j) + S2 (∏ j, n j)) := by
    intro n hn
    have hm1 : 1 ≤ ∏ j, n j := by
      have h1 : (1:ℝ) ≤ ((∏ j, n j : ℕ) : ℝ) := by
        rw [hcast n]; exact Pn_one_le_pt hn
      exact_mod_cast h1
    have hPn : Pn_pt n = ((∏ j, n j : ℕ) : ℝ) := (hcast n).symm
    have h1 := Bterm_v_bound_pt (N := N) hN2 (T := T) (v := u) hT2 hu0 huN hm1
    have h2 := Bterm_v_bound_pt (N := N) hN2 (T := T) (v := (N:ℝ) - A) hT2 hu'0 hu'N hm1
    have h1' : Bterm_pt (1 + 1 / Real.log N) T (u / ((∏ j, n j : ℕ) : ℝ))
        ≤ S1 (∏ j, n j) := by
      rw [hS1]
      exact h1
    have h2' : Bterm_pt (1 + 1 / Real.log N) T (((N:ℝ) - A) / ((∏ j, n j : ℕ) : ℝ))
        ≤ S2 (∏ j, n j) := by
      rw [hS2]
      exact h2
    rw [hPn]
    exact mul_le_mul_of_nonneg_left (add_le_add h1' h2') (norm_nonneg _)
  refine le_trans (Finset.sum_le_sum hper) ?_
  have hdist : ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      ‖coef_pt χ n‖ * (S1 (∏ j, n j) + S2 (∏ j, n j))
      = (∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ * S1 (∏ j, n j))
        + ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ * S2 (∏ j, n j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hdist]
  have hCc : ∀ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      ‖coef_pt χ n‖ ≤ (21 * Real.log (2 * N))^20 := fun n hn => coef_norm_le_pt χ hC hN2 hn
  have hCc0 : (0:ℝ) ≤ (21 * Real.log (2 * N))^20 := by positivity
  have hM₀1 : 1 ≤ 2^20 * N + 1 := by omega
  have hAdivdef : ∀ m : ℕ, 1 ≤ m → m ≤ 2^20 * N + 1 →
      ((m.divisors.card : ℝ))^20 ≤ Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4) := by
    intro m hm1 hmM
    have h1 : (m.divisors.card : ℝ) ≤ Cdiv * (m:ℝ)^((k:ℝ)⁻¹) := hCdiv m hm1
    have h2 : (0:ℝ) ≤ (m.divisors.card : ℝ) := by positivity
    have h3 : ((m.divisors.card : ℝ))^20 ≤ (Cdiv * (m:ℝ)^((k:ℝ)⁻¹))^20 :=
      pow_le_pow_left₀ h2 h1 20
    have h5 : ((m:ℝ)^((k:ℝ)⁻¹))^20 = (m:ℝ)^(20*(k:ℝ)⁻¹) := by
      rw [← Real.rpow_natCast ((m:ℝ)^((k:ℝ)⁻¹)) 20, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    have h6 : (m:ℝ)^(20*(k:ℝ)⁻¹) ≤ (m:ℝ)^(ε/4) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm1) hkbound
    have h7 : (m:ℝ)^(ε/4) ≤ (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast hmM
    have h8 : (0:ℝ) ≤ Cdiv^20 := by positivity
    calc ((m.divisors.card : ℝ))^20
        ≤ (Cdiv * (m:ℝ)^((k:ℝ)⁻¹))^20 := h3
      _ = Cdiv^20 * ((m:ℝ)^((k:ℝ)⁻¹))^20 := by rw [mul_pow]
      _ = Cdiv^20 * (m:ℝ)^(20*(k:ℝ)⁻¹) := by rw [h5]
      _ ≤ Cdiv^20 * (m:ℝ)^(ε/4) := by
          apply mul_le_mul_of_nonneg_left h6 h8
      _ ≤ Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4) := by
          apply mul_le_mul_of_nonneg_left h7 h8
  have hb1 := sum_coef_le_pt (χ := χ) hC hN2 (Cc := (21 * Real.log (2 * N))^20)
    (Adiv := Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4)) hCc0 (by positivity) hCc hAdivdef
    S1 hS1nn
  have hb2 := sum_coef_le_pt (χ := χ) hC hN2 (Cc := (21 * Real.log (2 * N))^20)
    (Adiv := Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4)) hCc0 (by positivity) hCc hAdivdef
    S2 hS2nn
  have hs1 : ∑ m ∈ Finset.Icc 1 (2^20 * N + 1), S1 m
      ≤ 1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) / T := by
    have h := sum_S_bound2_pt (v := u) (T := T) (M := 2^20 * N + 1)
      hu1 hT2 hM₀1 (by push_cast; nlinarith) (by push_cast; linarith)
    rw [hS1]
    exact h
  have hs2 : ∑ m ∈ Finset.Icc 1 (2^20 * N + 1), S2 m
      ≤ 1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) / T := by
    have h := sum_S_bound2_pt (v := (N:ℝ) - A) (T := T) (M := 2^20 * N + 1)
      hu'1 hT2 hM₀1 (by push_cast; nlinarith) (by push_cast; linarith)
    rw [hS2]
    exact h
  have hM₀le : (((2^20 * N + 1 : ℕ)) : ℝ) ≤ 2^21 * (N:ℝ) := by push_cast; nlinarith
  have hlogM₀ : 1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ) ≤ 24 * (1 + Real.log (N:ℝ)) := by
    have h1 : (1:ℝ) ≤ ((2^20 * N + 1 : ℕ) : ℝ) := by push_cast; nlinarith
    have h2 : Real.log (((2^20 * N + 1 : ℕ)) : ℝ) ≤ Real.log (2^21 * (N:ℝ)) :=
      Real.log_le_log (by linarith) hM₀le
    have h3 : Real.log (2^21 * (N:ℝ)) = 21 * Real.log 2 + Real.log (N:ℝ) := by
      rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow]; push_cast; ring
    have hlog2 : Real.log 2 ≤ (1:ℝ) := by
      have := Real.log_two_lt_d9
      linarith
    have hLnonneg : (0:ℝ) ≤ Real.log (N:ℝ) :=
      Real.log_nonneg (by linarith : (1:ℝ) ≤ (N:ℝ))
    linarith
  have hAdivle : Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4)
      ≤ Cdiv^20 * ((2:ℝ)^(21*ε/4) * (N:ℝ)^(ε/4)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hbase : (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4) ≤ (2^21 * (N:ℝ))^(ε/4) :=
      Real.rpow_le_rpow (by positivity) hM₀le (by linarith)
    have heq : (2^21 * (N:ℝ))^(ε/4) = (2:ℝ)^(21*ε/4) * (N:ℝ)^(ε/4) := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      have h2 : ((2:ℝ)^21)^(ε/4) = (2:ℝ)^(21*ε/4) := by
        rw [← Real.rpow_natCast (2:ℝ) 21, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [h2]
    exact hbase.trans (le_of_eq heq)
  have hCcle : (21 * Real.log (2 * N))^20 ≤ 42^20 * (1 + Real.log (N:ℝ))^20 := by
    have h1 : Real.log (2 * (N:ℝ)) = Real.log 2 + Real.log (N:ℝ) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
    have h2 : Real.log 2 ≤ (1:ℝ) := by
      have := Real.log_two_lt_d9
      linarith
    have h6 : (21:ℝ) * Real.log (2 * ↑N) ≤ 42 * (1 + Real.log (↑N)) := by
      rw [h1]
      have h5 : (0:ℝ) ≤ Real.log (↑N) := Real.log_nonneg (by linarith)
      nlinarith
    calc (21 * Real.log (2 * N))^20 ≤ (42 * (1 + Real.log (N:ℝ)))^20 := by
          have hpos : (0:ℝ) ≤ 21 * Real.log (2 * (N:ℝ)) := by
            have h7 : (0:ℝ) ≤ Real.log (2 * (N:ℝ)) :=
              Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * (N:ℝ))
            linarith
          exact pow_le_pow_left₀ hpos h6 20
      _ = 42^20 * (1 + Real.log (N:ℝ))^20 := by rw [mul_pow]
  have hlam : (0:ℝ) < T := by linarith
  have hM₀1R : (1:ℝ) ≤ (((2^20 * N + 1 : ℕ)) : ℝ) := by
    have h2 : (((2^20 * N + 1 : ℕ)) : ℝ) = (2:ℝ)^20 * (N:ℝ) + 1 := by push_cast; ring
    rw [h2]
    have h3 : (0:ℝ) < (2:ℝ)^20 := by positivity
    have h4 : (0:ℝ) ≤ (N:ℝ) := by linarith
    nlinarith
  have hlogM₀nn : (0:ℝ) ≤ Real.log (((2^20 * N + 1 : ℕ)) : ℝ) := Real.log_nonneg hM₀1R
  have hbig : (21 * Real.log (2 * N))^20 * (Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4))
        * (1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) / T)
      ≤ (1/2) * X := by
    have hB' : (0:ℝ) ≤ Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4) := by positivity
    have hposA : (0:ℝ) ≤ (42^20 * (1 + Real.log (N:ℝ))^20) * (Cdiv^20 * ((2:ℝ)^(21*ε/4) * (N:ℝ)^(ε/4))) := by
      have h7 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg (by linarith)
      have h8 : (0:ℝ) ≤ 1 + Real.log (N:ℝ) := by linarith
      exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h8 20))
        (mul_nonneg (pow_nonneg (le_of_lt hCdivpos) 20)
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _)))
    have hposlog : (0:ℝ) ≤ 1 + Real.log (N:ℝ) := by
      have h7 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg (by linarith)
      linarith
    have hA : (0:ℝ) ≤ 42^20 * (1 + Real.log (N:ℝ))^20 :=
      mul_nonneg (by norm_num) (pow_nonneg hposlog 20)
    have hB : (0:ℝ) ≤ Cdiv^20 * ((2:ℝ)^(21*ε/4) * (N:ℝ)^(ε/4)) :=
      mul_nonneg (pow_nonneg (le_of_lt hCdivpos) 20)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _))
    have e3 : 1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) / T
        ≤ 1200 * (2^21 * (N:ℝ)) * (24 * (1 + Real.log (N:ℝ))) / T := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hlam)
      have h1 : (0:ℝ) ≤ (((2^20 * N + 1 : ℕ)) : ℝ) := by positivity
      have ha : 1200 * (((2^20 * N + 1 : ℕ)) : ℝ) ≤ 1200 * (2^21 * (N:ℝ)) :=
        mul_le_mul_of_nonneg_left hM₀le (by norm_num)
      have hb : (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) ≤ 24 * (1 + Real.log (N:ℝ)) := hlogM₀
      calc 1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ))
          ≤ 1200 * (2^21 * (N:ℝ)) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right ha; linarith
        _ ≤ 1200 * (2^21 * (N:ℝ)) * (24 * (1 + Real.log (N:ℝ))) := by
            apply mul_le_mul_of_nonneg_left hb; positivity
    have hs : (21 * Real.log (2 * N))^20 * (Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4))
          * (1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) / T)
        ≤ (42^20 * (1 + Real.log (N:ℝ))^20) * (Cdiv^20 * ((2:ℝ)^(21*ε/4) * (N:ℝ)^(ε/4)))
          * (1200 * (2^21 * (N:ℝ)) * (24 * (1 + Real.log (N:ℝ))) / T) := by
      exact mul_le_mul (mul_le_mul hCcle hAdivle hB' hA) e3 (by positivity) hposA
    refine hs.trans ?_
    have hsplit2 : (N:ℝ)^(1+ε/4) = (N:ℝ)^(ε/4) * (N:ℝ) := by
      nth_rewrite 1 [show (1:ℝ) + ε/4 = ε/4 + 1 by ring]
      rw [Real.rpow_add (by linarith : (0:ℝ) < (N:ℝ)), Real.rpow_one]
    have hCst : (42^20 * (1 + Real.log (N:ℝ))^20) * (Cdiv^20 * ((2:ℝ)^(21*ε/4) * (N:ℝ)^(ε/4)))
          * (1200 * (2^21 * (N:ℝ)) * (24 * (1 + Real.log (N:ℝ))) / T)
        = (Kc/2) * ((1 + Real.log (N:ℝ))^21 * ((N:ℝ)^(ε/4) * (N:ℝ)) / T) := by
      rw [hKc]
      field_simp
      ring
    rw [hCst]
    have hlog1 : (1:ℝ) ≤ 1 + Real.log (N:ℝ) := by
      have h7 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg (by linarith)
      linarith
    have hpow : (1 + Real.log (N:ℝ))^20 * (1 + Real.log (N:ℝ)) = (1 + Real.log (N:ℝ))^21 := by
      ring
    have hfin : (Kc/2) * ((1 + Real.log (N:ℝ))^21 * ((N:ℝ)^(ε/4) * (N:ℝ)) / T)
        ≤ (1/2) * X := by
      have h1 : (1 + Real.log (N:ℝ))^21 * ((N:ℝ)^(ε/4) * (N:ℝ))
          ≤ (N:ℝ)^(ε/4) * ((N:ℝ)^(ε/4) * (N:ℝ)) := by
        apply mul_le_mul_of_nonneg_right hlogkey
        positivity
      have h2 : (N:ℝ)^(ε/4) * ((N:ℝ)^(ε/4) * (N:ℝ)) = (N:ℝ)^(1+ε/2) := by
        rw [← hsplit2, ← Real.rpow_add (by linarith : (0:ℝ) < (N:ℝ))]
        congr 1
        ring
      have h3 : (N:ℝ)^(1+ε/2) ≤ (N:ℝ)^(1+ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (N:ℝ)) (by linarith)
      have hT0 : (0:ℝ) < T := hlam
      have hstep : (1 + Real.log (N:ℝ))^21 * ((N:ℝ)^(ε/4) * (N:ℝ)) / T ≤ (N:ℝ)^(1+ε)/T := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
        linarith [h1, h2, h3]
      have hKc0 : (0:ℝ) ≤ Kc/2 := by linarith [hKcpos]
      have hstep2 : (Kc/2) * ((1 + Real.log (N:ℝ))^21 * ((N:ℝ)^(ε/4) * (N:ℝ)) / T)
          ≤ (Kc/2) * ((N:ℝ)^(1+ε)/T) := by
        apply mul_le_mul_of_nonneg_left hstep hKc0
      have hXeq : (Kc/2) * ((N:ℝ)^(1+ε)/T) = (1/2) * X := by
        rw [hX]
        ring
      rw [hXeq] at hstep2
      exact hstep2
    exact hfin
  have hsumA1 : ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ * S1 (∏ j, n j)
      ≤ (21 * Real.log (2 * N))^20 * (Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4))
        * (1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) / T) :=
    le_trans hb1 (mul_le_mul_of_nonneg_left hs1 (by positivity))
  have hsumA2 : ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ * S2 (∏ j, n j)
      ≤ (21 * Real.log (2 * N))^20 * (Cdiv^20 * (((2^20 * N + 1 : ℕ)) : ℝ)^(ε/4))
        * (1200 * (((2^20 * N + 1 : ℕ)) : ℝ) * (1 + Real.log (((2^20 * N + 1 : ℕ)) : ℝ)) / T) :=
    le_trans hb2 (mul_le_mul_of_nonneg_left hs2 (by positivity))
  have hsum1 : ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ * S1 (∏ j, n j)
      ≤ (1/2) * X := by linarith [hsumA1, hbig]
  have hsum2 : ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)), ‖coef_pt χ n‖ * S2 (∏ j, n j)
      ≤ (1/2) * X := by linarith [hsumA2, hbig]
  linarith [hsum1, hsum2]

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
