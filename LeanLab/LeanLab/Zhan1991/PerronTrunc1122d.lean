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
import LeanLab.Zhan1991.PerronSingle1122d
import LeanLab.Zhan1991.PerronSum1122d

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

/-- LEAF: the single term Perron estimate used for page 263 display (3.3): for `c > 0`, `T > 0`,
`y > 0`, `|(1/2πi)∫_{c-iT}^{c+iT} y^s s⁻¹ ds - δ(y)| < y^c min(1, 1/(T|log y|))` for `y ≠ 1`,
and `|(1/2πi)∫ s⁻¹ ds - 1/2| < c/T` at `y = 1`, Davenport, Multiplicative Number Theory,
chapter 17, the lemma; Titchmarsh, Theory of Functions, 3.12. Class MEDIUM.
PROVED from the case `y = 1`, `perron_one_ps1`, and the four LEAFs of PerronSingle1122d.lean. -/
theorem perron_single_leaf_pt : ∀ c T y : ℝ, 0 < c → 0 < T → 0 < y →
    ‖Hstep_pt y - Jint_pt c T y‖ ≤ Bterm_pt c T y := by
  intro c T y hc hT hy
  rcases lt_trichotomy y 1 with h | h | h
  · have h1 := perron_lt_log_leaf_ps1 c T y hc hT hy h
    have h2 := perron_lt_unif_leaf_ps1 c T y hc hT hy h
    have hyc : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
    have hm : ‖Jint_pt c T y‖ ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := by
      rw [mul_min_of_nonneg _ _ hyc, mul_one]
      exact le_min h2 h1
    have hmin : 0 ≤ min 1 (1 / (T * |Real.log y|)) :=
      le_min zero_le_one (by positivity)
    unfold Bterm_pt Hstep_pt
    rw [if_neg h.ne, if_neg (not_le.mpr h), zero_sub, norm_neg]
    nlinarith [mul_nonneg hyc hmin]
  · subst h
    unfold Bterm_pt Hstep_pt Jint_pt
    rw [if_pos rfl, if_pos le_rfl]
    exact perron_one_ps1 c T hc hT
  · have h1 := perron_gt_log_leaf_ps1 c T y hc hT h
    have h2 := perron_gt_unif_leaf_ps1 c T y hc hT h
    have hyc : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
    have hm : ‖1 - Jint_pt c T y‖ ≤ y ^ c * min 1 (1 / (T * |Real.log y|)) := by
      rw [mul_min_of_nonneg _ _ hyc, mul_one]
      exact le_min h2 h1
    have hmin : 0 ≤ min 1 (1 / (T * |Real.log y|)) :=
      le_min zero_le_one (by positivity)
    unfold Bterm_pt Hstep_pt
    rw [if_neg h.ne', if_pos h.le]
    nlinarith [mul_nonneg hyc hmin]

/-- LEAF: page 263 display (3.3), the summation of the single term errors over the tuples of
(3.4), with `|a₁(n₁)⋯a₂₀(n₂₀)| ≤ log (2N) ≪ N^{ε/2}`, the divisor bound
`d₂₀(m) ≪ N^{ε/2}` for the tuples with product at or near `u` or `N - A`, the harmonic sum
`Σ 1/|u - m| ≪ log N` for the rest, and `T ≤ N` so the lattice point terms `N^ε` are
`≤ N^{1+ε}/T`. Class MEDIUM.
PROVED from the three LEAFs of PerronSum1122d.lean: coefficient, divisor and harmonic bounds. -/
theorem perron_sum_leaf_pt : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      ‖coef_pt χ n‖ * (Bterm_pt (1 + 1 / Real.log N) T (u / Pn_pt n) +
        Bterm_pt (1 + 1 / Real.log N) T (((N : ℝ) - A) / Pn_pt n))
      ≤ K * (N : ℝ) ^ (1 + ε) / T := by
  intro ε hε
  obtain ⟨KA, NA, hKA, hA⟩ := perron_coef_leaf_ps2 (ε / 3) (by positivity)
  obtain ⟨KB, NB, hKB, hB⟩ := perron_fiber_leaf_ps2 (ε / 3) (by positivity)
  obtain ⟨KC, NC, hKC, hC⟩ := perron_harmonic_leaf_ps2 (ε / 3) (by positivity)
  refine ⟨2 * KA * KB * KC, max (max NA NB) (max NC 2), by positivity, ?_⟩
  intro N A T u q χ Nv hN hA0 hA2 hC35 hT2 hTN hu1 hu2
  have hNA' : NA ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNB' : NB ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNC' : NC ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNA : 0 < (N : ℝ) - A := by
    have : (N : ℝ) ^ (2 / 3 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hT0 : 0 < T := by linarith
  set c : ℝ := 1 + 1 / Real.log N with hcdef
  have hc : 0 < c := by
    have : 0 ≤ 1 / Real.log N := by
      apply div_nonneg zero_le_one; exact Real.log_natCast_nonneg N
    linarith
  have hBnn : ∀ y : ℝ, 0 < y → 0 ≤ Bterm_pt c T y := by
    intro y hy
    unfold Bterm_pt
    split_ifs
    · positivity
    · have : 0 ≤ min 1 (1 / (T * |Real.log y|)) := le_min zero_le_one (by positivity)
      have := Real.rpow_nonneg hy.le c; positivity
  set box := Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)) with hbox
  have hPn : ∀ n : Fin 20 → ℕ, Pn_pt n = ((∏ j, n j : ℕ) : ℝ) := by
    intro n; unfold Pn_pt; push_cast; rfl
  have hmaps : ∀ n ∈ box, (∏ j, n j) ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N) := by
    intro n hn
    have hmem : ∀ j, 1 ≤ n j ∧ (n j : ℝ) ≤ 2 * Nv j := by
      intro j
      have h := Fintype.mem_piFinset.mp hn j
      unfold dyad at h
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp h).1
      refine ⟨h1.1, ?_⟩
      have h2 : (n j : ℝ) ≤ (⌊2 * Nv j⌋₊ : ℝ) := by exact_mod_cast h1.2
      have h3 : (⌊2 * Nv j⌋₊ : ℝ) ≤ 2 * Nv j := Nat.floor_le (by linarith [hC35.1 j])
      linarith
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.one_le_prod (fun j _ => (hmem j).1)
    · have hr : ((∏ j, n j : ℕ) : ℝ) ≤ ((2 ^ 20 * N : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        calc (∏ j, (n j : ℝ)) ≤ ∏ j, (2 * Nv j) :=
              Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => (hmem j).2)
          _ = 2 ^ 20 * ∏ j, Nv j := by rw [Finset.prod_mul_distrib]; simp
          _ ≤ 2 ^ 20 * (N : ℝ) := by linarith [hC35.2.2.1]
      exact_mod_cast hr
  have hkey : ∀ v : ℝ, 0 < v → v ≤ N → ∑ n ∈ box, Bterm_pt c T (v / Pn_pt n) ≤
      KB * (N : ℝ) ^ (ε / 3) * (KC * (N : ℝ) ^ (1 + ε / 3) / T) := by
    intro v hv0 hvN
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N), ∑ n ∈ box.filter (fun n => ∏ j, n j = m),
          Bterm_pt c T (v / Pn_pt n)
        = ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
            ((box.filter (fun n => ∏ j, n j = m)).card : ℝ) * Bterm_pt c T (v / (m : ℝ)) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.sum_congr rfl (g := fun _ => Bterm_pt c T (v / (m : ℝ)))]
          · simp [Finset.sum_const, nsmul_eq_mul]
          · intro n hn
            rw [hPn n, (Finset.mem_filter.mp hn).2]
      _ ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
            (KB * (N : ℝ) ^ (ε / 3)) * Bterm_pt c T (v / (m : ℝ)) := by
          apply Finset.sum_le_sum
          intro m hm
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
          exact mul_le_mul_of_nonneg_right (hB N Nv m hNB' (Finset.mem_Icc.mp hm).2)
            (hBnn _ (div_pos hv0 (by linarith)))
      _ = KB * (N : ℝ) ^ (ε / 3) * ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
            Bterm_pt c T (v / (m : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ KB * (N : ℝ) ^ (ε / 3) * (KC * (N : ℝ) ^ (1 + ε / 3) / T) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := hC N T v hNC' hT2 hTN hv0 hvN
          simpa only [Bterm_pt] using this
  have hcoef : ∀ n ∈ box, ‖coef_pt χ n‖ ≤ KA * (N : ℝ) ^ (ε / 3) := by
    intro n hn
    exact hA N q χ Nv n hNA' hC35 hn
  have hS1 := hkey u (lt_of_lt_of_le hNA hu1) hu2
  have hS2 := hkey ((N : ℝ) - A) hNA (by linarith)
  have hP : ∀ n ∈ box, 0 < Pn_pt n := fun n hn => Pn_pos_pt hn
  calc ∑ n ∈ box, ‖coef_pt χ n‖ * (Bterm_pt c T (u / Pn_pt n) +
          Bterm_pt c T (((N : ℝ) - A) / Pn_pt n))
      ≤ ∑ n ∈ box, (KA * (N : ℝ) ^ (ε / 3)) * (Bterm_pt c T (u / Pn_pt n) +
          Bterm_pt c T (((N : ℝ) - A) / Pn_pt n)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_right (hcoef n hn)
          (add_nonneg (hBnn _ (div_pos (lt_of_lt_of_le hNA hu1) (hP n hn)))
            (hBnn _ (div_pos hNA (hP n hn))))
    _ = KA * (N : ℝ) ^ (ε / 3) * (∑ n ∈ box, Bterm_pt c T (u / Pn_pt n) +
          ∑ n ∈ box, Bterm_pt c T (((N : ℝ) - A) / Pn_pt n)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ KA * (N : ℝ) ^ (ε / 3) * (2 * (KB * (N : ℝ) ^ (ε / 3) *
          (KC * (N : ℝ) ^ (1 + ε / 3) / T))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 2 * KA * KB * KC * (N : ℝ) ^ (1 + ε) / T := by
        have e : (N : ℝ) ^ (ε / 3) * ((N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (1 + ε / 3)) =
            (N : ℝ) ^ (1 + ε) := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring
        rw [← e]
        field_simp

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
