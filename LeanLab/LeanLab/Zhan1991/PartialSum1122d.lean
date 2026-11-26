/-
P0068 Zhan 1991, the step H5 of SPLIT_eq31_1122d.lean, page 264 last two displays and page 265
first display, split into three cited LEAF steps. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

The definitions `Psum`, `Vline` and the target `PartialSumLemma1` are copied from
SPLIT_eq31_1122d.lean with the suffix `_ps`, character for character apart from the names.
Falsity check: the statement looks true. `Psum (N - A) = 0` and `Vline (N - A) = 0`, so the
boundary terms of the partial summation vanish at `u = N - A`; the approximation error contributes
`E` at `u = N` and `2π|λ| A E` from the integral; the inner integral has `G = u^{-1/2}` with
`G ≤ (N - A)^{-1/2} ≤ 2 N^{-1/2}`, and `G/F'` with `F' = t/(2πu) + λ` changes monotonicity only at
`u = t/(2πλ)`, so Lemma 1 applies on at most two pieces, and the trivial bound `A (N-A)^{-1/2}`
covers the case `min_u |t + 2πλu| = 0`.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-- The partial sum (3.2), page 263: `Σ_{N-A<n≤u} Λ(n) χ(n)`. -/
def Psum_ps {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (Λ n : ℂ) * χ n

/-- The line integral of (3.4), page 264, on `Re s = σ`, written in `t` with `s = σ + it`:
`(1/2πi) ∫_{σ-iT}^{σ+iT} F(s,χ) (u^s - (N-A)^s) s⁻¹ ds`. -/
def Vline_ps {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A σ T u : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fprod Nv χ ((σ : ℂ) + t * Complex.I) *
    (((u : ℂ) ^ ((σ : ℂ) + t * Complex.I) - (((N : ℝ) - A : ℝ) : ℂ) ^ ((σ : ℂ) + t * Complex.I))
      / ((σ : ℂ) + t * Complex.I))


/-- Partial summation and Lemma 1, page 264 last two displays and page 265 first display: if the
partial sums (3.2) agree with a combination of the line integrals on `Re s = 1/2` up to `E` on
`[N-A, N]`, then `Σ Λ(n)χ(n)e(nλ) ≪ N^{-1/2} Σ |c_i| ∫ min(A, N/min_u |t+2πλu|) |F_i| dt
+ (1 + 2π|λ|A) E`. -/
def PartialSumLemma1_ps : Prop :=
  ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (κ : Type) (ι : Finset κ) (Nf : κ → Fin 20 → ℝ) (c : κ → ℂ) (E : ℝ),
    N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    (∀ u : ℝ, (N : ℝ) - A ≤ u → u ≤ N →
      ‖Psum_ps χ N A u - ∑ i ∈ ι, c i * Vline_ps (Nf i) χ N A (1 / 2) T u‖ ≤ E) →
    ‖Schi χ lam N A‖ ≤ K * (N : ℝ) ^ (-(1 / 2) : ℝ) * (∑ i ∈ ι, ‖c i‖ *
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod (Nf i) χ (1 / 2 + t * Complex.I)‖)
      + (1 + 2 * π * |lam| * A) * E


/-! ### The LEAF steps -/

/-- Step S1 and the first half of S2, page 264, the display after "Hence": partial summation of
`Σ Λ(n)χ(n)e(nλ)` against `e(λu)` over `N - A < u ≤ N`, the replacement of `Psum` by the
combination `Σ c_i Vline_i` at cost `E + 2π|λ| A E`, and integration by parts back, using
`Vline_i (N - A) = 0`. -/
def AbelApprox_ps : Prop :=
  ∃ N₀ : ℝ, ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (κ : Type) (ι : Finset κ) (Nf : κ → Fin 20 → ℝ) (c : κ → ℂ) (E : ℝ),
    N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    (∀ u : ℝ, (N : ℝ) - A ≤ u → u ≤ N →
      ‖Psum_ps χ N A u - ∑ i ∈ ι, c i * Vline_ps (Nf i) χ N A (1 / 2) T u‖ ≤ E) →
    ‖Schi χ lam N A - ∑ i ∈ ι, c i * ∫ u in ((N : ℝ) - A)..N,
        deriv (fun v => Vline_ps (Nf i) χ N A (1 / 2) T v) u * ee (lam * u)‖
      ≤ (1 + 2 * π * |lam| * A) * E

/-- Step S2 second half and S3, page 264 the display after "The inner integral above can be
estimated by Lemma 1" and page 265 first display: `∂_u Vline = (1/2π) ∫ F(s) u^{s-1} dt` on
`Re s = 1/2`, Fubini, and Lemma 1 for `∫_{N-A}^N u^{-1/2} e(t log u/2π + λu) du`. -/
def InnerBound_ps : Prop :=
  ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Nv : Fin 20 → ℝ), N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    ‖∫ u in ((N : ℝ) - A)..N, deriv (fun v => Vline_ps Nv χ N A (1 / 2) T v) u * ee (lam * u)‖
      ≤ K * (N : ℝ) ^ (-(1 / 2) : ℝ) *
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖

 /-- Step S1, page 264, the display after "Hence": Abel summation of `Σ_{N-A<n≤N} Λ(n)χ(n)e(nλ)`
against `e(λu)`, `= Psum(N)e(λN) - ∫_{N-A}^N Psum(u) 2πiλ e(λu) du`, using `Psum(N-A) = 0`. -/
def AbelSum_ps : Prop :=
  ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ A → A ≤ N →
    IntervalIntegrable (fun u => Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u)))
      MeasureTheory.volume ((N : ℝ) - A) N ∧
    Schi χ lam N A = Psum_ps χ N A N * ee (lam * N)
      - ∫ u in ((N : ℝ) - A)..N, Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u))

/-- Step S2 first half, page 264, the display after "Hence": integration by parts back for the
line integral, `Vline(N)e(λN) - ∫ Vline(u) 2πiλ e(λu) du = ∫ ∂_u Vline(u) e(λu) du`, using
`Vline(N - A) = 0`. -/
def ByParts_ps : Prop :=
  ∃ N₀ : ℝ, ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Nv : Fin 20 → ℝ), N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    IntervalIntegrable (fun u => Vline_ps Nv χ N A (1 / 2) T u *
        (2 * π * Complex.I * lam * ee (lam * u))) MeasureTheory.volume ((N : ℝ) - A) N ∧
    Vline_ps Nv χ N A (1 / 2) T N * ee (lam * N)
      - ∫ u in ((N : ℝ) - A)..N, Vline_ps Nv χ N A (1 / 2) T u *
          (2 * π * Complex.I * lam * ee (lam * u))
      = ∫ u in ((N : ℝ) - A)..N,
          deriv (fun v => Vline_ps Nv χ N A (1 / 2) T v) u * ee (lam * u)

/-! ### Private helpers for step S1 (Abel summation)

`Psum_ps` is the partial sum of `a n = Λ n χ n` over `N - A < n ≤ u`, so
`Schi = Σ_{N-A<n≤N} a n e(nλ)` is Abel summation of that partial sum against `u ↦ e(λu)`.
Mathlib's `sum_mul_eq_sub_sub_integral_mul` supplies the summation by parts; the work here is
identifying its sum over `Ioc ⌊N-A⌋₊ N` with `shortWin N A` and its partial sums with `Psum_ps`. -/

private lemma ee_hasDerivAt_ps (lam : ℝ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => ee (lam * v)) (2 * π * Complex.I * lam * ee (lam * u)) u := by
  have h1 : HasDerivAt (fun v : ℝ => ((lam * v : ℝ) : ℂ)) (lam : ℂ) u := by
    simpa using ((hasDerivAt_id u).const_mul lam).ofReal_comp
  have h2 := h1.const_mul (2 * π * Complex.I)
  have h3 := h2.cexp
  have hval : Complex.exp (2 * π * Complex.I * ((lam * u : ℝ) : ℂ)) *
      (2 * π * Complex.I * ↑lam) = 2 * π * Complex.I * lam * ee (lam * u) := by
    rw [ee]; ring
  rw [hval] at h3
  exact h3

private lemma continuous_ee_ps (lam : ℝ) : Continuous (fun u : ℝ => ee (lam * u)) := by
  unfold ee
  fun_prop

private lemma sum_Icc_zero_ps {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (A : ℝ) (m : ℕ)
    (hm : (0 : ℝ) ≤ (N : ℝ) - A) :
    (∑ k ∈ Finset.Icc 0 m, (if (N : ℝ) - A < (k : ℝ) then (Λ k : ℂ) * χ k else 0))
      = ∑ k ∈ (Finset.Icc 1 m).filter (fun k : ℕ => (N : ℝ) - A < k), (Λ k : ℂ) * χ k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hk⟩, hP⟩
    have hk1 : 1 ≤ k := by
      have : (0 : ℝ) < (k : ℝ) := lt_of_le_of_lt hm hP
      exact_mod_cast this
    exact ⟨⟨hk1, hk⟩, hP⟩
  · rintro ⟨⟨h1, hk⟩, hP⟩
    exact ⟨⟨by omega, hk⟩, hP⟩

private lemma shortWin_eq_Ioc_ps (N : ℕ) (A : ℝ) :
    Finset.Ioc ⌊(N : ℝ) - A⌋₊ N = shortWin N A := by
  ext n
  simp only [shortWin, Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (⌊(N : ℝ) - A⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h1
    refine ⟨⟨by omega, h2⟩, lt_of_lt_of_le (Nat.lt_floor_add_one ((N : ℝ) - A)) h1'⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, h2⟩
    exact (Nat.floor_lt' (by omega : n ≠ 0)).mpr h3

/-- LEAF: page 264, the display after "Hence", step S1: Abel summation
`Σ_{N-A<n≤N} Λ(n)χ(n)e(nλ) = Psum(N)e(λN) - ∫_{N-A}^N Psum(u) 2πiλ e(λu) du`. Class EASY. -/
theorem abelSum_leaf_ps : AbelSum_ps := by
  intro N A lam q χ hA1 hAN
  classical
  have ha : (0 : ℝ) ≤ (N : ℝ) - A := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  set c : ℕ → ℂ := fun n => if (N : ℝ) - A < n then (Λ n : ℂ) * χ n else 0 with hc
  set f : ℝ → ℂ := fun u => ee (lam * u) with hf
  have hf_diff : ∀ t ∈ Set.Icc ((N : ℝ) - A) (N : ℝ), DifferentiableAt ℝ f t := by
    intro t _
    have : DifferentiableAt ℝ (fun v : ℝ => ee (lam * v)) t :=
      (ee_hasDerivAt_ps lam t).differentiableAt
    simpa only [hf] using this
  have hderiv_eq : deriv f = fun u : ℝ => 2 * π * Complex.I * lam * ee (lam * u) := by
    funext u
    have : deriv (fun v : ℝ => ee (lam * v)) u = 2 * π * Complex.I * lam * ee (lam * u) :=
      (ee_hasDerivAt_ps lam u).deriv
    simpa only [hf] using this
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc ((N : ℝ) - A) (N : ℝ)) := by
    rw [hderiv_eq]
    exact ((continuous_ee_ps lam).const_mul (2 * π * Complex.I * lam)).continuousOn.integrableOn_Icc
  have hab_le : (N : ℝ) - A ≤ (N : ℝ) := by linarith
  have habel := sum_mul_eq_sub_sub_integral_mul c ha hab_le hf_diff hf_int
  -- the sum over `Ioc ⌊N-A⌋₊ N` is `Schi`
  have hLHS : (∑ k ∈ Finset.Ioc ⌊(N : ℝ) - A⌋₊ ⌊(N : ℝ)⌋₊, f k * c k) = Schi χ lam N A := by
    rw [Nat.floor_natCast, shortWin_eq_Ioc_ps N A]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (N : ℝ) - A < (n : ℝ) := (Finset.mem_filter.mp hn).2
    have hfn : f n = ee (lam * (n : ℝ)) := by simp only [hf]
    rw [hfn, show lam * (n : ℝ) = (n : ℝ) * lam by ring]
    simp only [hc, if_pos hn']
    ring
  -- the two partial sums
  have hsumN : (∑ k ∈ Finset.Icc 0 ⌊(N : ℝ)⌋₊, c k) = Psum_ps χ N A N := by
    simp only [hc, Psum_ps, Nat.floor_natCast]
    exact sum_Icc_zero_ps χ N A N ha
  have hsumA : (∑ k ∈ Finset.Icc 0 ⌊(N : ℝ) - A⌋₊, c k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk2 : (k : ℝ) ≤ (N : ℝ) - A := by
      have h1 : (k : ℝ) ≤ (⌊(N : ℝ) - A⌋₊ : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hk).2
      have h2 := Nat.floor_le ha
      linarith
    simp only [hc]
    rw [if_neg (by linarith)]
  -- the integral
  have hPsum_eq : ∀ t ∈ Set.Icc ((N : ℝ) - A) (N : ℝ),
      Psum_ps χ N A t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
    intro t _
    rw [Psum_ps, ← sum_Icc_zero_ps χ N A ⌊t⌋₊ ha]
  have hInt : (∫ t in Set.Ioc ((N : ℝ) - A) (N : ℝ),
        deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      = ∫ u in ((N : ℝ) - A)..(N : ℝ),
          Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u)) := by
    rw [intervalIntegral.integral_of_le hab_le]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hd : deriv f t = 2 * π * Complex.I * lam * ee (lam * t) := by
      rw [hderiv_eq]
    rw [hd, hPsum_eq t ⟨ht.1.le, ht.2⟩]
    ring
  constructor
  · -- interval integrability
    have hint : MeasureTheory.IntegrableOn (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        (Set.Icc ((N : ℝ) - A) (N : ℝ)) :=
      integrableOn_mul_sum_Icc c ha hf_int
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab_le]
    refine hint.congr_fun (fun t ht => ?_) measurableSet_Icc
    have hd : deriv f t = 2 * π * Complex.I * lam * ee (lam * t) := by rw [hderiv_eq]
    show deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
      = Psum_ps χ N A t * (2 * π * Complex.I * lam * ee (lam * t))
    rw [hd, hPsum_eq t ht]
    ring
  · -- the identity
    rw [← hLHS, habel, hsumN, hsumA, hInt]
    simp only [mul_zero, sub_zero, hf]
    ring

/-! ### Private helpers for step S2 (the line integral `Vline_ps` in `u`)

`Vline_ps u` is `(1/2π) ∫_t F(1/2+it) ((u^s - c^s)/s) dt` with `c = N - A`; its derivative in `u`
is `(1/2π) ∫_t F(1/2+it) u^{s-1} dt`, by differentiation under the integral sign, and it vanishes
at `u = c`. -/

private lemma Fprod_continuous_ps {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) := by
  unfold Fprod fj
  refine continuous_finsetProd _ fun j _ => ?_
  refine continuous_finsetSum _ fun n hn => ?_
  have hn1 : 1 ≤ n := by
    simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.1
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

private lemma continuous_cpow_affine_ps (x : ℝ) (hx : x ≠ 0) :
    Continuous (fun t : ℝ => (x : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx))

private lemma continuous_cpow_affine_sub_ps (x : ℝ) (hx : x ≠ 0) :
    Continuous (fun t : ℝ => (x : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx))

private lemma cpow_half_ne_zero_ps (t : ℝ) : (((1 / 2 : ℝ) : ℂ) + t * Complex.I) ≠ 0 := by
  intro h
  have hre : ((((1 / 2 : ℝ) : ℂ) + t * Complex.I)).re = 1 / 2 := by simp
  rw [h] at hre
  norm_num at hre

/-- The derivative in `u` of `(u^s - c^s)/s` with `Re s = 1/2`. -/
private lemma cpow_quot_hasDerivAt_ps (c t x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ =>
        (((y : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I)
          - ((c : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I)))
        / (((1 / 2 : ℝ) : ℂ) + t * Complex.I)))
      ((x : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)) x := by
  have hsne := cpow_half_ne_zero_ps t
  have h1 := ((hasDerivAt_ofReal_cpow_const hx hsne).sub_const
    ((c : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I))).div_const
      (((1 / 2 : ℝ) : ℂ) + t * Complex.I)
  convert h1 using 1
  field_simp

/-- Differentiation under the integral sign: `Vline_ps · (1/2) T` has derivative
`(1/2π) ∫_t F(1/2+it) u^{s-1} dt` at every `u ≥ N - A > 0`. -/
private lemma vline_ps_hasDerivAt {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q)
    (N : ℕ) (A T : ℝ) (hN : 2 ≤ N) (hA1 : 1 ≤ A) (hA2 : A ≤ (N : ℝ) ^ (2 / 3 : ℝ))
    {u : ℝ} (hu : ((N : ℝ) - A) / 2 < u) :
    HasDerivAt (fun v : ℝ => Vline_ps Nv χ N A (1 / 2) T v)
      ((1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
          ((u : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1))) u := by
  classical
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show (1 : ℕ) < N by omega)
  have hA_le : A ≤ (N : ℝ) := by
    refine le_trans hA2 ?_
    calc (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hlt : A < (N : ℝ) := by
    refine lt_of_le_of_lt hA2 ?_
    have h1 : (N : ℝ) ^ (2 / 3 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)
    rwa [Real.rpow_one] at h1
  have hcpos : 0 < (N : ℝ) - A := by linarith
  set c : ℝ := (N : ℝ) - A with hcdef
  set Ft : ℝ → ℂ := fun t => Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) with hFt
  set F : ℝ → ℝ → ℂ := fun x t => Ft t *
    (((x : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I)
        - ((c : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I)))
      / (((1 / 2 : ℝ) : ℂ) + t * Complex.I)) with hF
  set F' : ℝ → ℝ → ℂ := fun x t =>
    Ft t * ((x : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)) with hF'
  have hFt_cont : Continuous Ft := Fprod_continuous_ps Nv χ
  have hxpos_of : ∀ x ∈ Set.Ioi (c / 2), (0 : ℝ) < x := fun x hx => lt_trans (by linarith) hx
  have hcont_int : ∀ x ∈ Set.Ioi (c / 2), Continuous (fun t : ℝ => F x t) := by
    intro x hx
    have hx0 : x ≠ 0 := (hxpos_of x hx).ne'
    have hc0 : c ≠ 0 := hcpos.ne'
    rw [hF]
    exact hFt_cont.mul (((continuous_cpow_affine_ps x hx0).sub
      (continuous_cpow_affine_ps c hc0)).div (by fun_prop) (fun t => cpow_half_ne_zero_ps t))
  have hcont_int' : ∀ x ∈ Set.Ioi (c / 2), Continuous (fun t : ℝ => F' x t) := by
    intro x hx
    have hx0 : x ≠ 0 := (hxpos_of x hx).ne'
    rw [hF']
    exact hFt_cont.mul (continuous_cpow_affine_sub_ps x hx0)
  have hupos : (c / 2 : ℝ) < u := by rw [hcdef]; exact hu
  have hupos_mem : u ∈ Set.Ioi (c / 2) := hupos
  have hs_mem : Set.Ioi (c / 2) ∈ nhds u := isOpen_Ioi.mem_nhds hupos
  have hF_meas : ∀ᶠ x in nhds u,
      MeasureTheory.AEStronglyMeasurable (F x) (MeasureTheory.volume.restrict (Set.uIoc (-T) T)) := by
    filter_upwards [hs_mem] with x hx
    exact (hcont_int x hx).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F u) MeasureTheory.volume (-T) T :=
    (hcont_int u hupos_mem).intervalIntegrable (-T) T
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' u)
      (MeasureTheory.volume.restrict (Set.uIoc (-T) T)) :=
    (hcont_int' u hupos_mem).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ∈ Set.uIoc (-T) T →
      ∀ x ∈ Set.Ioi (c / 2), ‖F' x t‖ ≤ ‖Ft t‖ * (c / 2) ^ (-(1 / 2) : ℝ) := by
    refine Filter.Eventually.of_forall fun t _ x hx => ?_
    have hxpos : (0 : ℝ) < x := hxpos_of x hx
    have hnorm : ‖(x : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)‖
        = x ^ (-(1 / 2) : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      norm_num
    rw [hF', norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (le_of_lt hx) (by norm_num))
      (norm_nonneg _)
  have hbound_int : IntervalIntegrable (fun t : ℝ => ‖Ft t‖ * (c / 2) ^ (-(1 / 2) : ℝ))
      MeasureTheory.volume (-T) T :=
    (hFt_cont.norm.mul_const _).intervalIntegrable (-T) T
  have hdiff : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ∈ Set.uIoc (-T) T →
      ∀ x ∈ Set.Ioi (c / 2), HasDerivAt (fun x => F x t) (F' x t) x := by
    refine Filter.Eventually.of_forall fun t _ x hx => ?_
    have hxpos : (0 : ℝ) < x := hxpos_of x hx
    rw [hF, hF']
    exact (cpow_quot_hasDerivAt_ps c t x hxpos.ne').const_mul (Ft t)
  obtain ⟨-, hderiv⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := u) (s := Set.Ioi (c / 2)) (a := -T) (b := T)
    (bound := fun t => ‖Ft t‖ * (c / 2) ^ (-(1 / 2) : ℝ))
    hs_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff
  have hshape : (fun v : ℝ => Vline_ps Nv χ N A (1 / 2) T v)
      = fun v : ℝ => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, F v t := by
    funext v
    simp only [Vline_ps, hF, hFt, hcdef]
  rw [hshape]
  have hfin := hderiv.const_mul (1 / (2 * π) : ℂ)
  have hF'_apply : ∀ t : ℝ, F' u t = Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
      ((u : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)) := by
    intro t; simp only [hF', hFt]
  simp only [hF'_apply] at hfin
  exact hfin

/-- The line integral vanishes at the lower end `u = N - A`. -/
private lemma vline_ps_self {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q)
    (N : ℕ) (A T : ℝ) :
    Vline_ps Nv χ N A (1 / 2) T ((N : ℝ) - A) = 0 := by
  simp only [Vline_ps, sub_self, zero_div, mul_zero, intervalIntegral.integral_zero, mul_zero]

/-- The `u`-integral `∫_t F(1/2+it) u^{s-1} dt` is continuous in `u` for `u > N - A`. -/
private lemma u'_continuousOn {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q)
    (N : ℕ) (A T : ℝ) (hcpos : 0 < (N : ℝ) - A) :
    ContinuousOn (fun u : ℝ => ∫ t in (-T)..T,
      Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
        ((u : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1))) (Set.Ioi (((N : ℝ) - A) / 2)) := by
  classical
  set c : ℝ := ((N : ℝ) - A) / 2 with hcdef
  have hcpos' : 0 < c := by rw [hcdef]; linarith
  set Ft : ℝ → ℂ := fun t => Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) with hFt
  have hFt_cont : Continuous Ft := Fprod_continuous_ps Nv χ
  have hbound : ∀ x : ↥(Set.Ioi c), ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ∈ Set.uIoc (-T) T →
      ‖Ft t * (((x : ℝ) : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1))‖
        ≤ ‖Ft t‖ * c ^ (-(1 / 2) : ℝ) := by
    intro x
    refine Filter.Eventually.of_forall fun t _ => ?_
    have hxpos : (c : ℝ) < (x : ℝ) := x.2
    have hnorm : ‖(((x : ℝ)) : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)‖
        = (x : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans hcpos' hxpos)]
      norm_num
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hcpos' (le_of_lt hxpos) (by norm_num)) (norm_nonneg _)
  have hmain : Continuous (fun x : ↥(Set.Ioi c) => ∫ t in (-T)..T,
      Ft t * (((x : ℝ) : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1))) := by
    refine intervalIntegral.continuous_of_dominated_interval
      (a := -T) (b := T)
      (F := fun (x : ↥(Set.Ioi c)) (t : ℝ) =>
        Ft t * (((x : ℝ) : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)))
      (bound := fun t : ℝ => ‖Ft t‖ * c ^ (-(1 / 2) : ℝ)) ?_ hbound ?_ ?_
    · intro x
      have hx0 : (x : ℝ) ≠ 0 := (ne_of_gt (lt_trans hcpos' x.2))
      exact (hFt_cont.mul (continuous_cpow_affine_sub_ps (x : ℝ) hx0)).aestronglyMeasurable
    · exact ((hFt_cont.norm.mul_const _).continuousOn.mono (Set.subset_univ _)).intervalIntegrable
    · refine Filter.Eventually.of_forall fun t _ => ?_
      exact continuous_const.mul (Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.2 (lt_trans hcpos' x.2)))
  exact continuousOn_iff_continuous_domRestrict.mpr hmain

/-- LEAF: page 264, the display after "Hence", step S2 first half: integration by parts for
the line integral `Vline` on `Re s = 1/2`, which is differentiable in `u > 0` and vanishes at
`u = N - A`. Class MEDIUM. -/
theorem byParts_leaf_ps : ByParts_ps := by
  refine ⟨2, ?_⟩
  intro N A lam T q χ Nv hN hA1 hA2 hT
  classical
  have hNat : (2 : ℕ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hlt : A < (N : ℝ) := by
    refine lt_of_le_of_lt hA2 ?_
    have h1 : (N : ℝ) ^ (2 / 3 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)
    rwa [Real.rpow_one] at h1
  have hcpos : (0 : ℝ) < (N : ℝ) - A := by linarith
  set c : ℝ := (N : ℝ) - A with hcdef
  set W : ℝ → ℂ := fun u => Vline_ps Nv χ N A (1 / 2) T u with hW
  set u' : ℝ → ℂ := fun u => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
    Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
      ((u : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) - 1)) with hu'
  set v' : ℝ → ℂ := fun u => 2 * π * Complex.I * lam * ee (lam * u) with hv'
  have hcN : c ≤ (N : ℝ) := by rw [hcdef]; linarith
  have hmono : Set.uIcc c N ⊆ Set.Ioi (c / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hcN] at hx
    exact lt_of_lt_of_le (by linarith) hx.1
  have hW_diff : DifferentiableOn ℝ W (Set.Ioi (c / 2)) := by
    intro u hu
    rw [hW]
    exact (vline_ps_hasDerivAt Nv χ N A T hNat hA1 hA2 (show c / 2 < u from hu)
      ).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ Set.uIcc c N, HasDerivWithinAt W (u' u) (Set.uIcc c N) u := by
    intro u hu
    rw [Set.uIcc_of_le hcN] at hu ⊢
    rw [hW, hu']
    exact (vline_ps_hasDerivAt Nv χ N A T hNat hA1 hA2 (by linarith [hu.1])).hasDerivWithinAt
  have hvderiv : ∀ u ∈ Set.uIcc c N,
      HasDerivWithinAt (fun v : ℝ => ee (lam * v)) (v' u) (Set.uIcc c N) u := by
    intro u _
    rw [hv']
    exact (ee_hasDerivAt_ps lam u).hasDerivWithinAt
  have hu'int : IntervalIntegrable u' MeasureTheory.volume c N := by
    rw [hu']
    exact ((u'_continuousOn Nv χ N A T hcpos).mono hmono).const_mul (1 / (2 * π) : ℂ)
      |>.intervalIntegrable
  have hv'int : IntervalIntegrable v' MeasureTheory.volume c N := by
    rw [hv']
    exact ((continuous_const.mul (continuous_ee_ps lam)).continuousOn.mono
      (Set.subset_univ _)).intervalIntegrable
  have hW_int : IntervalIntegrable (fun u => W u * v' u) MeasureTheory.volume c N := by
    have hcont : ContinuousOn (fun u => W u * v' u) (Set.uIcc c N) := by
      refine (hW_diff.continuousOn.mono hmono).mul ?_
      rw [hv']
      exact (continuous_const.mul (continuous_ee_ps lam)).continuousOn
    exact hcont.intervalIntegrable
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (a := c) (b := (N : ℝ)) (u := W) (v := fun v : ℝ => ee (lam * v))
    (u' := u') (v' := v') hderiv hvderiv hu'int hv'int
  have hsplit := intervalIntegral.integral_add
    (hu'int.mul_continuousOn (continuous_ee_ps lam).continuousOn) hW_int
  have hWc : W c = 0 := by
    rw [hW]
    exact vline_ps_self Nv χ N A T
  rw [hWc, zero_mul, sub_zero] at hibp
  have hcongr : (∫ x in c..N, deriv W x * ee (lam * x))
      = ∫ x in c..N, u' x * ee (lam * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx' : x ∈ Set.Icc c N := by
      have h1 : x ∈ Set.uIcc c (N : ℝ) := hx
      rw [Set.uIcc_of_le hcN] at h1
      exact h1
    have hd : HasDerivAt W (u' x) x := by
      rw [hW, hu']
      exact vline_ps_hasDerivAt Nv χ N A T hNat hA1 hA2 (by linarith [hx'.1])
    rw [hd.deriv]
  have hWN : W N = Vline_ps Nv χ N A (1 / 2) T N := by rw [hW]
  have hWv : (∫ u in c..N, W u * v' u)
      = ∫ u in c..N, Vline_ps Nv χ N A (1 / 2) T u *
          (2 * π * Complex.I * lam * ee (lam * u)) := by
    rw [hW, hv']
  have hdW : (∫ u in c..N, deriv W u * ee (lam * u))
      = ∫ u in c..N, deriv (fun v : ℝ => Vline_ps Nv χ N A (1 / 2) T v) u * ee (lam * u) := by
    rw [hW]
  rw [hsplit] at hibp
  have hkey : (∫ x in c..N, u' x * ee (lam * x))
      = Vline_ps Nv χ N A (1 / 2) T N * ee (lam * N)
        - ∫ u in c..N, Vline_ps Nv χ N A (1 / 2) T u *
            (2 * π * Complex.I * lam * ee (lam * u)) := by
    rw [← hWN, ← hWv]
    linear_combination hibp
  constructor
  · show IntervalIntegrable (fun u => W u * v' u) MeasureTheory.volume c N
    exact hW_int
  · show Vline_ps Nv χ N A (1 / 2) T N * ee (lam * N)
        - ∫ u in c..N, Vline_ps Nv χ N A (1 / 2) T u *
            (2 * π * Complex.I * lam * ee (lam * u))
        = ∫ u in c..N, deriv (fun v : ℝ => Vline_ps Nv χ N A (1 / 2) T v) u * ee (lam * u)
    rw [← hdW, hcongr]
    exact hkey.symm

theorem norm_ee_ps (x : ℝ) : ‖ee x‖ = 1 := by
  simp [ee, Complex.norm_exp]

theorem combine_ps {κ : Type} (ι : Finset κ) (a b lam E : ℝ) (hab : a ≤ b) (P : ℝ → ℂ) (V : κ → ℝ → ℂ)
    (c : κ → ℂ) (D : κ → ℂ) (S : ℂ)
    (hS : S = P b * ee (lam * b) - ∫ u in a..b, P u * (2 * π * Complex.I * lam * ee (lam * u)))
    (hPi : IntervalIntegrable (fun u => P u * (2 * π * Complex.I * lam * ee (lam * u))) MeasureTheory.volume a b)
    (hV : ∀ i ∈ ι, IntervalIntegrable (fun u => V i u * (2 * π * Complex.I * lam * ee (lam * u))) MeasureTheory.volume a b ∧
      V i b * ee (lam * b) - ∫ u in a..b, V i u * (2 * π * Complex.I * lam * ee (lam * u)) = D i)
    (hE : ∀ u, a ≤ u → u ≤ b → ‖P u - ∑ i ∈ ι, c i * V i u‖ ≤ E) :
    ‖S - ∑ i ∈ ι, c i * D i‖ ≤ (1 + 2 * π * |lam| * (b - a)) * E := by
  set w : ℝ → ℂ := fun u => 2 * π * Complex.I * lam * ee (lam * u) with hw
  have hsum : ∑ i ∈ ι, c i * D i = (∑ i ∈ ι, c i * V i b) * ee (lam * b)
      - ∫ u in a..b, (∑ i ∈ ι, c i * V i u) * w u := by
    have hint : ∀ i ∈ ι, IntervalIntegrable (fun u => c i * (V i u * w u)) MeasureTheory.volume a b :=
      fun i hi => (hV i hi).1.const_mul (c i)
    have : (fun u => (∑ i ∈ ι, c i * V i u) * w u) = fun u => ∑ i ∈ ι, c i * (V i u * w u) := by
      funext u; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, intervalIntegral.integral_finsetSum hint, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [intervalIntegral.integral_const_mul, ← (hV i hi).2]; ring
  have hEn : 0 ≤ E := le_trans (norm_nonneg _) (hE b hab le_rfl)
  have hVi : IntervalIntegrable (fun u => (∑ i ∈ ι, c i * V i u) * w u) MeasureTheory.volume a b := by
    have : (fun u => (∑ i ∈ ι, c i * V i u) * w u) = fun u => ∑ i ∈ ι, c i * (V i u * w u) := by
      funext u; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have h := IntervalIntegrable.sum ι fun i hi => (hV i hi).1.const_mul (c i)
    convert h using 1
    funext u; simp [Finset.sum_apply, hw]
  have hdiff : S - ∑ i ∈ ι, c i * D i = (P b - ∑ i ∈ ι, c i * V i b) * ee (lam * b)
      - ∫ u in a..b, (P u - ∑ i ∈ ι, c i * V i u) * w u := by
    rw [hS, hsum]
    have : (fun u => (P u - ∑ i ∈ ι, c i * V i u) * w u) = fun u => P u * w u - (∑ i ∈ ι, c i * V i u) * w u := by
      funext u; ring
    rw [this, intervalIntegral.integral_sub hPi hVi]; ring
  have hint : ‖∫ u in a..b, (P u - ∑ i ∈ ι, c i * V i u) * w u‖ ≤ E * (2 * π * |lam|) * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [Set.uIoc_of_le hab] at hu
    rw [norm_mul, hw]
    simp only
    rw [norm_mul, norm_ee_ps, mul_one]
    have : ‖(2 * π * Complex.I * lam : ℂ)‖ = 2 * π * |lam| := by
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    rw [this]
    exact mul_le_mul_of_nonneg_right (hE u hu.1.le hu.2) (by positivity)
  rw [hdiff]
  calc _ ≤ ‖(P b - ∑ i ∈ ι, c i * V i b) * ee (lam * b)‖ + ‖∫ u in a..b, (P u - ∑ i ∈ ι, c i * V i u) * w u‖ :=
        norm_sub_le _ _
    _ ≤ E + E * (2 * π * |lam|) * |b - a| := by
        rw [norm_mul, norm_ee_ps, mul_one]; exact add_le_add (hE b hab le_rfl) hint
    _ = (1 + 2 * π * |lam| * (b - a)) * E := by rw [abs_of_nonneg (show (0:ℝ) ≤ b - a by linarith)]; ring

/-- PROVED from S1 and S2 first half: the approximation step `AbelApprox_ps`. -/
theorem abelApprox_of_parts_ps (hS : AbelSum_ps) (hBP : ByParts_ps) : AbelApprox_ps := by
  obtain ⟨N₁, hBP⟩ := hBP
  refine ⟨max N₁ 1, ?_⟩
  intro N A lam T q χ κ ι Nf c E hN hA1 hA2 hT hE
  have hN1 : (1 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hAN : A ≤ N := by
    refine le_trans hA2 ?_
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  obtain ⟨hPi, hSeq⟩ := hS N A lam q χ hA1 hAN
  have h := combine_ps ι ((N : ℝ) - A) N lam E (by linarith) (Psum_ps χ N A)
    (fun i => Vline_ps (Nf i) χ N A (1 / 2) T) c
    (fun i => ∫ u in ((N : ℝ) - A)..N,
      deriv (fun v => Vline_ps (Nf i) χ N A (1 / 2) T v) u * ee (lam * u))
    (Schi χ lam N A) hSeq hPi
    (fun i _ => hBP N A lam T q χ (Nf i) (le_trans (le_max_left _ _) hN) hA1 hA2 hT) hE
  rwa [show (N : ℝ) - ((N : ℝ) - A) = A by ring] at h

/-- LEAF: page 264, the display after "The inner integral above can be estimated by Lemma 1",
and page 265 first display: differentiation of `Vline` in `u`, Fubini over `t ∈ [-T, T]` and
`u ∈ [N-A, N]`, and Lemma 1 on the at most two pieces where `G/F'` is monotone, giving
`≪ N^{-1/2} wt38`. Class MEDIUM. -/
theorem innerBound_leaf_ps (h1 : Lemma1) : InnerBound_ps := by
  sorry

/-- PROVED from the approximation step and the inner bound: the target `PartialSumLemma1`,
copied as `PartialSumLemma1_ps`. -/
theorem partialSum_of_approx_ps (hA : AbelApprox_ps) (hB : Lemma1 → InnerBound_ps)
    (h1 : Lemma1) : PartialSumLemma1_ps := by
  obtain ⟨N₁, hA⟩ := hA
  obtain ⟨K, N₂, hK, hB⟩ := hB h1
  refine ⟨K, max N₁ N₂, hK, ?_⟩
  intro N A lam T q χ κ ι Nf c E hN hA1 hA2 hT hE
  have hab := hA N A lam T q χ κ ι Nf c E (le_trans (le_max_left _ _) hN) hA1 hA2 hT hE
  have hin := fun i => hB N A lam T q χ (Nf i) (le_trans (le_max_right _ _) hN) hA1 hA2 hT
  set I := fun i => ∫ u in ((N : ℝ) - A)..N,
    deriv (fun v => Vline_ps (Nf i) χ N A (1 / 2) T v) u * ee (lam * u) with hI
  set J := fun i => ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod (Nf i) χ (1 / 2 + t * Complex.I)‖
    with hJ
  have hS : ‖∑ i ∈ ι, c i * I i‖ ≤ ∑ i ∈ ι, ‖c i‖ * (K * (N : ℝ) ^ (-(1 / 2) : ℝ) * J i) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hin i) (norm_nonneg _)
  have htri : ‖Schi χ lam N A‖ ≤ ‖∑ i ∈ ι, c i * I i‖ + (1 + 2 * π * |lam| * A) * E := by
    have := norm_le_insert' (Schi χ lam N A) (∑ i ∈ ι, c i * I i)
    have := norm_sub_rev (Schi χ lam N A) (∑ i ∈ ι, c i * I i)
    have h3 := norm_sub_norm_le (Schi χ lam N A) (∑ i ∈ ι, c i * I i)
    linarith
  calc ‖Schi χ lam N A‖ ≤ ‖∑ i ∈ ι, c i * I i‖ + (1 + 2 * π * |lam| * A) * E := htri
    _ ≤ ∑ i ∈ ι, ‖c i‖ * (K * (N : ℝ) ^ (-(1 / 2) : ℝ) * J i)
          + (1 + 2 * π * |lam| * A) * E := by linarith
    _ = K * (N : ℝ) ^ (-(1 / 2) : ℝ) * (∑ i ∈ ι, ‖c i‖ * J i)
          + (1 + 2 * π * |lam| * A) * E := by
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring

/-- PROVED from the three LEAF Props and Lemma 1: the target `PartialSumLemma1_ps`. -/
theorem partialSum_of_parts_ps (hS : AbelSum_ps) (hBP : ByParts_ps)
    (hB : Lemma1 → InnerBound_ps) (h1 : Lemma1) : PartialSumLemma1_ps :=
  partialSum_of_approx_ps (abelApprox_of_parts_ps hS hBP) hB h1

/-- The target from the LEAF theorems and Lemma 1. -/
theorem partialSum_lemma1_ps (h1 : Lemma1) : PartialSumLemma1_ps :=
  partialSum_of_parts_ps abelSum_leaf_ps byParts_leaf_ps innerBound_leaf_ps h1

#print axioms partialSum_of_parts_ps

end

end LeanLab.Zhan1991
