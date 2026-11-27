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




private lemma ee_add_ps (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `u^{-1/2} ≤ 4 N^{-1/2}` for `N/2 ≤ u`, `N > 0`. -/
private lemma rpow_neg_half_le_ps {N : ℕ} {u : ℝ} (hN : 0 < N) (hu : (N : ℝ) / 2 ≤ u) :
    u ^ (-(1/2) : ℝ) ≤ 4 * (N : ℝ) ^ (-(1/2) : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hhalf : (0 : ℝ) < (N : ℝ) / 2 := by linarith
  have h1 : u ^ (-(1/2) : ℝ) ≤ ((N : ℝ) / 2) ^ (-(1/2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hhalf hu (by norm_num)
  have h2 : ((N : ℝ) / 2) ^ (-(1/2) : ℝ)
      = (N : ℝ) ^ (-(1/2) : ℝ) * ((1/2 : ℝ) ^ (-(1/2) : ℝ)) := by
    rw [show (N : ℝ) / 2 = (N : ℝ) * (1/2) by ring, Real.mul_rpow (le_of_lt hNpos) (by norm_num)]
  have h3 : ((1/2 : ℝ) ^ (-(1/2) : ℝ)) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
      (show (-(1:ℝ)) ≤ (-(1/2):ℝ) by norm_num)
    rw [Real.rpow_neg_one] at this
    norm_num at this ⊢
    simpa using this
  have hNpow : (0:ℝ) ≤ (N : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg (le_of_lt hNpos) _
  calc u ^ (-(1/2) : ℝ) ≤ ((N : ℝ) / 2) ^ (-(1/2) : ℝ) := h1
    _ = (N : ℝ) ^ (-(1/2) : ℝ) * ((1/2 : ℝ) ^ (-(1/2) : ℝ)) := h2
    _ ≤ (N : ℝ) ^ (-(1/2) : ℝ) * 2 := by nlinarith
    _ ≤ 4 * (N : ℝ) ^ (-(1/2) : ℝ) := by nlinarith


section mono

variable {t lam : ℝ}

/-- Derivative of `√u / (t + 2πλu)`. -/
private lemma sqrt_div_hasDerivAt_ps (t lam x : ℝ) (hx : 0 < x) (hden : t + 2*π*lam*x ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.sqrt u / (t + 2*π*lam*u))
      ((t - 2*π*lam*x) / (2*Real.sqrt x * (t + 2*π*lam*x)^2)) x := by
  have h1 := Real.hasDerivAt_sqrt hx.ne'
  have h2 : HasDerivAt (fun u : ℝ => t + 2*π*lam*u) (2*π*lam) x := by
    simpa using ((hasDerivAt_id x).const_mul (2*π*lam)).const_add t
  have h3 := h1.div h2 hden
  convert h3 using 1
  field_simp
  rw [Real.sq_sqrt hx.le]
  ring

/-- On `u > 0`, `u^{-1/2} / (t/(2πu) + λ) = 2π √u / (t + 2πλu)`. -/
private lemma phi_eq_ps (t lam u : ℝ) (hu : 0 < u) :
    u ^ (-(1/2) : ℝ) / (t / (2*π*u) + lam) = 2*π * (Real.sqrt u / (t + 2*π*lam*u)) := by
  have hu0 : u ≠ 0 := hu.ne'
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hden : t / (2*π*u) + lam = (t + 2*π*lam*u) / (2*π*u) := by
    field_simp
  have hp : u ^ (-(1/2) : ℝ) * u = Real.sqrt u := by
    have h1 : u ^ (-(1/2) : ℝ) * u ^ (1:ℝ) = Real.sqrt u := by
      rw [← Real.rpow_add hu, Real.sqrt_eq_rpow]
      norm_num
    simpa using h1
  have hnum : u ^ (-(1/2) : ℝ) * (2*π*u) = 2*π * Real.sqrt u := by
    rw [← hp]; ring
  rw [hden, div_div_eq_mul_div, hnum]
  ring

/-- Monotone case: `√u/(t+2πλu)` is nondecreasing when `t - 2πλu ≥ 0`. -/
private lemma sqrt_div_monotoneOn_ps (a b t lam : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hden : ∀ u ∈ Set.Icc a b, t + 2*π*lam*u ≠ 0)
    (hs : ∀ u ∈ Set.Icc a b, 0 ≤ t - 2*π*lam*u) :
    MonotoneOn (fun u : ℝ => Real.sqrt u / (t + 2*π*lam*u)) (Set.Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (f' := fun x => (t - 2*π*lam*x) / (2*Real.sqrt x * (t + 2*π*lam*x)^2)) ?_ ?_ ?_
  · exact Real.continuous_sqrt.continuousOn.div
      ((continuous_const.add (continuous_const.mul continuous_id')).continuousOn)
      (fun u hu => hden u hu)
  · intro x hx
    have hxa : a < x := by
      rw [interior_Icc] at hx
      exact hx.1
    have hx0 : 0 < x := lt_trans ha hxa
    exact (sqrt_div_hasDerivAt_ps t lam x hx0 (hden x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have hxa : a < x := by rw [interior_Icc] at hx; exact hx.1
    have hx0 : 0 < x := lt_trans ha hxa
    have hnum : 0 ≤ t - 2*π*lam*x := hs x hx'
    have hsq : 0 < 2*Real.sqrt x * (t + 2*π*lam*x)^2 := by
      have : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
      have : 0 < (t + 2*π*lam*x)^2 := by
        have := hden x hx'; positivity
      positivity
    exact div_nonneg hnum hsq.le

/-- Antitone case: `√u/(t+2πλu)` is nonincreasing when `t - 2πλu ≤ 0`. -/
private lemma sqrt_div_antitoneOn_ps (a b t lam : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hden : ∀ u ∈ Set.Icc a b, t + 2*π*lam*u ≠ 0)
    (hs : ∀ u ∈ Set.Icc a b, t - 2*π*lam*u ≤ 0) :
    AntitoneOn (fun u : ℝ => Real.sqrt u / (t + 2*π*lam*u)) (Set.Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
  · exact Real.continuous_sqrt.continuousOn.div
      ((continuous_const.add (continuous_const.mul continuous_id')).continuousOn)
      (fun u hu => hden u hu)
  · intro x hx
    have hx' := interior_subset hx
    have hxa : a < x := by rw [interior_Icc] at hx; exact hx.1
    have hx0 : 0 < x := lt_trans ha hxa
    exact (sqrt_div_hasDerivAt_ps t lam x hx0 (hden x hx')).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have hxa : a < x := by rw [interior_Icc] at hx; exact hx.1
    have hx0 : 0 < x := lt_trans ha hxa
    have hnum : t - 2*π*lam*x ≤ 0 := hs x hx'
    have hsq : 0 < 2*Real.sqrt x * (t + 2*π*lam*x)^2 := by
      have h1 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
      have h2 : 0 < (t + 2*π*lam*x)^2 := by
        have := hden x hx'; positivity
      positivity
    rw [(sqrt_div_hasDerivAt_ps t lam x hx0 (hden x hx')).deriv]
    exact div_nonpos_of_nonpos_of_nonneg hnum hsq.le

end mono


section piece

private lemma convex_comb_between_ps (a b X Y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    min X Y ≤ a*X + b*Y ∧ a*X + b*Y ≤ max X Y := by
  constructor
  · have hA : a * min X Y ≤ a * X := mul_le_mul_of_nonneg_left (min_le_left X Y) ha
    have hB : b * min X Y ≤ b * Y := mul_le_mul_of_nonneg_left (min_le_right X Y) hb
    have hsum : a * min X Y + b * min X Y ≤ a*X + b*Y := add_le_add hA hB
    have he : a * min X Y + b * min X Y = min X Y := by rw [← add_mul, hab, one_mul]
    linarith [hsum, he]
  · have hA : a * X ≤ a * max X Y := mul_le_mul_of_nonneg_left (le_max_left X Y) ha
    have hB : b * Y ≤ b * max X Y := mul_le_mul_of_nonneg_left (le_max_right X Y) hb
    have hsum : a*X + b*Y ≤ a * max X Y + b * max X Y := add_le_add hA hB
    have he : a * max X Y + b * max X Y = max X Y := by rw [← add_mul, hab, one_mul]
    linarith [hsum, he]

/-- Convex-combination form of an affine function: its values on `[p, q]` lie between the
endpoint values. -/
private lemma affine_between_ps (al be p q u : ℝ) (hpq : p ≤ q) (hu : p ≤ u) (hu' : u ≤ q) :
    min (al*p + be) (al*q + be) ≤ al*u + be ∧ al*u + be ≤ max (al*p + be) (al*q + be) := by
  rcases lt_or_eq_of_le hpq with hlt | heq
  · have hqp : (0:ℝ) < q - p := by linarith
    have hrepr : al*u + be = ((q-u)/(q-p)) * (al*p + be) + ((u-p)/(q-p)) * (al*q + be) := by
      field_simp
      ring
    have h1 : (0:ℝ) ≤ (q-u)/(q-p) := div_nonneg (by linarith) hqp.le
    have h2 : (0:ℝ) ≤ (u-p)/(q-p) := div_nonneg (by linarith) hqp.le
    have hs1 : (q-u)/(q-p) + (u-p)/(q-p) = 1 := by field_simp; ring
    have h := convex_comb_between_ps ((q-u)/(q-p)) ((u-p)/(q-p)) (al*p + be) (al*q + be) h1 h2 hs1
    rw [hrepr]
    exact h
  · subst heq
    have hup : u = p := le_antisymm hu' hu
    subst hup
    simp

end piece


section lem1app

/-- The inner integral over one piece where `G/F'` is monotone, by Lemma 1. -/
private lemma lemma1_piece_ps (K1 : ℝ)
    (hK1 : ∀ (a b m M : ℝ) (F F' G : ℝ → ℝ), a ≤ b → 0 < m →
      (∀ u ∈ Set.Icc a b, HasDerivAt F (F' u) u) → ContinuousOn F' (Set.Icc a b) →
      ContinuousOn G (Set.Icc a b) →
      (MonotoneOn (fun u => G u / F' u) (Set.Icc a b) ∨
        AntitoneOn (fun u => G u / F' u) (Set.Icc a b)) →
      (∀ u ∈ Set.Icc a b, m ≤ |F' u|) → (∀ u ∈ Set.Icc a b, |G u| ≤ M) →
      ‖∫ u in a..b, (G u : ℂ) * ee (F u)‖ ≤ K1 * M / m)
    (a b t lam m M : ℝ) (hab : a ≤ b) (ha : 0 < a) (hm : 0 < m) (hM : 0 ≤ M)
    (hden : ∀ u ∈ Set.Icc a b, t + 2*π*lam*u ≠ 0)
    (hsgn : (∀ u ∈ Set.Icc a b, 0 ≤ t - 2*π*lam*u) ∨ (∀ u ∈ Set.Icc a b, t - 2*π*lam*u ≤ 0))
    (hmle : ∀ u ∈ Set.Icc a b, m ≤ |t/(2*π*u) + lam|)
    (hGM : ∀ u ∈ Set.Icc a b, |u ^ (-(1/2) : ℝ)| ≤ M) :
    ‖∫ u in a..b, ((u ^ (-(1/2) : ℝ) : ℝ) : ℂ) * ee (t * Real.log u / (2*π) + lam*u)‖ ≤
      K1 * M / m := by
  have ha' : ∀ u ∈ Set.Icc a b, 0 < u := fun u hu => lt_of_lt_of_le ha hu.1
  -- the derivative of `F`
  have hF : ∀ u ∈ Set.Icc a b,
      HasDerivAt (fun v : ℝ => t * Real.log v / (2*π) + lam*v) (t/(2*π*u) + lam) u := by
    intro u hu
    have hu0 : u ≠ 0 := (ha' u hu).ne'
    have h1 : HasDerivAt (fun v : ℝ => t * Real.log v / (2*π)) (t * u⁻¹ / (2*π)) u :=
      (Real.hasDerivAt_log hu0).const_mul t |>.div_const (2*π)
    have h2 : HasDerivAt (fun v : ℝ => lam*v) lam u := by
      simpa using (hasDerivAt_id u).const_mul lam
    have h3 := h1.add h2
    convert h3 using 1
    field_simp
  have hF'c : ContinuousOn (fun u : ℝ => t/(2*π*u) + lam) (Set.Icc a b) := by
    have hne : ∀ u ∈ Set.Icc a b, 2*π*u ≠ 0 := by
      intro u hu
      have := ha' u hu
      positivity
    exact ContinuousOn.add (ContinuousOn.div continuousOn_const (by fun_prop) hne)
      continuousOn_const
  have hGc : ContinuousOn (fun u : ℝ => u ^ (-(1/2) : ℝ)) (Set.Icc a b) := by
    have h0 : ∀ u ∈ Set.Icc a b, u ≠ 0 := fun u hu => (ha' u hu).ne'
    exact ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl (h0 u hu))
  have hphi : MonotoneOn (fun u : ℝ => u ^ (-(1/2) : ℝ) / (t/(2*π*u) + lam)) (Set.Icc a b) ∨
      AntitoneOn (fun u : ℝ => u ^ (-(1/2) : ℝ) / (t/(2*π*u) + lam)) (Set.Icc a b) := by
    rcases hsgn with hs | hs
    · left
      have hg := sqrt_div_monotoneOn_ps a b t lam ha hab hden hs
      intro x hx y hy hxy
      show x ^ (-(1/2) : ℝ) / (t/(2*π*x) + lam) ≤ y ^ (-(1/2) : ℝ) / (t/(2*π*y) + lam)
      rw [phi_eq_ps t lam x (ha' x hx), phi_eq_ps t lam y (ha' y hy)]
      exact mul_le_mul_of_nonneg_left (hg hx hy hxy) (by positivity)
    · right
      have hg := sqrt_div_antitoneOn_ps a b t lam ha hab hden hs
      intro x hx y hy hxy
      show y ^ (-(1/2) : ℝ) / (t/(2*π*y) + lam) ≤ x ^ (-(1/2) : ℝ) / (t/(2*π*x) + lam)
      rw [phi_eq_ps t lam x (ha' x hx), phi_eq_ps t lam y (ha' y hy)]
      exact mul_le_mul_of_nonneg_left (hg hx hy hxy) (by positivity)
  exact hK1 a b m M _ _ _ hab hm hF hF'c hGc hphi hmle hGM

end lem1app

/-- `(u^s)' = u^{s-1}` in the form used below. -/
private lemma cpow_phase_ps (u t : ℝ) (hu : 0 < u) :
    (u : ℂ) ^ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1)
      = ((u ^ (-(1/2) : ℝ) : ℝ) : ℂ) * ee (t * Real.log u / (2 * π)) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [Complex.cpow_def_of_ne_zero hu0]
  have hlog : Complex.log (u : ℂ) = ((Real.log u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hu.le]
  rw [hlog]
  have hexp : (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1)
      = ((-(1/2) : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
  rw [hexp, mul_add, Complex.exp_add]
  have h1 : Complex.exp (((Real.log u : ℝ) : ℂ) * ((-(1/2) : ℝ) : ℂ))
      = ((u ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.rpow_def_of_pos hu]
  rw [h1]
  congr 1
  unfold ee
  have : ((Real.log u : ℝ) : ℂ) * ((t : ℂ) * Complex.I)
      = 2 * π * Complex.I * (t * Real.log u / (2 * π) : ℝ) := by
    push_cast
    field_simp
  rw [this]

private lemma norm_ee_aux_ps (x : ℝ) : ‖ee x‖ = 1 := by
  simp [ee, Complex.norm_exp]



/-- `N^{2/3} ≤ N/2` for `N ≥ 8`. -/
private lemma rpow_two_thirds_le_half_ps {N : ℕ} (hN : 8 ≤ N) :
    (N : ℝ) ^ (2/3 : ℝ) ≤ (N : ℝ) / 2 := by
  have hNr : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have h3 : (2:ℝ) ≤ (N:ℝ) ^ (1/3 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 8) hNr (by norm_num : (0:ℝ) ≤ 1/3)
    have h8 : (8:ℝ) ^ (1/3 : ℝ) = 2 := by
      have h8' : (8:ℝ) = 2^3 := by norm_num
      rw [h8', ← Real.rpow_natCast (2:ℝ) 3, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rwa [h8] at h
  have hinv : (N:ℝ) ^ (-(1/3) : ℝ) ≤ 1/2 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 2) h3 (by norm_num : (-(1:ℝ)) ≤ 0)
    rw [Real.rpow_neg_one] at h
    norm_num at h 
    calc (N:ℝ) ^ (-(1/3) : ℝ) = ((N:ℝ) ^ (1/3 : ℝ))⁻¹ := by
          rw [show (-(1/3) : ℝ) = (1/3) * (-(1:ℝ)) by norm_num, Real.rpow_mul (le_of_lt hNpos),
            Real.rpow_neg_one]
      _ ≤ 1/2 := h
  have hsplit : (N:ℝ) ^ (2/3 : ℝ) = (N:ℝ) * (N:ℝ) ^ (-(1/3) : ℝ) := by
    rw [show (2/3 : ℝ) = 1 + (-(1/3)) by norm_num, Real.rpow_add hNpos, Real.rpow_one]
  rw [hsplit]
  nlinarith [hinv, hNpos]




section inner

open MeasureTheory intervalIntegral

set_option maxHeartbeats 4000000

private lemma pos_of_mul_neg_of_neg_aux_ps {a b : ℝ} (ha : a < 0) (h : a*b < 0) : 0 < b := by
  by_contra hb
  push_neg at hb
  have := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha) hb
  linarith

private lemma neg_of_mul_pos_of_neg_aux_ps {a b : ℝ} (ha : a < 0) (h : 0 < a*b) : b < 0 := by
  by_contra hb
  push_neg at hb
  have := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha) hb
  linarith

private lemma pos_of_mul_pos_aux_ps {a b : ℝ} (ha : 0 < a) (h : 0 < a*b) : 0 < b := by
  by_contra hb
  push_neg at hb
  have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hb
  linarith

private lemma neg_of_mul_neg_aux_ps {a b : ℝ} (ha : 0 < a) (h : a*b < 0) : b < 0 := by
  by_contra hb
  push_neg at hb
  have := mul_nonneg (le_of_lt ha) hb
  linarith

private lemma const_upgrade_ps {x y M m1 : ℝ} (hxy : x ≤ y) (hM : 0 ≤ M) (hm : 0 < m1) :
    x * M / m1 ≤ y * M / m1 := by
  have h : 0 ≤ M / m1 := div_nonneg hM (le_of_lt hm)
  calc x * M / m1 = x * (M / m1) := by ring
    _ ≤ y * (M / m1) := mul_le_mul_of_nonneg_right hxy h
    _ = y * M / m1 := by ring

/-- The `u`-integral of one term of the line integral: bounded by `N^{-1/2}` times the weight
`wt38`, by the first derivative test on at most two monotonicity pieces. -/
private lemma inner_u_bound_ps (h1 : Lemma1) (N : ℕ) (A lam t : ℝ)
    (hN : 64 ≤ N) (hA1 : 1 ≤ A) (hA2 : A ≤ (N : ℝ) ^ (2/3 : ℝ)) :
    ‖∫ u in ((N : ℝ) - A)..(N : ℝ),
        (u : ℂ) ^ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1) * ee (lam * u)‖
      ≤ max 4 (16 * π * max h1.choose 0) * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t := by
  set K1 : ℝ := max h1.choose 0 with hK1def
  have hK1nn : (0 : ℝ) ≤ K1 := le_max_right _ _
  have hK1 := h1.choose_spec
  have hNr : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hAhalf : A ≤ (N : ℝ) / 2 := le_trans hA2 (rpow_two_thirds_le_half_ps (by omega))
  have hcpos : (0 : ℝ) < (N : ℝ) - A := by linarith
  have hchalf : (N : ℝ) / 2 ≤ (N : ℝ) - A := by linarith
  have hcN : (N : ℝ) - A ≤ (N : ℝ) := by linarith
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg (le_of_lt hNpos) _
  set M : ℝ := 4 * (N : ℝ) ^ (-(1/2) : ℝ) with hMdef
  have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; nlinarith [hNpow]
  -- the trivial bound
  have htriv :
      ‖∫ u in ((N : ℝ) - A)..(N : ℝ),
        (u : ℂ) ^ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1) * ee (lam * u)‖ ≤ M * A := by
    have hb : ∀ x ∈ Set.uIoc ((N : ℝ) - A) (N : ℝ),
        ‖(x : ℂ) ^ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1) * ee (lam * x)‖ ≤ M := by
      intro x hx
      rw [Set.uIoc_of_le hcN, Set.mem_Ioc] at hx
      have hx0 : 0 < x := lt_of_lt_of_le hcpos (le_of_lt hx.1)
      have hn1 : ‖(x : ℂ) ^ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1)‖
          = x ^ (-(1/2) : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        norm_num
      rw [norm_mul, hn1, norm_ee_aux_ps, mul_one, hMdef]
      exact rpow_neg_half_le_ps (N := N) (u := x) (by omega) (le_trans hchalf (le_of_lt hx.1))
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - ((N : ℝ) - A))] at h
    calc _ ≤ M * ((N : ℝ) - ((N : ℝ) - A)) := h
      _ = M * A := by ring
  set m : ℝ := sInf ((fun u : ℝ => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) (N : ℝ))
    with hmdef
  have hwtshape : wt38 N A lam t = if m = 0 then A else min A ((N : ℝ) / m) := by
    simp only [wt38]
    rw [← hmdef]
  have hmnn : (0 : ℝ) ≤ m := by
    rw [hmdef]
    exact Real.sInf_nonneg (by rintro _ ⟨u, hu, rfl⟩; exact abs_nonneg _)
  have hbdd : BddBelow ((fun u : ℝ => |t + 2 * π * lam * u|) ''
      Set.Icc ((N : ℝ) - A) (N : ℝ)) :=
    ⟨0, by rintro _ ⟨u, hu, rfl⟩; exact abs_nonneg _⟩
  have hmle_den : ∀ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ), m ≤ |t + 2 * π * lam * u| := by
    intro u hu
    rw [hmdef]
    exact csInf_le hbdd ⟨u, hu, rfl⟩
  by_cases hm0 : m = 0
  · -- the degenerate case: the weight is `A` and the trivial bound suffices
    rw [hwtshape, hm0, if_pos rfl]
    have h4 : (4 : ℝ) ≤ max 4 (16 * π * K1) := le_max_left _ _
    have hA0 : (0 : ℝ) ≤ A := by linarith
    refine htriv.trans ?_
    rw [hMdef]
    have hstep : 4 * (N : ℝ) ^ (-(1/2) : ℝ) ≤ max 4 (16 * π * K1) * (N : ℝ) ^ (-(1/2) : ℝ) :=
      mul_le_mul_of_nonneg_right h4 hNpow
    calc 4 * (N : ℝ) ^ (-(1/2) : ℝ) * A
        = (4 * (N : ℝ) ^ (-(1/2) : ℝ)) * A := by ring
      _ ≤ (max 4 (16 * π * K1) * (N : ℝ) ^ (-(1/2) : ℝ)) * A :=
          mul_le_mul_of_nonneg_right hstep hA0
  · have hmpos : (0 : ℝ) < m := by
      rcases lt_or_eq_of_le hmnn with h | h
      · exact h
      · exact absurd h.symm hm0
    have hden : ∀ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ), t + 2 * π * lam * u ≠ 0 := by
      intro u hu hz
      have h1 := hmle_den u hu
      rw [hz, abs_zero] at h1
      linarith
    -- rewrite the integral in the real form
    set ψ : ℝ → ℂ := fun u => ((u ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
      ee (t * Real.log u / (2 * π) + lam * u) with hψdef
    have hconv : ∫ u in ((N : ℝ) - A)..(N : ℝ),
          (u : ℂ) ^ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1) * ee (lam * u)
        = ∫ u in ((N : ℝ) - A)..(N : ℝ), ψ u := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hcN, Set.mem_Icc] at hx
      have hx0 : 0 < x := lt_of_lt_of_le hcpos hx.1
      simp only [hψdef, cpow_phase_ps x t hx0, mul_assoc, ← ee_add_ps]
    have hψcont : ContinuousOn ψ (Set.Icc ((N : ℝ) - A) (N : ℝ)) := by
      have h1 : ContinuousOn (fun u : ℝ => ((u ^ (-(1/2) : ℝ) : ℝ) : ℂ))
          (Set.Icc ((N : ℝ) - A) (N : ℝ)) := by
        exact Complex.continuous_ofReal.comp_continuousOn
          (ContinuousOn.rpow_const continuousOn_id
            (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le hcpos hu.1))))
      have h2 : ContinuousOn (fun u : ℝ => ee (t * Real.log u / (2 * π) + lam * u))
          (Set.Icc ((N : ℝ) - A) (N : ℝ)) := by
        have hlog : ContinuousOn (fun u : ℝ => Real.log u) (Set.Icc ((N : ℝ) - A) (N : ℝ)) :=
          Real.continuousOn_log.mono
            (fun u hu => ne_of_gt (lt_of_lt_of_le hcpos hu.1))
        have hph : ContinuousOn (fun u : ℝ => t * Real.log u / (2 * π) + lam * u)
            (Set.Icc ((N : ℝ) - A) (N : ℝ)) :=
          ((hlog.const_mul t).div_const (2 * π)).add (continuousOn_id.const_mul lam)
        exact (by unfold ee; fun_prop : Continuous fun x : ℝ => ee x).comp_continuousOn hph
      rw [hψdef]
      exact h1.mul h2
    -- the oscillation bound
    have hosc : ‖∫ u in ((N : ℝ) - A)..(N : ℝ), ψ u‖
        ≤ 16 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ) * ((N : ℝ) / m) := by
      set m1 : ℝ := m / (2 * π * (N : ℝ)) with hm1def
      have hm1pos : (0 : ℝ) < m1 := by rw [hm1def]; positivity
      have hmle : ∀ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ), m1 ≤ |t / (2 * π * u) + lam| := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le hcpos hu.1
        have h1 := hmle_den u hu
        have hden2 : (0 : ℝ) < 2 * π * u := by positivity
        have hle2pi : 2 * π * u ≤ 2 * π * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hu.2 (by positivity)
        have hform : t / (2 * π * u) + lam = (t + 2 * π * lam * u) / (2 * π * u) := by
          field_simp
        rw [hform, abs_div, abs_of_pos hden2, hm1def]
        have hA1 : m / (2 * π * (N : ℝ)) ≤ |t + 2 * π * lam * u| / (2 * π * (N : ℝ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        have hA2 : |t + 2 * π * lam * u| / (2 * π * (N : ℝ))
            ≤ |t + 2 * π * lam * u| / (2 * π * u) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hinv : (2 * π * (N : ℝ))⁻¹ ≤ (2 * π * u)⁻¹ :=
            (inv_le_inv₀ (by positivity : (0:ℝ) < 2 * π * (N : ℝ)) hden2).mpr hle2pi
          exact mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
        linarith
      have hGM : ∀ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ), |u ^ (-(1/2) : ℝ)| ≤ M := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le hcpos hu.1
        rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu0) _), hMdef]
        exact rpow_neg_half_le_ps (N := N) (u := u) (by omega) (le_trans hchalf hu.1)
      have hconst : K1 * M / m1 = 8 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ) * ((N : ℝ) / m) := by
        rw [hMdef, hm1def]
        field_simp
        ring
      by_cases hsingle : (∀ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ), 0 ≤ t - 2 * π * lam * u) ∨
          (∀ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ), t - 2 * π * lam * u ≤ 0)
      · have hp0 := lemma1_piece_ps h1.choose hK1 ((N : ℝ) - A) (N : ℝ) t lam m1 M hcN hcpos
          hm1pos hMnn hden hsingle hmle hGM
        have hp : ‖∫ u in ((N : ℝ) - A)..(N : ℝ), ψ u‖ ≤ K1 * M / m1 :=
          hp0.trans (const_upgrade_ps (le_max_left _ _) hMnn hm1pos)
        calc ‖∫ u in ((N : ℝ) - A)..(N : ℝ), ψ u‖ ≤ K1 * M / m1 := hp
          _ = 8 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ) * ((N : ℝ) / m) := hconst
          _ ≤ 16 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ) * ((N : ℝ) / m) := by
              have h2 : (0 : ℝ) ≤ 2 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ) * ((N : ℝ) / m) := by
                have h3 : (0 : ℝ) ≤ (N : ℝ) / m := div_nonneg (by positivity) (le_of_lt hmpos)
                positivity
              linarith
      · obtain ⟨⟨u1, hu1, h1neg⟩, ⟨u2, hu2, h2pos⟩⟩ : (∃ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ),
            t - 2 * π * lam * u < 0) ∧ (∃ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ),
            0 < t - 2 * π * lam * u) := by
          constructor
          · by_contra h
            push_neg at h
            exact hsingle (Or.inl h)
          · by_contra h
            push_neg at h
            exact hsingle (Or.inr h)
        have hlamne : lam ≠ 0 := by
          intro h
          rw [h] at h1neg h2pos
          simp at h1neg h2pos
          linarith
        set s : ℝ := t / (2 * π * lam) with hsdef
        have h2ne : (2 : ℝ) * π * lam ≠ 0 :=
          mul_ne_zero (by positivity) hlamne
        have hsroot : t - 2 * π * lam * s = 0 := by
          rw [hsdef, mul_div_cancel₀ t h2ne]
          ring
        -- `s` lies in `[N - A, N]`
        have hcs : (N : ℝ) - A ≤ s := by
          rcases lt_or_gt_of_ne hlamne with hneg | hpos
          · have h2pil : 2 * π * lam < 0 := by nlinarith [Real.pi_pos]
            have hprod : 2 * π * lam * (s - u1) < 0 := by nlinarith [h1neg, hsroot]
            have : 0 < s - u1 := pos_of_mul_neg_of_neg_aux_ps h2pil hprod
            linarith [hu1.1]
          · have h2pil : 0 < 2 * π * lam := by nlinarith [Real.pi_pos]
            have hprod : 0 < 2 * π * lam * (s - u2) := by nlinarith [h2pos, hsroot]
            have : 0 < s - u2 := pos_of_mul_pos_aux_ps h2pil hprod
            linarith [hu2.1]
        have hsN : s ≤ (N : ℝ) := by
          rcases lt_or_gt_of_ne hlamne with hneg | hpos
          · have h2pil : 2 * π * lam < 0 := by nlinarith [Real.pi_pos]
            have hprod : 2 * π * lam * (s - u2) > 0 := by nlinarith [h2pos, hsroot]
            have : s - u2 < 0 := neg_of_mul_pos_of_neg_aux_ps h2pil hprod
            linarith [hu2.2]
          · have h2pil : 0 < 2 * π * lam := by nlinarith [Real.pi_pos]
            have hprod : 2 * π * lam * (s - u1) < 0 := by nlinarith [h1neg, hsroot]
            have : s - u1 < 0 := neg_of_mul_neg_aux_ps h2pil hprod
            linarith [hu1.2]
        have hsgt : 0 < s := lt_of_lt_of_le hcpos hcs
        -- sign of `t - 2πλu` on each piece
        have hsval : (-(2 * π * lam)) * s + t = 0 := by linarith [hsroot]
        have hsig1 : (∀ u ∈ Set.Icc ((N : ℝ) - A) s, 0 ≤ t - 2 * π * lam * u) ∨
            (∀ u ∈ Set.Icc ((N : ℝ) - A) s, t - 2 * π * lam * u ≤ 0) := by
          rcases le_total 0 (t - 2 * π * lam * ((N : ℝ) - A)) with hc0 | hc0
          · left
            intro u hu
            have hb := (affine_between_ps (-(2 * π * lam)) t ((N : ℝ) - A) s u hcs hu.1 hu.2).1
            have hc0' : 0 ≤ (-(2 * π * lam)) * ((N : ℝ) - A) + t := by linarith
            rw [hsval, min_eq_right hc0'] at hb
            linarith
          · right
            intro u hu
            have hb := (affine_between_ps (-(2 * π * lam)) t ((N : ℝ) - A) s u hcs hu.1 hu.2).2
            have hc0' : (-(2 * π * lam)) * ((N : ℝ) - A) + t ≤ 0 := by linarith
            rw [hsval, max_eq_right hc0'] at hb
            linarith
        have hsig2 : (∀ u ∈ Set.Icc s (N : ℝ), 0 ≤ t - 2 * π * lam * u) ∨
            (∀ u ∈ Set.Icc s (N : ℝ), t - 2 * π * lam * u ≤ 0) := by
          rcases le_total 0 (t - 2 * π * lam * (N : ℝ)) with hN0 | hN0
          · left
            intro u hu
            have hb := (affine_between_ps (-(2 * π * lam)) t s (N : ℝ) u hsN hu.1 hu.2).1
            have hN0' : 0 ≤ (-(2 * π * lam)) * (N : ℝ) + t := by linarith
            rw [hsval, min_eq_left hN0'] at hb
            linarith
          · right
            intro u hu
            have hb := (affine_between_ps (-(2 * π * lam)) t s (N : ℝ) u hsN hu.1 hu.2).2
            have hN0' : (-(2 * π * lam)) * (N : ℝ) + t ≤ 0 := by linarith
            rw [hsval, max_eq_left hN0'] at hb
            linarith
        have hsub1 : Set.Icc ((N : ℝ) - A) s ⊆ Set.Icc ((N : ℝ) - A) (N : ℝ) :=
          Set.Icc_subset_Icc le_rfl hsN
        have hsub2 : Set.Icc s (N : ℝ) ⊆ Set.Icc ((N : ℝ) - A) (N : ℝ) :=
          Set.Icc_subset_Icc hcs le_rfl
        have hp1' := lemma1_piece_ps h1.choose hK1 ((N : ℝ) - A) s t lam m1 M hcs hcpos hm1pos
          hMnn (fun u hu => hden u (hsub1 hu)) hsig1
          (fun u hu => hmle u (hsub1 hu)) (fun u hu => hGM u (hsub1 hu))
        have hp2' := lemma1_piece_ps h1.choose hK1 s (N : ℝ) t lam m1 M hsN hsgt hm1pos hMnn
          (fun u hu => hden u (hsub2 hu)) hsig2
          (fun u hu => hmle u (hsub2 hu)) (fun u hu => hGM u (hsub2 hu))
        have hup1 : ‖∫ u in ((N : ℝ) - A)..s, ψ u‖ ≤ K1 * M / m1 :=
          hp1'.trans (const_upgrade_ps (le_max_left _ _) hMnn hm1pos)
        have hup2 : ‖∫ u in s..(N : ℝ), ψ u‖ ≤ K1 * M / m1 :=
          hp2'.trans (const_upgrade_ps (le_max_left _ _) hMnn hm1pos)
        have hI1 : IntervalIntegrable ψ volume ((N : ℝ) - A) s := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hcs]
          exact hψcont.mono (Set.Icc_subset_Icc le_rfl hsN)
        have hI2 : IntervalIntegrable ψ volume s (N : ℝ) := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hsN]
          exact hψcont.mono (Set.Icc_subset_Icc hcs le_rfl)
        have hsplit : ∫ u in ((N : ℝ) - A)..(N : ℝ), ψ u
            = (∫ u in ((N : ℝ) - A)..s, ψ u) + (∫ u in s..(N : ℝ), ψ u) :=
          (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
        rw [hsplit]
        calc ‖(∫ u in ((N : ℝ) - A)..s, ψ u) + (∫ u in s..(N : ℝ), ψ u)‖
            ≤ ‖∫ u in ((N : ℝ) - A)..s, ψ u‖ + ‖∫ u in s..(N : ℝ), ψ u‖ := norm_add_le _ _
          _ ≤ K1 * M / m1 + K1 * M / m1 := add_le_add hup1 hup2
          _ = 16 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ) * ((N : ℝ) / m) := by
              rw [hconst]; ring
    -- finish
    have htriv' : ‖∫ u in ((N : ℝ) - A)..(N : ℝ), ψ u‖ ≤ M * A := by
      rw [← hconv]; exact htriv
    rw [hwtshape, if_neg hm0, hconv]
    by_cases hfin : A ≤ (N : ℝ) / m
    · rw [min_eq_left hfin]
      have h4 : (4 : ℝ) ≤ max 4 (16 * π * K1) := le_max_left _ _
      have hA0 : (0 : ℝ) ≤ A := by linarith
      refine htriv'.trans ?_
      rw [hMdef]
      have hstep : 4 * (N : ℝ) ^ (-(1/2) : ℝ) ≤ max 4 (16 * π * K1) * (N : ℝ) ^ (-(1/2) : ℝ) :=
        mul_le_mul_of_nonneg_right h4 hNpow
      calc 4 * (N : ℝ) ^ (-(1/2) : ℝ) * A
          = (4 * (N : ℝ) ^ (-(1/2) : ℝ)) * A := by ring
        _ ≤ (max 4 (16 * π * K1) * (N : ℝ) ^ (-(1/2) : ℝ)) * A :=
            mul_le_mul_of_nonneg_right hstep hA0
    · rw [min_eq_right (le_of_lt (not_le.mp hfin))]
      refine hosc.trans ?_
      have h8 : (16 * π * K1) ≤ max 4 (16 * π * K1) := le_max_right _ _
      have hnm : (0 : ℝ) ≤ (N : ℝ) / m := div_nonneg (by positivity) (le_of_lt hmpos)
      have hstep : 16 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ)
          ≤ max 4 (16 * π * K1) * (N : ℝ) ^ (-(1/2) : ℝ) :=
        mul_le_mul_of_nonneg_right h8 hNpow
      calc 16 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ) * ((N : ℝ) / m)
          = (16 * π * K1 * (N : ℝ) ^ (-(1/2) : ℝ)) * ((N : ℝ) / m) := by ring
        _ ≤ (max 4 (16 * π * K1) * (N : ℝ) ^ (-(1/2) : ℝ)) * ((N : ℝ) / m) :=
            mul_le_mul_of_nonneg_right hstep hnm

end inner



section wtfacts

private lemma wt38_nonneg_ps (N : ℕ) (A lam t : ℝ) (hA : 0 ≤ A) : 0 ≤ wt38 N A lam t := by
  unfold wt38
  simp only
  have hm : 0 ≤ sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) ↑N) :=
    Real.sInf_nonneg (by rintro _ ⟨u, _, rfl⟩; exact abs_nonneg _)
  split_ifs
  · exact hA
  · exact le_min hA (div_nonneg (Nat.cast_nonneg _) hm)

private lemma wt38_le_A_ps (N : ℕ) (A lam t : ℝ) : wt38 N A lam t ≤ A := by
  unfold wt38
  simp only
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _ 

/-- If the affine function `t + 2πλu` has values of the same sign at the two endpoints then its
absolute value is at least the smaller of the two endpoint absolute values on the whole interval. -/
private lemma aff_sign_ps (c Nd t lam : ℝ) (hcN : c ≤ Nd)
    (hP : (0 ≤ t + 2 * π * lam * c ∧ 0 ≤ t + 2 * π * lam * Nd) ∨
          (t + 2 * π * lam * c ≤ 0 ∧ t + 2 * π * lam * Nd ≤ 0)) :
    ∀ u ∈ Set.Icc c Nd, min |t + 2 * π * lam * c| |t + 2 * π * lam * Nd|
      ≤ |t + 2 * π * lam * u| := by
  intro u hu
  obtain ⟨hb1, hb2⟩ := affine_between_ps (2 * π * lam) t c Nd u hcN hu.1 hu.2
  have e1 : 2 * π * lam * c + t = t + 2 * π * lam * c := by ring
  have e2 : 2 * π * lam * Nd + t = t + 2 * π * lam * Nd := by ring
  have e3 : 2 * π * lam * u + t = t + 2 * π * lam * u := by ring
  rw [e1, e2, e3] at hb1 hb2
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hu0 : 0 ≤ t + 2 * π * lam * u := le_trans (le_min h1 h2) hb1
    rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg hu0]
    exact hb1
  · have hu0 : t + 2 * π * lam * u ≤ 0 := le_trans hb2 (max_le h1 h2)
    rw [abs_of_nonpos h1, abs_of_nonpos h2, abs_of_nonpos hu0]
    have hmin : min (-(t + 2 * π * lam * c)) (-(t + 2 * π * lam * Nd))
        = -(max (t + 2 * π * lam * c) (t + 2 * π * lam * Nd)) := by
      rcases le_total (t + 2 * π * lam * c) (t + 2 * π * lam * Nd) with h | h
      · rw [max_eq_right h, min_eq_right (by linarith)]
      · rw [max_eq_left h, min_eq_left (by linarith)]
    rw [hmin]
    linarith

/-- The inner minimum of (3.8): `0` when the affine function has a zero on the interval, and the
smaller endpoint value otherwise. -/
private lemma sInf_abs_affine_ps (c Nd lam t : ℝ) (hcN : c ≤ Nd) :
    sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc c Nd)
      = if ((0 ≤ t + 2 * π * lam * c ∧ 0 ≤ t + 2 * π * lam * Nd) ∨
            (t + 2 * π * lam * c ≤ 0 ∧ t + 2 * π * lam * Nd ≤ 0))
        then min |t + 2 * π * lam * c| |t + 2 * π * lam * Nd| else 0 := by
  have hbdd : BddBelow ((fun u => |t + 2 * π * lam * u|) '' Set.Icc c Nd) :=
    ⟨0, by rintro _ ⟨u, _, rfl⟩; exact abs_nonneg _⟩
  have hne : ((fun u => |t + 2 * π * lam * u|) '' Set.Icc c Nd).Nonempty :=
    ⟨_, ⟨c, ⟨le_rfl, hcN⟩, rfl⟩⟩
  have hmem : ∀ u ∈ Set.Icc c Nd,
      sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc c Nd) ≤ |t + 2 * π * lam * u| :=
    fun u hu => csInf_le hbdd ⟨u, hu, rfl⟩
  by_cases hP : (0 ≤ t + 2 * π * lam * c ∧ 0 ≤ t + 2 * π * lam * Nd) ∨
      (t + 2 * π * lam * c ≤ 0 ∧ t + 2 * π * lam * Nd ≤ 0)
  · rw [if_pos hP]
    refine le_antisymm (le_min (hmem c ⟨le_rfl, hcN⟩) (hmem Nd ⟨hcN, le_rfl⟩)) ?_
    exact le_csInf hne (by rintro _ ⟨u, hu, rfl⟩; exact aff_sign_ps c Nd t lam hcN hP u hu)
  · rw [if_neg hP]
    have hzero : ∃ u ∈ Set.Icc c Nd, t + 2 * π * lam * u = 0 := by
      have h1 : ¬ (0 ≤ t + 2 * π * lam * c ∧ 0 ≤ t + 2 * π * lam * Nd) := fun h => hP (Or.inl h)
      have h2 : ¬ (t + 2 * π * lam * c ≤ 0 ∧ t + 2 * π * lam * Nd ≤ 0) := fun h => hP (Or.inr h)
      push_neg at h1 h2
      have hcases : (t + 2 * π * lam * c ≤ 0 ∧ 0 ≤ t + 2 * π * lam * Nd) ∨
          (0 ≤ t + 2 * π * lam * c ∧ t + 2 * π * lam * Nd ≤ 0) := by
        rcases le_total 0 (t + 2 * π * lam * c) with hc | hc
        · exact Or.inr ⟨hc, le_of_lt (h1 hc)⟩
        · exact Or.inl ⟨hc, le_of_lt (h2 hc)⟩
      have hcont : ContinuousOn (fun u : ℝ => t + 2 * π * lam * u) (Set.Icc c Nd) := by fun_prop
      rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have hsub := intermediate_value_Icc hcN (f := fun u : ℝ => t + 2 * π * lam * u) hcont
        have hmem0 : (0 : ℝ) ∈ Set.Icc ((fun u : ℝ => t + 2 * π * lam * u) c)
            ((fun u : ℝ => t + 2 * π * lam * u) Nd) := ⟨ha, hb⟩
        obtain ⟨u, hu, hfu⟩ := hsub hmem0
        exact ⟨u, hu, hfu⟩
      · have hsub := intermediate_value_Icc' hcN (f := fun u : ℝ => t + 2 * π * lam * u) hcont
        have hmem0 : (0 : ℝ) ∈ Set.Icc ((fun u : ℝ => t + 2 * π * lam * u) Nd)
            ((fun u : ℝ => t + 2 * π * lam * u) c) := ⟨hb, ha⟩
        obtain ⟨u, hu, hfu⟩ := hsub hmem0
        exact ⟨u, hu, hfu⟩
    refine le_antisymm ?_ (Real.sInf_nonneg (by rintro _ ⟨u, _, rfl⟩; exact abs_nonneg _))
    obtain ⟨u, hu, hfu⟩ := hzero
    have := hmem u hu
    rw [hfu, abs_zero] at this
    exact this

/-- Explicit formula for the weight of (3.8) as a function of `t`. -/
private lemma wt38_formula_ps (N : ℕ) (A lam t : ℝ) (hA : 0 ≤ A) :
    wt38 N A lam t
      = if ((0 ≤ t + 2 * π * lam * ((N : ℝ) - A) ∧ 0 ≤ t + 2 * π * lam * (N : ℝ)) ∨
            (t + 2 * π * lam * ((N : ℝ) - A) ≤ 0 ∧ t + 2 * π * lam * (N : ℝ) ≤ 0))
        then (if t + 2 * π * lam * ((N : ℝ) - A) = 0 ∨ t + 2 * π * lam * (N : ℝ) = 0 then A
          else min A ((N : ℝ) / min |t + 2 * π * lam * ((N : ℝ) - A)|
            |t + 2 * π * lam * (N : ℝ)|))
        else A := by
  have hcN : (N : ℝ) - A ≤ (N : ℝ) := by linarith
  unfold wt38
  simp only
  have hs : sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) ↑N)
      = if ((0 ≤ t + 2 * π * lam * ((N : ℝ) - A) ∧ 0 ≤ t + 2 * π * lam * (N : ℝ)) ∨
            (t + 2 * π * lam * ((N : ℝ) - A) ≤ 0 ∧ t + 2 * π * lam * (N : ℝ) ≤ 0))
        then min |t + 2 * π * lam * ((N : ℝ) - A)| |t + 2 * π * lam * (N : ℝ)| else 0 :=
    sInf_abs_affine_ps ((N : ℝ) - A) (N : ℝ) lam t hcN
  by_cases hP : (0 ≤ t + 2 * π * lam * ((N : ℝ) - A) ∧ 0 ≤ t + 2 * π * lam * (N : ℝ)) ∨
      (t + 2 * π * lam * ((N : ℝ) - A) ≤ 0 ∧ t + 2 * π * lam * (N : ℝ) ≤ 0)
  · rw [hs, if_pos hP, if_pos hP]
    by_cases hz : min |t + 2 * π * lam * ((N : ℝ) - A)| |t + 2 * π * lam * (N : ℝ)| = 0
    · have hzc : t + 2 * π * lam * ((N : ℝ) - A) = 0 ∨ t + 2 * π * lam * (N : ℝ) = 0 := by
        rcases le_total |t + 2 * π * lam * ((N : ℝ) - A)| |t + 2 * π * lam * (N : ℝ)| with h | h
        · rw [min_eq_left h, abs_eq_zero] at hz
          exact Or.inl hz
        · rw [min_eq_right h, abs_eq_zero] at hz
          exact Or.inr hz
      rw [if_pos hz, if_pos hzc]
    · rw [if_neg hz, if_neg (by
        rintro (h | h)
        · exact hz (by rw [h, abs_zero, min_eq_left (abs_nonneg _)])
        · exact hz (by rw [h, abs_zero, min_eq_right (abs_nonneg _)]))]
  · rw [hs, if_neg hP, if_neg hP]
    simp

/-- The weight of (3.8) is a measurable function of `t`. -/
private lemma wt38_measurable_ps (N : ℕ) (A lam : ℝ) (hA : 0 ≤ A) :
    Measurable fun t : ℝ => wt38 N A lam t := by
  have hform : (fun t : ℝ => wt38 N A lam t) = fun t : ℝ =>
      if ((0 ≤ t + 2 * π * lam * ((N : ℝ) - A) ∧ 0 ≤ t + 2 * π * lam * (N : ℝ)) ∨
            (t + 2 * π * lam * ((N : ℝ) - A) ≤ 0 ∧ t + 2 * π * lam * (N : ℝ) ≤ 0))
        then (if t + 2 * π * lam * ((N : ℝ) - A) = 0 ∨ t + 2 * π * lam * (N : ℝ) = 0 then A
          else min A ((N : ℝ) / min |t + 2 * π * lam * ((N : ℝ) - A)|
            |t + 2 * π * lam * (N : ℝ)|))
        else A := funext (wt38_formula_ps N A lam · hA)
  rw [hform]
  have h1 : Measurable fun t : ℝ => t + 2 * π * lam * ((N : ℝ) - A) := by fun_prop
  have h2 : Measurable fun t : ℝ => t + 2 * π * lam * (N : ℝ) := by fun_prop
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le measurable_const h1 |>.inter (measurableSet_le measurable_const h2)) |>
      MeasurableSet.union <| measurableSet_le h1 measurable_const |>.inter
        (measurableSet_le h2 measurable_const)
  · refine Measurable.ite ?_ measurable_const ?_
    · exact (measurableSet_eq_fun h1 measurable_const).union
        (measurableSet_eq_fun h2 measurable_const)
    · fun_prop

end wtfacts

open MeasureTheory intervalIntegral



/-- LEAF: page 264, the display after "The inner integral above can be estimated by Lemma 1",
and page 265 first display: differentiation of `Vline` in `u`, Fubini over `t ∈ [-T, T]` and
`u ∈ [N-A, N]`, and Lemma 1 on the at most two pieces where `G/F'` is monotone, giving
`≪ N^{-1/2} wt38`. Class MEDIUM. -/
theorem innerBound_leaf_ps (h1 : Lemma1) : InnerBound_ps := by
  refine ⟨max 4 (16 * π * max h1.choose 0), 64, by positivity, ?_⟩
  intro N A lam T q χ Nv hN hA1 hA2 hT
  classical
  have hNat : (2 : ℕ) ≤ N := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h2
  have h8 : 8 ≤ N := by
    have h8' : (8 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h8'
  have h64 : 64 ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hAhalf : A ≤ (N : ℝ) / 2 := le_trans hA2 (rpow_two_thirds_le_half_ps h8)
  have hcpos : (0 : ℝ) < (N : ℝ) - A := by linarith
  have hcN : (N : ℝ) - A ≤ (N : ℝ) := by linarith
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hFF : ∀ t : ℝ, (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = (1 / 2 + (t : ℂ) * Complex.I) := by
    intro t
    push_cast
    ring
  set K2 : ℝ := max 4 (16 * π * max h1.choose 0) with hK2def
  have hK2nn : (0 : ℝ) ≤ K2 :=
    le_trans (by norm_num : (0:ℝ) ≤ 4) (le_max_left 4 (16 * π * max h1.choose 0))
  -- the derivative of `Vline_ps` in `u`
  have hderiv : ∀ u ∈ Set.Icc ((N : ℝ) - A) (N : ℝ),
      deriv (fun v : ℝ => Vline_ps Nv χ N A (1/2) T v) u
        = (1/(2*π) : ℂ) * ∫ t in (-T)..T,
            Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) := by
    intro u hu
    have hu2 : ((N : ℝ) - A)/2 < u := by linarith [hu.1]
    exact (vline_ps_hasDerivAt Nv χ N A T hNat hA1 hA2 hu2).deriv
  -- step A: differentiate and move `ee` inside the `t`-integral
  have stepA : ∫ u in ((N : ℝ) - A)..(N : ℝ),
        deriv (fun v : ℝ => Vline_ps Nv χ N A (1/2) T v) u * ee (lam * u)
      = (1/(2*π) : ℂ) * ∫ u in ((N : ℝ) - A)..(N : ℝ), ∫ t in (-T)..T,
          Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hcN, Set.mem_Icc] at hu
    rw [hderiv u hu, intervalIntegral.integral_mul_const]
    ring
  -- continuity of the two-variable integrand on the compact box
  have hcont : ContinuousOn (Function.uncurry fun u t : ℝ =>
      Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u))
      (Set.Icc ((N : ℝ) - A) (N : ℝ) ×ˢ Set.Icc (-T) T) := by
    have hF : Continuous fun p : ℝ × ℝ =>
        Fprod Nv χ (((1/2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) :=
      (Fprod_continuous_ps Nv χ).comp (by fun_prop)
    have hcp : ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) - 1))
        (Set.Icc ((N : ℝ) - A) (N : ℝ) ×ˢ Set.Icc (-T) T) := by
      refine ContinuousOn.cpow (by fun_prop) (by fun_prop) ?_
      rintro ⟨u, t⟩ ⟨hu, ht⟩
      exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le hcpos hu.1)
    have hee : Continuous fun p : ℝ × ℝ => ee (lam * p.1) :=
      (continuous_ee_ps lam).comp (by fun_prop)
    exact ((hF.continuousOn.mul hcp).mul hee.continuousOn).congr (by intro p hp; rfl)
  -- Fubini
  have stepB : ∫ u in ((N : ℝ) - A)..(N : ℝ), ∫ t in (-T)..T,
        Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u)
      = ∫ t in (-T)..T, ∫ u in ((N : ℝ) - A)..(N : ℝ),
          Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u) := by
    refine MeasureTheory.intervalIntegral_intervalIntegral_swap ?_
    have hbox : MeasureTheory.IntegrableOn (Function.uncurry fun u t : ℝ =>
        Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u))
        (Set.Icc ((N : ℝ) - A) (N : ℝ) ×ˢ Set.Icc (-T) T) :=
      hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine hbox.mono_set ?_
    refine Set.prod_mono ?_ ?_
    · rw [Set.uIoc_of_le hcN]; exact Set.Ioc_subset_Icc_self
    · rw [Set.uIoc_of_le (by linarith : (-T:ℝ) ≤ T)]; exact Set.Ioc_subset_Icc_self
  -- factor out the `t`-independent constant
  have stepC : ∀ t : ℝ, ∫ u in ((N : ℝ) - A)..(N : ℝ),
        Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u)
      = Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        ∫ u in ((N : ℝ) - A)..(N : ℝ),
          (u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1) * ee (lam * u) := by
    intro t
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    ring
  -- the pointwise bound from Lemma 1
  have hpointwise : ∀ t : ℝ,
      ‖∫ u in ((N : ℝ) - A)..(N : ℝ),
        (u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1) * ee (lam * u)‖
      ≤ K2 * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t := by
    intro t
    have hp := inner_u_bound_ps ⟨h1.choose, h1.choose_spec⟩ N A lam t h64 hA1 hA2
    rw [hK2def]
    exact hp
  have hpoint : ∀ t : ℝ, ‖∫ u in ((N : ℝ) - A)..(N : ℝ),
        Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u)‖
      ≤ ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
        (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t) := by
    intro t
    rw [stepC t, norm_mul]
    exact mul_le_mul_of_nonneg_left (hpointwise t) (norm_nonneg _)
  -- integrability of the majorant
  have hFcont : Continuous fun t : ℝ => Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    simpa using Fprod_continuous_ps Nv χ
  have hwt_meas : Measurable fun t : ℝ => wt38 N A lam t := wt38_measurable_ps N A lam hA0
  have hg_int : MeasureTheory.IntegrableOn (fun t : ℝ =>
      ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
        (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * A)) (Set.Icc (-T) T) := by
    have hc : Continuous fun t : ℝ =>
        ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
          (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * A) := hFcont.norm.mul continuous_const
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hh_int : MeasureTheory.IntegrableOn (fun t : ℝ =>
      ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
        (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t)) (Set.Ioc (-T) T) := by
    refine MeasureTheory.Integrable.mono' (hg_int.mono_set Set.Ioc_subset_Icc_self) ?_ ?_
    · exact (hFcont.norm.measurable.mul (hwt_meas.const_mul
        (K2 * (N : ℝ) ^ (-(1/2) : ℝ)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      have hwt0 : (0 : ℝ) ≤ wt38 N A lam t := wt38_nonneg_ps N A lam t hA0
      have hwtA : wt38 N A lam t ≤ A := wt38_le_A_ps N A lam t
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine mul_le_mul_of_nonneg_left hwtA ?_
      exact mul_nonneg hK2nn (Real.rpow_nonneg (le_of_lt hNpos) _)
  -- integrate the pointwise bound
  have hG_bound : ∫ t in (-T)..T, ‖∫ u in ((N : ℝ) - A)..(N : ℝ),
        Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u)‖
      ≤ ∫ t in (-T)..T, ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
          (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t) := by
    rw [intervalIntegral.integral_of_le (by linarith : (-T:ℝ) ≤ T),
      intervalIntegral.integral_of_le (by linarith : (-T:ℝ) ≤ T)]
    exact MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
      hh_int (Filter.Eventually.of_forall fun t => hpoint t)
  -- the constant bookkeeping for the `t`-integral
  have hfr : (∫ t in (-T)..T, ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
        (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t))
      = K2 * (N : ℝ) ^ (-(1/2) : ℝ) * ∫ t in (-T)..T,
          wt38 N A lam t * ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hJ : (0 : ℝ) ≤ ∫ t in Set.Icc (-T) T,
      wt38 N A lam t * ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun t _ => by
      have := wt38_nonneg_ps N A lam t hA0
      positivity)
  calc ‖∫ u in ((N : ℝ) - A)..(N : ℝ),
        deriv (fun v : ℝ => Vline_ps Nv χ N A (1/2) T v) u * ee (lam * u)‖
      = ‖(1/(2*π) : ℂ) * ∫ t in (-T)..T, ∫ u in ((N : ℝ) - A)..(N : ℝ),
          Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u)‖ := by
        rw [stepA, stepB]
    _ = (1/(2*π)) * ‖∫ t in (-T)..T, ∫ u in ((N : ℝ) - A)..(N : ℝ),
          Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u)‖ := by
        rw [norm_mul]
        have hc : ‖(1/(2*(π:ℂ)))‖ = 1/(2*π) := by
          rw [show (1/(2*(π:ℂ))) = ((1/(2*π) : ℝ) : ℂ) by push_cast; ring]
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        rw [hc]
    _ ≤ (1/(2*π)) * ∫ t in (-T)..T, ‖∫ u in ((N : ℝ) - A)..(N : ℝ),
          Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            ((u : ℂ) ^ ((((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) * ee (lam * u)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact intervalIntegral.norm_integral_le_integral_norm (by linarith : (-T:ℝ) ≤ T)
    _ ≤ (1/(2*π)) * ∫ t in (-T)..T, ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
          (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t) :=
        mul_le_mul_of_nonneg_left hG_bound (by positivity)
    _ ≤ K2 * (N : ℝ) ^ (-(1/2) : ℝ) * ∫ t in Set.Icc (-T) T,
          wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + (t : ℂ) * Complex.I)‖ := by
        have hstep : (1/(2*π)) * (∫ t in (-T)..T,
              ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
                (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * wt38 N A lam t))
            ≤ K2 * (N : ℝ) ^ (-(1/2) : ℝ) * ∫ t in Set.Icc (-T) T,
              wt38 N A lam t * ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
          rw [hfr, intervalIntegral.integral_of_le (by linarith : (-T:ℝ) ≤ T),
            ← MeasureTheory.integral_Icc_eq_integral_Ioc]
          have hX : (0 : ℝ) ≤ K2 * (N : ℝ) ^ (-(1/2) : ℝ) * ∫ t in Set.Icc (-T) T,
              wt38 N A lam t * ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
            mul_nonneg (mul_nonneg hK2nn (Real.rpow_nonneg (le_of_lt hNpos) _)) hJ
          have ha1 : (1/(2*π) : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]
            nlinarith [Real.pi_gt_three]
          calc (1/(2*π) : ℝ) * (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * ∫ t in Set.Icc (-T) T,
                wt38 N A lam t * ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
              ≤ 1 * (K2 * (N : ℝ) ^ (-(1/2) : ℝ) * ∫ t in Set.Icc (-T) T,
                wt38 N A lam t * ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) :=
                mul_le_mul_of_nonneg_right ha1 hX
            _ = K2 * (N : ℝ) ^ (-(1/2) : ℝ) * ∫ t in Set.Icc (-T) T,
                wt38 N A lam t * ‖Fprod Nv χ (((1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
                ring
        simp only [← hFF]
        exact hstep

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
