import Mathlib
import LeanLab.HelfgottMajor.PVLemmas1122

/-!
Route burst S68, burst-20261122, tag cos-partial-lower.
Attack on the LEAF `PVLemmas1122.cos_partial_lower`: for real y and n ≥ 1,
`-(log 2 + 2/n) ≤ ∑_{j ≤ n} cos(jy)/j`.

Route, the standard one: reduce y to `[0, π]` by periodicity and evenness of cosine.
For `n y ≤ π/2` every term is nonnegative. Otherwise `s = sin(y/2) ≥ 1/(2n)`, and with
`z = e^{iy}` the partial sums of `Re ∑ z^j/j` converge to `Re(-log(1 - z)) = -log(2 s)`,
the boundary case of the Taylor series of `-log(1-z)` by Dirichlet's test, Zygmund,
Trigonometric Series, Chapter I, formula 2.8. The tail from `n+1` to `N` is at most
`1/((n+1) s)` in absolute value by Abel summation with the Dirichlet kernel bound
`|∑_{k=a}^{b} cos(ky)| ≤ 1/sin(y/2)`. An elementary concavity estimate then gives
`-log(2s) - 1/((n+1)s) ≥ -(log 2 + 2/n)` on `1/(2n) ≤ s ≤ 1`.

All steps are PROVED here, so the target LEAF is PROVED.

Lean subtlety: the series `∑ cos(jy)/j` is only conditionally convergent, so it is not
`Summable` in Lean, and the boundary value is stated with partial sums and `Tendsto`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVCosLower1122

open Real Finset Filter Topology

/-- Dirichlet kernel identity, Zygmund, Chapter I, formula 2.4 in telescoped form:
`2 sin(y/2) ∑_{k=a+1}^{b} cos(ky) = sin((b+1/2)y) - sin((a+1/2)y)`. PROVED. -/
theorem dirichlet_cos_sum (y : ℝ) (a b : ℕ) (hab : a ≤ b) :
    2 * sin (y / 2) * ∑ k ∈ Ioc a b, cos (k * y) =
      sin ((b + 1 / 2) * y) - sin ((a + 1 / 2) * y) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ioc_succ_top hb, mul_add, ih, two_mul_sin_mul_cos]
    push_cast
    have e1 : y / 2 - (b + 1) * y = -((b + 1 / 2) * y) := by ring
    have e2 : y / 2 + (b + 1) * y = (b + 1 + 1 / 2) * y := by ring
    rw [e1, e2, sin_neg]; ring

/-- Dirichlet kernel bound `|∑_{k=a+1}^{b} cos(ky)| ≤ 1/sin(y/2)` for `0 < y < 2π`. PROVED. -/
theorem abs_cos_sum_le (y : ℝ) (hy0 : 0 < y) (hy : y < 2 * π) (a b : ℕ) :
    |∑ k ∈ Ioc a b, cos (k * y)| ≤ 1 / sin (y / 2) := by
  have hs : 0 < sin (y / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rcases le_or_gt a b with hab | hab
  · have h := dirichlet_cos_sum y a b hab
    rw [le_div_iff₀ hs]
    have h1 := abs_le.1 (abs_sin_le_one ((b + 1 / 2 : ℝ) * y))
    have h2 := abs_le.1 (abs_sin_le_one ((a + 1 / 2 : ℝ) * y))
    have hS : |(∑ k ∈ Ioc a b, cos (k * y)) * sin (y / 2)| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    rwa [abs_mul, abs_of_pos hs] at hS
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity

/-- Abel summation bound for the tail of the cosine series, the standard estimate
behind Dirichlet's test, Zygmund, Trigonometric Series, Chapter I, Section 2: with
`C_j = ∑_{k=n+1}^{j} cos(ky)` and `|C_j| ≤ 1/sin(y/2)`, summation by parts gives
`|∑_{j=n+1}^{N} cos(jy)/j| ≤ 1/((n+1) sin(y/2))` for `0 < y < 2π`. PROVED. -/
theorem cos_tail_abs_le (y : ℝ) (hy0 : 0 < y) (hy : y < 2 * π) (n N : ℕ) :
    |∑ j ∈ Ioc n N, cos (j * y) / j| ≤ 1 / ((n + 1) * sin (y / 2)) := by
  have hs : 0 < sin (y / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set B := 1 / sin (y / 2) with hB
  have hB0 : 0 < B := by positivity
  have hC := abs_cos_sum_le y hy0 hy n
  rcases lt_or_ge N n with hNn | hNn
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity
  -- Abel summation by induction on N
  have key : ∀ M, n ≤ M → |∑ j ∈ Ioc n M, cos (j * y) / j -
      (∑ k ∈ Ioc n M, cos (k * y)) / ((M : ℝ) + 1)| ≤ B * (1 / ((n : ℝ) + 1) - 1 / ((M : ℝ) + 1)) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [sum_Ioc_succ_top hM, sum_Ioc_succ_top hM]
      push_cast
      have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
      have hM2 : (0:ℝ) < (M:ℝ) + 1 + 1 := by positivity
      set T := ∑ j ∈ Ioc n M, cos (j * y) / j
      set C := ∑ k ∈ Ioc n M, cos (k * y)
      set c := cos (((M:ℝ) + 1) * y)
      have hid : T + c / ((M:ℝ) + 1) - (C + c) / ((M:ℝ) + 1 + 1) =
          (T - C / ((M:ℝ) + 1)) + (C + c) * (1 / ((M:ℝ) + 1) - 1 / ((M:ℝ) + 1 + 1)) := by
        field_simp; ring
      rw [hid]
      have hCc : |C + c| ≤ B := by
        have := hC (M + 1)
        rw [sum_Ioc_succ_top hM] at this; push_cast at this; exact this
      have hd : 0 ≤ 1 / ((M:ℝ) + 1) - 1 / ((M:ℝ) + 1 + 1) := by
        rw [sub_nonneg]; exact one_div_le_one_div_of_le hM1 (by linarith)
      calc |(T - C / ((M:ℝ) + 1)) + (C + c) * (1 / ((M:ℝ) + 1) - 1 / ((M:ℝ) + 1 + 1))|
          ≤ |T - C / ((M:ℝ) + 1)| + |C + c| * (1 / ((M:ℝ) + 1) - 1 / ((M:ℝ) + 1 + 1)) := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hd]
        _ ≤ B * (1 / ((n : ℝ) + 1) - 1 / ((M : ℝ) + 1)) +
            B * (1 / ((M:ℝ) + 1) - 1 / ((M:ℝ) + 1 + 1)) := by
            gcongr
        _ = B * (1 / ((n : ℝ) + 1) - 1 / ((M:ℝ) + 1 + 1)) := by ring
  have h1 := key N hNn
  have h2 := hC N
  have hN1 : (0:ℝ) < (N:ℝ) + 1 := by positivity
  have h3 : |(∑ k ∈ Ioc n N, cos (k * y)) / ((N : ℝ) + 1)| ≤ B * (1 / ((N:ℝ) + 1)) := by
    rw [abs_div, abs_of_pos hN1, div_le_iff₀ hN1]
    have : B * (1 / ((N:ℝ) + 1)) * ((N:ℝ) + 1) = B := by field_simp
    rw [this]; exact h2
  have h4 := abs_sub_abs_le_abs_sub (∑ j ∈ Ioc n N, cos (j * y) / j)
    ((∑ k ∈ Ioc n N, cos (k * y)) / ((N : ℝ) + 1))
  have e : 1 / (((n:ℝ) + 1) * sin (y / 2)) = B * (1 / ((n:ℝ) + 1)) := by
    rw [hB]; field_simp
  rw [e]
  linarith

/-- `|1 - e^{iy}| = 2 sin(y/2)` for `0 < y < 2π`. PROVED. -/
theorem norm_one_sub_exp (y : ℝ) (hy0 : 0 < y) (hy : y < 2 * π) :
    ‖(1 : ℂ) - Complex.exp (y * Complex.I)‖ = 2 * sin (y / 2) := by
  have hs : 0 < sin (y / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [← pow_left_inj₀ (norm_nonneg _) (by positivity : (0:ℝ) ≤ 2 * sin (y / 2)) two_ne_zero,
    Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have h2 : cos y = 1 - 2 * sin (y / 2) ^ 2 := by
    have := cos_two_mul (y / 2); rw [show 2 * (y / 2) = y by ring] at this
    rw [this]; nlinarith [sin_sq_add_cos_sq (y / 2)]
  nlinarith [sin_sq_add_cos_sq y]

/-- Real part of the Taylor series of `-log(1 - w)` at `w = x e^{iy}`, `0 ≤ x < 1`,
from Mathlib's `Complex.hasSum_taylorSeries_neg_log`. PROVED. -/
theorem series_value (y : ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => cos (n * y) / n * x ^ n)
      (-log ‖(1 : ℂ) - (x : ℂ) * Complex.exp (y * Complex.I)‖) := by
  have hw : ‖(x : ℂ) * Complex.exp (y * Complex.I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx0]; linarith
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hw)
  rw [Complex.neg_re, Complex.log_re] at h
  convert h using 2 with n
  have e : ((x : ℂ) * Complex.exp (y * Complex.I)) ^ n / n =
      ((x ^ n / n : ℝ) : ℂ) * Complex.exp (((n * y : ℝ)) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; ring

/-- Boundary value of the logarithmic series, Zygmund, Trigonometric Series, Chapter I,
formula 2.8: for `0 < y < 2π` the partial sums of `∑ cos(jy)/j` converge to
`-log(2 sin(y/2))`, the real part of `-log(1 - e^{iy})`. Convergence by the Abel tail bound
`cos_tail_abs_le`, the value by Abel's limit theorem, Mathlib's
`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`, and continuity of `-log|1 - x e^{iy}|` at
`x = 1`. PROVED. -/
theorem cos_series_tendsto (y : ℝ) (hy0 : 0 < y) (hy : y < 2 * π) :
    Tendsto (fun N : ℕ => ∑ j ∈ Icc 1 N, cos (j * y) / j) atTop
      (𝓝 (-log (2 * sin (y / 2)))) := by
  have hs : 0 < sin (y / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set u : ℕ → ℝ := fun N => ∑ j ∈ Icc 1 N, cos (j * y) / j with hu
  have e : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => by
    simpa using Finset.Icc_add_one_left_eq_Ioc (0:ℕ) m
  have hsplit : ∀ M N, M ≤ N → u N - u M = ∑ j ∈ Ioc M N, cos (j * y) / j := by
    intro M N hMN
    simp only [hu, e]
    rw [← sum_Ioc_consecutive _ (Nat.zero_le M) hMN]; ring
  -- Cauchy by the Abel tail bound
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / (ε * sin (y / 2)))
    refine ⟨M, fun N hN => ?_⟩
    rw [Real.dist_eq, hsplit M N hN]
    refine lt_of_le_of_lt (cos_tail_abs_le y hy0 hy M N) ?_
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hM
    nlinarith
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- range form for Abel's theorem
  set f : ℕ → ℝ := fun n => cos (n * y) / n with hf
  have hrange : ∀ N, ∑ i ∈ range (N + 1), f i = u N := by
    intro N
    induction N with
    | zero => simp [hf, hu]
    | succ N ih =>
      rw [sum_range_succ, ih]
      simp only [hu, hf]
      rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  have hl' : Tendsto (fun n => ∑ i ∈ range n, f i) atTop (𝓝 l) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa only [hrange] using hl
  have hA := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl'
  -- the Abel means equal -log ‖1 - x e^{iy}‖
  set g : ℝ → ℝ := fun x => -log ‖(1 : ℂ) - (x : ℂ) * Complex.exp (y * Complex.I)‖ with hg
  have hev : (fun x => ∑' n, f n * x ^ n) =ᶠ[𝓝[<] 1] g := by
    have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [this] with x hx
    exact (series_value y x hx.1.le hx.2).tsum_eq
  have hg1 : g 1 = -log (2 * sin (y / 2)) := by
    simp only [hg]; push_cast; rw [one_mul, norm_one_sub_exp y hy0 hy]
  have hcont : ContinuousAt g 1 := by
    have hne : ‖(1 : ℂ) - ((1:ℝ) : ℂ) * Complex.exp (y * Complex.I)‖ ≠ 0 := by
      push_cast; rw [one_mul, norm_one_sub_exp y hy0 hy]; positivity
    apply ContinuousAt.neg
    exact ContinuousAt.log
      (f := fun x : ℝ => ‖(1 : ℂ) - (x : ℂ) * Complex.exp (y * Complex.I)‖) (by fun_prop) hne
  have hg' : Tendsto g (𝓝[<] 1) (𝓝 (g 1)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hA' : Tendsto g (𝓝[<] 1) (𝓝 l) := hA.congr' hev
  have := tendsto_nhds_unique hA' hg'
  rw [this, hg1] at hl
  exact hl

/-- Elementary concavity step: for `n ≥ 1` and `1/(2n) ≤ s ≤ 1`,
`-(log 2 + 2/n) ≤ -log(2s) - 1/((n+1)s)`. With `t = 1/s ∈ [1, 2n]` this is
`t/(n+1) ≤ log t + 2/n`, a concave function checked at the two endpoints. PROVED. -/
theorem log_calc (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs1 : 1 / (2 * n) ≤ s) (hs2 : s ≤ 1) :
    -(log 2 + 2 / n) ≤ -log (2 * s) - 1 / ((n + 1) * s) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs1
  set t := 1 / s with ht
  have ht0 : 0 < t := by positivity
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hs0]; linarith
  have ht2 : t ≤ 2 * n := by
    rw [ht, div_le_iff₀ hs0]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * n)).1 hs1
    linarith
  have hlog : log (2 * s) = log 2 - log t := by
    rw [ht, one_div, log_inv, log_mul (by norm_num) hs0.ne']; ring
  have hinv : 1 / ((n + 1) * s) = t / (n + 1) := by
    rw [ht]; field_simp
  rw [hlog, hinv]
  -- concavity of f t = log t - t/(n+1) on [1, 2n]
  set f : ℝ → ℝ := fun x => log x + (-(1 / ((n:ℝ) + 1))) * x with hf
  have hconc : ConcaveOn ℝ (Set.Icc 1 (2 * (n:ℝ))) f := by
    have h1 : ConcaveOn ℝ (Set.Icc 1 (2 * (n:ℝ))) log :=
      strictConcaveOn_log_Ioi.concaveOn.subset
        (fun x hx => Set.mem_Ioi.2 (lt_of_lt_of_le one_pos hx.1)) (convex_Icc _ _)
    have h2 : ConcaveOn ℝ (Set.Icc 1 (2 * (n:ℝ))) (fun x => (-(1 / ((n:ℝ) + 1))) * x) :=
      (LinearMap.mul ℝ ℝ (-(1 / ((n:ℝ) + 1)))).concaveOn (convex_Icc _ _)
    exact h1.add h2
  have hmin := hconc.min_le_of_mem_Icc (x := 1) (y := 2 * (n:ℝ)) (z := t)
    ⟨le_refl _, by linarith⟩ ⟨by linarith, le_refl _⟩ ⟨ht1, ht2⟩
  have hfa : f 1 = -(1 / ((n:ℝ) + 1)) := by simp [hf]
  have hA : -(2 / (n:ℝ)) ≤ f 1 := by
    rw [hfa, neg_le_neg_iff, div_le_div_iff₀ (by positivity) hn0]; linarith
  have hB : -(2 / (n:ℝ)) ≤ f (2 * n) := by
    simp only [hf]
    have l2 := Real.log_two_gt_d9
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this; norm_num; linarith
    rcases Nat.lt_or_ge n 4 with h' | h'
    · have hn2 : (2:ℝ) ≤ n := by exact_mod_cast h
      have hn4 : (n:ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
      have hl : log 4 ≤ log (2 * n) := log_le_log (by norm_num) (by linarith)
      have h4 : log 4 = 2 * log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
      have e1 : -(1 / ((n:ℝ) + 1)) * (2 * n) = -2 + 2 / (n + 1) := by field_simp; ring
      rw [e1]
      have : 2 / ((n:ℝ) + 1) ≥ 1 / 2 := by rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      have : 2 / (n:ℝ) ≥ 2 / 3 := by rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      linarith
    · have hn4 : (4:ℝ) ≤ n := by exact_mod_cast h'
      have hl : log 8 ≤ log (2 * n) := log_le_log (by norm_num) (by linarith)
      have h8 : 2 < log 8 := by
        rw [lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        have e : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
        rw [e]; nlinarith [exp_pos 1]
      have e1 : -(1 / ((n:ℝ) + 1)) * (2 * n) = -2 + 2 / (n + 1) := by field_simp; ring
      rw [e1]
      have : 0 < 2 / ((n:ℝ) + 1) := by positivity
      have : 0 < 2 / (n:ℝ) := by positivity
      linarith
  have hft : -(2 / (n:ℝ)) ≤ f t := le_trans (le_min hA hB) hmin
  simp only [hf] at hft
  have : -(1 / ((n:ℝ) + 1)) * t = -(t / (n + 1)) := by ring
  rw [this] at hft
  linarith

/-- The case `0 ≤ y ≤ π`, assembled from `cos_series_tendsto`, `cos_tail_abs_le` and `log_calc`. -/
theorem cos_partial_lower_Icc (y : ℝ) (hy0 : 0 ≤ y) (hyπ : y ≤ π) (n : ℕ) (hn : 1 ≤ n) :
    -(log 2 + 2 / n) ≤ ∑ j ∈ Icc 1 n, cos (j * y) / j := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  by_cases hsmall : n * y ≤ π / 2
  · have hsum : 0 ≤ ∑ j ∈ Icc 1 n, cos (j * y) / j := by
      refine sum_nonneg fun j hj => ?_
      have hj := mem_Icc.1 hj
      have hjr : (j : ℝ) ≤ n := by exact_mod_cast hj.2
      apply div_nonneg _ (Nat.cast_nonneg j)
      apply cos_nonneg_of_mem_Icc
      constructor
      · have : 0 ≤ (j:ℝ) * y := mul_nonneg (Nat.cast_nonneg j) hy0
        linarith [pi_pos]
      · calc (j:ℝ) * y ≤ n * y := mul_le_mul_of_nonneg_right hjr hy0
          _ ≤ π / 2 := hsmall
    have : 0 < 2 / (n:ℝ) := by positivity
    linarith
  · push_neg at hsmall
    have hypos : 0 < y := by
      by_contra h; push_neg at h
      have : (n:ℝ) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn0.le h
      linarith [pi_pos]
    have hy2 : y < 2 * π := by linarith [pi_pos]
    set s := sin (y / 2) with hs
    have hs1 : s ≤ 1 := sin_le_one _
    have hsl : 2 / π * (y / 2) ≤ s := mul_le_sin (by linarith) (by linarith)
    have hs2 : 1 / (2 * n) ≤ s := by
      refine le_trans ?_ hsl
      rw [div_le_iff₀ (by positivity)]
      have : 2 / π * (y / 2) * (2 * n) = 2 * (n * y) / π := by ring
      rw [this, le_div_iff₀ pi_pos]; linarith
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs2
    have hlim := cos_series_tendsto y hypos hy2
    have hbd : ∀ N, n ≤ N → ∑ j ∈ Icc 1 N, cos (j * y) / j ≤
        ∑ j ∈ Icc 1 n, cos (j * y) / j + 1 / ((n + 1) * s) := by
      intro N hN
      have hsplit : ∑ j ∈ Icc 1 N, cos (j * y) / j =
          ∑ j ∈ Icc 1 n, cos (j * y) / j + ∑ j ∈ Ioc n N, cos (j * y) / j := by
        have e : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => by
          simpa using Finset.Icc_add_one_left_eq_Ioc (0:ℕ) m
        rw [e, e]
        exact (sum_Ioc_consecutive _ (Nat.zero_le n) hN).symm
      rw [hsplit]
      have := cos_tail_abs_le y hypos hy2 n N
      have := le_abs_self (∑ j ∈ Ioc n N, cos (j * y) / j)
      linarith
    have hL : -log (2 * s) ≤ ∑ j ∈ Icc 1 n, cos (j * y) / j + 1 / ((n + 1) * s) :=
      le_of_tendsto hlim (eventually_atTop.2 ⟨n, hbd⟩)
    have := log_calc n hn s hs2 hs1
    linarith

/-- The target, same statement as `PVLemmas1122.cos_partial_lower`, by reduction of y to
`[0, π]`. -/
theorem cos_partial_lower (y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    -(log 2 + 2 / n) ≤ ∑ j ∈ Icc 1 n, cos (j * y) / j := by
  set y0 := toIcoMod two_pi_pos (-π) y with hy0
  have hmem := toIcoMod_mem_Ico two_pi_pos (-π) y
  rw [← hy0] at hmem
  have hk := self_sub_toIcoMod two_pi_pos (-π) y
  rw [← hy0, zsmul_eq_mul] at hk
  set k := toIcoDiv two_pi_pos (-π) y
  have hcos : ∀ j : ℕ, cos (j * y) = cos (j * |y0|) := by
    intro j
    have : (j:ℝ) * y = j * y0 + ((j:ℤ) * k : ℤ) * (2 * π) := by
      push_cast; linear_combination (j:ℝ) * hk
    rw [this, cos_add_int_mul_two_pi]
    rcases abs_cases y0 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, cos_neg]
  simp_rw [hcos]
  apply cos_partial_lower_Icc |y0| (abs_nonneg _) _ n hn
  rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2]

example : type_of% @cos_partial_lower = type_of% @PVLemmas1122.cos_partial_lower := rfl

#print axioms log_calc
#print axioms cos_partial_lower_Icc
#print axioms cos_partial_lower
#print axioms norm_one_sub_exp
#print axioms series_value
#print axioms cos_series_tendsto
#print axioms dirichlet_cos_sum
#print axioms abs_cos_sum_le
#print axioms cos_tail_abs_le

end LeanLab.HelfgottMajor.PVCosLower1122
