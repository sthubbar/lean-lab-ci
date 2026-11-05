/-
Gallagher 1970 p.335 display 23 and the endpoint estimate below it.
Source https://doi.org/10.1007/bf01403187
AI wrote this Lean code. Codex task335. Goldbach is open.
-/
import LeanLab.Linnik.Decomp335a
import LeanLab.Linnik.Decomp307a

open Complex MeasureTheory Finset
open scoped Classical
open LeanLab.Linnik.Decomp1532b LeanLab.Linnik.Decomp1532b2
open LeanLab.Linnik.Decomp307a

namespace LeanLab.Linnik.Decomp335b

/-- Gallagher p.335 the prime detector coefficients obey the von Mangoldt majorant. -/
theorem norm_primeWindowCoefficient_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x v : ℝ) (n : ℕ) :
    ‖primeWindowCoefficient χ x v n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  unfold primeWindowCoefficient
  split_ifs with hn
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hn.2]
    have hlog : 0 ≤ Real.log n / (n : ℝ) :=
      div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
    have hexp : ‖Complex.exp (-((Real.log n * v : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]
      norm_num only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, neg_zero, Real.exp_zero]
    have hcoef : ‖(Real.log n / (n : ℝ) : ℂ)‖ = Real.log n / (n : ℝ) := by
      rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg hlog]
    rw [norm_mul, norm_mul, hcoef, hexp, mul_one]
    exact mul_le_of_le_one_right hlog (χ.norm_le_one _)
  · simp only [norm_zero]
    positivity

/-- Gallagher p.335 the prime detector has at most logarithmic reciprocal mass. -/
theorem norm_primeDetector_le_log : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (x y v : ℝ), 1 ≤ y →
      ‖primeDetector χ x y v‖ ≤ Real.log y + K := by
  obtain ⟨K, hK, hmass⟩ := mangoldt_reciprocal_sum_le_log
  refine ⟨K, hK, ?_⟩
  intro q χ x y v hy
  rw [← sum_primeWindowCoefficient]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊y⌋₊, ‖primeWindowCoefficient χ x v n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
      sum_le_sum (fun n _ => norm_primeWindowCoefficient_le χ x v n)
    _ = ∑ n ∈ Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      symm
      apply sum_subset
      · intro n hn
        exact mem_Icc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩
      · intro n hn hnot
        have hn0 : n = 0 := by
          have hu := (mem_Icc.mp hn).2
          by_contra hne
          exact hnot (mem_Icc.mpr ⟨by omega, hu⟩)
        subst n
        simp
    _ ≤ _ := hmass y hy

/-- Gallagher p.335 the endpoint estimate before partial summation.
This bound has no zero or large series hypothesis. -/
theorem poisson_endpoint_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ D : ℝ, 0 < D →
    ∃ b₂ : ℝ, 0 < b₂ ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q)
      (k : ℕ) (r x y v : ℝ), 0 ≤ r → 1 ≤ y → b₂ * k ≤ r * Real.log y →
      Decomp1532b2.poissonKernel k (r * Real.log y) * ‖primeDetector χ x y v‖ ≤
        (1 / (2 * D)) ^ k * (Real.log y + K) := by
  obtain ⟨K, hK, hmass⟩ := norm_primeDetector_le_log
  refine ⟨K, hK, ?_⟩
  intro D hD
  obtain ⟨b₂, hb₂, htail⟩ := poissonKernel_large_tail D hD
  refine ⟨b₂, hb₂, ?_⟩
  intro q χ k r x y v hr hy hscale
  have hu : 0 ≤ r * Real.log y := mul_nonneg hr (Real.log_nonneg hy)
  have he : Real.exp (-(r * Real.log y) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hp : Decomp1532b2.poissonKernel k (r * Real.log y) ≤ (1 / (2 * D)) ^ k :=
    (htail k _ hu hscale).trans (mul_le_of_le_one_right (by positivity) he)
  exact mul_le_mul hp (hmass q χ x y v hy) (norm_nonneg _)
    (by positivity)

/-- Gallagher p.335 the endpoint geometric budget is absorbed for large k.
The index threshold is uniform in positive D and in positive r at most one. -/
theorem endpoint_budget_absorbed (H K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ k₀ : ℕ, ∀ D : ℝ, 0 < D → ∀ k : ℕ, k₀ ≤ k → ∀ r y : ℝ,
      0 < r → r ≤ 1 → r * Real.log y ≤ H * k →
      (1 / (2 * D)) ^ k * (Real.log y + K) ≤ η / (D ^ k * r) := by
  have hlim : Filter.Tendsto (fun k : ℕ => (H * k + K) / (2 : ℝ) ^ k)
      Filter.atTop (nhds 0) := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).const_mul H
    have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)).const_mul K
    convert h1.add h0 using 1 <;> simp [pow_one, pow_zero, div_eq_mul_inv, add_mul, mul_assoc]
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hlim).2 η hη)
  refine ⟨k₀, ?_⟩
  intro D hD k hk r y hr hr1 hscale
  apply (le_div_iff₀ (by positivity : 0 < D ^ k * r)).mpr
  have heq : ((1 / (2 * D)) ^ k * (Real.log y + K)) * (D ^ k * r) =
      (r * Real.log y + K * r) / (2 : ℝ) ^ k := by
    rw [div_pow, mul_pow]
    field_simp
    <;> ring
  rw [heq]
  calc
    _ ≤ (H * k + K) / (2 : ℝ) ^ k := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul_of_nonneg_left hr1 hK
      nlinarith
    _ ≤ η := (hk₀ k hk).le

/-- Gallagher p.335 the endpoint term is negligible compared with the
supplied Poisson scale for a sufficiently large index and two cutoff scales.
No zero or lower bound for the full series is assumed. -/
theorem poisson_endpoint_negligible (H η : ℝ) (hη : 0 < η) :
    ∀ D : ℝ, 0 < D → ∃ b₂ : ℝ, 0 < b₂ ∧ ∃ k₀ : ℕ,
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (k : ℕ) (r x y v : ℝ),
        k₀ ≤ k → 0 < r → r ≤ 1 → 1 ≤ y →
        b₂ * k ≤ r * Real.log y → r * Real.log y ≤ H * k →
        Decomp1532b2.poissonKernel k (r * Real.log y) * ‖primeDetector χ x y v‖ ≤
          η / (D ^ k * r) := by
  obtain ⟨K, hK, hbound⟩ := poisson_endpoint_bound
  obtain ⟨k₀, hbudget⟩ := endpoint_budget_absorbed H K η hK hη
  intro D hD
  obtain ⟨b₂, hb₂, hend⟩ := hbound D hD
  refine ⟨b₂, hb₂, k₀, ?_⟩
  intro q χ k r x y v hk hr hr1 hy hlo hhi
  exact (hend q χ k r x y v hr.le hy hlo).trans (hbudget D hD k hk r y hr hr1 hhi)

/-- Gallagher p.335 choice of the dyadic index and the two cutoff slopes.
This is only the common integer index geometry. It makes no arithmetic
lower bound or prime power absorption claim. -/
theorem poisson_dyadic_cutoffs (E b₁ b₂ : ℝ)
    (hE : 1 ≤ E) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 < B ∧
      ∀ T r x : ℝ, 2 ≤ T → 1 / Real.log T ≤ r → T ^ A ≤ x →
        ∃ M : ℕ, E * r * Real.log T ≤ M ∧
          ∀ k : ℕ, M ≤ k → k < 2 * M →
            r * Real.log x ≤ b₁ * k ∧ b₂ * k ≤ r * Real.log (x ^ B) := by
  let H : ℝ := max 1 (1 / b₁)
  let B : ℝ := 2 * b₂ * (H + 1) + 2
  have hH : 1 ≤ H := le_max_left _ _
  have hH0 : 0 < H := by linarith
  have hB : 1 < B := by
    have hh := mul_pos hb₂ (show 0 < H + 1 by linarith)
    dsimp [B]
    nlinarith
  refine ⟨E, B, hE, hB, ?_⟩
  intro T r x hT hrlo hx
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlogT).trans_le hrlo
  have hscale : 1 ≤ r * Real.log T := by
    have hh := mul_le_mul_of_nonneg_right hrlo hlogT.le
    have he : (1 / Real.log T) * Real.log T = 1 := by field_simp
    rwa [he] at hh
  have hx1 : 1 ≤ x :=
    (Real.one_le_rpow (by linarith : 1 ≤ T) (by linarith : 0 ≤ E)).trans hx
  have hx0 : 0 < x := by linarith
  have hlogx : E * Real.log T ≤ Real.log x := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos (by linarith : 0 < T) E) hx
    rw [Real.log_rpow (by linarith : 0 < T)] at hh
    nlinarith
  let u : ℝ := r * Real.log x
  have huE : E * r * Real.log T ≤ u := by
    have hh := mul_le_mul_of_nonneg_left hlogx hr.le
    dsimp [u]
    nlinarith
  have hu1 : 1 ≤ u := by
    have hh := mul_le_mul_of_nonneg_right hE (mul_nonneg hr.le hlogT.le)
    nlinarith
  have hu0 : 0 ≤ u := by linarith
  let M : ℕ := ⌈H * u⌉₊
  have hMlo : H * u ≤ (M : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) < H * u + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨M, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hH hu0
    nlinarith
  · intro k hklo hkhi
    have hklo' : (M : ℝ) ≤ k := by exact_mod_cast hklo
    have hkhi' : (k : ℝ) < 2 * M := by exact_mod_cast hkhi
    have hsmall : 1 ≤ b₁ * H := by
      have hh := mul_le_mul_of_nonneg_left (le_max_right 1 (1 / b₁)) hb₁.le
      dsimp only [H]
      have he : b₁ * (1 / b₁) = 1 := by field_simp
      rwa [he] at hh
    constructor
    · have h1 := mul_le_mul_of_nonneg_left (hMlo.trans hklo') hb₁.le
      have h2 := mul_le_mul_of_nonneg_right hsmall hu0
      dsimp only [u] at *
      nlinarith
    · have hupper : (k : ℝ) ≤ 2 * (H + 1) * u := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hupper hb₂.le
      rw [Real.log_rpow hx0]
      dsimp only [B, u] at *
      nlinarith

/-- Gallagher p.335 prime power absorption audit. At radius one quarter,
base two and lower cutoff slope one eighth, the uniform square root error
bound is larger than the requested series lower bound for every x at least 64.
This disproves the scalar absorption route, not the localization statement. -/
theorem uniform_prime_power_budget_too_large {x : ℝ} (k : ℕ) (hx : 64 ≤ x)
    (hscale : (1 / 4 : ℝ) * Real.log x ≤ (1 / 8 : ℝ) * k) :
    4 / (2 : ℝ) ^ k < 1 / Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hklog : Real.log x ≤ (k : ℝ) * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hpow : x ≤ (2 : ℝ) ^ k := by
    have hh := Real.exp_le_exp.mpr hklog
    simpa only [Real.exp_log hx0, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hh
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs8 : 8 ≤ Real.sqrt x := by
    have hh := Real.sqrt_le_sqrt hx
    norm_num at hh
    exact hh
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  calc
    4 / (2 : ℝ) ^ k ≤ 4 / x := div_le_div_of_nonneg_left (by norm_num) hx0 hpow
    _ < 1 / Real.sqrt x := by
      apply (div_lt_div_iff₀ hx0 hs0).mpr
      nlinarith

/-- Gallagher p.333 Theorem 5 display 20 and p.335 partial summation.
CONDITIONAL ON the sealed poisson_window_localization only.
The full arithmetic series detector is proved in Decomp335a.
The target statement is exact and this assembly has no proof hole of its own. -/
theorem gallagher_zero_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  obtain ⟨r₀, E, D, η, hr₀, hr₀hi, hE, hD, hη, hseries⟩ :=
    LeanLab.Linnik.Decomp335a.poisson_series_detector_of_turan hpower
  obtain ⟨r₁, A, B, C, c, hr₁, hA, hB, hC, hc, hwindow⟩ :=
    LeanLab.Linnik.Decomp307a.poisson_window_localization E D η hE hD hη
  refine ⟨min r₀ r₁, A, B, C, c, lt_min hr₀ hr₁, (min_le_left _ _).trans hr₀hi,
    hA, hB, hC, hc, ?_⟩
  intro T hT q hq hqT χ v r hv hχ hrlo hrhi hz x hx
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hl).trans_le hrlo
  have hx1 : 1 ≤ x :=
    (Real.one_le_rpow (by linarith : 1 ≤ T) (by linarith : 0 ≤ A)).trans hx
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  obtain ⟨k, hk⟩ := hwindow T hT q hqT χ v r hv hrlo (hrhi.trans (min_le_right _ _))
    (hseries T hT q hqT χ v r hv hχ hrlo (hrhi.trans (min_le_left _ _)) hz) x hx
  have hh := hk.trans (LeanLab.Linnik.Decomp307a.prime_poisson_partial_summation χ k v hr.le hx1 hxy)
  exact (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_comm r] using hh)


end LeanLab.Linnik.Decomp335b
