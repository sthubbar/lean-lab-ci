import LeanLab.PNTPort.DirichletZF.Siegel

/-!
# An effective lower bound for `L(1, χ)` without an exceptional zero

Lab proof, unit U-5176. AI wrote this file. Known mathematics, no cited input; the one-character
form of Estermann's argument, Davenport chapter 21, on `F(s) = ζ(s) L(s, χ)`.

`effective_L_one`: there is an absolute `c > 0` such that for every `N ≥ 8` and every real
non-principal `χ` mod `N` with no real zero of `L(s, χ)` in `[1 - 1/(8 log N), 1)`,

  `‖L(1, χ)‖ ≥ c / log N`.

Unlike `siegel` the constant here is effective, though not computed: it comes from
`norm_G1_sphere_le`, a compactness bound for `ζ` on a circle.
-/

namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Topology Metric Nat LSeries
open scoped LSeries.notation ComplexOrder Real

variable {N : ℕ} [NeZero N]

/-- `F = ζ L(χ)`. -/
noncomputable def F1 (χ : DirichletCharacter ℂ N) : ℂ → ℂ := fun s ↦
  riemannZeta s * DirichletCharacter.LFunction χ s

/-- `c(n) = Λ(n)(1 + χ(n))`. -/
noncomputable def c1 (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  ↗ArithmeticFunction.vonMangoldt + ↗χ * ↗ArithmeticFunction.vonMangoldt

omit [NeZero N] in
lemma c1_eq_real {χ : DirichletCharacter ℂ N} (h : χ ^ 2 = 1) (n : ℕ) :
    c1 χ n = ((ArithmeticFunction.vonMangoldt n * (1 + (χ n).re) : ℝ) : ℂ) := by
  simp only [c1, Pi.add_apply, Pi.mul_apply]
  apply Complex.ext <;> simp [im_eq_zero_of_sq h n, Complex.mul_re, Complex.mul_im]
  ring

omit [NeZero N] in
lemma summable_c1 {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (c1 χ) s := by
  unfold c1
  exact LSeriesSummable.add (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)

omit [NeZero N] in
lemma abscissa_c1_le (χ : DirichletCharacter ℂ N) : abscissaOfAbsConv (c1 χ) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
    summable_c1 (by simpa using hy)

omit [NeZero N] in
lemma two_gt_abscissa_c1 (χ : DirichletCharacter ℂ N) : abscissaOfAbsConv (c1 χ) < (2 : ℂ).re :=
  lt_of_le_of_lt (abscissa_c1_le χ)
    (by simp only [Complex.re_ofNat]; exact_mod_cast (show (1 : ℝ) < 2 by norm_num))

omit [NeZero N] in
lemma Q1_signs {χ : DirichletCharacter ℂ N} (h : χ ^ 2 = 1) (j : ℕ) :
    0 ≤ (-1) ^ j * iteratedDeriv j (LSeries (c1 χ)) 2 := by
  rw [LSeries_iteratedDeriv j (two_gt_abscissa_c1 χ), ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  unfold LSeries
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, logMul_iter_apply, c1_eq_real h]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : (n : ℂ) ^ (2 : ℂ) = (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, Complex.ofReal_cpow hn0.le]
  have e2 : Complex.log n = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [e1, e2]
  obtain ⟨a, -⟩ := real_char_bound χ n
  have : 0 ≤ Real.log n ^ j * (ArithmeticFunction.vonMangoldt n * (1 + (χ n).re)) /
      (n : ℝ) ^ (2 : ℝ) :=
    div_nonneg (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _)
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by linarith)))
      (Real.rpow_nonneg hn0.le _)
  have h' := Complex.zero_le_real.mpr this
  push_cast at h' ⊢
  exact h'

/-- `(-1)^m F^{(m)}(2) ≥ 0`. -/
theorem F1_taylor_nonneg {χ : DirichletCharacter ℂ N} (h : χ ^ 2 = 1) (m : ℕ) :
    0 ≤ (-1) ^ m * iteratedDeriv m (F1 χ) 2 := by
  set U : Set ℂ := {z | 1 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2 : ℂ) ∈ U := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hne : ∀ z ∈ U, z ≠ 1 := by intro z hz h; simp [U, h] at hz
  have hdL : ∀ z ∈ U, DifferentiableAt ℂ (DirichletCharacter.LFunction χ) z :=
    fun z hz ↦ DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (hne z hz))
  have hdZ : ∀ z ∈ U, DifferentiableAt ℂ riemannZeta z :=
    fun z hz ↦ differentiableAt_riemannZeta (hne z hz)
  have hdF : DifferentiableOn ℂ (F1 χ) U := fun z hz ↦
    ((hdZ z hz).mul (hdL z hz)).differentiableWithinAt
  have hFan : AnalyticAt ℂ (F1 χ) 2 := hdF.analyticAt (hUo.mem_nhds h2U)
  have hQan : AnalyticAt ℂ (LSeries (c1 χ)) 2 := LSeries_analyticOnNhd _ 2 (two_gt_abscissa_c1 χ)
  refine sign_of_logDeriv hFan hQan ?_ ?_ (Q1_signs h) m
  · filter_upwards [hUo.mem_nhds h2U] with z hz
    have hz1 : 1 < z.re := hz
    have nZ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz1
    have nL : DirichletCharacter.LFunction χ z ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (hne z hz)) hz1.le
    have hlog : logDeriv (F1 χ) z = -LSeries (c1 χ) z := by
      have e : F1 χ = riemannZeta * DirichletCharacter.LFunction χ := rfl
      rw [e, logDeriv_mul z nZ nL (hdZ z hz) (hdL z hz)]
      simp only [logDeriv_apply]
      have eZ : deriv riemannZeta z / riemannZeta z =
          -LSeries ↗ArithmeticFunction.vonMangoldt z := by
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz1]; ring
      have eL : deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z =
          -LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) z := by
        rw [← neg_logDeriv_eq_LSeries χ hz1]; ring
      rw [eZ, eL]
      have s1 := ArithmeticFunction.LSeriesSummable_vonMangoldt hz1
      have s2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hz1
      have eQ : LSeries (c1 χ) z = LSeries ↗ArithmeticFunction.vonMangoldt z +
          LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) z := by
        unfold c1; rw [LSeries_add s1 s2]
      rw [eQ]; ring
    have hFz : F1 χ z ≠ 0 := mul_ne_zero nZ nL
    rw [logDeriv_apply] at hlog
    rw [show deriv (F1 χ) z = F1 χ z * (deriv (F1 χ) z / F1 χ z) by field_simp, hlog]
    ring
  · have e2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    simp only [F1]
    rw [e2]
    exact mul_nonneg (riemannZeta_real_nonneg (by norm_num)) (LFunction_real_nonneg h (by norm_num))

/-- `G = dslope ((s - 1) ζ L(χ)) 1`. -/
noncomputable def G1 (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  dslope (fun s ↦ zetaOne s * DirichletCharacter.LFunction χ s) 1

lemma G1_differentiable {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : Differentiable ℂ (G1 χ) := by
  rw [← differentiableOn_univ]
  unfold G1
  rw [differentiableOn_dslope univ_mem]
  exact (zetaOne_differentiable.mul (DirichletCharacter.differentiable_LFunction hχ)).differentiableOn

lemma G1_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    G1 χ s = F1 χ s - DirichletCharacter.LFunction χ 1 / (s - 1) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold G1
  rw [dslope_of_ne _ hs, slope_def_field, zetaOne_of_ne hs]
  have h1 : zetaOne 1 = 1 := by simp [zetaOne]
  rw [h1]
  simp only [F1]
  field_simp

lemma iteratedDeriv_G1_two {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (m : ℕ) :
    iteratedDeriv m (G1 χ) 2 =
      iteratedDeriv m (F1 χ) 2 - DirichletCharacter.LFunction χ 1 * ((-1) ^ m * (m ! : ℂ)) := by
  have hne : ∀ᶠ z in 𝓝 (2 : ℂ), z ≠ 1 := isOpen_ne.mem_nhds (by norm_num)
  have hev : G1 χ =ᶠ[𝓝 (2 : ℂ)]
      fun z ↦ F1 χ z - DirichletCharacter.LFunction χ 1 * (z - 1)⁻¹ := by
    filter_upwards [hne] with z hz
    rw [G1_eq χ hz, div_eq_mul_inv]
  rw [(hev.iteratedDeriv m).eq_of_nhds]
  set U : Set ℂ := {z | 1 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2 : ℂ) ∈ U := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hneU : ∀ z ∈ U, z ≠ 1 := by intro z hz h; simp [U, h] at hz
  have hdF : DifferentiableOn ℂ (F1 χ) U := fun z hz ↦
    ((differentiableAt_riemannZeta (hneU z hz)).mul
      (DirichletCharacter.differentiable_LFunction hχ z)).differentiableWithinAt
  have hFc : ContDiffAt ℂ m (F1 χ) 2 := (hdF.analyticAt (hUo.mem_nhds h2U)).contDiffAt
  have hdI : DifferentiableOn ℂ (fun z : ℂ ↦ (z - 1)⁻¹) U := fun z hz ↦
    (DifferentiableAt.inv (h := fun z : ℂ ↦ z - 1) (by fun_prop)
      (sub_ne_zero.mpr (hneU z hz))).differentiableWithinAt
  have hIc : ContDiffAt ℂ m (fun z : ℂ ↦ DirichletCharacter.LFunction χ 1 * (z - 1)⁻¹) 2 :=
    contDiffAt_const.mul (hdI.analyticAt (hUo.mem_nhds h2U)).contDiffAt
  rw [iteratedDeriv_fun_sub hFc hIc, iteratedDeriv_const_mul_field,
    iteratedDeriv_inv_sub_one m (by norm_num)]
  norm_num

lemma F1_two_ge (χ : DirichletCharacter ℂ N) : 1 ≤ ‖F1 χ 2‖ := by
  have hz : ‖riemannZeta 2‖ = π ^ 2 / 6 := by
    rw [riemannZeta_two, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  have a := norm_LFunction_two_ge χ
  simp only [F1, norm_mul, hz]
  have hpi : 0 < π ^ 2 := by positivity
  calc (1 : ℝ) = π ^ 2 / 6 * (6 / π ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left a (by positivity)

theorem norm_G1_sphere_le : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ s ∈ sphere (2 : ℂ) (3 / 2), ‖G1 χ s‖ ≤ C * N := by
  have hcont : ContinuousOn riemannZeta (sphere (2 : ℂ) (3 / 2)) := fun s hs ↦
    (differentiableAt_riemannZeta (sphere_facts hs).1).continuousAt.continuousWithinAt
  obtain ⟨Cz, hCz⟩ := (isCompact_sphere (2 : ℂ) (3 / 2)).exists_bound_of_continuousOn hcont
  refine ⟨7 * max Cz 0 + 2, by positivity, fun N _ χ hχ s hs ↦ ?_⟩
  obtain ⟨hs1, hsd, hsre, hsn⟩ := sphere_facts hs
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hL : ‖DirichletCharacter.LFunction χ s‖ ≤ 7 * N := by
    have := norm_LFunction_le hχ (s := s) (by linarith)
    calc _ ≤ N * ‖s‖ / s.re := this
      _ ≤ N * (7 / 2) / (1 / 2) := by
          apply div_le_div₀ (by positivity) (by gcongr) (by norm_num) hsre
      _ = 7 * N := by ring
  have hL1 : ‖DirichletCharacter.LFunction χ 1‖ ≤ N := by
    have := norm_LFunction_le hχ (s := 1) (by norm_num)
    simpa using this
  rw [G1_eq χ hs1]
  have hF : ‖F1 χ s‖ ≤ max Cz 0 * (7 * N) := by
    simp only [F1, norm_mul]
    exact mul_le_mul ((hCz s hs).trans (le_max_left Cz 0)) hL (norm_nonneg _) (le_max_right _ _)
  have hpos : 0 < ‖s - 1‖ := by linarith
  have hQ : ‖DirichletCharacter.LFunction χ 1 / (s - 1)‖ ≤ 2 * N := by
    rw [norm_div, div_le_iff₀ hpos]
    nlinarith [norm_nonneg (DirichletCharacter.LFunction χ 1)]
  calc ‖F1 χ s - DirichletCharacter.LFunction χ 1 / (s - 1)‖
      ≤ ‖F1 χ s‖ + ‖DirichletCharacter.LFunction χ 1 / (s - 1)‖ := norm_sub_le _ _
    _ ≤ max Cz 0 * (7 * N) + 2 * N := add_le_add hF hQ
    _ = (7 * max Cz 0 + 2) * N := by ring

theorem estermann1 : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 → ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 → ∀ K : ℕ,
      1 ≤ K → 1 - ‖DirichletCharacter.LFunction χ 1‖ * (2 - σ) ^ K / (1 - σ) -
        4 * (C * (N : ℝ)) * (3 / 4) ^ K ≤ (F1 χ σ).re := by
  obtain ⟨C, hC, hCb⟩ := norm_G1_sphere_le
  refine ⟨C, hC, fun N _ χ h1 r1 σ hσ hσ1 K hK1 ↦ ?_⟩
  set B := C * (N : ℝ) with hB
  have hB0 : 0 ≤ B := by positivity
  set lam := DirichletCharacter.LFunction χ 1 with hlam
  set x : ℝ := 2 - σ with hx
  have hx1 : 1 < x := by rw [hx]; linarith
  have hx98 : x ≤ 9 / 8 := by rw [hx]; linarith
  have hGd := G1_differentiable h1
  have hT := Complex.hasSum_taylorSeries_of_entire hGd 2 (σ : ℂ)
  set g : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (G1 χ) 2
    with hg
  -- the coefficients
  set b : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (F1 χ) 2) with hb
  have hbn : ∀ n, 0 ≤ b n := fun n ↦
    mul_nonneg (by
      have : (0 : ℂ) ≤ (n ! : ℂ) := by exact_mod_cast Nat.zero_le _
      exact inv_nonneg.mpr this) (F1_taylor_nonneg r1 n)
  have hgform : ∀ n, g n = (x : ℂ) ^ n * b n - lam * (x : ℂ) ^ n := by
    intro n
    simp only [hg, hb, smul_eq_mul]
    rw [iteratedDeriv_G1_two h1 n]
    have hs : (σ : ℂ) - 2 = -(x : ℂ) := by rw [hx]; push_cast; ring
    rw [hs, neg_pow]
    have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have h11 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    have hinv : (n ! : ℂ)⁻¹ * (n ! : ℂ) = 1 := inv_mul_cancel₀ hf
    linear_combination (-lam * (x : ℂ) ^ n) * h11 +
      (-lam * (x : ℂ) ^ n * ((-1) ^ n * (-1) ^ n)) * hinv
  -- tail estimate
  have hgn : ∀ n, ‖g n‖ ≤ B * (3 / 4) ^ n := by
    intro n
    have hc : ‖iteratedDeriv n (G1 χ) 2‖ ≤ n ! * B / (3 / 2) ^ n :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
        (G1_differentiable h1).diffContOnCl (hCb N χ h1)
    simp only [hg, smul_eq_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have hs : ‖(σ : ℂ) - 2‖ = x := by
      rw [show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (by linarith), hx]; ring
    rw [hs]
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    calc (n ! : ℝ)⁻¹ * (x ^ n * ‖iteratedDeriv n (G1 χ) 2‖)
        ≤ (n ! : ℝ)⁻¹ * (x ^ n * (n ! * B / (3 / 2) ^ n)) := by gcongr
      _ = B * (x * (2 / 3)) ^ n := by
          have h32 : ((3 : ℝ) / 2) ^ n * (2 / 3) ^ n = 1 := by rw [← mul_pow]; norm_num
          have h32' : ((3 : ℝ) / 2) ^ n ≠ 0 := by positivity
          rw [mul_pow]
          field_simp
          linear_combination (-B) * h32
      _ ≤ B * (3 / 4) ^ n := by
          gcongr
          linarith
  have hsum_norm : Summable fun n ↦ ‖g n‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hgn
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left B)
  have hsum : Summable g := hsum_norm.of_norm
  have hsplit := (hsum.sum_add_tsum_nat_add K).symm
  rw [hT.tsum_eq] at hsplit
  -- the tail
  have htail : ‖∑' n, g (n + K)‖ ≤ 4 * B * (3 / 4) ^ K := by
    have hs2 : Summable fun n ↦ ‖g (n + K)‖ := (summable_nat_add_iff K).mpr hsum_norm
    calc ‖∑' n, g (n + K)‖ ≤ ∑' n, ‖g (n + K)‖ := norm_tsum_le_tsum_norm hs2
      _ ≤ ∑' n, B * (3 / 4) ^ K * (3 / 4) ^ n := by
          refine hs2.tsum_le_tsum (fun n ↦ ?_) ?_
          · have := hgn (n + K); rw [pow_add] at this; linarith
          · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      _ = 4 * B * (3 / 4) ^ K := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  -- the head
  have hhead : ∑ n ∈ Finset.range K, g n =
      ∑ n ∈ Finset.range K, (x : ℂ) ^ n * b n - lam * ∑ n ∈ Finset.range K, (x : ℂ) ^ n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ hgform n
  have hgeom : ∑ n ∈ Finset.range K, (x : ℂ) ^ n = ((x : ℂ) ^ K - 1) / ((x : ℂ) - 1) :=
    geom_sum_eq (by exact_mod_cast hx1.ne') K
  have hF : F1 χ σ = G1 χ σ + lam / ((σ : ℂ) - 1) := by
    rw [G1_eq χ (by intro h; have := congrArg Complex.re h; simp at this; linarith)]
    ring
  have hx1c : (x : ℂ) - 1 = -((σ : ℂ) - 1) := by rw [hx]; push_cast; ring
  have hσc : (σ : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hkey : F1 χ σ = ∑ n ∈ Finset.range K, (x : ℂ) ^ n * b n -
      lam * (x : ℂ) ^ K / (1 - σ) + ∑' n, g (n + K) := by
    rw [hF, hsplit, hhead, hgeom, hx1c]
    have h1σ : (1 : ℂ) - σ ≠ 0 := by
      intro h; apply hσc; linear_combination -h
    field_simp
    ring
  -- real parts
  have hpos : 0 < 1 - σ := by linarith
  have hb0 : 1 ≤ (b 0).re := by
    have h0 := hbn 0
    have hn := F1_two_ge χ
    simp only [hb, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul] at h0 ⊢
    have hre : (iteratedDeriv 0 (F1 χ) 2).im = 0 := by
      have := (Complex.nonneg_iff.mp h0).2; simp at this ⊢; linarith
    rw [iteratedDeriv_zero] at hre ⊢
    have hzr : F1 χ 2 = ((F1 χ 2).re : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [hzr, Complex.norm_real, Real.norm_eq_abs] at hn
    have hre0 : 0 ≤ (F1 χ 2).re := by
      have := (Complex.nonneg_iff.mp h0).1; simpa using this
    rwa [abs_of_nonneg hre0] at hn
  have hheadre : 1 ≤ (∑ n ∈ Finset.range K, (x : ℂ) ^ n * b n).re := by
    have hK : 0 < K := hK1
    rw [Complex.re_sum]
    have hterm : ∀ n ∈ Finset.range K, 0 ≤ ((x : ℂ) ^ n * b n).re := by
      intro n _
      have : (0 : ℂ) ≤ (x : ℂ) ^ n * b n :=
        mul_nonneg (pow_nonneg (by exact_mod_cast (by linarith : (0 : ℝ) ≤ x)) n) (hbn n)
      exact (Complex.nonneg_iff.mp this).1
    have h0 : 0 ∈ Finset.range K := Finset.mem_range.mpr hK
    calc 1 ≤ ((x : ℂ) ^ 0 * b 0).re := by simpa using hb0
      _ ≤ _ := Finset.single_le_sum hterm h0
  have hmid : -(‖lam‖ * x ^ K / (1 - σ)) ≤ (-(lam * (x : ℂ) ^ K / (1 - σ))).re := by
    have := Complex.re_le_norm (lam * (x : ℂ) ^ K / (1 - σ))
    have hn : ‖lam * (x : ℂ) ^ K / (1 - σ)‖ = ‖lam‖ * x ^ K / (1 - σ) := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < x)]
      rw [show ((1 : ℂ) - σ) = ((1 - σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpos]
    rw [neg_re]; linarith
  have htailre : -(4 * B * (3 / 4) ^ K) ≤ (∑' n, g (n + K)).re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm (∑' n, g (n + K))).trans htail)).1
    linarith
  rw [neg_re] at hmid
  rw [hkey, add_re, sub_re]
  linarith


/-- **Effective lower bound.** With no real zero of `L(s, χ)` in `[1 - 1/(8 log N), 1)`,
`‖L(1, χ)‖ ≥ c / log N` with an absolute `c`. -/
theorem effective_L_one : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N], 8 ≤ N →
    ∀ (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      (∀ σ : ℝ, 1 - 1 / (8 * Real.log N) ≤ σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
        c / Real.log N ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  obtain ⟨C₀, hC₀, hest⟩ := estermann1
  set C := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  set T := (4 * Real.log (8 * C) + 1) / 16 + 1 / 2 with hT
  refine ⟨Real.exp (-T) / 16, by positivity, fun N _ hN χ hχ hχ2 hnz ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 2 ≤ Real.log N := one_le_log_half hN
  have hlp : 0 < Real.log N := by linarith
  set u := 1 / (8 * Real.log N) with hu
  have hu0 : 0 < u := by positivity
  have hu16 : u ≤ 1 / 16 := by
    rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set β := 1 - u with hβ
  have hβ78 : 7 / 8 ≤ β := by linarith
  have hβ1 : β < 1 := by linarith
  set A := 8 * C * (N : ℝ) with hA
  have hA8 : 8 ≤ A := by rw [hA]; nlinarith
  have hApos : 0 < A := by linarith
  have hl43 := log_four_thirds_ge
  have hl43p : 0 < Real.log (4 / 3) := by linarith
  set K : ℕ := ⌈Real.log A / Real.log (4 / 3)⌉₊ with hK
  have hKge : Real.log A / Real.log (4 / 3) ≤ K := Nat.le_ceil _
  have hK1 : 1 ≤ K := by
    have hpos : 0 < Real.log A / Real.log (4 / 3) := div_pos (Real.log_pos (by linarith)) hl43p
    have : (0 : ℝ) < K := lt_of_lt_of_le hpos hKge
    exact_mod_cast this
  have hKle : (K : ℝ) ≤ Real.log A / Real.log (4 / 3) + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Real.log A / Real.log (4 / 3) by
      exact div_nonneg (Real.log_nonneg (by linarith)) hl43p.le)
    rw [← hK] at this; linarith
  have h34 : (3 / 4 : ℝ) ^ K ≤ 1 / A := by
    rw [le_div_iff₀ hApos]
    have : Real.log A ≤ K * Real.log (4 / 3) := by rwa [div_le_iff₀ hl43p] at hKge
    have e1 : (3 / 4 : ℝ) ^ K = Real.exp (-(K * Real.log (4 / 3))) := by
      rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, inv_pow, ← Real.exp_log
        (show (0 : ℝ) < (4 / 3) ^ K by positivity), Real.log_pow, Real.exp_neg]
    rw [e1]
    calc Real.exp (-(K * Real.log (4 / 3))) * A
        = Real.exp (-(K * Real.log (4 / 3))) * Real.exp (Real.log A) := by
          rw [Real.exp_log hApos]
      _ = Real.exp (Real.log A - K * Real.log (4 / 3)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  -- `(2 - β)^K ≤ e^T`
  have hxK : (2 - β) ^ K ≤ Real.exp T := by
    have hx : (2 - β) = 1 + u := by rw [hβ]; ring
    rw [hx]
    have h1 : (1 + u) ^ K ≤ Real.exp (u * K) := by
      rw [← Real.exp_log (show (0 : ℝ) < (1 + u) ^ K by positivity), Real.log_pow]
      apply Real.exp_le_exp.mpr
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have hKA : (K : ℝ) ≤ 4 * Real.log A + 1 := by
      have : Real.log A / Real.log (4 / 3) ≤ 4 * Real.log A := by
        rw [div_le_iff₀ hl43p]; nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ A by linarith)]
      linarith
    have hlogA : Real.log A = Real.log (8 * C) + Real.log N := by
      rw [hA, Real.log_mul (by positivity) hN0.ne']
    have hC8 : 0 ≤ Real.log (8 * C) := Real.log_nonneg (by linarith)
    have huK : u * K ≤ u * (4 * Real.log (8 * C) + 1) + 4 * u * Real.log N := by
      have := mul_le_mul_of_nonneg_left hKA hu0.le
      rw [hlogA] at this; linarith
    have hu1 : u * Real.log N = 1 / 8 := by rw [hu]; field_simp
    have hu2 : u * (4 * Real.log (8 * C) + 1) ≤ (4 * Real.log (8 * C) + 1) / 16 := by
      have : 0 ≤ 4 * Real.log (8 * C) + 1 := by linarith
      nlinarith
    rw [hT]; nlinarith
  -- Estermann at `σ = β`, where `F(β) ≤ 0`
  have hest' := hest N χ hχ hχ2 β hβ78 hβ1 K hK1
  have hFle : (F1 χ β).re ≤ 0 := by
    obtain ⟨hzi, hzr⟩ := riemannZeta_real_neg (show 0 < β by linarith) hβ1
    have hL := LFunction_nonneg_of_no_zero hχ hχ2 hβ1 fun σ hσ hσ1 ↦
      hnz σ hσ hσ1
    obtain ⟨hLr, hLi⟩ := Complex.nonneg_iff.mp hL
    simp only [F1, Complex.mul_re, hzi, ← hLi]
    nlinarith
  set lam := ‖DirichletCharacter.LFunction χ 1‖ with hlam
  have hB : 4 * (C₀ * (N : ℝ)) * (3 / 4) ^ K ≤ 1 / 2 := by
    have : C₀ ≤ C := le_max_left _ _
    calc 4 * (C₀ * (N : ℝ)) * (3 / 4) ^ K ≤ 4 * (C * (N : ℝ)) * (1 / A) := by gcongr
      _ = 1 / 2 := by rw [hA]; field_simp; ring
  have hxpos : 0 < (2 - β) ^ K := pow_pos (by linarith) K
  have hlam_ge : u / (2 * Real.exp T) ≤ lam := by
    have h4 : 1 - lam * (2 - β) ^ K / (1 - β) ≤ 1 / 2 := by linarith
    have h1β : 1 - β = u := by rw [hβ]; ring
    rw [h1β] at h4
    have : 1 / 2 ≤ lam * (2 - β) ^ K / u := by linarith
    rw [le_div_iff₀ hu0] at this
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hxK (norm_nonneg (DirichletCharacter.LFunction χ 1))
    nlinarith
  have e : Real.exp (-T) / 16 / Real.log N = u / (2 * Real.exp T) := by
    rw [hu, Real.exp_neg]; field_simp; ring
  rw [e]; exact hlam_ge

/-- The effective dichotomy: either `‖L(1, χ)‖ ≥ c/log N`, or `L(s, χ)` has a real zero
`β ∈ [1 - 1/(8 log N), 1)`, and then `‖L(1, χ)‖ ≤ 5e²(1 - β) log² N`. -/
theorem effective_dichotomy : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N], 8 ≤ N →
    ∀ (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c / Real.log N ≤ ‖DirichletCharacter.LFunction χ 1‖ ∨
      ∃ β : ℝ, 1 - 1 / (8 * Real.log N) ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ β = 0 ∧
        ‖DirichletCharacter.LFunction χ 1‖ ≤
          5 * (Real.exp 1 * Real.exp 1) * Real.log N ^ 2 * (1 - β) := by
  obtain ⟨c, hc, h⟩ := effective_L_one
  refine ⟨c, hc, fun N _ hN χ hχ hχ2 ↦ ?_⟩
  by_cases hz : ∃ β : ℝ, 1 - 1 / (8 * Real.log N) ≤ β ∧ β < 1 ∧
      DirichletCharacter.LFunction χ β = 0
  · obtain ⟨β, hb, hb1, hzero⟩ := hz
    right
    have hl2 : 2 ≤ Real.log N := one_le_log_half hN
    have hb' : 1 - 1 / Real.log N ≤ β := by
      have : 1 / (8 * Real.log N) ≤ 1 / Real.log N :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      linarith
    exact ⟨β, hb, hb1, hzero, norm_LFunction_one_le_of_zero hχ hN hb' hb1.le hzero⟩
  · left
    push Not at hz
    exact h N hN χ hχ hχ2 fun σ hσ hσ1 ↦ hz σ hσ hσ1

end LeanLab.PNTPort.DirichletZF
