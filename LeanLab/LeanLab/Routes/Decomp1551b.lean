/-
Unit U-1551, track T1, DECOMPOSE, run 20261026T1219Z-15327, 2026-10-26. PALOMAR line I5171.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Decomposition of the input `SmoothT2.HadamardK gZ` of
`LeanLab.Routes.U1508.goldbach_445_hsw_gZ` under RH:
`Σ_{j ∈ s} 4/(4 + (γ_i - γ_j)²) ≤ log |γ_i|` for every finite set `s` of zeros.

The textbook route, Davenport, Multiplicative Number Theory, chapter 12, equations (17) and (18):
the Hadamard product of `ξ(s) = s(s-1)/2 · π^{-s/2} Γ(s/2) ζ(s)` gives
`Re ζ'/ζ(s) = -Re 1/(s-1) + (1/2) log π - (1/2) Re ψ(s/2 + 1) + Σ_ρ Re 1/(s - ρ)`, with
multiplicity and absolutely convergent, LEAF `hadamard_re_sum_of` from the LEAVES `xi_growth`,
`xi_zero_iff`, `logDeriv_xi` and the cited Hadamard theorem `hadamard_logDeriv_order_one`;
`ξ(1-s) = ξ(s)` is PROVED here as `xi_one_sub`.
At `s = 5/2 + iγ` and under RH, `Re 1/(s - ρ_j) = 2/(4 + (γ - γ_j)²)`, the terms are positive,
so any finite partial sum of the kernel is at most twice the full sum. Then
`|ζ'/ζ(5/2 + it)| ≤ 3/10`, LEAF `logDeriv_bound_5half`, true value `0.28874` at `t = 0`;
`Re ψ(9/4 + iu) ≤ log|9/4 + iu| + 1/10`, LEAF `digamma_re_le`; and the real inequality LEAF
`final_numeric` for `|γ| ≥ 14`, which comes from `Ordinates14` under RH, the assembly
`Decomp1551c.ordinates14_gZ_of_RH`.

A float check: at `s = 5/2 + 20i` the identity of `hadamard_re_sum_of` reads `0.617322` against
`0.617312` from the first 150 zeros with an integral tail.

ASSEMBLY `hadamardK_gZ_of_RH`, CONDITIONAL ON the leaves here and in `Decomp1551c`.
-/
import Mathlib
import LeanLab.Routes.Decomp1551c

namespace LeanLab.Routes.Decomp1551b

open Complex Filter Topology
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx re_half_of_RH)
open LeanLab.ChirreHagen2025.SmoothKernel (K)

local notation "ζ" => riemannZeta

/-- Riemann's `ξ(s) = s(s-1)/2 · Λ(s)`, written with Mathlib's entire `completedRiemannZeta₀`:
`s(s-1)Λ(s) = s(s-1)Λ₀(s) + 1`, so `ξ(s) = (s(s-1)Λ₀(s) + 1)/2`. -/
noncomputable def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- `ξ(1-s) = ξ(s)`, from Mathlib's `completedRiemannZeta₀_one_sub`. Proved. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Cited, not proved in the lab: Hadamard's factorization theorem, Hadamard 1893, in the
logarithmic derivative form for an entire function of order at most one, Davenport,
Multiplicative Number Theory, chapter 11. If `f` is entire, `f 0 ≠ 0` and
`|f(s)| ≤ C exp(C |s| log(|s| + 2))`, then there is `B` with
`f'/f(s) = B + Σ_ρ (1/(s-ρ) + 1/ρ)` over the zeros with multiplicity, absolutely convergent,
wherever `f(s) ≠ 0`. Mathlib v4.35.0 has no Hadamard factorization. -/
theorem hadamard_logDeriv_order_one (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hg : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖f s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2))) :
    ∃ B : ℂ, ∀ s : ℂ, f s ≠ 0 →
      Summable (fun i : (Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))) =>
        1 / (s - (i.1 : ℂ)) + 1 / (i.1 : ℂ)) ∧
      logDeriv f s = B + ∑' i : (Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))),
        (1 / (s - (i.1 : ℂ)) + 1 / (i.1 : ℂ)) := by
  sorry

private lemma norm_cpow_nat_neg (n : ℕ) (s : ℂ) (hn : 0 < n) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

private lemma zeta_sum_le (N : ℕ) (s : ℂ) (hσ : 0 ≤ s.re) :
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ ≤ (N : ℝ) + 1 := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ n ∈ Finset.range (N + 1), ‖1 / (n : ℂ) ^ s‖ ≤ 1 := by
    intro n _
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.cast_zero, norm_div, norm_one]
      by_cases hs : s = 0
      · simp [hs]
      · rw [Complex.zero_cpow hs]
        simp
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h]
      simpa [one_div] using
        inv_le_one_of_one_le₀ (Real.one_le_rpow (x := (n : ℝ)) (by exact_mod_cast h) hσ)
  calc ∑ n ∈ Finset.range (N + 1), ‖1 / (n : ℂ) ^ s‖ ≤ ∑ n ∈ Finset.range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum h1
    _ = (N : ℝ) + 1 := by simp

/-- `‖ζ(σ + it)‖ ≤ 5 |t|` for `σ ≥ 1/2` and `|t| > 3`, from the Euler–Maclaurin
decomposition `riemannZeta0`. -/
private lemma zeta_bound_im (σ t : ℝ) (hσ : 1 / 2 ≤ σ) (ht : 3 < |t|) :
    ‖ζ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 5 * |t| := by
  have hσpos : 0 < σ := by linarith
  set N : ℕ := ⌊|t|⌋₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact Nat.le_floor (by push_cast; linarith)
  have hNle : (N : ℝ) ≤ |t| := by rw [hN]; exact Nat.floor_le (abs_nonneg t)
  have htne : t ≠ 0 := by
    intro h; rw [h] at ht; simp only [abs_zero] at ht; linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hsim : s.im = t := by simp [hsdef]
  have hsre : s.re = σ := by simp [hsdef]
  have him1 : (1 - s).im = -t := by simp [hsim]
  have hne1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    rw [hsim] at him
    simp at him
    exact htne him
  have hre : 0 < s.re := by rw [hsre]; exact hσpos
  rw [← Zeta0EqZeta (N := N) (by omega) hre hne1, riemannZeta0]
  have hI : ‖∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ (N : ℝ) ^ (-σ) / σ :=
    ZetaBnd_aux1b N hN1 (σ := σ) (t := t) hσpos
  have hsum : ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ ≤ (N : ℝ) + 1 :=
    zeta_sum_le N s (by rw [hsre]; linarith)
  have hnum2 : ‖(N : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [hsre]
  have hden2 : |t| ≤ ‖1 - s‖ := by
    have h := Complex.abs_im_le_norm (1 - s)
    rw [him1, abs_neg] at h
    exact h
  have hNpos : (0 : ℝ) < ‖1 - s‖ := by
    rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    rw [him1] at him
    simp at him
    exact htne him
  have hterm2 : ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_neg, hnum2, div_le_one hNpos]
    have h1 : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ ((1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have h2a : (N : ℝ) ^ ((1 / 2 : ℝ)) ≤ |t| ^ ((1 / 2 : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hNle (by norm_num)
    have h2b : |t| ^ ((1 / 2 : ℝ)) ≤ |t| := by
      simpa using Real.rpow_le_rpow_of_exponent_le (x := |t|) (by linarith)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
    linarith
  have hterm3 : ‖(-(N : ℂ) ^ (-s)) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_neg, norm_cpow_nat_neg N s (by omega), hsre]
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    calc (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
      _ = 1 := Real.rpow_zero _
  have hterm4 : ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ 1 + 2 * |t| := by
    rw [norm_mul]
    have h1 : ‖s‖ ≤ σ + |t| := by
      calc ‖s‖ = ‖(σ : ℂ) + (t : ℂ) * I‖ := by rw [hsdef]
        _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = σ + |t| := by simp [abs_of_pos hσpos]
    have h2 : (N : ℝ) ^ (-σ) ≤ 1 := by
      calc (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
        _ = 1 := Real.rpow_zero _
    have h4 : ‖s‖ * ((N : ℝ) ^ (-σ) / σ) ≤ (σ + |t|) * (1 / σ) := by
      exact mul_le_mul h1 ((div_le_div_iff_of_pos_right hσpos).mpr h2) (by positivity)
        (by linarith [abs_nonneg t])
    have h5 : (σ + |t|) * (1 / σ) = 1 + |t| / σ := by field_simp
    have h6 : |t| / σ ≤ 2 * |t| := by
      rw [div_le_iff₀ hσpos]
      nlinarith [abs_nonneg t]
    calc ‖s‖ * ‖∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
        ≤ ‖s‖ * ((N : ℝ) ^ (-σ) / σ) := mul_le_mul_of_nonneg_left hI (norm_nonneg _)
      _ ≤ (σ + |t|) * (1 / σ) := h4
      _ = 1 + |t| / σ := h5
      _ ≤ 1 + 2 * |t| := by linarith
  have hsum4 : ‖(∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
      + ((-(N : ℂ) ^ (1 - s)) / (1 - s)) + ((-(N : ℂ) ^ (-s)) / 2)
      + (s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1))‖
      ≤ ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖
        + ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-(N : ℂ) ^ (-s)) / 2‖
        + ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ :=
    norm_add₄_le
  have hfin : ((N : ℝ) + 1) + 1 + 1 / 2 + (1 + 2 * |t|) ≤ 5 * |t| := by
    nlinarith [hNle, abs_nonneg t, ht]
  have h1 : ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖
      + ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-(N : ℂ) ^ (-s)) / 2‖
      + ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ((N : ℝ) + 1) + 1 + 1 / 2 + (1 + 2 * |t|) := by linarith
  exact hsum4.trans (h1.trans hfin)

/-- `‖ζ(σ + it)‖ ≤ 6 (1 + |t|)` for `σ ≥ 2`, from the Euler–Maclaurin decomposition with
`N = 3`. -/
private lemma zeta_bound_re (σ t : ℝ) (hσ : 2 ≤ σ) :
    ‖ζ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 6 * (1 + |t|) := by
  have hσpos : 0 < σ := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hsim : s.im = t := by simp [hsdef]
  have hsre : s.re = σ := by simp [hsdef]
  have hne1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith
  have hre : 0 < s.re := by rw [hsre]; exact hσpos
  rw [← Zeta0EqZeta (N := 3) (by norm_num) hre hne1, riemannZeta0]
  have hI : ‖∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ (3 : ℝ) ^ (-σ) / σ :=
    ZetaBnd_aux1b 3 (by norm_num) (σ := σ) (t := t) hσpos
  have hsum : ‖∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s‖ ≤ (3 : ℝ) + 1 :=
    zeta_sum_le 3 s (by rw [hsre]; linarith)
  have hnum2 : ‖((3 : ℝ) : ℂ) ^ (1 - s)‖ = (3 : ℝ) ^ (1 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp [hsre]
  have hden2 : (1 : ℝ) ≤ ‖1 - s‖ := by
    have h := Complex.abs_re_le_norm (1 - s)
    rw [show (1 - s).re = 1 - σ by simp [hsre], abs_of_neg (by linarith)] at h
    linarith
  have hNpos : (0 : ℝ) < ‖1 - s‖ := by linarith
  have hterm2 : ‖(-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_neg, hnum2, div_le_iff₀ hNpos]
    have h1 : (3 : ℝ) ^ (1 - σ) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h0 : (3 : ℝ) ^ (-1 : ℝ) = 1 / 3 := by
      rw [Real.rpow_neg_one]; norm_num
    rw [h0] at h1
    nlinarith [h1, hden2]
  have hterm3 : ‖(-((3 : ℝ) : ℂ) ^ (-s)) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
      show (-s).re = -σ from by simp [hsre]]
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    calc (3 : ℝ) ^ (-σ) ≤ (3 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero _
  have hterm4 : ‖s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ (1 + |t|) / 3 := by
    rw [norm_mul]
    have h1 : ‖s‖ ≤ σ + |t| := by
      calc ‖s‖ = ‖(σ : ℂ) + (t : ℂ) * I‖ := by rw [hsdef]
        _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = σ + |t| := by simp [abs_of_pos hσpos]
    have h2 : (3 : ℝ) ^ (-σ) ≤ 1 / 3 := by
      calc (3 : ℝ) ^ (-σ) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 3 := by rw [Real.rpow_neg_one]; norm_num
    have h4 : ‖s‖ * ((3 : ℝ) ^ (-σ) / σ) ≤ (σ + |t|) * ((1 / 3) / σ) := by
      exact mul_le_mul h1 ((div_le_div_iff_of_pos_right hσpos).mpr h2) (by positivity)
        (by linarith [abs_nonneg t])
    have h5 : (σ + |t|) * ((1 / 3) / σ) = (1 + |t| / σ) / 3 := by field_simp
    have h6 : |t| / σ ≤ |t| := by
      rw [div_le_iff₀ hσpos]
      nlinarith [abs_nonneg t]
    calc ‖s‖ * ‖∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
        ≤ ‖s‖ * ((3 : ℝ) ^ (-σ) / σ) := mul_le_mul_of_nonneg_left hI (norm_nonneg _)
      _ ≤ (σ + |t|) * ((1 / 3) / σ) := h4
      _ = (1 + |t| / σ) / 3 := h5
      _ ≤ (1 + |t|) / 3 := by linarith
  have hsum4 : ‖(∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s)
      + ((-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)) + ((-((3 : ℝ) : ℂ) ^ (-s)) / 2)
      + (s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1))‖
      ≤ ‖∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s‖
        + ‖(-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-((3 : ℝ) : ℂ) ^ (-s)) / 2‖
        + ‖s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ :=
    norm_add₄_le
  have h1 : ‖∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s‖
      + ‖(-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-((3 : ℝ) : ℂ) ^ (-s)) / 2‖
      + ‖s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ((3 : ℝ) + 1) + 1 / 3 + 1 / 2 + (1 + |t|) / 3 := by linarith
  have hfin : ((3 : ℝ) + 1) + 1 / 3 + 1 / 2 + (1 + |t|) / 3 ≤ 6 * (1 + |t|) := by
    nlinarith [abs_nonneg t]
  exact hsum4.trans (h1.trans hfin)

/-- `‖ζ s‖ ≤ 6 (1 + ‖s‖)` for `Re s ≥ 1/2` and `‖s‖ ≥ 4`. -/
private lemma zeta_bound (s : ℂ) (hre : 1 / 2 ≤ s.re) (hn : 4 ≤ ‖s‖) :
    ‖ζ s‖ ≤ 6 * (1 + ‖s‖) := by
  have hrw : ((s.re : ℂ) + (s.im : ℂ) * I) = s := Complex.re_add_im s
  have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rcases le_or_gt |s.im| 3 with ht | ht
  · have hσ2 : 2 ≤ s.re := by
      have h1 : (16 : ℝ) ≤ ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
      have h2 : s.im ^ 2 ≤ 9 := by nlinarith [abs_le.mp ht]
      have h3 : 0 < s.re := by linarith
      nlinarith
    have := zeta_bound_re s.re s.im hσ2
    rw [hrw] at this
    have h2 : 6 * (1 + |s.im|) ≤ 6 * (1 + ‖s‖) := by
      linarith [Complex.abs_im_le_norm s]
    linarith
  · have := zeta_bound_im s.re s.im hre ht
    rw [hrw] at this
    have h2 : 5 * |s.im| ≤ 6 * (1 + ‖s‖) := by linarith [Complex.abs_im_le_norm s]
    linarith

/-! ### Auxiliary numeric facts -/

private lemma one_le_log_add_two {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.log (x + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_three.le]

private lemma sqrt_two_pi_le : Real.sqrt (2 * Real.pi) ≤ 3 := by
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [Real.pi_lt_four]

private lemma inv_le_four {x : ℝ} (hx : 1 / 4 ≤ x) : x⁻¹ ≤ 4 := by
  rw [← one_div, div_le_iff₀ (by linarith : (0:ℝ) < x)]
  linarith

private lemma twelve_sq_le_exp (x : ℝ) (hx : 2 ≤ x) :
    12 * (x + 2) ^ 2 ≤ Real.exp (100 * x * Real.log (x + 2)) := by
  have h1 : 12 * (x + 2) ^ 2 ≤ 48 * x ^ 2 := by nlinarith
  have h2 : 48 * x ^ 2 ≤ Real.exp (100 * x) := by
    have h := Real.pow_div_factorial_le_exp (100 * x) (by linarith) 3
    have hfac : (((3 : ℕ).factorial : ℝ)) = 6 := by norm_num
    rw [hfac] at h
    nlinarith [h, sq_nonneg x, hx]
  have h3 : Real.exp (100 * x) ≤ Real.exp (100 * x * Real.log (x + 2)) := by
    apply Real.exp_le_exp.mpr
    have hL := one_le_log_add_two hx
    nlinarith
  linarith

private lemma three_mul_pow_le_exp (x : ℝ) (hx : 2 ≤ x) (k : ℕ) (hk : (k : ℝ) ≤ x) :
    3 * (2 * x + 1) ^ (k + 2) ≤ Real.exp (100 * x * Real.log (x + 2)) := by
  have hL := one_le_log_add_two hx
  have hpos : 0 < 3 * (2 * x + 1) ^ (k + 2) := by positivity
  rw [← Real.log_le_iff_le_exp hpos]
  have hbase : 0 < 2 * x + 1 := by linarith
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast
  have hlog2 : Real.log (2 * x + 1) ≤ 2 * Real.log (x + 2) := by
    have h1 : 2 * x + 1 ≤ (x + 2) ^ 2 := by nlinarith
    have h2 := Real.log_le_log hbase h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    nlinarith [Real.exp_one_gt_two, Real.exp_pos 1,
      show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
  have hLnn : (0:ℝ) ≤ Real.log (x + 2) := by linarith
  have hstep1 : ((k : ℝ) + 2) * Real.log (2 * x + 1) ≤ (x + 3) * (2 * Real.log (x + 2)) := by
    apply mul_le_mul _ hlog2 (Real.log_nonneg (by linarith)) (by linarith)
    linarith
  nlinarith [hstep1, hlog3, hL, hx, hLnn]

/-! ### Growth of `Γ` -/

private lemma Gamma_shift (k : ℕ) (w : ℂ) (h : (k : ℝ) < w.re) :
    Gamma w = Gamma (w - k) * ∏ j ∈ Finset.range k, (w - 1 - (j : ℂ)) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    have hk : (k : ℝ) < w.re := by
      have h' : ((k : ℕ) : ℝ) + 1 < w.re := by
        have := h; push_cast at this; exact this
      linarith
    rw [ih w hk, Finset.prod_range_succ]
    have hne : w - (k : ℂ) - 1 ≠ 0 := by
      intro h0
      have hre0 : w.re = (k : ℝ) + 1 := by
        have h1 := congrArg Complex.re h0
        have h2 : w.re - (k : ℝ) - 1 = 0 := by simpa using h1
        linarith
      have h' : ((k : ℕ) : ℝ) + 1 < w.re := by have := h; push_cast at this; exact this
      linarith
    have hadd : Gamma (w - (k : ℂ)) = (w - (k : ℂ) - 1) * Gamma (w - (k : ℂ) - 1) := by
      have := Complex.Gamma_add_one (w - (k : ℂ) - 1) hne
      rwa [show w - (k : ℂ) - 1 + 1 = w - (k : ℂ) by ring] at this
    have hcast : w - (((k + 1 : ℕ)) : ℂ) = w - (k : ℂ) - 1 := by push_cast; ring
    rw [hadd, hcast]
    ring

private lemma fac_bound (w : ℂ) (m : ℕ) (hm : (m : ℝ) ≤ ‖w‖) :
    ‖w - 1 - (m : ℂ)‖ ≤ 2 * ‖w‖ + 1 := by
  have h2 : ‖-1 - (m : ℂ)‖ ≤ ‖(-1 : ℂ)‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
  have h3 : ‖(-1 : ℂ)‖ = 1 := by norm_num
  have h4 : ‖(m : ℂ)‖ = (m : ℝ) := by simp
  have h5 : ‖w - 1 - (m : ℂ)‖ ≤ ‖w‖ + ‖-1 - (m : ℂ)‖ := by
    have := norm_add_le w (-1 - (m : ℂ))
    rwa [show w + (-1 - (m : ℂ)) = w - 1 - (m : ℂ) by ring] at this
  rw [h3, h4] at h2
  linarith

private lemma prod_bound (w : ℂ) (m : ℕ) (hm : (m : ℝ) ≤ ‖w‖) :
    ‖∏ j ∈ Finset.range m, (w - 1 - (j : ℂ))‖ ≤ (2 * ‖w‖ + 1) ^ m := by
  rw [norm_prod]
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : (m : ℝ) ≤ ‖w‖ := by
      have : ((m : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
      linarith
    rw [Finset.prod_range_succ, pow_succ]
    exact mul_le_mul (ih hm') (fac_bound w m hm') (norm_nonneg _) (by positivity)

private lemma Gamma_bound_of_im (w : ℂ) (hre : 1 / 4 ≤ w.re) (hn : 2 ≤ ‖w‖) (him : 0 ≤ w.im) :
    ‖Gamma w‖ ≤ Real.exp (100 * ‖w‖ * Real.log (‖w‖ + 2)) := by
  have hx : (2:ℝ) ≤ ‖w‖ := hn
  rcases lt_or_ge w.re (1 / 2) with hlt | hge
  · have hwne : w ≠ 0 := by
      intro h; rw [h] at hre; simp at hre; linarith
    have hsplit : Gamma w = Gamma (w + 1) / w := by
      rw [Complex.Gamma_add_one w hwne]; field_simp
    have hPL := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL2 (s := w + 1)
      (by simp; linarith) (by simp; linarith)
    have him1 : (w + 1).im = w.im := by simp
    have hexp : Real.exp (-(Real.pi * (w + 1).im / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff, him1]
      nlinarith [Real.pi_pos]
    have h2 : ‖(w + 1) + 1‖ ≤ ‖w‖ + 2 := by
      calc ‖(w + 1) + 1‖ = ‖w + 2‖ := by ring_nf
        _ ≤ ‖w‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
        _ = ‖w‖ + 2 := by norm_num
    have hs : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hnum : ‖Gamma (w + 1)‖ ≤ Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 := by
      have hstep : Real.sqrt (2 * Real.pi) * ‖(w + 1) + 1‖ ^ 2 *
          Real.exp (-(Real.pi * (w + 1).im / 2)) ≤ Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 * 1 := by
        apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
        apply mul_le_mul_of_nonneg_left _ hs
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc ‖Gamma (w + 1)‖
          ≤ Real.sqrt (2 * Real.pi) * ‖(w + 1) + 1‖ ^ 2 *
              Real.exp (-(Real.pi * (w + 1).im / 2)) := hPL
        _ ≤ Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 * 1 := hstep
        _ = Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 := by ring
    have hinv : ‖w‖⁻¹ ≤ 4 := inv_le_four (le_trans hre (le_trans (le_abs_self _)
      (Complex.abs_re_le_norm w)))
    have hmain : ‖Gamma w‖ ≤ 12 * (‖w‖ + 2) ^ 2 := by
      rw [hsplit, norm_div, div_eq_mul_inv]
      have hstep : ‖Gamma (w + 1)‖ * ‖w‖⁻¹ ≤ (Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2) * 4 :=
        mul_le_mul hnum hinv (by positivity) (by positivity)
      have hstep2 : (Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2) * 4 ≤ 12 * (‖w‖ + 2) ^ 2 := by
        nlinarith [sqrt_two_pi_le, sq_nonneg (‖w‖ + 2)]
      linarith
    have hfin : 12 * (‖w‖ + 2) ^ 2 ≤ Real.exp (100 * ‖w‖ * Real.log (‖w‖ + 2)) :=
      twelve_sq_le_exp ‖w‖ hx
    linarith
  · set k : ℕ := ⌊w.re - 1 / 2⌋₊ with hkdef
    have hk_le : (k : ℝ) ≤ w.re - 1 / 2 := by
      rw [hkdef]; exact Nat.floor_le (by linarith)
    have hk_lt : w.re - 1 / 2 < (k : ℝ) + 1 := by
      rw [hkdef]; exact Nat.lt_floor_add_one _
    have hkre : 1 / 2 ≤ (w - (k : ℂ)).re := by simp; linarith
    have hkre' : (w - (k : ℂ)).re ≤ 3 / 2 := by simp; linarith
    have hPL := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL2 (s := w - (k : ℂ))
      (by linarith) (by linarith)
    have himk : (w - (k : ℂ)).im = w.im := by simp
    have hkx : (k : ℝ) ≤ ‖w‖ := by
      have h1 : w.re ≤ ‖w‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm w)
      linarith
    have hs : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hstep2 : ‖(w - (k : ℂ)) + 1‖ ≤ 2 * ‖w‖ + 1 := by
      have ha : ‖(w - (k : ℂ)) + 1‖ ≤ ‖w - (k : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      have hb : ‖w - (k : ℂ)‖ ≤ ‖w‖ + ‖(k : ℂ)‖ := norm_sub_le _ _
      have hc : ‖(k : ℂ)‖ = (k : ℝ) := by simp
      have hd : ‖(1 : ℂ)‖ = 1 := by norm_num
      rw [hc] at hb
      rw [hd] at ha
      linarith
    have hGk : ‖Gamma (w - (k : ℂ))‖ ≤ Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 := by
      have hexp : Real.exp (-(Real.pi * (w - (k : ℂ)).im / 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff, himk]
        nlinarith [Real.pi_pos]
      have hstep : Real.sqrt (2 * Real.pi) * ‖(w - (k : ℂ)) + 1‖ ^ 2 *
          Real.exp (-(Real.pi * (w - (k : ℂ)).im / 2)) ≤
          Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 * 1 := by
        apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
        apply mul_le_mul_of_nonneg_left _ hs
        exact pow_le_pow_left₀ (norm_nonneg _) hstep2 2
      calc ‖Gamma (w - (k : ℂ))‖
          ≤ Real.sqrt (2 * Real.pi) * ‖(w - (k : ℂ)) + 1‖ ^ 2 *
              Real.exp (-(Real.pi * (w - (k : ℂ)).im / 2)) := hPL
        _ ≤ Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 * 1 := hstep
        _ = Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 := by ring
    have hP : ‖∏ j ∈ Finset.range k, (w - 1 - (j : ℂ))‖ ≤ (2 * ‖w‖ + 1) ^ k :=
      prod_bound w k hkx
    have hshift := Gamma_shift k w (by linarith)
    have hfinal : ‖Gamma w‖ ≤ Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ (k + 2) := by
      rw [hshift, norm_mul]
      have hstep : ‖Gamma (w - (k : ℂ))‖ * ‖∏ j ∈ Finset.range k, (w - 1 - (j : ℂ))‖
          ≤ (Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2) * (2 * ‖w‖ + 1) ^ k :=
        mul_le_mul hGk hP (norm_nonneg _) (by positivity)
      calc ‖Gamma (w - (k : ℂ))‖ * ‖∏ j ∈ Finset.range k, (w - 1 - (j : ℂ))‖
          ≤ (Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2) * (2 * ‖w‖ + 1) ^ k := hstep
        _ = Real.sqrt (2 * Real.pi) * ((2 * ‖w‖ + 1) ^ 2 * (2 * ‖w‖ + 1) ^ k) := by ring
        _ = Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ (k + 2) := by
            rw [← pow_add]; ring_nf
    have h3 : Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ (k + 2) ≤ 3 * (2 * ‖w‖ + 1) ^ (k + 2) := by
      have h0 : (0:ℝ) ≤ (2 * ‖w‖ + 1) ^ (k + 2) := by positivity
      nlinarith [sqrt_two_pi_le]
    exact hfinal.trans (h3.trans (three_mul_pow_le_exp ‖w‖ hx k hkx))

private lemma Gamma_growth (w : ℂ) (hre : 1 / 4 ≤ w.re) (hn : 2 ≤ ‖w‖) :
    ‖Gamma w‖ ≤ Real.exp (100 * ‖w‖ * Real.log (‖w‖ + 2)) := by
  rcases le_or_gt 0 w.im with him | him
  · exact Gamma_bound_of_im w hre hn him
  · have h1 : ‖Gamma ((starRingEnd ℂ) w)‖ ≤
        Real.exp (100 * ‖(starRingEnd ℂ) w‖ * Real.log (‖(starRingEnd ℂ) w‖ + 2)) :=
      Gamma_bound_of_im ((starRingEnd ℂ) w) (by simpa using hre) (by simpa using hn)
        (by simpa using him.le)
    rwa [Complex.Gamma_conj, Complex.norm_conj, Complex.norm_conj] at h1

/-! ### Bounds for `Λ₀` -/

private lemma norm_pi_cpow_le_one (s : ℂ) (hre : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  rw [show (-s / 2).re = -s.re / 2 from by simp]
  calc (Real.pi : ℝ) ^ (-s.re / 2) ≤ Real.pi ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
          (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi) (by linarith)
    _ = 1 := Real.rpow_zero _

/-- `‖Λ₀ s‖` bound for `Re s ≥ 1/2` and `‖s‖ ≥ 4`. -/
private lemma completedZeta_bound_half (s : ℂ) (hre : 1 / 2 ≤ s.re) (hn : 4 ≤ ‖s‖) :
    ‖completedRiemannZeta₀ s‖ ≤ Real.exp (1000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hn; simp at hn; linarith
  have hx : (2:ℝ) ≤ ‖s‖ := by linarith
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hG : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hid : completedRiemannZeta₀ s
      = (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s + 1 / (1 - s) := by
    have h := riemannZeta_eq_completedRiemannZeta₀ hs0
    rw [eq_div_iff (mul_ne_zero hpi hG)] at h
    linear_combination -h
  -- bounds for the three pieces
  have hpi1 := norm_pi_cpow_le_one s (by linarith)
  have hGn : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [Complex.norm_div]; norm_num
  have hGbd : ‖Gamma (s / 2)‖ ≤ Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) := by
    have h1 : (1 / 4 : ℝ) ≤ (s / 2).re := by simp; linarith
    have h2 : (2 : ℝ) ≤ ‖s / 2‖ := by rw [hGn]; linarith
    have h3 := Gamma_growth (s / 2) h1 h2
    rwa [hGn] at h3
  have hzbd := zeta_bound s hre hn
  have hsix : 6 * (1 + ‖s‖) ≤ Real.exp (100 * ‖s‖) := by
    have h := Real.pow_div_factorial_le_exp (100 * ‖s‖) (by positivity) 2
    have hfac : (((2 : ℕ).factorial : ℝ)) = 2 := by norm_num
    rw [hfac] at h
    have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
    nlinarith [h, hx0]
  have hinv1 : ‖(1:ℂ) / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  have hden : (1:ℝ) ≤ ‖1 - s‖ := by
    rcases le_or_gt 2 s.re with h2 | h2
    · have h := Complex.abs_re_le_norm (1 - s)
      rw [show (1 - s).re = 1 - s.re by simp, abs_of_neg (by linarith)] at h
      linarith
    · have h := Complex.abs_im_le_norm (1 - s)
      rw [show (1 - s).im = -s.im by simp, abs_neg] at h
      have hsq : s.re ^ 2 + s.im ^ 2 = ‖s‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hsq' : (12:ℝ) ≤ s.im ^ 2 := by nlinarith
      have : (3:ℝ) ≤ |s.im| := by nlinarith [abs_nonneg s.im, sq_abs s.im]
      linarith
  have hinv2 : ‖(1:ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    exact hden
  -- assemble
  have hbd : ‖completedRiemannZeta₀ s‖ ≤
      Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) + 2 := by
    rw [hid]
    have h1 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s + 1 / (1 - s)‖
        ≤ ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := by
      have h2 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s + 1 / (1 - s)‖
          ≤ ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s‖ + ‖1 / (1 - s)‖ :=
        norm_add_le _ _
      have h3 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s‖
          ≤ ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s‖ + ‖1 / s‖ := norm_add_le _ _
      linarith
    have h1' : ‖1 / s‖ ≤ 1 := by simpa [one_div] using hinv1
    have h1'' : ‖1 / (1 - s)‖ ≤ 1 := by simpa [one_div] using hinv2
    have h4 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s‖
        ≤ Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) := by
      rw [norm_mul, norm_mul]
      have hA : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Gamma (s / 2)‖
          ≤ 1 * Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) :=
        mul_le_mul hpi1 hGbd (norm_nonneg _) (by norm_num)
      have hz2 : ‖ζ s‖ ≤ Real.exp (100 * ‖s‖) := le_trans hzbd hsix
      have h5 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Gamma (s / 2)‖ * ‖ζ s‖
          ≤ 1 * Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) :=
        mul_le_mul hA hz2 (norm_nonneg _) (by positivity)
      linarith
    linarith
  have hcomb : Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖)
      ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hL := one_le_log_add_two hx
    have hlog : Real.log (‖s‖ / 2 + 2) ≤ Real.log (‖s‖ + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
    nlinarith [hL, hlog, hx0, mul_nonneg hx0 (by linarith : (0:ℝ) ≤ Real.log (‖s‖ + 2))]
  have htwo : (2:ℝ) ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by
    have hL := one_le_log_add_two hx
    have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
    have h1 : 500 * ‖s‖ * Real.log (‖s‖ + 2) + 1 ≤
        Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) :=
      Real.add_one_le_exp (500 * ‖s‖ * Real.log (‖s‖ + 2))
    have h2 : (1:ℝ) ≤ 500 * ‖s‖ * Real.log (‖s‖ + 2) := by nlinarith
    linarith
  calc ‖completedRiemannZeta₀ s‖
      ≤ Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) + 2 := hbd
    _ ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) +
        Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by linarith
    _ = 2 * Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by ring
    _ ≤ Real.exp (1000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
        have hL := one_le_log_add_two hx
        have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
        have h1 : Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) * Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2))
            = Real.exp (1000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
          rw [← Real.exp_add]; ring_nf
        have h2 : (2:ℝ) ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := htwo
        have h0 : (0:ℝ) < Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := Real.exp_pos _
        nlinarith [h1, h2, h0]

/-- LEAF. Unit U-1551. Davenport chapter 12, page 80, first displays: `ξ` has order one,
`|ξ(s)| ≤ C exp(C |s| log(|s| + 2))` for all `s`, from Stirling for `Γ(s/2)` and
`ζ(s) ≪ |s|` on `Re s ≥ 1/2`, with `ξ(1-s) = ξ(s)` for the other half plane. -/
theorem xi_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖xi s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_bound_of_continuousOn
    differentiable_completedZeta₀.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp [Metric.mem_closedBall]))
  refine ⟨1000 * (M + 1) + 10000, by positivity, fun s => ?_⟩
  have hC1 : (10 * M + 1 / 2 : ℝ) ≤ 1000 * (M + 1) + 10000 := by linarith
  have hC2 : (1100 : ℝ) ≤ 1000 * (M + 1) + 10000 := by linarith
  have hC0 : (0:ℝ) < 1000 * (M + 1) + 10000 := by linarith
  rcases le_or_gt ‖s‖ 4 with hs | hs
  · have hb : ‖completedRiemannZeta₀ s‖ ≤ M :=
      hM s (by simpa [Metric.mem_closedBall, dist_zero_right] using hs)
    have h1 : ‖s - 1‖ ≤ 5 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by norm_num
        _ ≤ 5 := by linarith
    have h4 : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
        ≤ ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1 := by
      have h5 : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
          ≤ ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      rw [norm_mul, norm_mul, show ‖(1 : ℂ)‖ = 1 from by norm_num] at h5
      linarith
    have h5 : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ ≤ 4 * 5 * M := by
      have h6 : ‖s‖ * ‖s - 1‖ ≤ 4 * 5 :=
        mul_le_mul hs h1 (norm_nonneg _) (by norm_num)
      have h7 : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ ≤ (4 * 5) * M :=
        mul_le_mul h6 hb (norm_nonneg _) (by norm_num)
      linarith
    have h2 : ‖xi s‖ ≤ 10 * M + 1 / 2 := by
      unfold xi
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have hexp1 : (1:ℝ) ≤ Real.exp ((1000 * (M + 1) + 10000) * ‖s‖ * Real.log (‖s‖ + 2)) := by
      apply Real.one_le_exp
      have hL : (0:ℝ) ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
      have hnn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
      positivity
    have hpos : (0:ℝ) < Real.exp ((1000 * (M + 1) + 10000) * ‖s‖ * Real.log (‖s‖ + 2)) :=
      Real.exp_pos _
    nlinarith [h2, hC1, hexp1, hpos]
  · have hΛ : ‖completedRiemannZeta₀ s‖ ≤ Real.exp (8000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
      rcases le_or_gt (1 / 2 : ℝ) s.re with hre | hre
      · have h := completedZeta_bound_half s hre (le_of_lt hs)
        calc ‖completedRiemannZeta₀ s‖ ≤ Real.exp (1000 * ‖s‖ * Real.log (‖s‖ + 2)) := h
          _ ≤ Real.exp (8000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
              apply Real.exp_le_exp.mpr
              have hL : (0:ℝ) ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
              have : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
              nlinarith
      · -- use `Λ₀ (1 - s) = Λ₀ s`
        have hsym : completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
          completedRiemannZeta₀_one_sub s
        have hre' : (1 / 2 : ℝ) ≤ (1 - s).re := by simp; linarith
        have hn' : (4:ℝ) ≤ ‖1 - s‖ := by
          have hsq : (1 - s).re ^ 2 + (1 - s).im ^ 2 = ‖1 - s‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          have hsq2 : s.re ^ 2 + s.im ^ 2 = ‖s‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          have h1 : (1 - s).re = 1 - s.re := by simp
          have h2 : (1 - s).im = -s.im := by simp
          have h3 : (16:ℝ) ≤ ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
          have h16 : (16:ℝ) ≤ (1 - s).re ^ 2 + (1 - s).im ^ 2 := by
            rw [h1, h2]
            nlinarith
          have h5 : (16:ℝ) ≤ Complex.normSq (1 - s) := by
            rw [Complex.normSq_apply]
            nlinarith
          rw [Complex.norm_def]
          refine (Real.le_sqrt (show (0:ℝ) ≤ 4 by norm_num) (by positivity)).mpr ?_
          have h6 : (4:ℝ) ^ 2 = 16 := by norm_num
          rw [h6]
          exact h5
        have h := completedZeta_bound_half (1 - s) hre' hn'
        rw [hsym] at h
        have hle : ‖1 - s‖ ≤ 2 * ‖s‖ := by
          have h1 : ‖1 - s‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := by
            have := norm_sub_le (1:ℂ) s
            rwa [show (1:ℂ) - s = 1 - s from rfl] at this
          rw [show ‖(1:ℂ)‖ = 1 from by norm_num] at h1
          linarith
        have hnn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
        calc ‖completedRiemannZeta₀ s‖ ≤ Real.exp (1000 * ‖1 - s‖ * Real.log (‖1 - s‖ + 2)) := h
          _ ≤ Real.exp (8000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
              apply Real.exp_le_exp.mpr
              have hL : (0:ℝ) ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
              have hlog : Real.log (‖1 - s‖ + 2) ≤ Real.log (2 * ‖s‖ + 2) :=
                Real.log_le_log (by linarith) (by linarith)
              have hlog2 : Real.log (2 * ‖s‖ + 2) ≤ 2 * Real.log (‖s‖ + 2) := by
                have h1 : 2 * ‖s‖ + 2 ≤ (‖s‖ + 2) ^ 2 := by nlinarith
                have h2 := Real.log_le_log (by linarith : (0:ℝ) < 2 * ‖s‖ + 2) h1
                rw [Real.log_pow] at h2
                push_cast at h2
                linarith
              have h0log : (0:ℝ) ≤ Real.log (‖1 - s‖ + 2) :=
                Real.log_nonneg (by linarith)
              have hprod : ‖1 - s‖ * Real.log (‖1 - s‖ + 2)
                  ≤ (2 * ‖s‖) * (2 * Real.log (‖s‖ + 2)) :=
                mul_le_mul hle (le_trans hlog hlog2) h0log (by linarith)
              nlinarith [hprod]
    -- final assembly in the large case
    have h1 : ‖s - 1‖ ≤ 2 * ‖s‖ := by
      have := norm_sub_le s (1:ℂ)
      rw [show ‖(1:ℂ)‖ = 1 from by norm_num] at this
      linarith
    have h4 : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
        ≤ ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1 := by
      have h5 : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
          ≤ ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      rw [norm_mul, norm_mul, show ‖(1 : ℂ)‖ = 1 from by norm_num] at h5
      linarith
    have h6 : ‖s‖ * ‖s - 1‖ ≤ 2 * ‖s‖ ^ 2 := by
      have h7 := mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
      nlinarith [h7, norm_nonneg s]
    have h9 : (2 * ‖s‖ ^ 2 : ℝ) ≤ Real.exp (100 * ‖s‖) := by
      have h := Real.pow_div_factorial_le_exp (100 * ‖s‖) (by positivity) 2
      have hfac : (((2 : ℕ).factorial : ℝ)) = 2 := by norm_num
      rw [hfac] at h
      nlinarith [h, norm_nonneg s]
    have hΛnn : (0:ℝ) ≤ Real.exp (8000 * ‖s‖ * Real.log (‖s‖ + 2)) := (Real.exp_pos _).le
    have h7 : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
        ≤ Real.exp (100 * ‖s‖) * Real.exp (8000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
      have h8 : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
          ≤ (2 * ‖s‖ ^ 2) * Real.exp (8000 * ‖s‖ * Real.log (‖s‖ + 2)) :=
        mul_le_mul h6 hΛ (norm_nonneg _) (by positivity)
      have h10 := mul_le_mul_of_nonneg_right h9 hΛnn
      linarith
    have h11 : Real.exp (100 * ‖s‖) * Real.exp (8000 * ‖s‖ * Real.log (‖s‖ + 2))
        ≤ Real.exp (8100 * ‖s‖ * Real.log (‖s‖ + 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hL := one_le_log_add_two (by linarith : (2:ℝ) ≤ ‖s‖)
      have hnn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
      nlinarith [hL, hnn]
    have h3 : ‖xi s‖ ≤ Real.exp (8100 * ‖s‖ * Real.log (‖s‖ + 2)) := by
      unfold xi
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have hone : (1:ℝ) ≤ Real.exp (8100 * ‖s‖ * Real.log (‖s‖ + 2)) := by
        apply Real.one_le_exp
        have hL : (0:ℝ) ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
        have hnn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
        positivity
      linarith
    have hmono : Real.exp (8100 * ‖s‖ * Real.log (‖s‖ + 2))
        ≤ Real.exp ((1000 * (M + 1) + 10000) * ‖s‖ * Real.log (‖s‖ + 2)) := by
      apply Real.exp_le_exp.mpr
      have hL : (0:ℝ) ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
      have hnn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
      have h21 : (8100:ℝ) ≤ 1000 * (M + 1) + 10000 := by linarith
      nlinarith [hL, hnn, mul_nonneg hnn hL]
    have hcle : (1:ℝ) ≤ 1000 * (M + 1) + 10000 := by linarith
    have hpos : (0:ℝ) < Real.exp ((1000 * (M + 1) + 10000) * ‖s‖ * Real.log (‖s‖ + 2)) :=
      Real.exp_pos _
    have hfin : ‖xi s‖ ≤ Real.exp ((1000 * (M + 1) + 10000) * ‖s‖ * Real.log (‖s‖ + 2)) :=
      le_trans h3 hmono
    nlinarith [hfin, hcle, hpos]

/-- LEAF. Unit U-1551. Davenport chapter 12, page 79: the zeros of `ξ` are exactly the zeros
of `ζ` in the critical strip, with the same multiplicity, since `s(s-1)/2 · π^{-s/2} Γ(s/2)`
is analytic and nonzero on `0 < Re s < 1`, and `ξ ≠ 0` off the strip. -/
theorem xi_zero_iff :
    (∀ ρ : ℂ, xi ρ = 0 ↔ (ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)) ∧
    (∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      analyticOrderNatAt xi ρ = analyticOrderNatAt ζ ρ) := by
  have heq : ∀ z : ℂ, 0 < z.re → z ≠ 1 → xi z =
      (z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) / 2) * riemannZeta z := by
    intro z hz hz1
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have hG : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [riemannZeta_eq_completedRiemannZeta₀ hz0]
    unfold xi
    field_simp
    ring
  have hfac : ∀ z : ℂ, 0 < z.re → z ≠ 1 →
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) / 2 ≠ 0 := by
    intro z hz hz1
    apply div_ne_zero _ (by norm_num)
    apply mul_ne_zero _ (Gamma_ne_zero_of_re_pos (by simp; linarith))
    apply mul_ne_zero _ ((Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
    exact mul_ne_zero (by intro h; norm_num [h] at hz) (sub_ne_zero.mpr hz1)
  have hp : ∀ z : ℂ, 0 < z.re → z ≠ 1 → (xi z = 0 ↔ riemannZeta z = 0) := by
    intro z hz hz1
    rw [heq z hz hz1, mul_eq_zero, or_iff_right (hfac z hz hz1)]
  constructor
  · intro z
    constructor
    · intro hz
      have hz0 : z ≠ 0 := by intro h; subst z; norm_num [xi] at hz
      have hz1 : z ≠ 1 := by intro h; subst z; norm_num [xi] at hz
      have hre : 0 < z.re := by
        by_contra hn
        have hwr : 1 ≤ (1 - z).re := by simp; linarith
        have hw1 : 1 - z ≠ 1 := by intro h; apply hz0; linear_combination -h
        have hw0 := riemannZeta_ne_zero_of_one_le_re hwr
        have hsym : xi (1 - z) = xi z := by
          unfold xi
          rw [completedRiemannZeta₀_one_sub]
          ring
        exact hw0 ((hp (1 - z) (by linarith) hw1).mp (hsym.trans hz))
      have hzero := (hp z hre hz1).mp hz
      refine ⟨hzero, hre, ?_⟩
      by_contra hn
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hn) hzero
    · rintro ⟨hz, h0, h1⟩
      exact (hp z h0 (by intro h; norm_num [h] at h1)).mpr hz
  · intro z hz h0 h1
    let a : ℂ → ℂ := fun w => w * (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2) / 2
    have hza : z ≠ 1 := by intro h; norm_num [h] at h1
    have ha0 : a z ≠ 0 := hfac z h0 hza
    have ha : AnalyticAt ℂ a z := by
      apply DifferentiableOn.analyticAt _ ((isOpen_re_gt 0).mem_nhds h0)
      intro w hw
      change 0 < w.re at hw
      apply DifferentiableAt.differentiableWithinAt
      unfold a
      have hdG : DifferentiableAt ℂ (fun v : ℂ => Gamma (v / 2)) w :=
        (hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt.comp w (by fun_prop)
      have hdpi : DifferentiableAt ℂ (fun v : ℂ => (Real.pi : ℂ) ^ (-v / 2)) w :=
        (show DifferentiableAt ℂ (fun v : ℂ => -v / 2) w by fun_prop).const_cpow
          (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
      fun_prop
    have he : xi =ᶠ[𝓝 z] a * riemannZeta := by
      filter_upwards [(isOpen_re_gt 0).mem_nhds h0, isOpen_ne.mem_nhds hza] with w hw hw1
      exact heq w hw hw1
    have hζ : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hza
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hζ,
      analyticOrderAt_eq_zero.mpr (Or.inr ha0), zero_add]

/-- LEAF. Unit U-1551. Davenport chapter 12, logarithmic differentiation of
`ξ(s) = s(s-1)/2 · π^{-s/2} Γ(s/2) ζ(s)`: for `Re s > 1`,
`ξ'/ξ(s) = 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2) + ζ'/ζ(s)`. -/
theorem logDeriv_xi (s : ℂ) (hs : 1 < s.re) :
    logDeriv xi s = 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2
      + logDeriv ζ s := by
  have heq : ∀ z : ℂ, 1 < z.re → xi z =
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) * riemannZeta z * (2 : ℂ)⁻¹ := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : 1 - z ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
    have hG : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hpi : (Real.pi : ℂ) ^ (-z / 2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    rw [riemannZeta_eq_completedRiemannZeta₀ hz0]
    unfold xi
    field_simp
    ring
  have heq' : xi =ᶠ[𝓝 s] (fun z =>
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) * riemannZeta z * (2 : ℂ)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact heq z hz
  rw [(logDeriv_congr_nhds heq').self_of_nhds, logDeriv_mul_const _ _ (by norm_num)]
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hG : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hdG : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s := by
    apply DifferentiableAt.comp s ((hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt)
    fun_prop
  have hdpi : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    exact (show DifferentiableAt ℂ (fun z : ℂ => -z / 2) s by fun_prop).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [logDeriv_fun_mul s (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1) hpi) hG)
    (riemannZeta_ne_zero_of_one_lt_re hs) (by fun_prop) (differentiableAt_riemannZeta (by intro h; norm_num [h] at hs))]
  rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Gamma (z / 2)) s (mul_ne_zero (mul_ne_zero hs0 hs1) hpi) hG
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdpi) hdG]
  rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1))
    (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s (mul_ne_zero hs0 hs1) hpi (by fun_prop) hdpi]
  rw [logDeriv_fun_mul s hs0 hs1 (by fun_prop) (by fun_prop)]
  have hp : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_fun_comp (f := fun z : ℂ => (Real.pi : ℂ) ^ z)
      (g := fun z : ℂ => -z / 2) (by fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))) (by fun_prop)]
    simp only [Complex.logDeriv_const_cpow (ofReal_ne_zero.mpr Real.pi_ne_zero)]
    simp [← Complex.ofReal_log Real.pi_pos.le]
    ring
  have hgamma : logDeriv (fun z : ℂ => Gamma (z / 2)) s = digamma (s / 2) / 2 := by
    rw [logDeriv_fun_comp (f := Gamma) (g := fun z : ℂ => z / 2)
      (hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt (by fun_prop)]
    simp [← digamma_def, div_eq_mul_inv]
  rw [hp, hgamma]
  simp [logDeriv_apply]
  ring

/-- LEAF. Unit U-1551. Davenport chapter 12, equations (17) and (18), real part form: for
`Re s > 1`, `Σ_ρ Re 1/(s - ρ) = Re ζ'/ζ(s) + Re 1/(s-1) - (1/2) log π + (1/2) Re ψ(s/2 + 1)`,
the sum over the nontrivial zeros with multiplicity, as a `HasSum` over `ZIdx`. From
`hadamard_logDeriv_order_one` applied to `ξ`, `ξ(0) = 1/2`, the three hypotheses, `xi_one_sub`
for `Re B = -Σ_ρ Re 1/ρ`, and `ψ(s/2 + 1) = ψ(s/2) + 2/s`, Mathlib's `digamma_apply_add_one`.
The reindexing from the zeros of `ξ` to `ZIdx` uses the first two hypotheses. -/
theorem hadamard_re_sum_of
    (hg : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖xi s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)))
    (hz : (∀ ρ : ℂ, xi ρ = 0 ↔ (ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)) ∧
      (∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        analyticOrderNatAt xi ρ = analyticOrderNatAt ζ ρ))
    (hl : ∀ s : ℂ, 1 < s.re → logDeriv xi s = 1 / s + 1 / (s - 1)
      - (Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2 + logDeriv ζ s)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun i : ZIdx => (1 / (s - (i.1 : ℂ))).re)
      ((logDeriv ζ s).re + (1 / (s - 1)).re - Real.log Real.pi / 2
        + (digamma (s / 2 + 1)).re / 2) := by
  sorry

set_option maxHeartbeats 3200000
set_option maxRecDepth 2000

/-- LEAF. Unit U-1551. `|ζ'/ζ(5/2 + it)| ≤ Σ Λ(n) n^{-5/2} = -ζ'/ζ(5/2) = 0.28874 ≤ 3/10`,
from Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and a finite sum with a tail
bound. -/
theorem logDeriv_bound_5half (t : ℝ) : ‖logDeriv ζ ((5 / 2 : ℂ) + t * I)‖ ≤ 3 / 10 := by
  -- Exact prime powers below 64, followed by a telescoped logarithmic tail.
  -- Rational logarithm bounds use twenty positive terms of the exponential series.
  let f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n)
  have hf0 : ∀ n, 0 ≤ f n := by intro n; exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hprefix : ∑ n ∈ Finset.range 64, f n ≤ (288/1000 : ℝ) := by
    change ∑ n ∈ Finset.range 64, ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ (288/1000 : ℝ)
    have l2 : Real.log 2 ≤ (6932/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 20, (6932/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l3 : Real.log 3 ≤ (10987/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 20, (10987/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l5 : Real.log 5 ≤ (16095/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 20, (16095/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l7 : Real.log 7 ≤ (19460/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 20, (19460/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l11 : Real.log 11 ≤ (23979/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (11 : ℝ) ≤ ∑ i ∈ Finset.range 20, (23979/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l13 : Real.log 13 ≤ (25650/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (13 : ℝ) ≤ ∑ i ∈ Finset.range 20, (25650/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l17 : Real.log 17 ≤ (28333/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (17 : ℝ) ≤ ∑ i ∈ Finset.range 20, (28333/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l19 : Real.log 19 ≤ (29445/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (19 : ℝ) ≤ ∑ i ∈ Finset.range 20, (29445/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l23 : Real.log 23 ≤ (31355/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (23 : ℝ) ≤ ∑ i ∈ Finset.range 20, (31355/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l29 : Real.log 29 ≤ (33673/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (29 : ℝ) ≤ ∑ i ∈ Finset.range 20, (33673/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l31 : Real.log 31 ≤ (34340/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (31 : ℝ) ≤ ∑ i ∈ Finset.range 20, (34340/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l37 : Real.log 37 ≤ (36110/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (37 : ℝ) ≤ ∑ i ∈ Finset.range 20, (36110/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l41 : Real.log 41 ≤ (37136/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (41 : ℝ) ≤ ∑ i ∈ Finset.range 20, (37136/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l43 : Real.log 43 ≤ (37613/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (43 : ℝ) ≤ ∑ i ∈ Finset.range 20, (37613/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l47 : Real.log 47 ≤ (38502/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (47 : ℝ) ≤ ∑ i ∈ Finset.range 20, (38502/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l53 : Real.log 53 ≤ (39703/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (53 : ℝ) ≤ ∑ i ∈ Finset.range 20, (39703/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l59 : Real.log 59 ≤ (40776/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (59 : ℝ) ≤ ∑ i ∈ Finset.range 20, (40776/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l61 : Real.log 61 ≤ (41109/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (61 : ℝ) ≤ ∑ i ∈ Finset.range 20, (41109/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    let b : ℕ → ℝ := fun n => ([(0/100000000 : ℝ),(0/100000000 : ℝ),(12254279/100000000 : ℝ),(7048371/100000000 : ℝ),(2166250/100000000 : ℝ),(2879249/100000000 : ℝ),(0/100000000 : ℝ),(1501089/100000000 : ℝ),(382947/100000000 : ℝ),(452140/100000000 : ℝ),(0/100000000 : ℝ),(597521/100000000 : ℝ),(0/100000000 : ℝ),(420955/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(67696/100000000 : ℝ),(237778/100000000 : ℝ),(0/100000000 : ℝ),(187128/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(123592/100000000 : ℝ),(0/100000000 : ℝ),(51504/100000000 : ℝ),(0/100000000 : ℝ),(29006/100000000 : ℝ),(0/100000000 : ℝ),(74352/100000000 : ℝ),(0/100000000 : ℝ),(64181/100000000 : ℝ),(11968/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(43364/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(34502/100000000 : ℝ),(0/100000000 : ℝ),(31022/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(25424/100000000 : ℝ),(0/100000000 : ℝ),(11579/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(19415/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(15251/100000000 : ℝ),(0/100000000 : ℝ),(14146/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ)].getD n 0)
    have hb : ∀ n ∈ Finset.range 64, ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ b n := by
      intro n hn
      have hn64 : n < 64 := Finset.mem_range.mp hn
      interval_cases n
      · norm_num [b, ArithmeticFunction.vonMangoldt_apply]
      · norm_num [b, ArithmeticFunction.vonMangoldt_apply]
      · have hv : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (14142/10000 : ℝ) ≤ Real.sqrt 2 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (17320/10000 : ℝ) ≤ Real.sqrt 3 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · have hv : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (20000/10000 : ℝ) ≤ Real.sqrt 4 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (22360/10000 : ℝ) ≤ Real.sqrt 5 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l5]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 6 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (26457/10000 : ℝ) ≤ Real.sqrt 7 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l7]
      · have hv : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (28284/10000 : ℝ) ≤ Real.sqrt 8 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (30000/10000 : ℝ) ≤ Real.sqrt 9 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 10 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (33166/10000 : ℝ) ≤ Real.sqrt 11 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l11]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 12 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (36055/10000 : ℝ) ≤ Real.sqrt 13 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l13]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 14 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 15 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (40000/10000 : ℝ) ≤ Real.sqrt 16 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (41231/10000 : ℝ) ≤ Real.sqrt 17 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l17]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 18 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (43588/10000 : ℝ) ≤ Real.sqrt 19 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l19]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 20 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 21 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 22 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (47958/10000 : ℝ) ≤ Real.sqrt 23 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l23]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 24 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (50000/10000 : ℝ) ≤ Real.sqrt 25 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l5]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 26 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (51961/10000 : ℝ) ≤ Real.sqrt 27 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 28 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (53851/10000 : ℝ) ≤ Real.sqrt 29 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l29]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 30 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (55677/10000 : ℝ) ≤ Real.sqrt 31 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l31]
      · have hv : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (56568/10000 : ℝ) ≤ Real.sqrt 32 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 33 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 34 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 35 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 36 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (60827/10000 : ℝ) ≤ Real.sqrt 37 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l37]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 38 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 39 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 40 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 41 = Real.log 41 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (64031/10000 : ℝ) ≤ Real.sqrt 41 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l41]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 42 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 43 = Real.log 43 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (65574/10000 : ℝ) ≤ Real.sqrt 43 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l43]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 44 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 45 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 46 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 47 = Real.log 47 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (68556/10000 : ℝ) ≤ Real.sqrt 47 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l47]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 48 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 49 = Real.log 7 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (70000/10000 : ℝ) ≤ Real.sqrt 49 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l7]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 50 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 51 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 52 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 53 = Real.log 53 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (72801/10000 : ℝ) ≤ Real.sqrt 53 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l53]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 54 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 55 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 56 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 57 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 58 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 59 = Real.log 59 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (76811/10000 : ℝ) ≤ Real.sqrt 59 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l59]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 60 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 61 = Real.log 61 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (78102/10000 : ℝ) ≤ Real.sqrt 61 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l61]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 62 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 63 by decide +kernel)]
        norm_num [b]
    calc _ ≤ ∑ n ∈ Finset.range 64, b n := Finset.sum_le_sum hb
         _ ≤ (288/1000 : ℝ) := by norm_num [b, Finset.sum_range_succ]
  have htail (n : ℕ) (hn : 64 ≤ n) : f n ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.fl n / 8 := by
    change ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.fl n / 8
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : (8 : ℝ) ≤ Real.sqrt n := by
      apply (Real.le_sqrt (by norm_num) hn0.le).2
      norm_num; exact_mod_cast hn
    have hp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hn0) hp)).2
    have hv : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hh : Real.log n ≤ Real.log n * (Real.sqrt n / 8) := by nlinarith
    calc ArithmeticFunction.vonMangoldt n ≤ Real.log n := hv
         _ ≤ Real.log n * (Real.sqrt n / 8) := hh
         _ = Real.log n / (n : ℝ)^2 / 8 * ((n : ℝ)^2 * Real.sqrt n) := by field_simp
  have hgt : LeanLab.PNTPort.ExplicitPsi1.Trivial.gt 63 / 8 ≤ (11/1000 : ℝ) := by
    have hlog : Real.log 63 ≤ (21/5 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (63 : ℝ) ≤ ∑ i ∈ Finset.range 20, (21/5 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.gt
    norm_num
    linarith
  have haux (M : ℕ) (hM : 64 ≤ M) :
      ∑ n ∈ Finset.range M, f n ≤ ∑ n ∈ Finset.range 64, f n + LeanLab.PNTPort.ExplicitPsi1.Trivial.gt 63 / 8 - LeanLab.PNTPort.ExplicitPsi1.Trivial.gt ((M : ℝ) - 1) / 8 := by
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      rw [Finset.sum_range_succ]
      have hn : (4 : ℝ) ≤ M := by exact_mod_cast (by omega : 4 ≤ M)
      have htele := LeanLab.PNTPort.ExplicitPsi1.Trivial.tele_step hn
      have ht := htail M hM
      unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl at ht
      rw [show ((M + 1 : ℕ) : ℝ) - 1 = M by push_cast; ring]
      linarith
  have hpartial (M : ℕ) : ∑ n ∈ Finset.range M, f n ≤ (3/10 : ℝ) := by
    by_cases hM : 64 ≤ M
    · have h1 := haux M hM
      have h2 : 0 ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.gt ((M : ℝ) - 1) := LeanLab.PNTPort.ExplicitPsi1.Trivial.gt_nonneg (by
        have hMr : (64 : ℝ) ≤ M := by exact_mod_cast hM
        linarith)
      linarith
    · have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := f)
        (Finset.range_subset_range.mpr (by omega : M ≤ 64)) (fun n _ _ => hf0 n)
      linarith
  have hsum : Summable f := summable_of_sum_range_le hf0 hpartial
  have hn (n : ℕ) : ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖ = f n := by
    rw [LSeries.norm_term_eq]
    split_ifs with hz
    · subst n; simp [f]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      norm_num
      change ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5/2 : ℝ) = f n
      rw [show (5/2 : ℝ) = 2 + 1/2 by norm_num, Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by norm_num), Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hsn : Summable (fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖) := hsum.congr (fun n => (hn n).symm)
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (5/2 : ℂ) + t * I) (by simp; norm_num)
  have he : logDeriv riemannZeta ((5/2 : ℂ) + t * I) = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) := by
    rw [hL, logDeriv_apply]; ring
  rw [he, norm_neg]
  calc _ ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hsn
       _ = ∑' n, f n := tsum_congr hn
       _ ≤ 3/10 := Real.tsum_le_of_sum_range_le hf0 hpartial

set_option maxHeartbeats 200000
set_option maxRecDepth 1000

/-- LEAF. Unit U-1551. Stirling for the digamma function: `Re ψ(9/4 + iu) ≤ log|9/4 + iu| + 1/10`
for every real `u`; the float maximum of `Re ψ(9/4 + iu) - log|9/4 + iu|` over `|u| ≤ 200` is
negative, `-2.6·10⁻⁵`, and `Re ψ(z) = log|z| - Re z/(2|z|²) + O(|z|⁻²)`. -/
theorem digamma_re_le (u : ℝ) :
    (digamma ((9 / 4 : ℂ) + u * I)).re ≤ Real.log ‖(9 / 4 : ℂ) + u * I‖ + 1 / 10 := by
  sorry

/-- LEAF. Unit U-1551. The real inequality closing the bound: for `|g| ≥ 14`,
`2 (3/10 + Re 1/(3/2 + ig) - (1/2) log π + (log|9/4 + ig/2| + 1/10)/2) ≤ log |g|`; the left
side is at most `log |g| - 1.07`. -/
theorem final_numeric (g : ℝ) (hg : 14 ≤ |g|) :
    2 * (3 / 10 + (1 / ((3 / 2 : ℂ) + g * I)).re - Real.log Real.pi / 2
      + (Real.log ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ + 1 / 10) / 2) ≤ Real.log |g| := by
  have hg0 : 0 < |g| := by linarith
  have hsq : 196 ≤ g ^ 2 := by nlinarith [sq_abs g, sq_nonneg (|g| - 14)]
  have hn : ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ ≤ |g| := by
    apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith
  have hn0 : 0 < ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ := by
    apply norm_pos_iff.mpr
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hl := Real.log_le_log hn0 hn
  have hpi : 1 ≤ Real.log Real.pi := by
    exact (Real.le_log_iff_exp_le Real.pi_pos).mpr
      (Real.exp_one_lt_three.le.trans Real.pi_gt_three.le)
  have hi : (1 / ((3 / 2 : ℂ) + g * I)).re ≤ 1 / 10 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    norm_num
    apply (div_le_iff₀ (by nlinarith [sq_nonneg g] : (0 : ℝ) < 9 / 4 + g * g)).mpr
    nlinarith
  linarith

lemma re_inv_two (d : ℝ) : (1 / ((2 : ℂ) + d * I)).re = 2 / (4 + d ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp
  ring

/-- ASSEMBLY. Under RH, `HadamardK gZ`: for every finite set `s` of zeros and every zero `i`,
`Σ_{j ∈ s} 4/(4 + (γ_i - γ_j)²) ≤ log |γ_i|`. CONDITIONAL ON the leaves `xi_growth`,
`xi_zero_iff`, `logDeriv_xi`, `hadamard_re_sum_of`, `logDeriv_bound_5half`, `digamma_re_le`,
`final_numeric`, and through `Decomp1551c.ordinates14_gZ_of_RH` on the leaves of that file. -/
theorem hadamardK_gZ_of_RH (hRH : RiemannHypothesis) :
    LeanLab.ChirreHagen2025.SmoothT2.HadamardK gZ := by
  intro s i
  set g := gZ i with hg
  have h14 : 14 ≤ |g| := Decomp1551c.ordinates14_gZ_of_RH hRH i
  set z : ℂ := (5 / 2 : ℂ) + g * I with hzdef
  have hzre : 1 < z.re := by simp [hzdef]; norm_num
  have hS := hadamard_re_sum_of xi_growth xi_zero_iff logDeriv_xi z hzre
  have hrho : ∀ j : ZIdx, (j.1 : ℂ) = (1 / 2 : ℂ) + (gZ j : ℂ) * I := by
    intro j
    apply Complex.ext <;> simp [re_half_of_RH hRH j.1, gZ]
  have hterm : ∀ j : ZIdx, (1 / (z - (j.1 : ℂ))).re = K (g - gZ j) / 2 := by
    intro j
    have : z - (j.1 : ℂ) = (2 : ℂ) + ((g - gZ j : ℝ) : ℂ) * I := by
      rw [hrho j, hzdef]; push_cast; ring
    rw [this, re_inv_two]
    unfold K
    ring
  have hnn : ∀ j : ZIdx, 0 ≤ (1 / (z - (j.1 : ℂ))).re := by
    intro j; rw [hterm j]; unfold K; positivity
  have hsum := sum_le_hasSum s (fun j _ => hnn j) hS
  have hK : ∑ j ∈ s, K (g - gZ j) = 2 * ∑ j ∈ s, (1 / (z - (j.1 : ℂ))).re := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [hterm j]; ring
  have hb1 : (logDeriv ζ z).re ≤ 3 / 10 :=
    (Complex.re_le_norm _).trans (logDeriv_bound_5half g)
  have hz1 : z - 1 = (3 / 2 : ℂ) + g * I := by rw [hzdef]; ring
  have hz2 : z / 2 + 1 = (9 / 4 : ℂ) + ((g / 2 : ℝ) : ℂ) * I := by rw [hzdef]; push_cast; ring
  have hb2 := digamma_re_le (g / 2)
  have hfin := final_numeric g h14
  rw [hz1, hz2] at hsum
  rw [hK]
  linarith

end LeanLab.Routes.Decomp1551b
