/-
ZeroFreeHigh is the qualitative textbook input in State1535.
Reuse PNTPort.DirichletZF.RealZero and StrongPNT.ZetaZeroFree1.
The logarithmic comparison and compact height strip are derived bridges.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.State1535
import LeanLab.PNTPort.DirichletZF.RealZero

namespace LeanLab.Ternary.U1535.Task361
open Set Filter Topology Complex
open LeanLab.PNTPort.DirichletZF

/-- A compact height segment away from the real axis has a uniform zero free
strip to the left of one. Derived bridge from Mathlib nonvanishing on Re s one.
Textbook source: Davenport chapter 14, the compact height part. -/
theorem zeta_compact_strip :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ t : ℝ, 1 ≤ |t| → |t| ≤ 3 →
      1 - δ ≤ σ → σ ≤ 1 → riemannZeta (σ + t * I) ≠ 0 := by
  let K : Set ℂ := (fun t : ℝ => (1 : ℂ) + t * I) '' (Icc (-3 : ℝ) (-1) ∪ Icc 1 3)
  let U : Set ℂ := {s | s ≠ 1 ∧ riemannZeta s ≠ 0}
  have hK : IsCompact K := (isCompact_Icc.union isCompact_Icc).image (by fun_prop)
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    exact (eventually_ne_nhds hs.1).and
      ((differentiableAt_riemannZeta hs.1).continuousAt.eventually_ne hs.2)
  have hKU : K ⊆ U := by
    rintro s ⟨t, ht, rfl⟩
    constructor
    · intro heq
      have hi := congrArg Complex.im heq
      simp at hi
      rcases ht with ht | ht <;> rcases ht with ⟨hl, hu⟩ <;> linarith
    · apply riemannZeta_ne_zero_of_one_le_re
      simp
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro σ t ht1 ht3 hσ hσ1
  apply (hsub ?_).2
  apply Metric.mem_cthickening_of_dist_le _ ((1 : ℂ) + t * I) δ K
  · refine ⟨t, ?_, rfl⟩
    rcases le_or_gt t 0 with ht | ht
    · left
      rw [abs_of_nonpos ht] at ht1 ht3
      constructor <;> linarith
    · right
      rw [abs_of_pos ht] at ht1 ht3
      exact ⟨ht1, ht3⟩
  · rw [dist_eq_norm]
    have heq : (σ : ℂ) + t * I - (1 + t * I) = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith

/-- The ported logarithmic zero free strip and the compact strip give a single
positive coefficient for zeta at all heights at least one.
Derived bridge to the qualitative region in Davenport chapter 14. -/
theorem zeta_log_strip :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∀ σ t : ℝ, 1 ≤ |t| →
      1 - a / Real.log (|t| + 2) ≤ σ → riemannZeta (σ + t * I) ≠ 0 := by
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  obtain ⟨δ, hδ, hsmall⟩ := zeta_compact_strip
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let a := min A (min (δ * Real.log 3) (Real.log 3 / 2))
  have ha : 0 < a := lt_min hA.1 (lt_min (mul_pos hδ hl3) (by positivity))
  have haA : a ≤ A := min_le_left _ _
  have haδ : a ≤ δ * Real.log 3 := (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ Real.log 3 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min a (1 / 2), lt_min ha (by norm_num), min_le_right _ _, ?_⟩
  intro σ t ht hσ
  have hl : Real.log 3 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlpos : 0 < Real.log (|t| + 2) := hl3.trans_le hl
  have ha' : min a (1 / 2) ≤ a := min_le_left _ _
  by_cases hσ1 : 1 ≤ σ
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hσ1)
  have hσ1' : σ ≤ 1 := (lt_of_not_ge hσ1).le
  by_cases ht3 : |t| ≤ 3
  · apply hsmall σ t ht ht3 _ hσ1'
    have hdiv : min a (1 / 2) / Real.log (|t| + 2) ≤ δ :=
      (div_le_iff₀ hlpos).mpr ((ha'.trans haδ).trans
        (mul_le_mul_of_nonneg_left hl hδ.le))
    linarith
  · have ht3' : 3 < |t| := lt_of_not_ge ht3
    apply hlarge σ t ht3'
    constructor
    · rw [Real.rpow_one]
      have hlt : 0 < Real.log |t| := Real.log_pos (by linarith)
      have hmono : Real.log |t| ≤ Real.log (|t| + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hdiv : min a (1 / 2) / Real.log (|t| + 2) ≤ A / Real.log |t| :=
        (div_le_div_of_nonneg_right (ha'.trans haA) hlpos.le).trans
          (div_le_div_of_nonneg_left hA.1.le hlt hmono)
      linarith
    · exact lt_of_not_ge hσ1

/-- Principal characters inherit a zero free strip from zeta. Euler factors
cannot vanish at positive real part. Derived from the Mathlib Euler product. -/
theorem principal_log_strip :
    ∃ a : ℝ, 0 < a ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 ≤ |t| →
      1 - a / Real.log (q * (|t| + 2)) ≤ σ →
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ + t * I) ≠ 0 := by
  obtain ⟨a, ha, ha2, hz⟩ := zeta_log_strip
  refine ⟨min a (Real.log 3 / 2), lt_min ha (by positivity), ?_⟩
  intro q _ σ t ht hσ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hu : (3 : ℝ) ≤ |t| + 2 := by linarith
  have hv : |t| + 2 ≤ q * (|t| + 2) := by nlinarith
  have hlu : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith)
  have hlv : Real.log (|t| + 2) ≤ Real.log (q * (|t| + 2)) :=
    Real.log_le_log (by linarith) hv
  have hlvpos : 0 < Real.log (q * (|t| + 2)) := hlu.trans_le hlv
  have hl3 : Real.log 3 ≤ Real.log (q * (|t| + 2)) :=
    Real.log_le_log (by norm_num) (hu.trans hv)
  have hamin : 0 < min a (Real.log 3 / 2) := lt_min ha (by positivity)
  have hhalf : min a (Real.log 3 / 2) / Real.log (q * (|t| + 2)) ≤ 1 / 2 := by
    apply (div_le_iff₀ hlvpos).mpr
    linarith [min_le_right a (Real.log 3 / 2)]
  have hσpos : 0 < σ := by linarith
  have hs : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    norm_num [hi] at ht
  change DirichletCharacter.LFunctionTrivChar q (σ + t * I) ≠ 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpprime := (Nat.mem_primeFactors.mp hp).1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hnorm : ‖(p : ℂ) ^ (-((σ : ℂ) + t * I))‖ < 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p)]
      simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    intro hzero
    have hone : (p : ℂ) ^ (-((σ : ℂ) + t * I)) = 1 := by linear_combination -hzero
    rw [hone, norm_one] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  · apply hz σ t ht
    have hdiv : min a (Real.log 3 / 2) / Real.log (q * (|t| + 2)) ≤
        a / Real.log (|t| + 2) :=
      (div_le_div_of_nonneg_right (min_le_left _ _) hlvpos.le).trans
        (div_le_div_of_nonneg_left ha.le hlu hlv)
    linarith

/-- The lab zero region uses log of Bt. Its denominator is bounded by a
fixed multiple of the textbook denominator, uniformly in modulus and height.
Derived change of normalization for Davenport chapter 14. -/
theorem log_Bt_comparison :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (t : ℝ), 1 ≤ |t| →
      Real.log (Bt q t) ≤ D * Real.log (q * (|t| + 2)) := by
  have hZ := one_le_Z
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlZ : 0 ≤ Real.log (4 * Z) := Real.log_nonneg (by linarith)
  let D : ℝ := 1 + Real.log (4 * Z) / Real.log 3
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro q _ t ht
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hu : (3 : ℝ) ≤ q * (|t| + 2) := by nlinarith
  have hlu : Real.log 3 ≤ Real.log (q * (|t| + 2)) :=
    Real.log_le_log (by norm_num) hu
  have hBt : Bt q t ≤ (4 * Z) * (q * (|t| + 2)) := by
    unfold Bt
    nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ (q : ℝ)) (by linarith : 0 ≤ Z))
      (by linarith [abs_nonneg t] : 0 ≤ |t| + 1)]
  calc
    Real.log (Bt q t) ≤ Real.log ((4 * Z) * (q * (|t| + 2))) :=
      Real.log_le_log (lt_trans zero_lt_one (one_lt_Bt t)) hBt
    _ = Real.log (4 * Z) + Real.log (q * (|t| + 2)) :=
      Real.log_mul (by positivity) (by linarith)
    _ ≤ D * Real.log (q * (|t| + 2)) := by
      have hm := mul_le_mul_of_nonneg_left hlu
        (div_nonneg hlZ hl3.le)
      have heq : Real.log (4 * Z) / Real.log 3 * Real.log 3 = Real.log (4 * Z) :=
        div_mul_cancel₀ _ hl3.ne'
      rw [heq] at hm
      dsimp [D]
      nlinarith

/-- Every nonprincipal character is nonzero in a uniform textbook strip
away from the real axis. The possible exceptional zero in the port is real.
Derived from PNTPort zero_free_region_real and the denominator comparison. -/
theorem nonprincipal_log_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ t : ℝ, 1 ≤ |t| → 1 - 1 / (C * Real.log (q * (|t| + 2))) ≤ σ →
        DirichletCharacter.LFunction χ (σ + t * I) ≠ 0 := by
  obtain ⟨c, c', hc, hc', hreg⟩ := zero_free_region_real
  obtain ⟨D, hD, hcomp⟩ := log_Bt_comparison
  let C : ℝ := 2 * D / c
  have hC : 0 < C := by dsimp [C]; positivity
  have hcC : c * C = 2 * D := by dsimp [C]; field_simp <;> ring
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ σ t ht hσ hz
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlu : 0 < Real.log (q * (|t| + 2)) := Real.log_pos (by nlinarith)
  have hlB : 0 < Real.log (Bt q t) := Real.log_pos (one_lt_Bt t)
  have hlt : 1 / (C * Real.log (q * (|t| + 2))) < c / Real.log (Bt q t) := by
    apply (div_lt_div_iff₀ (mul_pos hC hlu) hlB).mpr
    calc
      1 * Real.log (Bt q t) ≤ D * Real.log (q * (|t| + 2)) := by simpa using hcomp q t ht
      _ < 2 * D * Real.log (q * (|t| + 2)) := by nlinarith [mul_pos hD hlu]
      _ = c * (C * Real.log (q * (|t| + 2))) := by rw [← hcC]; ring
  rcases (hreg q χ hχ).1 (σ + t * I) hz with hr | hr
  · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero, add_im, mul_im, mul_one, zero_add] at hr
    linarith
  · have him := hr.2.2.2
    simp at him
    norm_num [him] at ht

/-- Increasing a positive strip denominator narrows the region.
Elementary comparison used for the two character cases in chapter 14. -/
theorem strip_denominator_mono {C D u σ : ℝ} (hC : 0 < C) (hCD : C ≤ D)
    (hu : 0 < u) (hσ : 1 - 1 / (D * u) ≤ σ) :
    1 - 1 / (C * u) ≤ σ := by
  have hdiv : 1 / (D * u) ≤ 1 / (C * u) :=
    one_div_le_one_div_of_le (mul_pos hC hu) (mul_le_mul_of_nonneg_right hCD hu.le)
  linarith

/-- The exact sealed qualitative input, proved by the existing lab zero region
and the ported zeta strip. No cited analytic input is assumed. -/
theorem zeroFreeHigh_exists_decomposed : ∃ c : ℝ, 0 < c ∧ ZeroFreeHigh c := by
  obtain ⟨a, ha, hprincipal⟩ := principal_log_strip
  obtain ⟨C, hC, hnonprincipal⟩ := nonprincipal_log_strip
  refine ⟨max (1 / a) C, lt_of_lt_of_le hC (le_max_right _ _), ?_⟩
  intro q _ χ σ t ht hσ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlu : 0 < Real.log (q * (|t| + 2)) := Real.log_pos (by nlinarith)
  by_cases hχ : χ = 1
  · subst χ
    apply hprincipal q σ t ht
    have hs := strip_denominator_mono (one_div_pos.mpr ha) (le_max_left _ _) hlu hσ
    have heq : 1 / ((1 / a) * Real.log (q * (|t| + 2))) =
        a / Real.log (q * (|t| + 2)) := by field_simp
    rwa [heq] at hs
  · exact hnonprincipal q χ hχ σ t ht
      (strip_denominator_mono hC (le_max_right _ _) hlu hσ)

end LeanLab.Ternary.U1535.Task361
