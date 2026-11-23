/-
Copyright: Lean Lab. AI wrote this Lean code.
BHP1997, P0069 page 22, Lemma 8, with Rademacher reference 28 page 195 display 3.1.
Port of the finite order growth input for `Decomp530a.leaf_regularPart_finite_order_growth`:
bounds on the Mathlib completed L-function and on the reciprocal Gamma factor.
The final compact and pole step is in `Decomp530a`, which imports this file.
Binary Goldbach is open; this file proves nothing about it.
-/
import Mathlib
import LeanLab.BHP1997.Decomp560a

namespace LeanLab.BHP1997.FiniteOrderPortS64
open Complex HurwitzZeta

/-- A Mellin transform that converges absolutely on the two edges of a closed vertical
strip is bounded on the whole strip, since `t ^ (σ - 1) ≤ t ^ (a - 1) + t ^ (b - 1)`
for positive `t`. Port step 1 for Rademacher page 195 display 3.1. -/
theorem mellin_strip_bounded {f : ℝ → ℂ} {a b : ℝ}
    (ha : MellinConvergent f a) (hb : MellinConvergent f b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖mellin f s‖ ≤ M := by
  let g : ℝ → ℝ := fun t => ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖ + ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) := ha.norm.add hb.norm
  refine ⟨∫ t in Set.Ioi (0 : ℝ), g t, MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun t _ => by positivity), ?_⟩
  intro s hsa hsb
  refine MeasureTheory.norm_integral_le_of_norm_le hg ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t (ht : 0 < t)
  simp only [g, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ofReal_re]
  have hf := norm_nonneg (f t)
  have hpa := Real.rpow_nonneg ht.le (a - 1)
  have hpb := Real.rpow_nonneg ht.le (b - 1)
  rcases le_or_gt t 1 with h1 | h1
  · have : t ^ (s.re - 1) ≤ t ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht h1 (by linarith)
    nlinarith
  · have : t ^ (s.re - 1) ≤ t ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    nlinarith

/-- The entire part `Λ₀` of any weak FE pair is bounded on every closed vertical strip.
Port step 1 for Rademacher page 195 display 3.1. -/
theorem WeakFEPair_Λ₀_strip_bounded (P : WeakFEPair ℂ) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ₀ s‖ ≤ M :=
  mellin_strip_bounded (P.isStrongFEPair_toStrongFEPair.hasMellin (a : ℂ)).1
    (P.isStrongFEPair_toStrongFEPair.hasMellin (b : ℂ)).1

/-- Rademacher page 195 display 3.1, finite order input, port step 1.
The entire completed L-function of Mathlib, `ZMod.completedLFunction₀`, is a finite
sum of Mellin transforms of rapidly decaying theta kernels, so it is bounded on
every closed vertical strip. -/
theorem completedLFunction₀_strip_bounded {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖ZMod.completedLFunction₀ Φ s‖ ≤ M := by
  have hE (j : ZMod N) := WeakFEPair_Λ₀_strip_bounded
    (hurwitzEvenFEPair (ZMod.toAddCircle j)) (a / 2) (b / 2)
  have hO (j : ZMod N) := WeakFEPair_Λ₀_strip_bounded
    (hurwitzOddFEPair (ZMod.toAddCircle j)) ((a + 1) / 2) ((b + 1) / 2)
  choose ME hME0 hME using hE
  choose MO hMO0 hMO using hO
  set P : ℝ := (N : ℝ) ^ |a| with hPdef
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  refine ⟨P * ∑ j, ‖Φ j‖ * ME j + P * ∑ j, ‖Φ j‖ * MO j,
    add_nonneg (mul_nonneg hP0 (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hME0 j)))
      (mul_nonneg hP0 (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hMO0 j))), ?_⟩
  intro s hsa hsb
  have hNs : ‖(N : ℂ) ^ (-s)‖ ≤ P := by
    rw [norm_natCast_cpow_of_pos (NeZero.pos N), neg_re]
    apply Real.rpow_le_rpow_of_exponent_le hN
    linarith [neg_abs_le a]
  rw [ZMod.completedLFunction₀]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    refine mul_le_mul hNs ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      (norm_nonneg _) hP0
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [completedHurwitzZetaEven₀, norm_div]
    have := hME j (s / 2) (by simp; linarith) (by simp; linarith)
    simp only [Complex.norm_ofNat]
    linarith [norm_nonneg ((hurwitzEvenFEPair (ZMod.toAddCircle j)).Λ₀ (s / 2))]
  · rw [norm_mul]
    refine mul_le_mul hNs ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      (norm_nonneg _) hP0
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [completedHurwitzZetaOdd, norm_div]
    have hΛ : (hurwitzOddFEPair (ZMod.toAddCircle j)).Λ ((s + 1) / 2) =
        (hurwitzOddFEPair (ZMod.toAddCircle j)).Λ₀ ((s + 1) / 2) := by
      simp [WeakFEPair.Λ]
    have := hMO j ((s + 1) / 2) (by simp; linarith) (by simp; linarith)
    rw [hΛ]
    simp only [Complex.norm_ofNat]
    linarith [norm_nonneg ((hurwitzOddFEPair (ZMod.toAddCircle j)).Λ₀ ((s + 1) / 2))]

/-- Reciprocal Gamma grows at most exponentially in the height on every closed
vertical strip, with no positivity condition on the strip. DLMF 5.5.1 and 5.5.3, the
port step 2 input for Rademacher page 195 display 3.1. Same proof as
`Decomp560a.leaf_reciprocal_Gamma_strip`, which needs no lower bound on the strip. -/
theorem reciprocal_Gamma_strip_any {a b : ℝ} (hab : a ≤ b) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (B * |z.im|) := by
  obtain ⟨A, hA, hlarge⟩ := Decomp560a.reciprocal_Gamma_high_strip hab
  let S : Set ℂ := Set.Icc a b ×ℂ Set.Icc (-1 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun z : ℂ => (Complex.Gamma z)⁻¹) S :=
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc
  let C : ℝ := A + max M 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, Real.pi, hC, Real.pi_pos, ?_⟩
  intro z hza hzb
  have hAC : A ≤ C := by dsimp [C]; linarith [le_max_right M 0]
  by_cases ht : 1 ≤ |z.im|
  · exact (hlarge z hza hzb ht).trans
      (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
  · have hz : z ∈ S := by
      change z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc (-1 : ℝ) 1
      exact ⟨⟨hza, hzb⟩, (abs_le.mp (le_of_lt (lt_of_not_ge ht)))⟩
    have he : 1 ≤ Real.exp (Real.pi * |z.im|) := Real.one_le_exp (by positivity)
    calc
      _ ≤ M := hM z hz
      _ ≤ C := by dsimp [C]; linarith [le_max_left M 0]
      _ ≤ C * Real.exp (Real.pi * |z.im|) := le_mul_of_one_le_right hC.le he

/-- Rademacher page 195 display 3.1, finite order input, port step 2.
The reciprocal archimedean factor `1 / Gammaℝ s` grows at most exponentially in the
height on every closed vertical strip. DLMF 5.5.1 and 5.5.3. -/
theorem inv_Gammaℝ_strip_growth (a b : ℝ) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖(Gammaℝ s)⁻¹‖ ≤ C * Real.exp (B * |s.im|) := by
  obtain ⟨C, B, hC, hB, hG⟩ :=
    reciprocal_Gamma_strip_any (a := a / 2) (b := max a b / 2)
      (by have := le_max_left a b; linarith)
  refine ⟨Real.pi ^ |b| * C, B / 2, by positivity, by positivity, ?_⟩
  intro s hsa hsb
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [Gammaℝ_def, mul_inv, norm_mul, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : (Real.pi ^ (-s / 2).re)⁻¹ ≤ Real.pi ^ |b| := by
    rw [← Real.rpow_neg Real.pi_pos.le]
    apply Real.rpow_le_rpow_of_exponent_le hpi
    have : (-s / 2).re = -(s.re / 2) := by simp; ring
    rw [this, neg_neg]
    have := le_abs_self b
    rcases le_or_gt 0 s.re with h | h
    · linarith
    · linarith [abs_nonneg b]
  have h2 := hG (s / 2) (by simp; linarith)
    (by simp; have := le_max_right a b; linarith)
  have him : |(s / 2).im| = |s.im| / 2 := by
    simp [abs_div]
  rw [him] at h2
  calc _ ≤ Real.pi ^ |b| * (C * Real.exp (B * (|s.im| / 2))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring_nf

/-- P0069 page 22 and Rademacher page 195 display 3.1, the completed L-function
part of the bound at height at least one. Proved from the two port steps above. -/
theorem LFunction_bound_high {δ : ℝ} (_hδ : 0 < δ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∃ E G B : ℝ, 0 ≤ E ∧ 0 < G ∧ 0 < B ∧ ∀ s : ℂ, -δ ≤ s.re → s.re ≤ 1 + δ →
      1 ≤ |s.im| → ‖χ.LFunction s‖ ≤ E * (G * Real.exp (B * |s.im|)) := by
  obtain ⟨M, hM0, hM⟩ := completedLFunction₀_strip_bounded (χ : ZMod q → ℂ) (-δ) (1 + δ)
  obtain ⟨G, B, hG, hB, hgam⟩ := inv_Gammaℝ_strip_growth (-δ) (2 + δ)
  set P : ℝ := (q : ℝ) ^ δ with hPdef
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  refine ⟨M + P * ‖(χ : ZMod q → ℂ) 0‖ + P * ‖∑ j, (χ : ZMod q → ℂ) j‖, G, B,
    by positivity, hG, hB, ?_⟩
  intro s hsl hsu ht
  have hsim : 1 ≤ ‖s‖ := ht.trans (abs_im_le_norm s)
  have h1s : 1 ≤ ‖1 - s‖ := by
    have := abs_im_le_norm (1 - s)
    simp only [sub_im, one_im, zero_sub, abs_neg] at this
    linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h, norm_zero] at hsim; linarith
  have hs1 : (1 : ℂ) - s ≠ 0 := by
    intro h; rw [h, norm_zero] at h1s; linarith
  have hNs : ‖(q : ℂ) ^ (-s)‖ ≤ P := by
    rw [norm_natCast_cpow_of_pos (NeZero.pos q), neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hcomp : ‖χ.completedLFunction s‖ ≤
      M + P * ‖(χ : ZMod q → ℂ) 0‖ + P * ‖∑ j, (χ : ZMod q → ℂ) j‖ := by
    rw [DirichletCharacter.completedLFunction, ZMod.completedLFunction_eq]
    have e1 : ‖(q : ℂ) ^ (-s) * (χ : ZMod q → ℂ) 0 / s‖ ≤ P * ‖(χ : ZMod q → ℂ) 0‖ := by
      rw [norm_div, norm_mul]
      calc _ ≤ ‖(q : ℂ) ^ (-s)‖ * ‖(χ : ZMod q → ℂ) 0‖ :=
            div_le_self (by positivity) hsim
        _ ≤ _ := mul_le_mul_of_nonneg_right hNs (norm_nonneg _)
    have e2 : ‖(q : ℂ) ^ (-s) * (∑ j, (χ : ZMod q → ℂ) j) / (1 - s)‖ ≤
        P * ‖∑ j, (χ : ZMod q → ℂ) j‖ := by
      rw [norm_div, norm_mul]
      calc _ ≤ ‖(q : ℂ) ^ (-s)‖ * ‖∑ j, (χ : ZMod q → ℂ) j‖ :=
            div_le_self (by positivity) h1s
        _ ≤ _ := mul_le_mul_of_nonneg_right hNs (norm_nonneg _)
    calc _ ≤ ‖ZMod.completedLFunction₀ (χ : ZMod q → ℂ) s‖
          + ‖(q : ℂ) ^ (-s) * (χ : ZMod q → ℂ) 0 / s‖
          + ‖(q : ℂ) ^ (-s) * (∑ j, (χ : ZMod q → ℂ) j) / (1 - s)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (hM s hsl hsu) e1) e2
  have hgf : ‖(χ.gammaFactor s)⁻¹‖ ≤ G * Real.exp (B * |s.im|) := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def]
      exact hgam s (by linarith) (by linarith)
    · rw [ho.gammaFactor_def]
      have := hgam (s + 1) (by simp; linarith) (by simp; linarith)
      simpa using this
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0),
    div_eq_mul_inv, norm_mul]
  exact mul_le_mul hcomp hgf (norm_nonneg _) (by positivity)

end LeanLab.BHP1997.FiniteOrderPortS64
