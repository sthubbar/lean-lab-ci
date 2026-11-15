import LeanLab.RamareSaouter2003.Decomp579a
import LeanLab.RamareSaouter2003.Decomp537a
import LeanLab.RamareSaouter2003.Decomp563d

/-!
Backlund pp. 366 and 367 displays 70, 71 and 73.
This file imports no target file and no descendant of the target.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp579b
open Real Complex Set
open Decomp579a

/-- Backlund p. 366 display 70, the completed zeta product at positive height. -/
theorem completed_product (σ t : ℝ) (ht : 0 < t) :
    Complex.Gammaℝ ((σ : ℂ) + t * I) * riemannZeta ((σ : ℂ) + t * I) =
      completedRiemannZeta ((σ : ℂ) + t * I) := by
  have hs : (σ : ℂ) + t * I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hg : Complex.Gammaℝ ((σ : ℂ) + t * I) ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
    have hi := congrArg Complex.im hn
    simp at hi
    linarith
  rw [riemannZeta_def_of_ne_zero hs, mul_div_cancel₀ _ hg]

/-- Backlund p. 366 display 70, exact completed-product norm symmetry.
Mathlib supplies the functional equation and conjugation. -/
theorem completed_norm_reflection (σ t : ℝ) (ht : 0 < t) :
    ‖Complex.Gammaℝ (((1 - σ : ℝ) : ℂ) + t * I) *
        riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ =
      ‖Complex.Gammaℝ ((σ : ℂ) + t * I) * riemannZeta ((σ : ℂ) + t * I)‖ := by
  let s : ℂ := (σ : ℂ) + t * I
  have hconj : (starRingEnd ℂ) s = (σ : ℂ) + (-t) * I := by simp [s]
  have hs : (starRingEnd ℂ) s ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [s] at hi
    linarith
  have hg : Complex.Gammaℝ ((starRingEnd ℂ) s) ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
    have hi := congrArg Complex.im hn
    simp [s] at hi
    linarith
  have hc : completedRiemannZeta ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (Complex.Gammaℝ s * riemannZeta s) := by
    rw [map_mul, ← Complex.Gammaℝ_conj, ← riemannZeta_conj,
      riemannZeta_def_of_ne_zero hs, mul_div_cancel₀ _ hg]
  have hr : (((1 - σ : ℝ) : ℂ) + t * I) = 1 - (starRingEnd ℂ) s := by
    simp [s]
    push_cast
    ring
  rw [completed_product (1 - σ) t ht, hr, completedRiemannZeta_one_sub, hc,
    Complex.norm_conj]

/-- Backlund p. 366 display 71, the scalar reflection error budget. -/
theorem reflection_budget (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2500) :
    (1 + u) ^ 2 ≤ (1 + 5 * u) * (1 - u) := by
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]

/-- Backlund p. 365 display 67, the upper normalizer bound.
CONDITIONAL ON gamma_relative. All sine and logarithm estimates are proved. -/
theorem normalizer_relative_upper (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (ht : 50 ≤ t) :
    ‖normalizer ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * π)) ^ ((σ - 1) / 2) / Real.log t * (1 + 4 / t ^ 2) := by
  let G := Real.sqrt (2 * π) * (t / 2) ^ ((σ - 1) / 2) * Real.exp (-π * t / 4)
  let S := Real.exp (π * t / 4) / Real.sqrt 2
  let u := 1 / t ^ 2
  have htpos : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 / 2500 := by
    dsimp [u]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2500)
    nlinarith
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hg := (gamma_relative σ t hσ ht).2
  have hs := (sine_relative σ t hσ ht).2
  have hl := (logarithm_relative σ t hσ ht).1
  change _ ≤ G * (1 + u) at hg
  change _ ≤ S * (1 + u) at hs
  have hpi : ‖(π : ℂ) ^ (-((σ : ℂ) + t * I) / 2)‖ = π ^ (-σ / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hp : 0 ≤ π ^ (-σ / 2) := Real.rpow_nonneg Real.pi_pos.le _
  have hnum := mul_le_mul_of_nonneg_left
    (mul_le_mul hg hs (norm_nonneg _) (mul_nonneg hG (by linarith))) hp
  have hdiv := div_le_div₀ (mul_nonneg hp
    (mul_nonneg (mul_nonneg hG (by linarith)) (mul_nonneg hS (by linarith))))
    hnum hlog hl
  have hscale : π ^ (-σ / 2) * G * S = (t / (2 * π)) ^ ((σ - 1) / 2) :=
    leading_factors σ t htpos
  have hbound : ‖normalizer ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * π)) ^ ((σ - 1) / 2) / Real.log t * (1 + u) ^ 2 := by
    rw [normalizer, norm_div, norm_mul, norm_mul, hpi]
    convert hdiv using 1
    · ring
    · rw [← hscale]; ring
  have herr := mul_le_mul_of_nonneg_left (upper_error_budget u hu0 hu1)
    (show 0 ≤ (t / (2 * π)) ^ ((σ - 1) / 2) / Real.log t by positivity)
  convert hbound.trans herr using 1 <;> dsimp [u] <;> ring

/-- Backlund p. 366 display 70, separating the completed product and elementary ratio. -/
theorem normalized_product (σ t : ℝ) :
    ‖normalizer ((σ : ℂ) + t * I) * riemannZeta ((σ : ℂ) + t * I)‖ =
      ‖Complex.Gammaℝ ((σ : ℂ) + t * I) * riemannZeta ((σ : ℂ) + t * I)‖ *
        (‖Complex.sqrt (Complex.sin (π * ((σ : ℂ) + t * I) / 2))‖ /
          ‖Complex.log (-((σ : ℂ) + t * I) * I)‖) := by
  rw [normalizer, norm_mul, norm_div, norm_mul, norm_mul, norm_mul, Complex.Gammaℝ_def,
    norm_mul]
  ring

/-- Backlund p. 366 displays 70 and 71, reflected elementary ratio bound.
No Gamma or zeta estimate is assumed. -/
theorem sine_log_reflection (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    (‖Complex.sqrt (Complex.sin (π * (((1 - σ : ℝ) : ℂ) + t * I) / 2))‖ /
      ‖Complex.log (-(((1 - σ : ℝ) : ℂ) + t * I) * I)‖) ≤
      (1 + 5 / t ^ 2) *
        (‖Complex.sqrt (Complex.sin (π * ((σ : ℂ) + t * I) / 2))‖ /
          ‖Complex.log (-((σ : ℂ) + t * I) * I)‖) := by
  let S := Real.exp (π * t / 4) / Real.sqrt 2
  let u := 1 / t ^ 2
  let L := Real.log t
  have htpos : 0 < t := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 / 2500 := by
    dsimp [u]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2500)
    nlinarith
  have hσr : 1 - σ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hsr := (sine_relative (1 - σ) t hσr ht).2
  have hss := (sine_relative σ t hσ ht).1
  have hlr := (logarithm_relative (1 - σ) t hσr ht).1
  have hls := logarithm_relative σ t hσ ht
  change _ ≤ S * (1 + u) at hsr
  change S * (1 - u) ≤ _ at hss
  have hupp := div_le_div₀ (mul_nonneg hS (by linarith)) hsr hL hlr
  have hlo := div_le_div₀ (norm_nonneg _) hss (hL.trans_le hls.1) hls.2
  have hbudget : S * (1 + u) / L ≤ (1 + 5 * u) * (S * (1 - u) / (L * (1 + u))) := by
    rw [div_le_iff₀ hL]
    have hLne : L ≠ 0 := hL.ne'
    have hune : 1 + u ≠ 0 := by positivity
    have h := mul_le_mul_of_nonneg_left (reflection_budget u hu0 hu1) hS
    field_simp
    nlinarith [h]
  have hscale := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 1 + 5 * u by positivity)
  convert hupp.trans (hbudget.trans hscale) using 1 <;> dsimp [u, L] <;> ring

/-- Backlund p. 366 displays 70 and 71, normalized reflection bound.
This theorem has no Stirling input. -/
theorem normalized_reflection (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖normalizer (((1 - σ : ℝ) : ℂ) + t * I) *
      riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ ≤
    (1 + 5 / t ^ 2) * ‖normalizer ((σ : ℂ) + t * I) *
      riemannZeta ((σ : ℂ) + t * I)‖ := by
  rw [normalized_product, normalized_product, completed_norm_reflection σ t (by linarith)]
  have h := mul_le_mul_of_nonneg_left (sine_log_reflection σ t hσ ht)
    (norm_nonneg (Complex.Gammaℝ ((σ : ℂ) + t * I) * riemannZeta ((σ : ℂ) + t * I)))
  convert h using 1 <;> ring

/-- Backlund pp. 366 and 367 display 73, normalized right half of the bottom.
CONDITIONAL ON gamma_relative and the explicit half-edge hypothesis h50. -/
theorem normalized_half_bottom
    (h50 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
        0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50)
    (σ : ℝ) (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    ‖normalizer ((σ : ℂ) + 50 * I) * riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
      0.9964 * (1 + 4 / (50 : ℝ) ^ 2) := by
  have hσ0 : σ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  have hN := normalizer_relative_upper σ 50 hσ0 (by norm_num)
  have hZ := h50 σ hσ
  have hl : 0 < Real.log (50 : ℝ) := Real.log_pos (by norm_num)
  have hb : 0 < (25 : ℝ) / π := by positivity
  have hbase : (50 : ℝ) / (2 * π) = 25 / π := by ring
  rw [hbase] at hN
  have hpow : ((25 : ℝ) / π) ^ ((σ - 1) / 2) * ((25 : ℝ) / π) ^ ((1 - σ) / 2) = 1 := by
    rw [← Real.rpow_add hb]
    convert Real.rpow_zero ((25 : ℝ) / π) using 1 <;> congr 1 <;> ring
  rw [norm_mul]
  have h := mul_le_mul hN hZ (norm_nonneg _) (by positivity)
  refine h.trans_eq ?_
  field_simp
  nlinarith [hpow]

/-- Backlund pp. 366 and 367 displays 71 and 73, the exact bottom-edge assembly.
CONDITIONAL ON gamma_relative and h50. No admission occurs in this proof. -/
theorem normalized_bottom_boundary
    (h50 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
        0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50)
    (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizer ((σ : ℂ) + 50 * I) * riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 1 := by
  by_cases hh : 1 / 2 ≤ σ
  · have h := normalized_half_bottom h50 σ ⟨hh, hσ.2⟩
    norm_num at h ⊢
    linarith
  · have hr : 1 - σ ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith [hσ.1]⟩
    have hr0 : 1 - σ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hσ.2], hr.2⟩
    have hreflection := normalized_reflection (1 - σ) 50 hr0 (by norm_num)
    rw [show 1 - (1 - σ) = σ by ring] at hreflection
    have hhalf := normalized_half_bottom h50 (1 - σ) hr
    have h := hreflection.trans (mul_le_mul_of_nonneg_left hhalf
      (by norm_num : (0 : ℝ) ≤ 1 + 5 / 50 ^ 2))
    exact h.trans (by norm_num)

/-- Backlund pp. 367 and 368 display 73, the actual half-edge input.
Reuse the existing finite H enclosure and the proved higher-order K estimate.
The sealed gamma74_upper and euler10_identity declarations are not changed. -/
theorem half_edge_fifty (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤
      0.9964 * ((25 : ℝ) / π) ^ ((1 - σ) / 2) * Real.log 50 := by
  obtain ⟨hr, hi⟩ := Decomp537a.boundaryH_components σ hσ
  have hh := Decomp537a.norm_of_boundary_components (Decomp537a.boundaryH σ) hr hi
  have hk := Decomp563d.boundaryK σ hσ
  change ‖riemannZeta ((σ : ℂ) + 50 * I) - Decomp537a.boundaryH σ‖ ≤ 0.281 at hk
  have htri := norm_add_le (Decomp537a.boundaryH σ)
    (riemannZeta ((σ : ℂ) + 50 * I) - Decomp537a.boundaryH σ)
  rw [add_sub_cancel] at htri
  have hsmall : ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 2.243 := by linarith
  exact hsmall.trans (Decomp537a.boundary73_budget σ hσ)

/-- Backlund pp. 366 through 368, the bottom edge with its actual half-edge supplied.
CONDITIONAL ON real_stirling_identity only. -/
theorem normalized_bottom (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizer ((σ : ℂ) + 50 * I) * riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 1 := by
  exact normalized_bottom_boundary half_edge_fifty σ hσ

end LeanLab.RamareSaouter2003.Decomp579b

#print axioms LeanLab.RamareSaouter2003.Decomp579b.completed_product
#print axioms LeanLab.RamareSaouter2003.Decomp579b.completed_norm_reflection
#print axioms LeanLab.RamareSaouter2003.Decomp579b.reflection_budget

#print axioms LeanLab.RamareSaouter2003.Decomp579b.normalizer_relative_upper
#print axioms LeanLab.RamareSaouter2003.Decomp579b.normalized_product
#print axioms LeanLab.RamareSaouter2003.Decomp579b.sine_log_reflection
#print axioms LeanLab.RamareSaouter2003.Decomp579b.normalized_reflection
#print axioms LeanLab.RamareSaouter2003.Decomp579b.normalized_half_bottom
#print axioms LeanLab.RamareSaouter2003.Decomp579b.normalized_bottom_boundary

#print axioms LeanLab.RamareSaouter2003.Decomp579b.half_edge_fifty
#print axioms LeanLab.RamareSaouter2003.Decomp579b.normalized_bottom
