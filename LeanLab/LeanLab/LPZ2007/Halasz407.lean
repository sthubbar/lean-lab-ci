import LeanLab.LPZ2007.Halasz373

/-!
Jutila 1977 page 53, display 3.7, and page 54.
DOI https://doi.org/10.7146/math.scand.a-11701.
The coefficients in display 3.7 are arbitrary complex numbers.
This version retains their magnitudes for the later totient normalization.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Halasz407

open Finset Complex

/-- Jutila 1977 page 53, display 3.7, for a finite Gram kernel.
The evaluation vectors include the character dependent pseudcharacter factor.
The outer coefficients have no unit norm restriction. -/
theorem finite_arbitrary_coefficients {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (z : κ → ι → ℂ) (b : ι → ℝ) (η : κ → ℂ)
    (hb : ∀ n ∈ s, 0 ≤ b n) (hpos : ∀ n ∈ s, a n ≠ 0 → 0 < b n) :
    ‖∑ j ∈ t, η j * (∑ n ∈ s, a n * z j n)‖ ^ 2 ≤
      (∑ n ∈ s, ‖a n‖ ^ 2 / b n) *
        (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
          (∑ n ∈ s, (b n : ℂ) * z j n * star (z k n))).re := by
  classical
  let v : ι → ℂ := fun n => ∑ j ∈ t, η j * z j n
  obtain ⟨ν, hν, h⟩ := Halasz373.finite_halasz_nonnegative s ({()} : Finset Unit)
    a (fun _ n => v n) b hb hpos
  have hn := hν ()
  simp only [sum_singleton, norm_mul, hn, one_mul] at h
  have he : (∑ j ∈ t, η j * (∑ n ∈ s, a n * z j n)) = ∑ n ∈ s, a n * v n := by
    simp only [v, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact h.trans_eq (congrArg (fun x : ℝ => (∑ n ∈ s, ‖a n‖ ^ 2 / b n) * x)
    (Halasz373.gram_energy s t z b η))

/-- Jutila 1977 page 53, display 3.7, with convergent kernels.
Arbitrary coefficients retain the modulus dependent magnitudes from page 54.
The Gram sum agrees with the source after swapping its two outer indices. -/
theorem series_arbitrary_coefficients {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (z : κ → ι → ℂ) (b : ι → ℝ) (η : κ → ℂ)
    (hb : ∀ n, 0 ≤ b n) (hpos : ∀ n ∈ s, a n ≠ 0 → 0 < b n)
    (hB : ∀ j ∈ t, ∀ k ∈ t, Summable (fun n => (b n : ℂ) * z j n * star (z k n))) :
    ‖∑ j ∈ t, η j * (∑ n ∈ s, a n * z j n)‖ ^ 2 ≤
      (∑ n ∈ s, ‖a n‖ ^ 2 / b n) *
        (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
          (∑' n, (b n : ℂ) * z j n * star (z k n))).re := by
  classical
  let v : ι → ℝ := fun n => b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2
  let w : ι → ℂ := fun n => ∑ j ∈ t, ∑ k ∈ t,
    η j * star (η k) * ((b n : ℂ) * z j n * star (z k n))
  have hpoint : ∀ n, (w n).re = v n := by
    intro n
    simpa [w, v] using (Halasz373.gram_energy ({n} : Finset ι) t z b η).symm
  have hsum : HasSum w (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
      (∑' n, (b n : ℂ) * z j n * star (z k n))) := by
    exact hasSum_sum (fun j hj => hasSum_sum (fun k hk =>
      (hB j hj k hk).hasSum.mul_left (η j * star (η k))))
  have hv : Summable v := (Complex.reCLM.summable hsum.summable).congr hpoint
  have htotal : (∑' n, v n) = (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
      (∑' n, (b n : ℂ) * z j n * star (z k n))).re := by
    calc
      _ = ∑' n, (w n).re := tsum_congr (fun n => (hpoint n).symm)
      _ = (∑' n, w n).re := (Complex.re_tsum hsum.summable).symm
      _ = _ := by rw [hsum.tsum_eq]
  have htail : (∑ n ∈ s, v n) ≤ ∑' n, v n :=
    hv.sum_le_tsum s (fun n _ => mul_nonneg (hb n) (sq_nonneg _))
  rw [htotal] at htail
  have h := finite_arbitrary_coefficients s t a z b η (fun n _ => hb n) hpos
  rw [← Halasz373.gram_energy s t z b η] at h
  exact h.trans (mul_le_mul_of_nonneg_left htail
    (sum_nonneg (fun n hn => div_nonneg (sq_nonneg _) (hb n))))

/-- Jutila 1977 page 54, the choice of coefficient magnitudes in display 3.7.
Every nonnegative prescribed magnitude is allowed, including q over phi of q.
Mathlib supplies unit phases even when an evaluation is zero. -/
theorem weighted_norms_series {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (z : κ → ι → ℂ) (b : ι → ℝ) (w : κ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hpos : ∀ n ∈ s, a n ≠ 0 → 0 < b n)
    (hw : ∀ j, 0 ≤ w j)
    (hB : ∀ j ∈ t, ∀ k ∈ t, Summable (fun n => (b n : ℂ) * z j n * star (z k n))) :
    ∃ η : κ → ℂ, (∀ j, ‖η j‖ = w j) ∧
      (∑ j ∈ t, w j * ‖∑ n ∈ s, a n * z j n‖) ^ 2 ≤
        (∑ n ∈ s, ‖a n‖ ^ 2 / b n) *
          (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
            (∑' n, (b n : ℂ) * z j n * star (z k n))).re := by
  classical
  let F : κ → ℂ := fun j => ∑ n ∈ s, a n * z j n
  choose c hc hcF using (fun j => Complex.exists_norm_mul_eq_self (F j))
  let η : κ → ℂ := fun j => (w j : ℂ) * star (c j)
  have hη : ∀ j, ‖η j‖ = w j := by
    intro j
    simp only [η, norm_mul, norm_star, hc, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hw j)]
  have halign : ∀ j, η j * F j = ((w j * ‖F j‖ : ℝ) : ℂ) := by
    intro j
    have hcc : star (c j) * c j = 1 := by
      change (starRingEnd ℂ) (c j) * c j = 1
      rw [Complex.conj_mul', hc]
      norm_num
    calc
      η j * F j = (w j : ℂ) * ((star (c j) * c j) * (‖F j‖ : ℂ)) := by
        dsimp only [η]
        nth_rw 1 [← hcF j]
        ring
      _ = _ := by rw [hcc]; simp
  have he : (∑ j ∈ t, η j * (∑ n ∈ s, a n * z j n)) =
      ((∑ j ∈ t, w j * ‖F j‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact sum_congr rfl (fun j hj => halign j)
  have h := series_arbitrary_coefficients s t a z b η hb hpos hB
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg (fun j hj => mul_nonneg (hw j) (norm_nonneg _)))] at h
  exact ⟨η, hη, h⟩

end LeanLab.LPZ2007.Halasz407

#print axioms LeanLab.LPZ2007.Halasz407.finite_arbitrary_coefficients
#print axioms LeanLab.LPZ2007.Halasz407.series_arbitrary_coefficients

#print axioms LeanLab.LPZ2007.Halasz407.weighted_norms_series
