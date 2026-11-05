import LeanLab.LPZ2007.Statements

/-!
Jutila 1977 page 51, Lemma 7, the finite weighted Halasz inequality.
The arithmetic pseudcharacter estimates and integrations remain separate.
Mathlib supplies the scalar Cauchy Schwarz inequality.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Halasz373

open Finset Complex

/-- Jutila 1977 page 51, Lemma 7, the weighted Cauchy Schwarz step.
The weights are positive on the finite polynomial support. -/
theorem weighted_cauchy {ι : Type*} (s : Finset ι) (a z : ι → ℂ) (b : ι → ℝ)
    (hb : ∀ n ∈ s, 0 < b n) :
    ‖∑ n ∈ s, a n * z n‖ ^ 2 ≤
      (∑ n ∈ s, ‖a n‖ ^ 2 / b n) * (∑ n ∈ s, b n * ‖z n‖ ^ 2) := by
  have hnorm : ‖∑ n ∈ s, a n * z n‖ ≤ ∑ n ∈ s, ‖a n‖ * ‖z n‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun n => a n * z n)
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  have hC := Finset.sum_mul_sq_le_sq_mul_sq s (fun n => ‖a n‖ / Real.sqrt (b n))
    (fun n => Real.sqrt (b n) * ‖z n‖)
  have hleft : (∑ n ∈ s, ‖a n‖ / Real.sqrt (b n) * (Real.sqrt (b n) * ‖z n‖)) =
      ∑ n ∈ s, ‖a n‖ * ‖z n‖ := by
    apply sum_congr rfl
    intro n hn
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hb n hn))]
  have hA : (∑ n ∈ s, (‖a n‖ / Real.sqrt (b n)) ^ 2) =
      ∑ n ∈ s, ‖a n‖ ^ 2 / b n := by
    apply sum_congr rfl
    intro n hn
    rw [div_pow, Real.sq_sqrt (hb n hn).le]
  have hB : (∑ n ∈ s, (Real.sqrt (b n) * ‖z n‖) ^ 2) =
      ∑ n ∈ s, b n * ‖z n‖ ^ 2 := by
    apply sum_congr rfl
    intro n hn
    rw [mul_pow, Real.sq_sqrt (hb n hn).le]
  rw [hleft, hA, hB] at hC
  nlinarith

/-- Jutila 1977 page 51, Lemma 7, in its finite energy form.
Unit phases align the polynomial evaluations before weighted Cauchy Schwarz. -/
theorem finite_halasz {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (z : κ → ι → ℂ) (b : ι → ℝ)
    (hb : ∀ n ∈ s, 0 < b n) :
    ∃ η : κ → ℂ, (∀ j, ‖η j‖ = 1) ∧
      (∑ j ∈ t, ‖∑ n ∈ s, a n * z j n‖) ^ 2 ≤
        (∑ n ∈ s, ‖a n‖ ^ 2 / b n) *
          (∑ n ∈ s, b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2) := by
  classical
  let F : κ → ℂ := fun j => ∑ n ∈ s, a n * z j n
  let η : κ → ℂ := fun j => if F j = 0 then 1 else star (F j) / (‖F j‖ : ℂ)
  have hunit : ∀ j, ‖η j‖ = 1 := by
    intro j
    by_cases h : F j = 0
    · simp [η, h]
    · simp [η, h, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), norm_ne_zero_iff.mpr h]
  have halign : ∀ j, η j * F j = (‖F j‖ : ℂ) := by
    intro j
    by_cases h : F j = 0
    · simp [η, h]
    · dsimp [η]
      rw [if_neg h, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self]
      rw [Complex.normSq_eq_norm_sq]
      have hn : (‖F j‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
      push_cast
      field_simp [hn] <;> ring
  refine ⟨η, hunit, ?_⟩
  have he : (∑ n ∈ s, a n * (∑ j ∈ t, η j * z j n)) =
      ((∑ j ∈ t, ‖F j‖ : ℝ) : ℂ) := by
    calc
      _ = ∑ j ∈ t, η j * F j := by
        simp only [Finset.mul_sum, F]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro j hj
        apply sum_congr rfl
        intro n hn
        ring
      _ = _ := by simp only [halign, Complex.ofReal_sum]
  have h := weighted_cauchy s a (fun n => ∑ j ∈ t, η j * z j n) b hb
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg (fun j hj => norm_nonneg (F j)))] at h
  exact h

/-- Jutila 1977 page 51, Lemma 7, allowing zero weights away from the polynomial support. -/
theorem finite_halasz_nonnegative {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (z : κ → ι → ℂ) (b : ι → ℝ)
    (hb : ∀ n ∈ s, 0 ≤ b n) (hpos : ∀ n ∈ s, a n ≠ 0 → 0 < b n) :
    ∃ η : κ → ℂ, (∀ j, ‖η j‖ = 1) ∧
      (∑ j ∈ t, ‖∑ n ∈ s, a n * z j n‖) ^ 2 ≤
        (∑ n ∈ s, ‖a n‖ ^ 2 / b n) *
          (∑ n ∈ s, b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2) := by
  classical
  let u := s.filter (fun n => a n ≠ 0)
  obtain ⟨η, hη, h⟩ := finite_halasz u t a z b
    (fun n hn => hpos n (mem_filter.mp hn).1 (mem_filter.mp hn).2)
  have hpoly : ∀ j, (∑ n ∈ u, a n * z j n) = ∑ n ∈ s, a n * z j n := by
    intro j
    apply sum_subset (filter_subset _ _)
    intro n hn hnu
    have ha : a n = 0 := by simpa [u, hn] using hnu
    simp [ha]
  have hA : (∑ n ∈ u, ‖a n‖ ^ 2 / b n) = ∑ n ∈ s, ‖a n‖ ^ 2 / b n := by
    apply sum_subset (filter_subset _ _)
    intro n hn hnu
    have ha : a n = 0 := by simpa [u, hn] using hnu
    simp [ha]
  have hB : (∑ n ∈ u, b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2) ≤
      ∑ n ∈ s, b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ => mul_nonneg (hb n hn) (sq_nonneg _))
  simp_rw [hpoly, hA] at h
  exact ⟨η, hη, h.trans (mul_le_mul_of_nonneg_left hB
    (sum_nonneg (fun n hn => div_nonneg (sq_nonneg _) (hb n hn))))⟩

/-- Jutila 1977 page 51, the Gram sum in Lemma 7.
Expanding the finite energy gives the double kernel sum with its phases intact. -/
theorem gram_energy {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (z : κ → ι → ℂ) (b : ι → ℝ) (η : κ → ℂ) :
    (∑ n ∈ s, b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2) =
      (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
        (∑ n ∈ s, (b n : ℂ) * z j n * star (z k n))).re := by
  have hnorm : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
    intro w
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    change star w * w = w * star w
    exact mul_comm _ _
  have he : ((∑ n ∈ s, b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
        (∑ n ∈ s, (b n : ℂ) * z j n * star (z k n)) := by
    simp_rw [Complex.ofReal_sum, Complex.ofReal_mul, hnorm, star_sum, star_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro n hn
    ring
  simpa only [Complex.ofReal_re] using congrArg Complex.re he

/-- Jutila 1977 page 51, Lemma 7, with a finite kernel B.
This is the double sum form used before the arithmetic and integration steps. -/
theorem finite_halasz_gram {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (z : κ → ι → ℂ) (b : ι → ℝ)
    (hb : ∀ n ∈ s, 0 ≤ b n) (hpos : ∀ n ∈ s, a n ≠ 0 → 0 < b n) :
    ∃ η : κ → ℂ, (∀ j, ‖η j‖ = 1) ∧
      (∑ j ∈ t, ‖∑ n ∈ s, a n * z j n‖) ^ 2 ≤
        (∑ n ∈ s, ‖a n‖ ^ 2 / b n) *
          (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
            (∑ n ∈ s, (b n : ℂ) * z j n * star (z k n))).re := by
  obtain ⟨η, hη, h⟩ := finite_halasz_nonnegative s t a z b hb hpos
  exact ⟨η, hη, by simpa only [← gram_energy s t z b η] using h⟩

/-- Jutila 1977 page 51, Lemma 7, with convergent Gram kernels.
The finite polynomial support is retained and the nonnegative energy tail is added.
The Gram orientation agrees with the source after conjugating the phases. -/
theorem halasz_series {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (z : κ → ι → ℂ) (b : ι → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hpos : ∀ n ∈ s, a n ≠ 0 → 0 < b n)
    (hB : ∀ j ∈ t, ∀ k ∈ t, Summable (fun n => (b n : ℂ) * z j n * star (z k n))) :
    ∃ η : κ → ℂ, (∀ j, ‖η j‖ = 1) ∧
      (∑ j ∈ t, ‖∑ n ∈ s, a n * z j n‖) ^ 2 ≤
        (∑ n ∈ s, ‖a n‖ ^ 2 / b n) *
          (∑ j ∈ t, ∑ k ∈ t, η j * star (η k) *
            (∑' n, (b n : ℂ) * z j n * star (z k n))).re := by
  classical
  obtain ⟨η, hη, h⟩ := finite_halasz_nonnegative s t a z b (fun n _ => hb n) hpos
  let v : ι → ℝ := fun n => b n * ‖∑ j ∈ t, η j * z j n‖ ^ 2
  let w : ι → ℂ := fun n => ∑ j ∈ t, ∑ k ∈ t,
    η j * star (η k) * ((b n : ℂ) * z j n * star (z k n))
  have hpoint : ∀ n, (w n).re = v n := by
    intro n
    simpa [w, v] using (gram_energy ({n} : Finset ι) t z b η).symm
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
  exact ⟨η, hη, h.trans (mul_le_mul_of_nonneg_left htail
    (sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (hb n))))⟩

end LeanLab.LPZ2007.Halasz373

#print axioms LeanLab.LPZ2007.Halasz373.weighted_cauchy
#print axioms LeanLab.LPZ2007.Halasz373.finite_halasz

#print axioms LeanLab.LPZ2007.Halasz373.finite_halasz_nonnegative

#print axioms LeanLab.LPZ2007.Halasz373.gram_energy

#print axioms LeanLab.LPZ2007.Halasz373.finite_halasz_gram

#print axioms LeanLab.LPZ2007.Halasz373.halasz_series
