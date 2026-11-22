import LeanLab.HelfgottMajor.Continuation457

/-!
Preparation 1121, the public decay of the Gaussian Mellin transform on the strip
`1/2 ≤ Re s ≤ 5/2`: quadratic decay in the imaginary part, by two integrations by parts.

This is the public port of the private `pcsB_mellin_decay_strip` of
`SPLIT_principal_contour_identity`, which has exactly the statement proved here.
The recurrence used is the shifted Gaussian Mellin recurrence, which is one integration
by parts; applying it at `s`, `s+1` and `s+2` and inserting the uniform line bound on
`1/2 ≤ Re ≤ 13/2` gains the second power.

Degenerate values.  The constant is the integral of a positive function over the open
positive half line, so it is nonnegative, and the statement holds at `δ = 0`, where the
transform is the plain Gaussian.  At `t = 0` the bound reads `‖gaussianMellin δ σ‖ ≤ K`,
which is the uniform line bound.  Every recurrence is applied at a point of real part at
least `1/2`, so no exponent vanishes; the only inversion in the proof is the positive
denominator `1 + t^2`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DCtDecay

open MeasureTheory Real
open LeanLab.HelfgottMajor.Decomp269a
open LeanLab.HelfgottArcs

/-- The imaginary part is dominated by the modulus of any nonnegative real shift. -/
private theorem abs_im_le_norm_add_nat (s : ℂ) (k : ℕ) : |s.im| ≤ ‖s + (k : ℂ)‖ := by
  have him : (s + (k : ℂ)).im = s.im := by simp
  have hsq : ‖s + (k : ℂ)‖ ^ 2 = (s + (k : ℂ)).re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
    ring
  have h1 : s.im ^ 2 ≤ ‖s + (k : ℂ)‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (s + (k : ℂ)).re]
  have h2 : |s.im| ^ 2 ≤ ‖s + (k : ℂ)‖ ^ 2 := by
    rwa [sq_abs]
  simpa using (sq_le_sq.mp h2)

/-- A constant bound for the Gaussian Mellin transform on the wide strip of real parts
`[1/2, 13/2]`, uniform in the imaginary part. -/
private theorem line_const_uniform (δ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 13 / 2 →
      ‖gaussianMellin δ s‖ ≤ B := by
  have hint1 : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := -(1 / 2 : ℝ)) (by norm_num)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
  have hint2 : IntegrableOn (fun x : ℝ => x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (11 / 2 : ℝ)) (by linarith)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
  set g : ℝ → ℝ := fun x =>
    x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) +
      x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2) with hg
  have hsum : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    rw [hg]
    exact hint1.add hint2
  refine ⟨∫ x in Set.Ioi (0 : ℝ), g x, setIntegral_nonneg measurableSet_Ioi ?_, ?_⟩
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have h2 : (0 : ℝ) ≤ x ^ (11 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have h3 : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
    have h4 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) := mul_nonneg h1 h3.le
    have h5 : (0 : ℝ) ≤ x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2) := mul_nonneg h2 h3.le
    rw [hg]
    linarith
  · intro s hs1 hs2
    refine (Gaussian269.mellin_norm_le δ s).trans ?_
    have hint : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * Real.exp (-x ^ 2 / 2))
        (Set.Ioi (0 : ℝ)) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
        (s := s.re - 1) (by linarith)
      refine h.congr_fun ?_ measurableSet_Ioi
      intro x _
      simp only [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
    refine setIntegral_mono_on hint hsum measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hlo : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hhi : (0 : ℝ) ≤ x ^ (11 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have hexp : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
    have hkey : x ^ (s.re - 1) ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (11 / 2 : ℝ) := by
      rcases le_or_gt x 1 with h1 | h1
      · have hle : x ^ (s.re - 1) ≤ x ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 h1 (by linarith)
        linarith
      · have hle : x ^ (s.re - 1) ≤ x ^ (11 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
        linarith
    have hfac : x ^ (s.re - 1) * Real.exp (-x ^ 2 / 2) ≤
        (x ^ (-(1 / 2 : ℝ)) + x ^ (11 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hkey hexp.le
    rw [hg]
    calc x ^ (s.re - 1) * Real.exp (-x ^ 2 / 2)
        ≤ (x ^ (-(1 / 2 : ℝ)) + x ^ (11 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) := hfac
      _ = x ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / 2) +
          x ^ (11 / 2 : ℝ) * Real.exp (-x ^ 2 / 2) := by ring

/-- One integration by parts in norms: the recurrence at a point of positive real part
bounds the transform by the two shifted values. -/
private theorem recurrence_norm (δ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    ‖gaussianMellin δ s‖ * ‖s‖ ≤
      ‖gaussianMellin δ (s + 2)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖gaussianMellin δ (s + 1)‖ := by
  have h := Continuation457.gaussian_mellin_recurrence δ s hs
  have he : ‖gaussianMellin δ s‖ * ‖s‖ = ‖s * gaussianMellin δ s‖ := by
    rw [norm_mul, mul_comm]
  rw [he, h]
  calc ‖gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖
      ≤ ‖gaussianMellin δ (s + 2)‖ +
        ‖(2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)‖ := norm_sub_le _ _
    _ = ‖gaussianMellin δ (s + 2)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ * ‖gaussianMellin δ (s + 1)‖ := by rw [norm_mul]

/-- Two integrations by parts on the strip: the transform times the modulus times the
imaginary part is at most the uniform constant. -/
private theorem decay_step (δ : ℝ) {B c : ℝ}
    (hB : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 13 / 2 → ‖gaussianMellin δ z‖ ≤ B)
    (hc : c = ‖(2 * π * Complex.I * δ : ℂ)‖) {s : ℂ}
    (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 5 / 2) :
    ‖gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤ (B + c * B) * (1 + c) := by
  have hs0 : 0 < s.re := by linarith
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; exact norm_nonneg _
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB s hs1 (by linarith))
  have hshift : ∀ k : ℕ, k ≤ 4 → ‖gaussianMellin δ (s + (k : ℂ))‖ ≤ B := by
    intro k hk
    refine hB _ ?_ ?_
    · have hr : (s + (k : ℂ)).re = s.re + (k : ℝ) := by simp
      rw [hr]; linarith
    · have hr : (s + (k : ℂ)).re = s.re + (k : ℝ) := by simp
      have hk4 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
      rw [hr]; linarith
  have h1 : ‖gaussianMellin δ (s + 1)‖ ≤ B := by simpa using hshift 1 (by norm_num)
  have h2 : ‖gaussianMellin δ (s + 2)‖ ≤ B := by simpa using hshift 2 (by norm_num)
  have h3 : ‖gaussianMellin δ (s + 3)‖ ≤ B := by simpa using hshift 3 (by norm_num)
  have h4 : ‖gaussianMellin δ (s + 4)‖ ≤ B := by simpa using hshift 4 (by norm_num)
  have e31 : (s + 1) + 2 = s + 3 := by ring
  have e21 : (s + 1) + 1 = s + 2 := by ring
  have e42 : (s + 2) + 2 = s + 4 := by ring
  have e32 : (s + 2) + 1 = s + 3 := by ring
  have hr1 : (0 : ℝ) < (s + 1).re := by
    have hh : (s + 1).re = s.re + 1 := by simp
    linarith
  have hr2 : (0 : ℝ) < (s + 2).re := by
    have hh : (s + 2).re = s.re + 2 := by simp
    linarith
  -- the recurrence at `s+1` and at `s+2`, with the shifts normalised
  have r1 : ‖gaussianMellin δ (s + 1)‖ * ‖s + 1‖ ≤
      ‖gaussianMellin δ (s + 3)‖ + c * ‖gaussianMellin δ (s + 2)‖ := by
    have h := recurrence_norm δ (s := s + 1) hr1
    rw [← hc] at h
    rwa [e31, e21] at h
  have r2 : ‖gaussianMellin δ (s + 2)‖ * ‖s + 2‖ ≤
      ‖gaussianMellin δ (s + 4)‖ + c * ‖gaussianMellin δ (s + 3)‖ := by
    have h := recurrence_norm δ (s := s + 2) hr2
    rw [← hc] at h
    rwa [e42, e32] at h
  have n1 : ‖gaussianMellin δ (s + 1)‖ * |s.im| ≤ B + c * B := by
    have him : |s.im| ≤ ‖s + 1‖ := by simpa using abs_im_le_norm_add_nat s 1
    have hb : ‖gaussianMellin δ (s + 1)‖ * ‖s + 1‖ ≤ B + c * B := by
      linarith [r1, mul_le_mul_of_nonneg_left h2 hc0]
    exact (mul_le_mul_of_nonneg_left him (norm_nonneg _)).trans hb
  have n2 : ‖gaussianMellin δ (s + 2)‖ * |s.im| ≤ B + c * B := by
    have him : |s.im| ≤ ‖s + 2‖ := by simpa using abs_im_le_norm_add_nat s 2
    have hb : ‖gaussianMellin δ (s + 2)‖ * ‖s + 2‖ ≤ B + c * B := by
      linarith [r2, mul_le_mul_of_nonneg_left h3 hc0]
    exact (mul_le_mul_of_nonneg_left him (norm_nonneg _)).trans hb
  -- the recurrence at `s`, multiplied through by the imaginary part
  have r0 : ‖gaussianMellin δ s‖ * ‖s‖ ≤
      ‖gaussianMellin δ (s + 2)‖ + c * ‖gaussianMellin δ (s + 1)‖ := by
    have h := recurrence_norm δ (s := s) hs0
    rw [← hc] at h
    exact h
  have hmul : ‖gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤
      ‖gaussianMellin δ (s + 2)‖ * |s.im| + c * (‖gaussianMellin δ (s + 1)‖ * |s.im|) := by
    have h := mul_le_mul_of_nonneg_right r0 (abs_nonneg s.im)
    calc ‖gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤
        (‖gaussianMellin δ (s + 2)‖ + c * ‖gaussianMellin δ (s + 1)‖) * |s.im| := h
      _ = ‖gaussianMellin δ (s + 2)‖ * |s.im| +
          c * (‖gaussianMellin δ (s + 1)‖ * |s.im|) := by ring
  have hY : (0 : ℝ) ≤ B + c * B := by nlinarith
  calc ‖gaussianMellin δ s‖ * ‖s‖ * |s.im|
      ≤ (B + c * B) + c * (B + c * B) := by
        linarith [hmul, n2, mul_le_mul_of_nonneg_left n1 hc0]
    _ = (B + c * B) * (1 + c) := by ring

/-- Quadratic decay of the Gaussian Mellin transform to the right of the critical line,
uniform on `1/2 ≤ Re s ≤ 5/2`, by two integrations by parts. -/
theorem gaussianMellin_decay_right (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 5 / 2 → ∀ t : ℝ,
      ‖gaussianMellin δ ((σ : ℂ) + t * Complex.I)‖ ≤ K / (1 + t ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := line_const_uniform δ
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; exact norm_nonneg _
  have hY : (0 : ℝ) ≤ (B + c * B) * (1 + c) := by
    have : (0 : ℝ) ≤ B + c * B := by nlinarith
    have : (0 : ℝ) ≤ 1 + c := by linarith
    exact mul_nonneg ‹(0 : ℝ) ≤ B + c * B› ‹(0 : ℝ) ≤ 1 + c›
  refine ⟨2 * ((B + c * B) * (1 + c)) + 2 * B + 1, by linarith, ?_⟩
  intro σ hσ1 hσ2 t
  set s : ℂ := (σ : ℂ) + t * Complex.I with hsdef
  have hsr : s.re = σ := by rw [hsdef]; simp
  have hsi : s.im = t := by rw [hsdef]; simp
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)]
  by_cases ht : 1 ≤ |t|
  · have hstep : ‖gaussianMellin δ s‖ * ‖s‖ * |s.im| ≤ (B + c * B) * (1 + c) :=
      decay_step δ hB hc (s := s) (by rw [hsr]; exact hσ1) (by rw [hsr]; exact hσ2)
    have ht2 : (1 : ℝ) ≤ t ^ 2 := by
      have hs := sq_abs t
      nlinarith [abs_nonneg t]
    have hnorm : ‖gaussianMellin δ s‖ * t ^ 2 ≤ (B + c * B) * (1 + c) := by
      have hle : t ^ 2 ≤ ‖s‖ * |s.im| := by
        have h1 : |s.im| ≤ ‖s‖ := by simpa using abs_im_le_norm_add_nat s 0
        have hsq : t ^ 2 = |s.im| ^ 2 := by rw [← hsi, ← sq_abs]
        rw [hsq, sq]
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg s.im)
      calc ‖gaussianMellin δ s‖ * t ^ 2
          ≤ ‖gaussianMellin δ s‖ * (‖s‖ * |s.im|) :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = ‖gaussianMellin δ s‖ * ‖s‖ * |s.im| := by ring
        _ ≤ (B + c * B) * (1 + c) := hstep
    have h2le : 1 + t ^ 2 ≤ 2 * t ^ 2 := by linarith
    calc ‖gaussianMellin δ s‖ * (1 + t ^ 2)
        ≤ ‖gaussianMellin δ s‖ * (2 * t ^ 2) :=
          mul_le_mul_of_nonneg_left h2le (norm_nonneg _)
      _ = 2 * (‖gaussianMellin δ s‖ * t ^ 2) := by ring
      _ ≤ 2 * ((B + c * B) * (1 + c)) := by linarith
      _ ≤ 2 * ((B + c * B) * (1 + c)) + 2 * B + 1 := by linarith
  · have ht1 : |t| < 1 := lt_of_not_ge ht
    have ht2 : t ^ 2 < 1 := by
      have hs := sq_abs t
      nlinarith [abs_nonneg t]
    have hBs : ‖gaussianMellin δ s‖ ≤ B := by
      refine hB s ?_ ?_
      · rw [hsr]; linarith
      · rw [hsr]; linarith
    have hfac : 1 + t ^ 2 ≤ 2 := by linarith
    calc ‖gaussianMellin δ s‖ * (1 + t ^ 2)
        ≤ B * (1 + t ^ 2) := mul_le_mul_of_nonneg_right hBs (by positivity)
      _ ≤ B * 2 := by nlinarith
      _ ≤ 2 * ((B + c * B) * (1 + c)) + 2 * B + 1 := by linarith

end LeanLab.HelfgottMajor.Prep1121DCtDecay
