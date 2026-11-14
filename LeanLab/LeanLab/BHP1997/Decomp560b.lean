/-
An auxiliary polynomial Gamma bound for P0069 page 22 Lemma 8.
This bound has an explicit extra constant. It does not replace the exact sealed comparison.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp560a
import Mathlib

namespace LeanLab.BHP1997.Decomp560b
open Complex Set Filter Asymptotics
open scoped Topology
open LeanLab.BHP1997.Decomp560a

/-- Rademacher page 195 display 3.4 with constant edge weights on the half-unit strip.
CONDITIONAL ON the explicit growth and boundary premises. -/
theorem exponential_three_lines {f : ℂ → ℂ} {C B a b : ℝ}
    (hf : DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hC : 0 < C) (hB : 0 < B) (ha : 0 < a) (hb : 0 < b)
    (hg : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖f s‖ ≤ C * Real.exp (B * |s.im|))
    (hl : ∀ s : ℂ, s.re = -(1 / 2 : ℝ) → ‖f s‖ ≤ a)
    (hr : ∀ s : ℂ, s.re = 1 / 2 → ‖f s‖ ≤ b)
    {s : ℂ} (hsl : -(1 / 2 : ℝ) ≤ s.re) (hsu : s.re ≤ 1 / 2) :
    ‖f s‖ ≤ a ^ (1 / 2 - s.re) * b ^ (s.re + 1 / 2) := by
  let E : ℂ → ℝ := fun z => (z.re - 1 / 2) * Real.log a + (-1 / 2 - z.re) * Real.log b
  let F : ℂ → ℂ := fun z => f z * Complex.exp
    ((z - 1 / 2) * (Real.log a : ℂ) + (-1 / 2 - z) * (Real.log b : ℂ))
  have hn (z : ℂ) : ‖F z‖ = ‖f z‖ * Real.exp (E z) := by
    dsimp [F, E]
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  have hE (z : ℂ) (hzl : -(1 / 2 : ℝ) ≤ z.re) (hzu : z.re ≤ 1 / 2) :
      E z ≤ |Real.log a| + |Real.log b| := by
    have h1 : (z.re - 1 / 2) * Real.log a ≤ |Real.log a| := by
      calc
        _ ≤ |(z.re - 1 / 2) * Real.log a| := le_abs_self _
        _ = |z.re - 1 / 2| * |Real.log a| := abs_mul _ _
        _ ≤ 1 * |Real.log a| := by gcongr; exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = _ := one_mul _
    have h2 : (-1 / 2 - z.re) * Real.log b ≤ |Real.log b| := by
      calc
        _ ≤ |(-1 / 2 - z.re) * Real.log b| := le_abs_self _
        _ = |-1 / 2 - z.re| * |Real.log b| := abs_mul _ _
        _ ≤ 1 * |Real.log b| := by gcongr; exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = _ := one_mul _
    dsimp [E]
    linarith
  have hFd : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    have he : Differentiable ℂ (fun z : ℂ => Complex.exp
        ((z - 1 / 2) * (Real.log a : ℂ) + (-1 / 2 - z) * (Real.log b : ℂ))) := by fun_prop
    simpa only [F, smul_eq_mul] using hf.smul he.diffContOnCl
  have hFg (z : ℂ) (hzl : -(1 / 2 : ℝ) ≤ z.re) (hzu : z.re ≤ 1 / 2) :
      ‖F z‖ ≤ (C * Real.exp (|Real.log a| + |Real.log b|)) * Real.exp (B * |z.im|) := by
    rw [hn]
    calc
      _ ≤ (C * Real.exp (B * |z.im|)) * Real.exp (|Real.log a| + |Real.log b|) :=
        mul_le_mul (hg z hzl hzu) (Real.exp_le_exp.mpr (hE z hzl hzu)) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hFl (z : ℂ) (hz : z.re = -(1 / 2 : ℝ)) : ‖F z‖ ≤ 1 := by
    have he : E z = -Real.log a := by dsimp [E]; rw [hz]; ring
    rw [hn, he]
    calc
      _ ≤ a * Real.exp (-Real.log a) := mul_le_mul_of_nonneg_right (hl z hz) (Real.exp_pos _).le
      _ = 1 := by rw [Real.exp_neg, Real.exp_log ha]; exact mul_inv_cancel₀ ha.ne'
  have hFr (z : ℂ) (hz : z.re = 1 / 2) : ‖F z‖ ≤ 1 := by
    have he : E z = -Real.log b := by dsimp [E]; rw [hz]; ring
    rw [hn, he]
    calc
      _ ≤ b * Real.exp (-Real.log b) := mul_le_mul_of_nonneg_right (hr z hz) (Real.exp_pos _).le
      _ = 1 := by rw [Real.exp_neg, Real.exp_log hb]; exact mul_inv_cancel₀ hb.ne'
  have hmax := exponential_strip_maximum hFd (by positivity) hB hFg hFl hFr hsl hsu
  rw [hn] at hmax
  have he : Real.exp (-(E s)) = a ^ (1 / 2 - s.re) * b ^ (s.re + 1 / 2) := by
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
    congr 1
    dsimp [E]
    ring
  calc
    ‖f s‖ ≤ 1 / Real.exp (E s) := (le_div_iff₀ (Real.exp_pos _)).mpr hmax
    _ = _ := by rw [one_div, ← Real.exp_neg, he]

/-- The elementary Gaussian bound used to localize Rademacher page 195 display 3.4. -/
theorem gaussian_linear_decay (u : ℝ) : (|u| + 2) * Real.exp (-(u ^ 2)) ≤ 3 := by
  have h1 : 1 ≤ Real.exp (u ^ 2) := Real.one_le_exp (sq_nonneg u)
  have hu : |u| ≤ Real.exp (u ^ 2) := by
    have he := Real.add_one_le_exp (u ^ 2)
    nlinarith [sq_nonneg (|u| - 1 / 2), sq_abs u]
  have hh := mul_le_mul_of_nonneg_right (by linarith : |u| + 2 ≤ 3 * Real.exp (u ^ 2))
    (Real.exp_pos (-(u ^ 2))).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hh

/-- Gaussian localization norm identity for Rademacher page 195 display 3.4. -/
theorem localized_norm (f : ℂ → ℂ) (t σ : ℝ) (z : ℂ) :
    ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ =
      ‖f (z + t * I)‖ * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [pow_two, Complex.mul_re]

/-- An auxiliary version of Rademacher page 197 display 5.1 with an explicit extra constant.
The height exponent is exact. No harmonic multiplier input is used. -/
theorem gammaRatio_uniform_polynomial {Q : ℝ} (hQ : 0 ≤ Q) {s : ℂ}
    (hsl : -(1 / 2 : ℝ) ≤ s.re) (hsu : s.re ≤ 1 / 2) :
    ‖gammaRatio Q s‖ ≤ (3 * Real.exp 1) * (Q + |s.im| + 2) ^ (1 / 2 - s.re) := by
  obtain ⟨A, B, hA, hB, hg⟩ := gammaRatio_strip_growth hQ
  let σ : ℝ := s.re
  let t : ℝ := s.im
  let K : ℝ := 3 * Real.exp 1
  let P : ℝ := Q + |t| + 2
  let g : ℂ → ℂ := fun z => gammaRatio Q (z + t * I) * Complex.exp ((z - σ) ^ 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hsq (z : ℂ) (hzl : -(1 / 2 : ℝ) ≤ z.re) (hzu : z.re ≤ 1 / 2) :
      (z.re - σ) ^ 2 ≤ 1 := by
    dsimp [σ]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (z.re - s.re))
      (by linarith : 0 ≤ 1 + (z.re - s.re))]
  have hgd : DiffContOnCl ℂ g (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    have ht : DiffContOnCl ℂ (fun z : ℂ => z + t * I)
        (Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
      (differentiable_id.add_const _).diffContOnCl
    have hh := (gammaRatio_diffContOnCl hQ).comp ht (by intro z hz; simpa using hz)
    have he : Differentiable ℂ (fun z : ℂ => Complex.exp ((z - σ) ^ 2)) := by fun_prop
    simpa only [g, Function.comp_def, smul_eq_mul] using hh.smul he.diffContOnCl
  have hgg (z : ℂ) (hzl : -(1 / 2 : ℝ) ≤ z.re) (hzu : z.re ≤ 1 / 2) :
      ‖g z‖ ≤ (A * Real.exp (B * |t| + 1)) * Real.exp (B * |z.im|) := by
    have hh := hg (z + t * I) (by simpa using hzl) (by simpa using hzu)
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at hh
    change ‖gammaRatio Q (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ (A * Real.exp (B * (|z.im| + |t|))) * Real.exp 1 := by
        apply mul_le_mul
        · exact hh.trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_add_le _ _) hB.le)) hA.le)
        · exact Real.exp_le_exp.mpr (by nlinarith [hsq z hzl hzu, sq_nonneg z.im])
        · exact (Real.exp_pos _).le
        · positivity
      _ = _ := by rw [show B * (|z.im| + |t|) = B * |z.im| + B * |t| by ring,
        Real.exp_add, Real.exp_add]; ring
  have hgl (z : ℂ) (hz : z.re = -(1 / 2 : ℝ)) : ‖g z‖ ≤ K * P := by
    have hl := gamma_ratio_left_edge hQ (s := z + t * I) (by simpa using hz)
    have hn : ‖(Q : ℂ) + 1 + (z + t * I)‖ / 2 ≤ P * (|z.im| + 2) := by
      have hh := Complex.norm_le_abs_re_add_abs_im ((Q : ℂ) + 1 + (z + t * I))
      simp only [add_re, ofReal_re, one_re, mul_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_zero, add_zero, add_im, one_im, mul_im, zero_mul, zero_add, hz] at hh
      rw [abs_of_nonneg (by linarith : 0 ≤ Q + 1 + -(1 / 2 : ℝ))] at hh
      have ht := abs_add_le z.im t
      dsimp [P]
      nlinarith [abs_nonneg z.im, abs_nonneg t,
        mul_nonneg hQ (abs_nonneg z.im), mul_nonneg (abs_nonneg t) (abs_nonneg z.im)]
    have hdec : (|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) ≤ K := by
      calc
        _ ≤ (|z.im| + 2) * Real.exp (1 - z.im ^ 2) := by
          gcongr
          exact hsq z (by rw [hz]) (by rw [hz]; norm_num)
        _ = Real.exp 1 * ((|z.im| + 2) * Real.exp (-(z.im ^ 2))) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ Real.exp 1 * 3 := mul_le_mul_of_nonneg_left (gaussian_linear_decay z.im) (Real.exp_pos _).le
        _ = K := by dsimp [K]; ring
    change ‖gammaRatio Q (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ (P * (|z.im| + 2)) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) :=
        mul_le_mul_of_nonneg_right (hl.trans hn) (Real.exp_pos _).le
      _ = P * ((|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2)) := by ring
      _ ≤ P * K := mul_le_mul_of_nonneg_left hdec hP.le
      _ = _ := mul_comm _ _
  have hgr (z : ℂ) (hz : z.re = 1 / 2) : ‖g z‖ ≤ K := by
    change ‖gammaRatio Q (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm, gammaRatio, gamma_ratio_right_edge hQ (by simpa using hz), one_mul]
    calc
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr
        (by nlinarith [hsq z (by rw [hz]; norm_num) (by rw [hz]), sq_nonneg z.im])
      _ ≤ K := by dsimp [K]; nlinarith [Real.exp_pos 1]
  have hh := exponential_three_lines hgd (by positivity) hB (mul_pos hK hP) hK hgg hgl hgr
    (s := (σ : ℂ)) (by simpa [σ] using hsl) (by simpa [σ] using hsu)
  simp only [g, sub_self, zero_pow (by norm_num : 2 ≠ 0), Complex.exp_zero, mul_one, ofReal_re] at hh
  have halg : (K * P) ^ (1 / 2 - σ) * K ^ (σ + 1 / 2) = K * P ^ (1 / 2 - σ) := by
    rw [Real.mul_rpow hK.le hP.le]
    calc
      _ = (K ^ (1 / 2 - σ) * K ^ (σ + 1 / 2)) * P ^ (1 / 2 - σ) := by ring
      _ = _ := by rw [← Real.rpow_add hK, show (1 / 2 - σ) + (σ + 1 / 2) = (1 : ℝ) by ring, Real.rpow_one]
  rw [halg] at hh
  simpa [σ, t, K, P, Complex.re_add_im] using hh

/-- An auxiliary left-edge Gamma estimate for the two character parities.
Source Rademacher pages 197 to 199. The explicit constant is six times exp one. -/
theorem gammaRatio_left_uniform {δ Q : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1) (s : ℂ) (hs : s.re = -δ) :
    ‖gammaRatio Q s‖ ≤ (6 * Real.exp 1) * (|s.im| + 2) ^ (1 / 2 + δ) := by
  have hh := gammaRatio_uniform_polynomial hQ
    (s := s) (by rw [hs]; linarith) (by rw [hs]; linarith)
  rw [hs, sub_neg_eq_add] at hh
  have hp : (Q + |s.im| + 2) ^ (1 / 2 + δ) ≤
      2 * (|s.im| + 2) ^ (1 / 2 + δ) := by
    calc
      _ ≤ (2 * (|s.im| + 2)) ^ (1 / 2 + δ) :=
        Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) (by linarith)
      _ = (2 : ℝ) ^ (1 / 2 + δ) * (|s.im| + 2) ^ (1 / 2 + δ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (|s.im| + 2) ^ (1 / 2 + δ) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by linarith)) (by positivity)
  calc
    _ ≤ (3 * Real.exp 1) * (2 * (|s.im| + 2) ^ (1 / 2 + δ)) :=
      hh.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by ring

/-- Rademacher pages 197 to 199, a proved conductor-uniform archimedean quotient bound.
The extra absolute constant is harmless for the left edge of P0069 page 22 Lemma 8.
This supplier does not use the exact constant-one comparison or its harmonic leaf. -/
theorem gamma_quotient_uniform {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ G : ℝ, 0 < G ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (s : ℂ), s.re = -δ →
      ‖χ⁻¹.gammaFactor (1 - s) / χ.gammaFactor s‖ ≤
        G * (|s.im| + 2) ^ (1 / 2 + δ) := by
  refine ⟨6 * Real.exp 1, by positivity, ?_⟩
  intro q _ χ s hs
  have haux (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
      ‖Complex.Gammaℝ ((Q : ℂ) + 1 - s) / Complex.Gammaℝ ((Q : ℂ) + s)‖ ≤
        (6 * Real.exp 1) * (|s.im| + 2) ^ (1 / 2 + δ) := by
    have hr := gammaRatio_left_uniform hδ hδhalf hQ0 hQ1 s hs
    have hpi : Real.pi ^ (-δ - 1 / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, mul_div_mul_comm,
      ← Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    rw [show -((Q : ℂ) + 1 - s) / 2 - (-((Q : ℂ) + s) / 2) = s - 1 / 2 by ring]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    rw [show (s - 1 / 2).re = -δ - 1 / 2 by simp [hs]]
    rw [show ((Q : ℂ) + 1 - s) / 2 = (Q : ℂ) / 2 + (1 - s) / 2 by ring,
      show ((Q : ℂ) + s) / 2 = (Q : ℂ) / 2 + s / 2 by ring]
    simpa only [gammaRatio, one_mul] using
      mul_le_mul hpi hr (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hi : χ⁻¹.Even ↔ χ.Even := by
    simp only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_eq_one]
  by_cases he : χ.Even
  · simpa only [DirichletCharacter.gammaFactor, ite_eq_left he, ite_eq_left (hi.mpr he), ofReal_zero, zero_add]
      using haux 0 (by norm_num) (by norm_num)
  · have hin : ¬χ⁻¹.Even := fun h => he (hi.mp h)
    simp only [DirichletCharacter.gammaFactor, ite_eq_right he, ite_eq_right hin]
    rw [show (1 - s) + 1 = (1 : ℂ) + 1 - s by ring,
      show s + 1 = (1 : ℂ) + s by ring]
    exact haux 1 (by norm_num) (by norm_num)

end LeanLab.BHP1997.Decomp560b
