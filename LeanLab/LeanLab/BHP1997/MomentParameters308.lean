/-
BHP1997, pages 46 and 47. The printed N range supplies the scalar moment parameters.
The Holder identity and M exponent margin reuse the existing Lemma32 results.
The functional moment estimates remain unproved.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Selection308
import LeanLab.BHP1997.Lemma32

namespace LeanLab.BHP1997.Task308

/-- Page 46, the N range before Lemma 32. Its epsilon loss is sufficient
for the denominator perturbation in Lemma 31 display 5.8. -/
theorem reciprocal_gap_le_loss {d ε φ : ℝ} (hd : 2 ≤ d) (hε : 0 ≤ ε)
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) :
    1 / d - ε / (1 - φ) ≤ 1 / (d + 2 * ε) := by
  have hd0 : 0 < d := by linarith
  have hde : 0 < d + 2 * ε := by linarith
  have hφ : 0 < 1 - φ := by linarith
  have hprod : 2 * (1 - φ) ≤ d * (d + 2 * ε) := by
    nlinarith [sq_nonneg (d - 2), mul_nonneg hd0.le hε]
  have hquot : (2 * ε) / (d * (d + 2 * ε)) ≤ ε / (1 - φ) := by
    apply (div_le_div_iff₀ (mul_pos hd0 hde) hφ).2
    nlinarith only [mul_le_mul_of_nonneg_left hprod hε]
  have he : 1 / d - 1 / (d + 2 * ε) = (2 * ε) / (d * (d + 2 * ε)) := by
    field_simp
    <;> ring
  linarith only [he, hquot]

/-- Pages 46 and 47, Lemma 32. For the printed exponent n of N in Y,
choose alpha and h, with a uniform h bound for fixed epsilon.
The selected Holder exponents and M power margin are included.
This is the scalar selection, not a claim of either polynomial moment estimate. -/
theorem lemma32_parameter_selection (j : ℕ) (hj : 4 ≤ j) (φ : ℝ)
    (hφl : 1 / (2 * (j : ℝ) + 2) < φ) (hφu : φ ≤ 1 / (2 * (j : ℝ))) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η → ∀ n : ℝ,
      ε ≤ n → n ≤ φ + (1 - φ) / (2 * (j : ℝ) - 1) - ε →
      ∃ (α : ℝ) (h : ℕ), ε ≤ α ∧ α ≤ 1 ∧ j ≤ h ∧
        (h : ℝ) ≤ 2 * (1 - φ) / ε ∧
        2 / (2 * (h : ℝ) + α) ≤ n / (1 - φ) ∧
        n / (1 - φ) ≤ φ / (1 - φ) + 1 / (2 * (h : ℝ) - 1 + 2 * α) ∧
        1 / (2 * ((h : ℝ) + α)) +
          1 / (2 * ((h : ℝ) + α) / ((h : ℝ) - 1 + α)) = 1/2 ∧
        4 ≤ (2 + 2 * ((h : ℝ) + α) / ((h : ℝ) - 1 + α)) *
          (1 / (1 - φ) - n / (1 - φ)) := by
  have hjR : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hφ0 : 0 < φ := lt_trans (by positivity) hφl
  have hφ1 : φ < 1 := by
    have hh : 1 / (2 * (j : ℝ)) ≤ 1/2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    linarith
  have hφ : 0 < 1 - φ := by linarith
  have hdj : 0 < 2 * (j : ℝ) - 1 := by linarith
  obtain ⟨η, hη, hselect⟩ := lemma31_selection j hj φ hφl hφu
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη n hn hnu
  have hnpos : 0 < n := hε.trans_le hn
  have hlampos : 0 < n / (1 - φ) := div_pos hnpos hφ
  have hgap := reciprocal_gap_le_loss (by linarith : 2 ≤ 2 * (j : ℝ) - 1)
    hε.le hφ0.le hφ1
  have hlamupper : n / (1 - φ) ≤ φ / (1 - φ) + 1 / (2 * (j : ℝ) - 1 + 2 * ε) := by
    calc
      _ ≤ (φ + (1 - φ) / (2 * (j : ℝ) - 1) - ε) / (1 - φ) :=
        div_le_div_of_nonneg_right hnu hφ.le
      _ = φ / (1 - φ) + (1 / (2 * (j : ℝ) - 1) - ε / (1 - φ)) := by
        field_simp
        <;> ring
      _ ≤ _ := by linarith only [hgap]
  obtain ⟨α, h, hα, hα1, hjh, hhsize, hlo, hhi⟩ :=
    hselect ε hε hεη (n / (1 - φ)) hlampos hlamupper
  have hhR : (1 : ℝ) ≤ h := by
    exact_mod_cast (show 1 ≤ h by omega)
  have hαpos : 0 < α := hε.trans_le hα
  have hsize : (h : ℝ) ≤ 2 * (1 - φ) / ε := by
    calc
      _ ≤ 2 / (n / (1 - φ)) := hhsize
      _ ≤ 2 / (ε / (1 - φ)) :=
        div_le_div_of_nonneg_left (by norm_num) (div_pos hε hφ)
          (div_le_div_of_nonneg_right hn hφ.le)
      _ = _ := by field_simp
  exact ⟨α, h, hα, hα1, hjh, hsize, hlo, hhi,
    Lemma32.holder hhR hαpos, Lemma32.M_exponent hhR hαpos hφ1 hhi⟩

/-- Pages 46 and 47. A nonempty rational exponent instance for the parameter bridge.
Take j and h four, phi one eighth, n one fifth, epsilon one thousandth
and alpha three quarters. -/
theorem lemma32_parameter_instance :
    let j : ℕ := 4
    let φ : ℝ := 1/8
    let ε : ℝ := 1/1000
    let n : ℝ := 1/5
    let h : ℕ := 4
    let α : ℝ := 3/4
    ε ≤ n ∧ n ≤ φ + (1-φ)/(2*(j:ℝ)-1)-ε ∧
      ε ≤ α ∧ α ≤ 1 ∧ j ≤ h ∧ (h:ℝ) ≤ 2*(1-φ)/ε ∧
      2/(2*(h:ℝ)+α) ≤ n/(1-φ) ∧
      n/(1-φ) ≤ φ/(1-φ)+1/(2*(h:ℝ)-1+2*α) ∧
      1/(2*((h:ℝ)+α))+1/(2*((h:ℝ)+α)/((h:ℝ)-1+α)) = 1/2 ∧
      4 ≤ (2+2*((h:ℝ)+α)/((h:ℝ)-1+α))*(1/(1-φ)-n/(1-φ)) := by
  norm_num

end LeanLab.BHP1997.Task308
