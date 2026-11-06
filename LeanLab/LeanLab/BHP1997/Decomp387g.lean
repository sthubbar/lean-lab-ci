/-
BHP1997, pages 3 and 52. Distribution under logarithmic upper rescaling.
The variable-center character estimate is an explicit conditional input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp387f
import LeanLab.BHP1997.ShortConditions308

namespace LeanLab.BHP1997.Task387
open Classical Complex DecompC165b

/-- Page 3 condition iii. A prefix of the supported dyadic interval is
exactly the integer Ioc interval ending at floor t. -/
theorem right_prefix_eq_Ioc {ε x t : ℝ} (ht : 0 ≤ t)
    (htu : t ≤ 2*x^(11/20+ε)) :
    (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) =
      Finset.Ioc ⌊x^(11/20+ε)⌋₊ ⌊t⌋₊ := by
  ext m
  simp only [rightInterval, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hmt⟩
    exact ⟨hlo, (Nat.le_floor_iff ht).mpr hmt⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨⟨hlo, hhi.trans (Nat.floor_mono htu)⟩, (Nat.le_floor_iff ht).mp hhi⟩

/-- Pages 3 and 52, auxiliary upper normalization. Uniform character
prefix estimates with the variable reciprocal-log center imply the exact
ShortDistribution predicate for the logarithmically rescaled coefficient.
CONDITIONAL on the displayed variable-center character estimates.
Those estimates are not asserted for the raw page 53 coefficient. -/
theorem short_distribution_of_variable_log_center {ε v : ℝ}
    {b : ℝ → ℕ → ℝ} (hε : 0 ≤ ε)
    (hraw : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ 2*x^(11/20+ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b x m : ℂ)*χ (m : ZMod q)-Thm2.delta χ*v/(Real.log m : ℂ))‖ ≤
            C*x^(11/20+ε)*Real.log x^(-A)) :
    Task308.ShortDistribution ε v
      (fun x m => upperLogFactor (x^(11/20+ε)) m*b x m) := by
  intro A hA
  obtain ⟨C, hC⟩ := hraw A hA
  let D : ℝ := max C 1
  let K : ℝ := max (max C 4) (3*D)
  refine ⟨K, ?_⟩
  intro x hx q hq hqx χ t ht
  have hxC : C ≤ x := (le_max_left C 4).trans ((le_max_left _ _).trans hx)
  have hx4 : 4 ≤ x := (le_max_right C 4).trans ((le_max_left _ _).trans hx)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hD : 1 ≤ D := le_max_right _ _
  have hDK : 3*D ≤ K := le_max_right _ _
  have hK : 0 ≤ K := by linarith
  let Y : ℝ := x^(11/20+ε)
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hY2 : 2 ≤ Y := by
    have hfour : (4 : ℝ)^(1/2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc
      (2 : ℝ) = (4 : ℝ)^(1/2 : ℝ) := hfour.symm
      _ ≤ x^(1/2 : ℝ) := Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
      _ ≤ Y := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hlog : 0 ≤ Real.log x^(-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hright : 0 ≤ K*Y*Real.log x^(-A) := by positivity
  change ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      (((upperLogFactor Y m*b x m : ℝ) : ℂ)*χ (m : ZMod q)-Thm2.delta χ*v/(Real.log Y : ℂ))‖ ≤
        K*Y*Real.log x^(-A)
  by_cases ht0 : 0 ≤ t
  · rw [right_prefix_eq_Ioc ht0 ht]
    let L : ℕ := ⌊Y⌋₊
    let U : ℕ := ⌊t⌋₊
    change ‖∑ m ∈ Finset.Ioc L U,
      (((upperLogFactor Y m*b x m : ℝ) : ℂ)*χ (m : ZMod q)-Thm2.delta χ*v/(Real.log Y : ℂ))‖ ≤
        K*Y*Real.log x^(-A)
    by_cases hLU : L < U
    · have hL : Y ≤ ((L+1 : ℕ) : ℝ) := by
        simpa only [L, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one Y).le
      have hU : (U : ℝ) ≤ 2*Y := (Nat.floor_le ht0).trans ht
      have hR : 0 ≤ D*Y*Real.log x^(-A) := by positivity
      have hpref : ∀ k ≤ U-L, ‖∑ m ∈ Finset.Ioc L (L+k),
          ((b x m : ℂ)*χ (m : ZMod q)-Thm2.delta χ*v/(Real.log m : ℂ))‖ ≤
            D*Y*Real.log x^(-A) := by
        intro k hk
        have hku : L+k ≤ U := by omega
        have htu : ((L+k : ℕ) : ℝ) ≤ 2*Y := (Nat.cast_le.mpr hku).trans hU
        have hh := hC x hxC q hq hqx χ ((L+k : ℕ) : ℝ) htu
        rw [right_prefix_eq_Ioc (Nat.cast_nonneg _) htu, Nat.floor_natCast] at hh
        change ‖∑ m ∈ Finset.Ioc L (L+k),
          ((b x m : ℂ)*χ (m : ZMod q)-Thm2.delta χ*v/(Real.log m : ℂ))‖ ≤
            C*Y*Real.log x^(-A) at hh
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C 1) hY0.le) hlog)
      have hh := logarithmic_center_rescaling_Ioc Y L U
        (fun m => (b x m : ℂ)*χ (m : ZMod q)) (Thm2.delta χ) (v : ℂ)
        hY2 hL hU hLU hR hpref
      have he : (∑ m ∈ Finset.Ioc L U,
          (((upperLogFactor Y m*b x m : ℝ) : ℂ)*χ (m : ZMod q)-Thm2.delta χ*v/(Real.log Y : ℂ))) =
          ∑ m ∈ Finset.Ioc L U,
            (((Real.log m/Real.log Y : ℝ) : ℂ)*((b x m : ℂ)*χ (m : ZMod q))-
              Thm2.delta χ*v/(Real.log Y : ℂ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm' := Finset.mem_Ioc.mp hm
        have hml : Y ≤ (m : ℝ) := (Nat.lt_of_floor_lt hm'.1).le
        have hmu : (m : ℝ) ≤ 2*Y := (Nat.cast_le.mpr hm'.2).trans hU
        rw [upperLogFactor, ite_eq_left ⟨hY2, hml, hmu⟩]
        push_cast
        ring
      rw [he]
      apply hh.trans
      calc
        3*(D*Y*Real.log x^(-A)) = (3*D)*Y*Real.log x^(-A) := by ring
        _ ≤ K*Y*Real.log x^(-A) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hDK hY0.le) hlog
    · rw [Finset.Ioc_eq_empty_of_le (le_of_not_gt hLU), Finset.sum_empty, norm_zero]
      exact hright
  · have he : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro m hm hmt
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [he, Finset.sum_empty, norm_zero]
    exact hright

end LeanLab.BHP1997.Task387
