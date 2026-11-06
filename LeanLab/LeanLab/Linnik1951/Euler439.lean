/-
P0093 page 168 equation 10.6. The full Ramanujan series identity.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.TailBridge376

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.6. The real Ramanujan coefficient equals
the already proved multiplicative Heath Brown coefficient, including modulus zero. -/
theorem ramanujan_weight_eq_gm439 (n q : ℕ) (hn : 1 ≤ n) :
    ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re =
        LeanLab.HeathBrown1985.gm n q := by
  by_cases hq : q = 0
  · subst q
    simp [LeanLab.HeathBrown1985.gm_zero]
  · have h := congrArg Complex.re
      (LeanLab.PerelliPintz1992.Decomp1519.ram_term_eq_gm n q hn)
    rw [← ramanujan_eq_perelli_pintz376 q n (by omega)] at h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    simpa [LeanLab.PerelliPintz1992.Decomp1519.muφ, div_pow] using h

/-- P0093 page 168 equation 10.6. The Euler product and the closed finite
prime divisor form agree at every positive residual, including odd residuals. -/
theorem singular_eq_heath_brown_all439 (n : ℕ) (hn : 2 ≤ n) :
    singularSeries111 n = LeanLab.HeathBrown1985.singular n := by
  by_cases he : Even n
  · exact singular_eq_heath_brown376 n hn he
  · have ho : Odd n := Nat.not_even_iff_odd.mp he
    change LeanLab.Perelli1996.Sing n = _
    rw [LeanLab.HeathBrown1985.singular, if_neg he]
    unfold LeanLab.Perelli1996.Sing
    apply tprod_of_exists_eq_zero
    refine ⟨⟨2, Nat.prime_two⟩, ?_⟩
    have h2 : ¬ 2 ∣ n := fun h => he (even_iff_two_dvd.mpr h)
    norm_num [h2]

/-- P0093 page 168 equation 10.6. Exact sealed singular_series_has_sum357
statement, proved from the existing clean multiplicative series theorem. -/
theorem singular_series_has_sum_proved439 (n : ℕ) (hn : 2 ≤ n) :
    HasSum (fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (singularSeries111 n) := by
  simp_rw [ramanujan_weight_eq_gm439 n _ (by omega)]
  rw [singular_eq_heath_brown_all439 n hn]
  exact LeanLab.HeathBrown1985.hasSum_gm n (by omega)

end LeanLab.Linnik1951
