/-
P0093 page 168 equation 10.6. Bridge the existing general Euler series proof.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.TailBridge376
import LeanLab.Linnik1951.SPLIT_singular_tail357

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.6. At an odd positive residual,
the prime two local factor vanishes, so the full product is zero.
Together with the proved even bridge this identifies the product
with the existing general Heath Brown singular series. -/
theorem singular_eq_heath_brown_all435 (n : ℕ) (hn : 2 ≤ n) :
    singularSeries111 n = LeanLab.HeathBrown1985.singular n := by
  classical
  by_cases hev : Even n
  · exact singular_eq_heath_brown376 n hn hev
  · rw [LeanLab.HeathBrown1985.singular, if_neg hev]
    unfold singularSeries111
    apply tprod_of_exists_eq_zero
    refine ⟨⟨2, Nat.prime_two⟩, ?_⟩
    have htwo : ¬ 2 ∣ n := by
      intro h
      exact hev (even_iff_two_dvd.mpr h)
    norm_num [htwo]

/-- P0093 page 168 equation 10.6. The real weighted Ramanujan
coefficient agrees with the already proved Heath Brown Euler product
coefficient. The proof reuses the existing lab Ramanujan range bridge. -/
theorem ramanujan_real_eq_gm435 (n q : ℕ) (hn : 2 ≤ n) :
    ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re =
        LeanLab.HeathBrown1985.gm n q := by
  classical
  by_cases hq : q = 0
  · subst q
    simp [LeanLab.HeathBrown1985.gm]
  · have hq1 : 1 ≤ q := by omega
    have hc := LeanLab.PerelliPintz1992.Decomp1519.ram_term_eq_gm n q (by omega)
    rw [← ramanujan_eq_perelli_pintz376 q n hq1] at hc
    have hre := congrArg Complex.re hc
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, LeanLab.PerelliPintz1992.Decomp1519.muφ, div_pow] using hre

/-- P0093 page 168 equation 10.6. Exact singular_series_has_sum357
statement from the already proved lab Euler product theorem.
No truncation rate or uniformity in the residual is asserted here. -/
theorem singular_series_has_sum_proved435 (n : ℕ) (hn : 2 ≤ n) :
    HasSum (fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (singularSeries111 n) := by
  simp_rw [ramanujan_real_eq_gm435 n _ hn]
  rw [singular_eq_heath_brown_all435 n hn]
  exact LeanLab.HeathBrown1985.hasSum_gm n (by omega)

end LeanLab.Linnik1951
