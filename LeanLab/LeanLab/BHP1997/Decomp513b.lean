/-
P0069 page 11, the actual finite Dirichlet polynomial and its smooth sampling reduction.
This file supplies elementary calculus. The continuous hybrid moment estimate remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp513a
open scoped ContDiff

namespace LeanLab.BHP1997.Decomp513b

/-- P0069 page 11, the polynomial definition before display 3.1.
Positive lower support excludes the zero index. Each summand on the critical line
is a constant times the exponential of an affine complex function of the real height.
It therefore has continuous derivatives of every order. -/
theorem dirPoly_contDiff (a : ℕ → ℂ) (c1 c2 F : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (hlo : 0 < c1 * F) :
    ContDiff ℝ ∞ (fun t : ℝ => Thm4.dirPoly a c1 c2 F χ (Thm4.half t)) := by
  classical
  unfold Thm4.dirPoly
  apply ContDiff.sum
  intro n hn
  have hnpos : 0 < (n : ℝ) := hlo.trans (Finset.mem_filter.mp hn).2.1
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hnpos)
  have heq : (fun t : ℝ => a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t) =
      (fun t : ℝ => a n * χ (n : ZMod q) *
        Complex.exp (-(Complex.log (n : ℂ) * Thm4.half t))) := by
    funext t
    simp only [Complex.cpow_def_of_ne_zero hn0, div_eq_mul_inv, Complex.exp_neg]
  rw [heq]
  unfold Thm4.half
  have hcast : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

/-- P0069 page 11 display 3.3 and its page 12 sampling citation.
The actual polynomial square sum is bounded by continuous square values plus
absolute variation, summed over all characters. The continuous mean value bound
is a separate analytic input. -/
theorem dirPoly_square_sampling (a : ℕ → ℂ) (c1 c2 F : ℝ)
    {q : ℕ} (S : Finset (ℝ × DirichletCharacter ℂ q)) (hlo : 0 < c1 * F)
    (hspace : Thm4.WellSpaced S) {T : ℝ} (hT : 0 ≤ T)
    (ht : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) ≤
      ∑ χ : DirichletCharacter ℂ q, ∫ u in (-T)..(T + 1),
        ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half u)‖ ^ 2 +
          |deriv (fun v : ℝ => ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half v)‖ ^ 2) u| := by
  let f (χ : DirichletCharacter ℂ q) (t : ℝ) :=
    ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ^ 2
  have hfc (χ : DirichletCharacter ℂ q) : ContDiff ℝ ∞ (f χ) :=
    (dirPoly_contDiff a c1 c2 F χ hlo).norm_sq ℂ
  exact Decomp513a.character_spaced_sampling S f (fun χ => deriv (f χ))
    (fun χ u => ((hfc χ).differentiable (by simp) u).hasDerivAt)
    (fun χ => (hfc χ).continuous_deriv (by simp)) (fun χ u => sq_nonneg _)
    hspace hT ht
open MeanSquareC165

/-- P0069 page 11, the energy G of display 3.3 applied to logarithmic derivative coefficients.
For F at most x, multiplication by log n costs at most a fixed endpoint constant
squared times log x squared in coefficient energy. The endpoint constant is independent of F.
This explicit constant is an elementary lab bound, not a printed paper constant. -/
theorem log_weight_energy_le (a : ℕ → ℂ) {c1 c2 F x : ℝ}
    (hlo : 0 < c1 * F) (hc2 : 0 < c2) (hF : 2 ≤ F) (hFx : F ≤ x) :
    energy (fun n => (Real.log n : ℂ) * a n) c1 c2 F ≤
      ((1 + |Real.log c2| / Real.log 2) * Real.log x) ^ 2 * energy a c1 c2 F := by
  have hF0 : 0 < F := by linarith
  have hx : 2 ≤ x := hF.trans hFx
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogF : Real.log F ≤ Real.log x := Real.log_le_log hF0 hFx
  have hscale : |Real.log c2| ≤ (|Real.log c2| / Real.log 2) * Real.log x := by
    calc
      _ = (|Real.log c2| / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlx (by positivity)
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨_, hnlo, hnhi⟩ := Finset.mem_filter.mp hn
  have hnpos : 0 < (n : ℝ) := hlo.trans hnlo
  have hnN : 0 < n := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hupper : Real.log (n : ℝ) ≤ |Real.log c2| + Real.log x := by
    have hh := Real.log_le_log hnpos hnhi.le
    rw [Real.log_mul hc2.ne' hF0.ne'] at hh
    linarith [le_abs_self (Real.log c2)]
  have hbound : Real.log (n : ℝ) ≤ (1 + |Real.log c2| / Real.log 2) * Real.log x := by
    nlinarith
  have hnorm : ‖(Real.log (n : ℝ) : ℂ) * a n‖ ^ 2 ≤
      ((1 + |Real.log c2| / Real.log 2) * Real.log x) ^ 2 * ‖a n‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlogn hbound 2) (sq_nonneg _)
  calc
    _ ≤ (((1 + |Real.log c2| / Real.log 2) * Real.log x) ^ 2 * ‖a n‖ ^ 2) / (n : ℝ) :=
      div_le_div_of_nonneg_right hnorm hnpos.le
    _ = _ := by ring
/-- P0069 page 11, differentiating the polynomial used in display 3.3.
Its derivative with respect to the real height is minus I times the polynomial
whose coefficients are multiplied by log n. This is an exact finite identity. -/
theorem dirPoly_hasDerivAt (a : ℕ → ℂ) (c1 c2 F : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (hlo : 0 < c1 * F) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Thm4.dirPoly a c1 c2 F χ (Thm4.half u))
      (-Complex.I * Thm4.dirPoly (fun n => (Real.log n : ℂ) * a n)
        c1 c2 F χ (Thm4.half t)) t := by
  classical
  unfold Thm4.dirPoly
  rw [Finset.mul_sum]
  apply HasDerivAt.fun_sum
  intro n hn
  have hnpos : 0 < (n : ℝ) := hlo.trans (Finset.mem_filter.mp hn).2.1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
  have hcast : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt (x := t)
  have hhalf : HasDerivAt Thm4.half Complex.I t := by
    change HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * Complex.I) Complex.I t
    simpa only [one_mul] using! (hcast.mul_const Complex.I).const_add (1 / 2 : ℂ)
  have hexp : HasDerivAt
      (fun u : ℝ => Complex.exp (-(Complex.log (n : ℂ) * Thm4.half u)))
      (Complex.exp (-(Complex.log (n : ℂ) * Thm4.half t)) *
        -(Complex.log (n : ℂ) * Complex.I)) t :=
    ((hhalf.const_mul (Complex.log (n : ℂ))).neg).cexp
  have heq : (fun u : ℝ => a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half u) =
      (fun u : ℝ => a n * χ (n : ZMod q) *
        Complex.exp (-(Complex.log (n : ℂ) * Thm4.half u))) := by
    funext u
    simp only [Complex.cpow_def_of_ne_zero hn0, div_eq_mul_inv, Complex.exp_neg]
  rw [heq]
  convert hexp.const_mul (a n * χ (n : ZMod q)) using 1
  simp only [Complex.cpow_def_of_ne_zero hn0, div_eq_mul_inv, Complex.exp_neg]
  rw [← Complex.natCast_log]
  ring
/-- P0069 page 11 display 3.1, a diagnostic for the sampling input interface.
Constant coefficients obey the divisor bound at exponent zero. Their logarithmic
multipliers obey no fixed divisor bound, since divisor counts are two at arbitrarily
large primes. This is a route obstruction, not a claim that the paper is wrong. -/
theorem log_weight_not_divisor_bounded :
    Thm4.CoeffBound (fun _ => (1 : ℂ)) 0 ∧
      ∀ B : ℝ, ¬ Thm4.CoeffBound (fun n => (Real.log n : ℂ)) B := by
  constructor
  · intro n
    simp
  · intro B h
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp ((2 : ℝ) ^ B))
    obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
    have hp' : Real.exp ((2 : ℝ) ^ B) < (p : ℝ) :=
      hN.trans_le (by exact_mod_cast hNp)
    have hlog := Real.log_lt_log (Real.exp_pos ((2 : ℝ) ^ B)) hp'
    rw [Real.log_exp] at hlog
    have hbound := h p
    have hlogp : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have htau : p.divisors.card = 2 := by simp [hp.divisors, hp.ne_one.symm]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogp, htau] at hbound
    norm_num only [Nat.cast_ofNat] at hbound
    exact not_lt_of_ge hbound hlog
/-- P0069 page 11 display 3.1 and the derivative sampling step for display 3.3.
Truncate logarithmic derivative coefficients to the actual support and divide by
one plus the absolute endpoint logarithm over log two, all times log x.
This normalization preserves the original divisor exponent B. It complements the
unscaled logarithmic obstruction and supplies no continuous moment theorem. -/
theorem normalized_log_coeff_bound {a : ℕ → ℂ} {B c1 c2 F x : ℝ}
    (ha : Thm4.CoeffBound a B) (hlo : 0 < c1 * F) (hc2 : 0 < c2)
    (hF : 2 ≤ F) (hFx : F ≤ x) :
    Thm4.CoeffBound (fun n => if c1 * F < n ∧ (n : ℝ) < c2 * F then
      (Real.log n : ℂ) * a n /
        (((1 + |Real.log c2| / Real.log 2) * Real.log x : ℝ) : ℂ) else 0) B := by
  classical
  let R : ℝ := (1 + |Real.log c2| / Real.log 2) * Real.log x
  change Thm4.CoeffBound (fun n => if c1 * F < n ∧ (n : ℝ) < c2 * F then
    (Real.log n : ℂ) * a n / (R : ℂ) else 0) B
  have hF0 : 0 < F := by linarith
  have hx : 2 ≤ x := hF.trans hFx
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogx : 0 < Real.log x := hl2.trans_le hlx
  have hR : 0 < R := by dsimp [R]; positivity
  have hlogF : Real.log F ≤ Real.log x := Real.log_le_log hF0 hFx
  have hscale : |Real.log c2| ≤ (|Real.log c2| / Real.log 2) * Real.log x := by
    calc
      _ = (|Real.log c2| / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlx (by positivity)
  intro n
  dsimp only
  split_ifs with hn
  · have hnpos : 0 < (n : ℝ) := hlo.trans hn.1
    have hnN : 0 < n := by exact_mod_cast hnpos
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hupper : Real.log (n : ℝ) ≤ |Real.log c2| + Real.log x := by
      have hh := Real.log_le_log hnpos hn.2.le
      rw [Real.log_mul hc2.ne' hF0.ne'] at hh
      linarith [le_abs_self (Real.log c2)]
    have hbound : Real.log (n : ℝ) ≤ R := by dsimp [R]; nlinarith
    calc
      _ = Real.log (n : ℝ) * ‖a n‖ / R := by
        rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogn, abs_of_pos hR]
      _ ≤ ‖a n‖ := (div_le_iff₀ hR).mpr (by nlinarith [mul_le_mul_of_nonneg_right hbound (norm_nonneg (a n))])
      _ ≤ _ := ha n
  · rw [norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) B
end LeanLab.BHP1997.Decomp513b
