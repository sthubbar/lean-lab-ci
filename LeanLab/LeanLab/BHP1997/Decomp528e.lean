/-
P0069, page 27, display 4.13. CODEX task528.
An elementary zeta majorant for the finite reciprocal divisor tail.
This is not the completed Hildebrand asymptotic estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312c
import LeanLab.BHP1997.Repair499Euler
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace LeanLab.BHP1997.Decomp528e
open Classical Complex ArithmeticFunction Decomp312c
open scoped BigOperators

/-- Page 27, auxiliary logarithmic Euler bound for any finite set of primes. -/
theorem prime_power_sum_le_log (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {s : ℝ} (hs : 1 < s) :
    (∑ p ∈ S, (p : ℝ) ^ (-s)) ≤ Real.log (1 + 1 / (s - 1)) := by
  let f : ℕ → ℝ := fun n => vonMangoldt n / ((n : ℝ) ^ s * Real.log n)
  have hf0 (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    exact div_nonneg vonMangoldt_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.log_natCast_nonneg _))
  have hfle (n : ℕ) : f n ≤ (n : ℝ) ^ (-s) := by
    by_cases hn0 : n = 0
    · subst n
      simp [f, Real.zero_rpow (by linarith : -s ≠ 0)]
    by_cases hn1 : n = 1
    · subst n
      simp [f]
    have hn : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hl : 0 < Real.log n := Real.log_pos hn
    have hp : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos (by linarith) _
    calc
      f n = (vonMangoldt n / Real.log n) / (n : ℝ) ^ s := by dsimp [f]; ring
      _ ≤ 1 / (n : ℝ) ^ s :=
        div_le_div_of_nonneg_right ((div_le_one hl).mpr vonMangoldt_le_log) hp.le
      _ = _ := by rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  have hfs : Summable f := (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).of_nonneg_of_le hf0 hfle
  have hfprime (p : ℕ) (hp : p.Prime) : f p = (p : ℝ) ^ (-s) := by
    have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)).ne'
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    dsimp only [f]
    rw [vonMangoldt_apply_prime hp, Real.rpow_neg hp0.le]
    field_simp [hl, (Real.rpow_pos_of_pos hp0 s).ne']
  have hz : ‖riemannZeta (s : ℂ)‖ ≤ 1 + 1 / (s - 1) := by
    simpa only [DirichletCharacter.LFunction_modOne_eq, Complex.ofReal_re] using
      Repair499Euler.LFunction_norm_le (1 : DirichletCharacter ℂ 1) (s := (s : ℂ)) (by simpa using hs)
  calc
    _ = ∑ p ∈ S, f p := Finset.sum_congr rfl (fun p hp => (hfprime p (hS p hp)).symm)
    _ ≤ ∑' n, f n := hfs.sum_le_tsum S (fun n hn => hf0 n)
    _ = Real.log (riemannZeta (s : ℂ)).re := (log_riemannZeta_eq hs).symm
    _ ≤ _ := Real.log_le_log (riemannZeta_re_pos_of_one_lt hs) ((Complex.re_le_norm _).trans hz)

/-- Page 27, the formerly explicit Rankin prime product has a uniform zeta majorant. -/
theorem prime_product_zeta_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {w α δ : ℝ} (hw : 1 ≤ w) (hδ : 0 < δ) (hαδ : 0 ≤ α + δ)
    (hpw : ∀ p ∈ S, (p : ℝ) ≤ w) :
    (∏ p ∈ S, (1 + (p : ℝ) ^ (α - 1))) ≤
      Real.exp (w ^ (α + δ) * Real.log (1 + 1 / δ)) := by
  have hsum : (∑ p ∈ S, (p : ℝ) ^ (α - 1)) ≤
      w ^ (α + δ) * Real.log (1 + 1 / δ) := by
    calc
      _ ≤ ∑ p ∈ S, w ^ (α + δ) * (p : ℝ) ^ (-(1 + δ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
        have he : (p : ℝ) ^ (α - 1) = (p : ℝ) ^ (α + δ) * (p : ℝ) ^ (-(1 + δ)) := by
          rw [← Real.rpow_add hp0]
          congr 1
          ring
        rw [he]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hp0.le (hpw p hp) hαδ) (Real.rpow_nonneg hp0.le _)
      _ = w ^ (α + δ) * ∑ p ∈ S, (p : ℝ) ^ (-(1 + δ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith : 0 ≤ w) _)
        simpa only [add_sub_cancel_left] using
          prime_power_sum_le_log S hS (s := 1 + δ) (by linarith)
  calc
    _ ≤ ∏ p ∈ S, Real.exp ((p : ℝ) ^ (α - 1)) := by
      apply Finset.prod_le_prod₀ (fun p hp => by positivity)
      intro p hp
      simpa only [add_comm] using Real.add_one_le_exp ((p : ℝ) ^ (α - 1))
    _ = Real.exp (∑ p ∈ S, (p : ℝ) ^ (α - 1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

/-- Page 27, an explicit elementary reciprocal tail majorant.
This closes the finite Euler product step without asserting the final asymptotic choice. -/
theorem squarefree_reciprocal_tail_zeta (N : ℕ) (hN : Squarefree N)
    {w γ α δ : ℝ} (hw : 1 ≤ w) (hγ : 0 < γ)
    (hα0 : 0 ≤ α) (hα : α < 1) (hδ : 0 < δ)
    (hpw : ∀ p : ℕ, p.Prime → p ∣ N → (p : ℝ) ≤ w) :
    (∑ d ∈ N.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ)) ≤
      γ ^ (-α) * Real.exp (w ^ (α + δ) * Real.log (1 + 1 / δ)) := by
  apply (squarefree_reciprocal_rankin N hN hγ hα0 hα).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hγ.le _)
  exact prime_product_zeta_bound N.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hw hδ (by linarith)
    (fun p hp => hpw p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))

/-- Page 27, every logarithmic saving for the reciprocal smooth divisor tail
at the paper roughness scale. The proof chooses the Rankin parameters explicitly. -/
theorem primorial_reciprocal_tail_log_saving (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ L : ℝ in Filter.atTop,
      (∑ d ∈ (Thm2.primorialBelow (Real.exp (L ^ (9 / 10 : ℝ)))).divisors.filter
        (fun d : ℕ => Real.exp (c * L) ≤ (d : ℝ)), 1 / (d : ℝ)) ≤ L ^ (-A) := by
  have hs := (isLittleO_log_rpow_atTop (r := 9 / 10) (by norm_num)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hc40 : 0 < c / 40 := by positivity
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 40)).eventually
    (Filter.eventually_ge_atTop ((2 * Real.exp 1 + A) / (c / 40)))
  filter_upwards [hs, hp, Filter.eventually_ge_atTop (2 : ℝ)] with L hs hp hL2
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  let q : ℝ := L ^ (9 / 10 : ℝ)
  let α : ℝ := Real.log L / (40 * q)
  let δ : ℝ := 1 / q
  let w : ℝ := Real.exp q
  have hq : 0 < q := Real.rpow_pos_of_pos hL0 _
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hsmall : Real.log L ≤ q := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl,
      abs_of_nonneg (Real.rpow_nonneg hL0.le _), one_mul] using hs
  have hα0 : 0 ≤ α := div_nonneg hl (by positivity)
  have hα : α < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 40 * q)).mpr
    linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hw : 1 ≤ w := Real.one_le_exp_iff.mpr hq.le
  have htail := squarefree_reciprocal_tail_zeta
    (Thm2.primorialBelow w) (primorial_squarefree w) hw (Real.exp_pos (c * L))
    hα0 hα hδ (fun p hp hpd => (prime_lt_of_dvd_primorial hp hpd).le)
  have hdiv : L / q = L ^ (1 / 10 : ℝ) := by
    dsimp [q]
    rw [show (1 / 10 : ℝ) = 1 - 9 / 10 by norm_num,
      Real.rpow_sub hL0, Real.rpow_one]
  have hγ : (Real.exp (c * L)) ^ (-α) =
      Real.exp (-(c / 40) * L ^ (1 / 10 : ℝ) * Real.log L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    calc
      _ = -(c / 40) * (L / q) * Real.log L := by dsimp [α]; ring
      _ = _ := by rw [hdiv]
  have hwα : w ^ (α + δ) = Real.exp 1 * L ^ (1 / 40 : ℝ) := by
    dsimp only [w]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have he : q * (α + δ) = 1 + Real.log L / 40 := by
      dsimp [α, δ]
      field_simp [hq.ne']
      <;> ring
    rw [he, Real.exp_add, Real.rpow_def_of_pos hL0]
    congr 2
    ring
  have hqle : q ≤ L := by
    calc
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = _ := Real.rpow_one _
  have hlogq : Real.log (1 + q) ≤ 2 * Real.log L := by
    have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) hL2
    calc
      _ ≤ Real.log (2 * L) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log L := Real.log_mul (by norm_num) hL0.ne'
      _ ≤ _ := by linarith
  have hprod : w ^ (α + δ) * Real.log (1 + 1 / δ) ≤
      2 * Real.exp 1 * L ^ (1 / 40 : ℝ) * Real.log L := by
    rw [hwα]
    have hd : 1 / δ = q := by dsimp [δ]; rw [one_div_one_div]
    rw [hd]
    nlinarith [mul_le_mul_of_nonneg_left hlogq
      (mul_nonneg (Real.exp_pos 1).le (Real.rpow_nonneg hL0.le (1 / 40 : ℝ)))]
  have hC : 2 * Real.exp 1 + A ≤ (c / 40) * L ^ (3 / 40 : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hc40).mp hp
  have hmul : (2 * Real.exp 1 + A) * L ^ (1 / 40 : ℝ) ≤
      (c / 40) * L ^ (1 / 10 : ℝ) := by
    calc
      _ ≤ ((c / 40) * L ^ (3 / 40 : ℝ)) * L ^ (1 / 40 : ℝ) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL0.le _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hL0]
        norm_num
  have hcoef : 2 * Real.exp 1 * L ^ (1 / 40 : ℝ) + A ≤ (c / 40) * L ^ (1 / 10 : ℝ) := by
    have hy : 1 ≤ L ^ (1 / 40 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hy)]
  calc
    _ ≤ (Real.exp (c * L)) ^ (-α) *
        Real.exp (w ^ (α + δ) * Real.log (1 + 1 / δ)) := htail
    _ = Real.exp (-(c / 40) * L ^ (1 / 10 : ℝ) * Real.log L +
        w ^ (α + δ) * Real.log (1 + 1 / δ)) := by rw [hγ, Real.exp_add]
    _ ≤ Real.exp (-A * Real.log L) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcoef hl]
    _ = _ := by rw [Real.rpow_def_of_pos hL0]; congr 1; ring

/-- Page 27, the reciprocal tail at w equal to exp of log x to power 9/10
and gamma equal to x to power epsilon over 12 has every logarithmic saving. -/
theorem reciprocal_tail_every_log {ε A : ℝ} (hε : 0 < ε) (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (∑ d ∈ (Thm2.primorialBelow (Real.exp (Real.log x ^ (9 / 10 : ℝ)))).divisors.filter
        (fun d : ℕ => x ^ (ε / 12) ≤ (d : ℝ)), 1 / (d : ℝ)) ≤ Real.log x ^ (-A) := by
  have h := Real.tendsto_log_atTop.eventually
    (primorial_reciprocal_tail_log_saving (ε / 12) A (by positivity) hA)
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have he : Real.exp ((ε / 12) * Real.log x) = x ^ (ε / 12) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  simpa only [he] using hx

end LeanLab.BHP1997.Decomp528e
