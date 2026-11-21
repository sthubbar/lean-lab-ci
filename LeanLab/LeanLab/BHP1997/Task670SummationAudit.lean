/-
Audit of the sealed lab modulus summation leaf associated with P0069 page 7.
The missing growing length restriction permits a negative epsilon counterexample.
No existing statement is changed and no existing proof is replaced.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.PrincipalData635
namespace LeanLab.BHP1997.Task670SummationAudit
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m
/-- P0069 page 7 is an asymptotic argument with a growing interval length. The lab
modulus summation helper quantifies over every epsilon. At x equal to three and length
one half, its single modulus premise holds and its conclusion fails. This refutes the
lab helper as sealed, not the paper. -/
theorem short_modulus_summation_statement_false :
    ¬ (∀ (ε D x u v A C₀ : ℝ) (b : ℕ → ℂ) (N : ℕ),
      0 < A → 0 ≤ D → 3 ≤ x →
    (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
      ‖((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖ ≤
        C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
          (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖) →
    ‖∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖ ≤
      max 1 C₀ * Real.log x ^ (-A) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖) := by
  intro h
  let ε : ℝ := Real.log (1 / 2 : ℝ) / Real.log 3 - 11 / 20
  have hL : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hLpos : 0 < Real.log 3 := by linarith
  have hY : length512 ε 3 = 1 / 2 := by
    unfold length512
    have he : 11 / 20 + ε = Real.log (1 / 2 : ℝ) / Real.log 3 := by dsimp [ε]; ring
    rw [he, Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ hLpos.ne',
      Real.exp_log (by norm_num)]
  have hphase (t : ℝ) :
      @fourier (1 : ℝ) (3 : ℤ) (t : AddCircle (1 : ℝ)) *
        @fourier (1 : ℝ) (1 : ℤ) (((1 + t : ℝ)) : AddCircle (1 : ℝ)) *
        @fourier (1 : ℝ) (-4 : ℤ) (((1 + t : ℝ)) : AddCircle (1 : ℝ)) = 1 := by
    have hp : ((1 + t : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := by
      rw [add_comm, AddCircle.coe_add_period]
    simp only [hp, ← fourier_add]
    norm_num
  have hlong : Finset.Ioc ⌊(3 : ℝ) - 2 * length512 ε 3⌋₊ 3 = {3} := by
    rw [hY]; norm_num
  have hshort : Finset.Ioc ⌊length512 ε 3⌋₊ ⌊2 * length512 ε 3⌋₊ = {1} := by
    rw [hY]; norm_num
  have hi : (∫ t : ℝ in (-2 : ℝ)..2,
      polynomial512 (Finset.Ioc ⌊(3 : ℝ) - 2 * length512 ε 3⌋₊ 3) (fun _ => 1) t *
        polynomial512 (Finset.Ioc ⌊length512 ε 3⌋₊ ⌊2 * length512 ε 3⌋₊)
          (fun _ => 1) (1 + t) *
        @fourier 1 (-(4 : ℤ)) (((1 + t : ℝ)) : AddCircle (1 : ℝ))) = 4 := by
    simp only [polynomial512, hlong, hshort, Finset.sum_singleton, one_mul]
    norm_num only [Nat.cast_ofNat]
    simp_rw [hphase]
    norm_num [intervalIntegral.integral_const]
  have hi' := hi
  simp only [polynomial512, hlong, hshort, Finset.sum_singleton, one_mul] at hi'
  norm_num only [Nat.cast_ofNat] at hi'
  have h4norm : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
  have hlog4 : Real.log 3 ^ 4 ≤ 2 := by
    have hupper : Real.log 3 ≤ 7 / 6 := by linarith [Real.log_three_lt_d9]
    have hh := pow_le_pow_left₀ hLpos.le hupper 4
    norm_num at hh
    linarith
  have hspec := h ε 0 3 (Real.log 3) 0 1 4 (fun _ => 1) 4
    (by norm_num) (by norm_num) (by norm_num)
  have hfloor3 : ⌊(3 : ℝ)⌋₊ = 3 := by norm_num
  simp only [hfloor3, hlong, hshort] at hspec
  simp only [polynomial512, Finset.sum_singleton, one_mul] at hspec
  have hLc : (Real.log 3 : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
  simp only [mul_zero, Real.rpow_zero, hY, Complex.ofReal_zero, zero_div, zero_mul,
    sub_zero, norm_one, mul_one, div_self hLc, one_mul] at hspec
  have hbudget : (4 : ℝ) ≤ 4 * Real.log 3 ^ (-4 : ℝ) * 2 := by
    have he4 : Real.log 3 ^ (4 : ℝ) = Real.log 3 ^ (4 : ℕ) := Real.rpow_natCast _ _
    rw [Real.rpow_neg hLpos.le, he4]
    have h4pos : 0 < Real.log 3 ^ 4 := pow_pos hLpos 4
    have hh : (4 : ℝ) ≤ 8 / Real.log 3 ^ 4 :=
      (le_div_iff₀ h4pos).mpr (by nlinarith [hlog4])
    convert hh using 1 <;> ring
  have hc := hspec (by
    intro q hq1 hq2
    have hq2' : q ≤ 1 := by exact_mod_cast hq2
    have hq : q = 1 := by omega
    subst q
    norm_num only [Nat.cast_one, Nat.totient_one, ArithmeticFunction.moebius_apply_one,
      Int.cast_one, div_one, Finset.Icc_self, Finset.filter_singleton,
      Nat.coprime_one_left, ite_true, Finset.sum_singleton, one_mul,
      mul_one, norm_one, add_zero, Nat.cast_ofNat]
    rw [hi', h4norm]
    exact hbudget)
  have hfloor1 : ⌊(1 : ℝ)⌋₊ = 1 := by norm_num
  norm_num only [hfloor1, Finset.Icc_self, Nat.cast_one, Nat.totient_one,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, div_one, Finset.filter_singleton,
    Nat.coprime_one_left, ite_true, Finset.sum_singleton, one_mul,
    mul_one, norm_one, add_zero, Nat.cast_ofNat,
    max_eq_right (by norm_num : (1 : ℝ) ≤ 4)] at hc
  rw [hi', h4norm, Real.rpow_neg_one] at hc
  have hh : (4 : ℝ) * Real.log 3 ≤ 4 :=
    (le_div_iff₀ hLpos).mp (by simpa only [div_eq_mul_inv] using hc)
  linarith

end LeanLab.BHP1997.Task670SummationAudit
