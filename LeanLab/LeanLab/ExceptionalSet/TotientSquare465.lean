import LeanLab.ExceptionalSet.U1432MVNoExc
import LeanLab.HeathBrown1985.SingularSeries
import LeanLab.BhowmikGrimmelt2026.TotientRatio247

/-!
Arithmetic tail envelopes for P0082 pages361 and362, displays17 to19.
These helpers contain no prime distribution input.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset

/-- P0082 pages361 and362, an elementary reciprocal totient envelope for
the far tail. The squared totient ratio is at most four times the divisor count. -/
theorem totient_ratio_sq_le_divisors (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 ≤ 4 * (q.divisors.card : ℝ) := by
  let S := q.primeFactors
  let T := S.filter (fun p => p = 2 ∨ p = 3)
  have hlocal (p : ℕ) (hp : p ∈ S) :
      ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤ 2 * (if p = 2 ∨ p = 3 then 2 else 1) := by
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    by_cases hs : p = 2 ∨ p = 3
    · rw [if_pos hs]
      have hr : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by rw [div_le_iff₀ hp1]; linarith
      have h0 : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := by positivity
      have hsq := pow_le_pow_left₀ h0 hr 2
      norm_num at hsq ⊢
      exact hsq
    · rw [if_neg hs]
      have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (show 4 ≤ p by omega)
      norm_num only [mul_one]
      rw [div_pow, div_le_iff₀ (sq_pos_of_pos hp1)]
      have hm := mul_nonneg (show 0 ≤ (p : ℝ) by linarith) (show 0 ≤ (p : ℝ) - 4 by linarith)
      nlinarith
  have hT : T ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    rcases (mem_filter.mp hp).2 with rfl | rfl <;> simp
  have hcard : T.card ≤ 2 := (card_le_card hT).trans_eq (by decide)
  have hpow : (2 : ℝ) ^ T.card ≤ (2 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) hcard
  have hprod : ((q : ℝ) / q.totient) ^ 2 ≤ (2 : ℝ) ^ S.card * (2 : ℝ) ^ T.card := by
    rw [MV75U1432.div_totient_eq_prod (by omega), ← prod_pow]
    calc
      _ ≤ ∏ p ∈ S, (2 : ℝ) * (if p = 2 ∨ p = 3 then 2 else 1) :=
        prod_le_prod₀ (fun p _ => sq_nonneg _) hlocal
      _ = _ := by
        rw [prod_mul_distrib, prod_const, prod_ite, prod_const, prod_const_one, mul_one]
  have htau := LeanLab.HeathBrown1985.two_pow_le_card_divisors q hq
  calc
    _ = ((q : ℝ) / q.totient) ^ 2 := (div_pow _ _ _).symm
    _ ≤ (2 : ℝ) ^ S.card * (2 : ℝ) ^ T.card := hprod
    _ ≤ (2 : ℝ) ^ S.card * 4 := mul_le_mul_of_nonneg_left (by norm_num at hpow; exact hpow) (by positivity)
    _ ≤ 4 * (q.divisors.card : ℝ) := by dsimp [S]; nlinarith

/-- P0082 pages361 and362, summand envelope for the Gamma2 tail.
It is bounded by four times gcd m q times tau q divided by q squared. -/
theorem tail_totient_kernel_le (q : ℕ) (hq : 1 ≤ q) (m : ℤ) :
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) ≤
      4 * (Int.gcd m q : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 := by
  let g := Int.gcd m q
  have hq0 : 0 < q := by omega
  have hg0 : 0 < g := by
    simpa only [g, Int.gcd_def, Int.natAbs_natCast] using Nat.gcd_pos_of_pos_right m.natAbs hq0
  have hgd : g ∣ q := by have h := Int.gcd_dvd_right m (q : ℤ); exact_mod_cast h
  have hquot : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq0 hgd) hg0
  have hφq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hφt : (0 : ℝ) < (q / g).totient := by exact_mod_cast Nat.totient_pos.mpr hquot
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hr := LeanLab.BhowmikGrimmelt2026.totient_divisor_ratio247 q g hq0 hgd hg0
  have hsq := totient_ratio_sq_le_divisors q hq
  have hscaled := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (g : ℝ) / (q : ℝ) ^ 2 by positivity)
  calc
    _ = ((q.totient : ℝ) / (q / g).totient) / (q.totient : ℝ) ^ 2 := by dsimp only [g]; field_simp
    _ ≤ (g : ℝ) / (q.totient : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hr (sq_nonneg _)
    _ ≤ _ := by
      convert hscaled using 1 <;> field_simp <;> ring

/-- P0082 page362 display19, a derived finite far tail bound for a fixed
nonzero integer m. The existing Heath Brown divisor tail supplies it. -/
theorem far_totient_kernel_sum_le (m : ℤ) (hm : m ≠ 0) (R M : ℕ) (hR : 1 ≤ R) :
    ∑ q ∈ Ioc R M, 1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) ≤
      4 * (6 + 2 * Real.log R) * (m.natAbs.divisors.card : ℝ) ^ 2 / R := by
  have hm1 : 1 ≤ m.natAbs := by have := Int.natAbs_pos.mpr hm; omega
  have hbound := LeanLab.HeathBrown1985.tail_gcd_le m.natAbs R M hm1 hR
  have hgcd (q : ℕ) : Int.gcd m q = Nat.gcd q m.natAbs := by simp [Int.gcd_def, Nat.gcd_comm]
  calc
    _ ≤ ∑ q ∈ Ioc R M, 4 * (Int.gcd m q : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 :=
      sum_le_sum (fun q hq => tail_totient_kernel_le q (by have := (mem_Ioc.mp hq).1; omega) m)
    _ = 4 * ∑ q ∈ Ioc R M, (Nat.gcd q m.natAbs : ℝ) * (q.divisors.card : ℝ) / (q : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      rw [hgcd]
      ring
    _ ≤ 4 * ((6 + 2 * Real.log R) * (m.natAbs.divisors.card : ℝ) ^ 2 / R) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
