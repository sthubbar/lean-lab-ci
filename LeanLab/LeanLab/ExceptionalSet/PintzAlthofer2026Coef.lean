/-
# Pintz and Althöfer 2026, (4.18): the model coefficient is large, explicit and assembled

Unit U-1140, T2 FRONTIER, idea I-0080, run 20261020T0103Z-16649.

arXiv 2610.15559v1 Section 4.4, (4.14) to (4.18): the major arc model with weights
w_q = μ(q)² c_q(n)/φ(q)², q ≤ P, has n-th coefficient v(n) with |v(n)| ≫ X for even n in the
window. Here, assembled from the lab's pieces, for every even n ≥ 2, X > 0 and P ≥ 2:

  ‖vTrunc X P P w n‖ ≥ n e^{−n/X} (2 ∏_{2<p≤P} (1 − 1/(p−1)²) − 12 τ(n)²/√P)
                        − X/(2π²P) · C e (1 + log P/log 2) τ(n)² (1 + log P),       `coef418`

with an absolute C, from
* `trunc_eq`: Σ_{q≤P} w_q = Σ_{d | P#} w_d − Σ_{d | P#, d > P} w_d, since a squarefree q ≤ P
  divides P#, `sqfree_dvd_primorial`;
* `sing_trunc_ge`, PintzAlthofer2026Euler: Σ_{d | P#} w_d ≥ 2 ∏_{2<p≤P} (1 − 1/(p−1)²);
* `tail_sum`, PintzAlthofer2026Tail: |Σ_{d | P#, d > P} w_d| ≤ 12 τ(n)²/√P;
* `vTrunc_approx`, PintzAlthofer2026Beta, the β integrals cut at |β| ≤ P/(qX);
* `sum415`, PintzAlthofer2026Sum415, for Σ_{q≤P} q|w_q|.

With P = X^c and τ(n) ≪ X^η the bracket is at least 2C₂ − o(1) > 1.32 and the error is
X^{1−c+3η}, so |v(n)| ≥ c' X for n in (X/2, X]: the lower half of `BesselInput`'s coefficient
condition. The upper half, Lemma 4's zero sum, stays cited. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Beta
import LeanLab.ExceptionalSet.PintzAlthofer2026Euler
import LeanLab.ExceptionalSet.PintzAlthofer2026Tail
import LeanLab.ExceptionalSet.PintzAlthofer2026Sum415

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Coef

open Finset Real LeanLab.Routes.R5060
open scoped ArithmeticFunction.Moebius

/-- A squarefree `q ≤ P` divides the primorial of `P`. -/
lemma sqfree_dvd_primorial {q P : ℕ} (hq : Squarefree q) (hqP : q ≤ P) : q ∣ primorial P := by
  have hq0 : q ≠ 0 := hq.ne_zero
  rw [← Nat.prod_primeFactors_of_squarefree hq, primorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.dvd_of_mem_primeFactors hp)
  simp only [mem_filter, mem_range]
  exact ⟨by omega, hpp⟩

/-- `bS n q = 0` when `q` is not squarefree. -/
lemma bS_eq_zero {n q : ℕ} (hq : 1 ≤ q) (h : ¬ Squarefree q) : bS n q = 0 := by
  rw [bS_apply hq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp

/-- `|bS n q| ≤ |c_q(n)|/φ(q)²`. -/
lemma abs_bS_le (n q : ℕ) (hq : 1 ≤ q) :
    |bS n q| ≤ |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 := by
  rw [bS_apply hq, abs_div, abs_mul, abs_pow]
  have hμ : |(μ q : ℝ)| ^ 2 ≤ 1 := by
    have : |(μ q : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := q)
      exact_mod_cast h
    nlinarith [abs_nonneg (μ q : ℝ)]
  have hφ : 0 ≤ |(Nat.totient q : ℝ) ^ 2| := abs_nonneg _
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ) ^ 2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [abs_nonneg (LeanLab.HeathBrown1985.ramanujan q n)]

/-- The truncation identity: Σ_{q≤P} bS = Σ_{d | P#} bS − Σ_{d | P#, d > P} bS. -/
lemma trunc_eq (n P : ℕ) :
    ∑ q ∈ Icc 1 P, bS n q = ∑ d ∈ (primorial P).divisors, bS n d -
      ∑ d ∈ (primorial P).divisors.filter (P < ·), bS n d := by
  have hsplit := sum_filter_add_sum_filter_not (primorial P).divisors (P < ·) (fun d => bS n d)
  have hsmall : ∑ d ∈ (primorial P).divisors.filter (fun d => ¬ P < d), bS n d =
      ∑ q ∈ Icc 1 P, bS n q := by
    apply sum_subset
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors, not_lt] at hd
      exact mem_Icc.2 ⟨Nat.pos_of_dvd_of_pos hd.1.1 (primorial_pos P), hd.2⟩
    · intro q hq hnot
      have hq' := mem_Icc.1 hq
      by_contra hne
      apply hnot
      have hsq : Squarefree q := by
        by_contra hs; exact hne (bS_eq_zero hq'.1 hs)
      simp only [mem_filter, Nat.mem_divisors, not_lt]
      exact ⟨⟨sqfree_dvd_primorial hsq hq'.2, (primorial_pos P).ne'⟩, hq'.2⟩
  linarith

/-- **(4.18), explicit**: the model coefficient is large. -/
theorem coef418 : ∃ C : ℝ, 0 < C ∧ ∀ (n P : ℕ) (X : ℝ), Even n → 2 ≤ n → 2 ≤ P → 0 < X →
    (n * Real.exp (-n / X)) * (2 * ∏ p ∈ (Nat.primesLE P).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1) ^ 2)
        - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P)
      - X / (2 * π ^ 2 * P) * (C * (Real.exp 1 * (1 + Real.log P / Real.log 2)) *
          (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P))
      ≤ ‖LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc X P P
          (fun q => ((bS n q : ℝ) : ℂ)) n‖ := by
  obtain ⟨C, hC, h415⟩ := LeanLab.ExceptionalSet.PintzAlthofer2026Sum415.sum415
  refine ⟨C, hC, fun n P X hn hn2 hP hX => ?_⟩
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set τ := (n.divisors.card : ℝ)
  set w : ℕ → ℂ := fun q => ((bS n q : ℝ) : ℂ)
  set A := n * Real.exp (-n / X)
  have hA : 0 ≤ A := by positivity
  -- the sum of the weights
  have hsum : ∑ q ∈ Icc 1 P, w q = ((∑ q ∈ Icc 1 P, bS n q : ℝ) : ℂ) := by
    simp [w]
  have hlow : 2 * ∏ p ∈ (Nat.primesLE P).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1) ^ 2)
      - 12 * τ ^ 2 / Real.sqrt P ≤ ∑ q ∈ Icc 1 P, bS n q := by
    rw [trunc_eq]
    have h1 := LeanLab.ExceptionalSet.PintzAlthofer2026Euler.sing_trunc_ge (N := n) hn hP
    have h2 : |∑ d ∈ (primorial P).divisors.filter (P < ·), bS n d| ≤ 12 * τ ^ 2 / Real.sqrt P := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum fun d hd => abs_bS_le n d ?_).trans ?_
      · simp only [mem_filter, Nat.mem_divisors] at hd
        exact Nat.pos_of_dvd_of_pos hd.1.1 (primorial_pos P)
      · exact LeanLab.ExceptionalSet.PintzAlthofer2026Tail.tail_sum n (by omega) hPr _ (by
          intro q hq; simp only [mem_filter] at hq; exact_mod_cast hq.2)
    have := (abs_le.1 h2).2
    linarith
  -- the error
  have herr : ∑ q ∈ Icc 1 P, ‖w q‖ * (q * X / (2 * π ^ 2 * P)) ≤
      X / (2 * π ^ 2 * P) * (C * (Real.exp 1 * (1 + Real.log P / Real.log 2)) * τ ^ 2 *
        (1 + Real.log P)) := by
    have hpos : 0 ≤ X / (2 * π ^ 2 * P) := by positivity
    calc ∑ q ∈ Icc 1 P, ‖w q‖ * (q * X / (2 * π ^ 2 * P))
        = X / (2 * π ^ 2 * P) * ∑ q ∈ Icc 1 P, (q : ℝ) * |bS n q| := by
          rw [mul_sum]; refine sum_congr rfl fun q _ => ?_
          simp only [w, Complex.norm_real, Real.norm_eq_abs]; ring
      _ ≤ X / (2 * π ^ 2 * P) * ∑ q ∈ Icc 1 P,
            (q : ℝ) * |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hpos
          refine sum_le_sum fun q hq => ?_
          have hq1 := (mem_Icc.1 hq).1
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (abs_bS_le n q hq1) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (h415 n P (by omega)) hpos
  have happrox := LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc_approx hX hPr hnr P w
  -- combine
  have hmain : ‖((A : ℝ) : ℂ) * ∑ q ∈ Icc 1 P, w q‖ = A * |∑ q ∈ Icc 1 P, bS n q| := by
    rw [hsum, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hA]
  have htri := norm_sub_norm_le (((A : ℝ) : ℂ) * ∑ q ∈ Icc 1 P, w q)
    (((A : ℝ) : ℂ) * ∑ q ∈ Icc 1 P, w q -
      LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc X P P w n)
  rw [sub_sub_cancel] at htri
  rw [norm_sub_rev] at htri
  have hA2 : A * (2 * ∏ p ∈ (Nat.primesLE P).filter (2 < ·), (1 - 1 / ((p : ℝ) - 1) ^ 2)
      - 12 * τ ^ 2 / Real.sqrt P) ≤ A * |∑ q ∈ Icc 1 P, bS n q| :=
    mul_le_mul_of_nonneg_left (hlow.trans (le_abs_self _)) hA
  have hAeq : ((n * Real.exp (-n / X) : ℝ) : ℂ) = ((A : ℝ) : ℂ) := rfl
  rw [hAeq] at happrox
  linarith

end LeanLab.ExceptionalSet.PintzAlthofer2026Coef
