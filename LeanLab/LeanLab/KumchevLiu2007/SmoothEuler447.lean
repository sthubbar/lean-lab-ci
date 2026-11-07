/-
Finite smooth Euler comparison for the conservative coefficient majorant.
Source https://arxiv.org/abs/0801.0130 page 14 below display 50.
The local factor is the geometric series for one weight 64 per distinct prime.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438d
import Mathlib.NumberTheory.EulerProduct.Basic

namespace LeanLab.KumchevLiu2007.SmoothEuler447
open Real Task129b Task438d
open scoped BigOperators

/-- Page 14 below display 50, derived numerical reciprocal weight. -/
noncomputable def weightedReciprocal (s : ℝ) (q : ℕ) : ℝ :=
  coefficientMajorant q / (q : ℝ) ^ s

/-- Page 14 below display 50. The reciprocal weight is nonnegative. -/
theorem weightedReciprocal_nonneg (s : ℝ) (q : ℕ) : 0 ≤ weightedReciprocal s q := by
  unfold weightedReciprocal coefficientMajorant
  positivity

/-- Page 14 below display 50. The reciprocal weight equals one at modulus one. -/
theorem weightedReciprocal_one (s : ℝ) : weightedReciprocal s 1 = 1 := by
  simp [weightedReciprocal, coefficientMajorant]

/-- Page 14 below display 50. The reciprocal weight is multiplicative
at coprime moduli, including the zero cases. -/
theorem weightedReciprocal_mul (s : ℝ) (hs : 0 < s) (a b : ℕ) (hab : a.Coprime b) :
    weightedReciprocal s (a * b) = weightedReciprocal s a * weightedReciprocal s b := by
  by_cases ha : a = 0
  · subst a
    simp [weightedReciprocal, Real.zero_rpow hs.ne']
  by_cases hb : b = 0
  · subst b
    simp [weightedReciprocal, Real.zero_rpow hs.ne']
  have hM : coefficientMajorant (a * b) = coefficientMajorant a * coefficientMajorant b := by
    simp only [coefficientMajorant, Nat.primeFactors_mul ha hb,
      Finset.prod_union hab.disjoint_primeFactors]
  simp only [weightedReciprocal, hM, Nat.cast_mul, Real.mul_rpow (by positivity : (0 : ℝ) ≤ a)
    (by positivity : (0 : ℝ) ≤ b)]
  ring

/-- Page 14 below display 50. The reciprocal prime power series has
sum 1 plus 64 divided by p to s minus 1 for positive s. -/
theorem weighted_prime_power_hasSum (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℕ => weightedReciprocal s (p ^ k))
      (1 + 64 / ((p : ℝ) ^ s - 1)) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hps : 1 < (p : ℝ) ^ s := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hs
  let r := ((p : ℝ) ^ s)⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hps
  have hterm (k : ℕ) : weightedReciprocal s (p ^ k) =
      64 * r ^ k - (if k = 0 then 63 else 0) := by
    by_cases hk : k = 0
    · subst k
      norm_num [weightedReciprocal_one]
    · have hpow : (((p ^ k : ℕ) : ℝ)) ^ s = ((p : ℝ) ^ s) ^ k := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
          mul_comm (k : ℝ) s, Real.rpow_mul hp0.le, Real.rpow_natCast]
      simp only [weightedReciprocal, coefficientMajorant, Nat.primeFactors_prime_pow hk hp,
        Finset.prod_singleton, hpow, hk, ite_false, sub_zero]
      dsimp [r]
      rw [inv_pow, div_eq_mul_inv]
  have hh := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (64 : ℝ)).sub
    (hasSum_ite_eq (0 : ℕ) (63 : ℝ))
  have he : 64 * (1 - r)⁻¹ - 63 = 1 + 64 / ((p : ℝ) ^ s - 1) := by
    dsimp [r]
    have hpos : 0 < (p : ℝ) ^ s := by positivity
    field_simp [ne_of_gt hpos, ne_of_gt (sub_pos.mpr hps)]
    <;> ring
  rw [he] at hh
  simpa only [← hterm] using hh

/-- Page 14 below display 50, exact Task447c finite Euler comparison.
Mathlib factors the full sum over numbers supported on the finite prime set.
The desired finite sum is a nonnegative sub-sum of that series. -/
theorem smooth_moment_euler_bound (Q : ℝ) (M : ℕ) (hQ : 0 < Q) (s : ℝ) (hs : 0 < s) :
    (∑ q ∈ Finset.Icc 1 M,
      smoothWeight q Q * coefficientMajorant q / (q : ℝ) ^ s) ≤
      ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ s - 1)) := by
  classical
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
  let f := weightedReciprocal s
  have hsum (p : ℕ) (hp : p.Prime) : Summable (fun k : ℕ => ‖f (p ^ k)‖) := by
    change Summable (fun k : ℕ => ‖weightedReciprocal s (p ^ k)‖)
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (weightedReciprocal_nonneg s _)]
    exact (weighted_prime_power_hasSum p hp s hs).summable
  have H := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (weightedReciprocal_one s) (fun {a b} hab => weightedReciprocal_mul s hs a b hab)
    (fun {p} hp => hsum p hp) S).2
  have hfilter : S.filter Nat.Prime = S := by
    exact Finset.filter_eq_self.mpr (fun p hp => (Finset.mem_filter.mp hp).2)
  rw [hfilter] at H
  have hprod : (∏ p ∈ S, ∑' k : ℕ, f (p ^ k)) =
      ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact (weighted_prime_power_hasSum p (Finset.mem_filter.mp hp).2 s hs).tsum_eq
  rw [hprod] at H
  let T := (Finset.Icc 1 M).filter (fun q => ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q)
  have hT (q : ℕ) (hq : q ∈ T) : q ∈ Nat.factoredNumbers S := by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpq
    have hpQ := (Finset.mem_filter.mp hq).2 p hp hpq
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr (Nat.le_floor hpQ)), hp⟩
  have he : (∑ q ∈ Finset.Icc 1 M,
      smoothWeight q Q * coefficientMajorant q / (q : ℝ) ^ s) = ∑ q ∈ T, f q := by
    simp only [smoothWeight, ite_mul, one_mul, zero_mul, ite_div, zero_div]
    rw [← Finset.sum_filter]
    rfl
  rw [he]
  change (∑ q ∈ T, f q) ≤ ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))
  rw [← Finset.sum_subtype_of_mem f hT]
  exact (Summable.sum_le_tsum (T.subtype (fun q => q ∈ Nat.factoredNumbers S))
    (fun q hq => weightedReciprocal_nonneg s q) H.summable).trans_eq H.tsum_eq

#print axioms weightedReciprocal_nonneg
#print axioms weightedReciprocal_one
#print axioms weightedReciprocal_mul
#print axioms weighted_prime_power_hasSum
#print axioms smooth_moment_euler_bound
end LeanLab.KumchevLiu2007.SmoothEuler447
