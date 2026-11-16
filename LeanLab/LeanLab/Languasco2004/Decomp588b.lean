/-
Jia 1996 page 283 display 60.
Source https://doi.org/10.4064/aa-77-3-207-287.
The triangular prime sum reduces to one reciprocal prime sum and its diagonal.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Reserve578
import LeanLab.Languasco2004.Integral565
import LeanLab.Languasco2004.Decomp588d

namespace LeanLab.Languasco2004.Decomp588b
open Real Finset intervalIntegral Source565 Reserve578 Decomp316c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 283 display 60 support: split a square sum into its two ordered triangles and diagonal. -/
theorem square_sum_triangle (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ s, f p) ^ 2 =
      2 * (∑ p ∈ s, ∑ q ∈ s.filter (fun q => q < p), f p * f q) + ∑ p ∈ s, (f p)^2 := by
  have hsplit : (∑ p ∈ s, f p)^2 =
      (∑ p ∈ s, ∑ q ∈ s, if q < p then f p * f q else 0) +
      (∑ p ∈ s, ∑ q ∈ s, if p < q then f p * f q else 0) +
      (∑ p ∈ s, ∑ q ∈ s, if p = q then f p * f q else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    simp_rw [← sum_add_distrib]
    rw [pow_two, sum_mul_sum]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    rcases lt_trichotomy p q with h | rfl | h
    · simp [h, h.not_gt, h.ne]
    · simp
    · simp [h, h.not_gt, h.ne']
  have hswap : (∑ p ∈ s, ∑ q ∈ s, if p < q then f p * f q else 0) =
      ∑ p ∈ s, ∑ q ∈ s, if q < p then f p * f q else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    simp only [mul_comm]
  have hdiag : (∑ p ∈ s, ∑ q ∈ s, if p = q then f p * f q else 0) =
      ∑ p ∈ s, (f p)^2 := by
    apply sum_congr rfl
    intro p hp
    simp [← eq_comm, hp, pow_two]
  rw [hswap, hdiag] at hsplit
  simp_rw [sum_filter]
  linarith

/-- Page 283 display 60 support: reciprocal primes on a power range with exact source endpoints. -/
def powerPrimes (Y a b : ℝ) : Finset ℕ :=
  (Ioc ⌊Y ^ a⌋₊ ⌊Y ^ b⌋₊).filter Nat.Prime

/-- Page 283 display 60 support: the power range membership has exact real endpoints. -/
theorem mem_powerPrimes {Y a b : ℝ} (hY : 0 ≤ Y) (p : ℕ) :
    p ∈ powerPrimes Y a b ↔ p.Prime ∧ Y ^ a < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ b := by
  simp only [powerPrimes, mem_filter, mem_Ioc, Nat.floor_lt (Real.rpow_nonneg hY a),
    Nat.le_floor_iff (Real.rpow_nonneg hY b)]
  tauto

/-- Page 283 display 60 support: the truncated p bound makes both recovery caps redundant. -/
theorem pair_caps {Y p q : ℝ} (hY : 1 < Y) (hp : 1 ≤ p) (hq : 0 ≤ q) (hqp : q < p)
    (hpB : p ≤ Y ^ (89 / 462 - 0.00000001 : ℝ)) :
    p ≤ Real.sqrt (2 * Y) ∧ q < Real.sqrt (2 * Y / p) ∧ p ≤ Y := by
  have hY0 : 0 ≤ Y := by linarith
  have hpow3 : p ^ 3 ≤ Y := by
    calc p ^ 3 ≤ (Y ^ (89 / 462 - 0.00000001 : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by linarith) hpB 3
      _ = Y ^ ((89 / 462 - 0.00000001 : ℝ) * 3) :=
          (Real.rpow_mul_natCast hY0 _ 3).symm
      _ ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num)
      _ = Y := Real.rpow_one _
  have hsq : p ^ 2 ≤ p ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hp)]
  have hpY : p ≤ Y := (by nlinarith [sq_nonneg (p - 1)] : p ≤ p ^ 2).trans (hsq.trans hpow3)
  refine ⟨(Real.le_sqrt (by linarith) (by positivity)).mpr (by linarith), ?_, hpY⟩
  apply (Real.lt_sqrt hq).mpr
  rw [lt_div_iff₀ (by linarith : 0 < p)]
  have hqq : q ^ 2 < p ^ 2 := by nlinarith
  have hmul := mul_lt_mul_of_pos_right hqq (by linarith : 0 < p)
  nlinarith

/-- Page 283 display 60 support: the selected clipped pair domain is exactly one prime triangle. -/
theorem pairDomain_eq_triangle {Y : ℝ} {n : ℕ} (hY : 1 < Y) (hn : 2 * Y ≤ (n : ℝ)) :
    pairDomain true Y n =
      ((powerPrimes Y (16 / 135) (89 / 462 - 0.00000001)).product
        (powerPrimes Y (16 / 135) (89 / 462 - 0.00000001))).filter
        (fun pq => pq.2 < pq.1) := by
  ext pq
  rcases pq with ⟨p, q⟩
  simp only [pairDomain, Finset.product_eq_sprod, mem_filter, mem_product, mem_range, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨⟨hpn, hqn⟩, hp, hpa, hpS, hq, hqa, hqp, hg, hi, hB⟩
    have hqp' : (q : ℝ) < p := lt_of_lt_of_le hqp (min_le_left _ _)
    have hpB := hB trivial
    have hqB := hqp'.le.trans hpB
    exact ⟨⟨(mem_powerPrimes (by linarith) p).mpr ⟨hp, hpa, hpB⟩,
      (mem_powerPrimes (by linarith) q).mpr ⟨hq, hqa, hqB⟩⟩, by exact_mod_cast hqp'⟩
  · rintro ⟨⟨hp, hq⟩, hqp⟩
    obtain ⟨hp, hpa, hpB⟩ := (mem_powerPrimes (by linarith) p).mp hp
    obtain ⟨hq, hqa, hqB⟩ := (mem_powerPrimes (by linarith) q).mp hq
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
    have hc := pair_caps hY hp1 (Nat.cast_nonneg q) hqp' hpB
    have hpN : p < n + 1 := by
      have : (p : ℝ) ≤ n := by linarith [hc.2.2]
      exact Nat.lt_succ_of_le (by exact_mod_cast this)
    have hqN : q < n + 1 := by omega
    have hregion : regionIndex Y p q = 1 := by
      apply (GroupSplit548.regionIndex_eq_iff (0 : Fin 69) Y p q hY hp.pos hq.pos).mpr
      norm_num [regionData]
      have hpB' : (p : ℝ) ≤ Y ^ (89 / 462 : ℝ) :=
        hpB.trans (Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num))
      exact ⟨hpa, hpB', hqa, by exact_mod_cast hqp'⟩
    refine ⟨⟨hpN, hqN⟩, hp, hpa, hc.1, hq, hqa, lt_min hqp' hc.2.1, ?_, ?_, fun _ => hpB⟩
    · simp [hregion, groupOf]
    · simp [hregion]

/-- LEAF. Jia page 283 display 60, the Mertens type reciprocal prime sum used by partial summation.
For fixed positive exponents a at most b, the reciprocal prime sum over Y^a less than p at most
Y^b tends to log of b over a. This is a single prime sum, with no rough count or pair sum. -/
theorem reciprocal_prime_power_limit (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Filter.Tendsto (fun Y : ℝ => ∑ p ∈ powerPrimes Y a b, (1 : ℝ) / p)
      Filter.atTop (nhds (log (b / a))) := by
  exact Decomp588d.reciprocal_power_limit a b ha hab

/-- Page 283 display 60 support: the source truncated integral is half a square logarithm. -/
theorem pair_coefficient_eq_square :
    pairCoefficient = (0.5612 * (135 / 16)) *
      (log ((89 / 462 - 0.00000001) / (16 / 135 : ℝ)) ^ 2 / 2) := by
  unfold pairCoefficient
  congr 1
  convert Integral565.integral_log_ratio (16 / 135) (89 / 462 - 0.00000001)
    (by norm_num) (by norm_num) using 1
  congr 1
  ext t
  congr 2
  ring

/-- Page 283 display 60 support: the reciprocal pair sum has its exact diagonal correction. -/
theorem pair_reciprocal_eq {Y : ℝ} {n : ℕ} (hY : 1 < Y) (hn : 2 * Y ≤ (n : ℝ)) :
    (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) =
      ((∑ p ∈ powerPrimes Y (16 / 135) (89 / 462 - 0.00000001), (1 : ℝ) / p)^2 -
        ∑ p ∈ powerPrimes Y (16 / 135) (89 / 462 - 0.00000001), ((1 : ℝ) / p)^2) / 2 := by
  have h := square_sum_triangle
    (powerPrimes Y (16 / 135) (89 / 462 - 0.00000001)) (fun p => (1 : ℝ) / p)
  rw [pairDomain_eq_triangle hY hn, sum_filter, Finset.product_eq_sprod, sum_product]
  simp_rw [sum_filter] at h
  simp only [one_div_mul_one_div] at h
  linarith

/-- Page 283 display 60 support: the diagonal is bounded by the reciprocal sum divided by Y^a. -/
theorem reciprocal_diagonal_le {Y a b : ℝ} (hY : 1 < Y) :
    (∑ p ∈ powerPrimes Y a b, ((1 : ℝ) / p)^2) ≤
      (∑ p ∈ powerPrimes Y a b, (1 : ℝ) / p) * (Y ^ a)⁻¹ := by
  rw [sum_mul]
  apply sum_le_sum
  intro p hp
  have hp' := (mem_powerPrimes (by linarith) p).mp hp
  have ha : 0 < Y ^ a := Real.rpow_pos_of_pos (by linarith) _
  have hi : (1 : ℝ) / p ≤ (Y ^ a)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha hp'.2.1.le
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (1 : ℝ) / p)

/-- Page 283 display 60 support: the diagonal contribution vanishes.
The single reciprocal prime power limit is proved in Decomp588d. -/
theorem reciprocal_diagonal_tendsto (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Filter.Tendsto (fun Y : ℝ => ∑ p ∈ powerPrimes Y a b, ((1 : ℝ) / p)^2)
      Filter.atTop (nhds 0) := by
  have hS := reciprocal_prime_power_limit a b ha hab
  have hI : Filter.Tendsto (fun Y : ℝ => (Y ^ a)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop ha)
  have hB := hS.mul hI
  simp only [mul_zero] at hB
  apply squeeze_zero' (Filter.Eventually.of_forall (fun Y => sum_nonneg (fun p _ => sq_nonneg _))) _ hB
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with Y hY
  exact reciprocal_diagonal_le hY

/-- Page 283 display 60: exact supplied reciprocal pair lower estimate.
The single Mertens type prime sum limit is proved in Decomp588d. No rough integer count is assumed. -/
theorem pair_prime_sum_from_mertens :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) → pairCoefficient - η ≤
        (0.5612 * (135 / 16)) *
          ∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
  let a : ℝ := 16 / 135
  let b : ℝ := 89 / 462 - 0.00000001
  have ha : 0 < a := by norm_num [a]
  have hab : a ≤ b := by norm_num [a, b]
  have hS := reciprocal_prime_power_limit a b ha hab
  have hD := reciprocal_diagonal_tendsto a b ha hab
  have hlim := ((hS.pow 2).sub hD).div_const 2
  have hlim' := hlim.const_mul (0.5612 * (135 / 16))
  simp only [sub_zero] at hlim'
  have hlimFinal : Filter.Tendsto (fun Y : ℝ => (0.5612 * (135 / 16)) *
      (((∑ p ∈ powerPrimes Y a b, (1 : ℝ) / p)^2 -
        ∑ p ∈ powerPrimes Y a b, ((1 : ℝ) / p)^2) / 2)) Filter.atTop (nhds pairCoefficient) := by
    simpa only [pair_coefficient_eq_square] using hlim'
  intro η hη
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp
    ((hlimFinal.eventually_const_le (show pairCoefficient - η < pairCoefficient by linarith)).and
      (Filter.eventually_gt_atTop (1 : ℝ)))
  refine ⟨Y₀, fun Y hY n hn => ?_⟩
  obtain ⟨hbound, hY1⟩ := hY₀ Y hY
  rw [pair_reciprocal_eq hY1 hn]
  exact hbound

#print axioms mem_powerPrimes
#print axioms pair_caps
#print axioms pairDomain_eq_triangle
#print axioms pair_reciprocal_eq
#print axioms reciprocal_diagonal_le
#print axioms reciprocal_diagonal_tendsto
#print axioms pair_prime_sum_from_mertens
#print axioms square_sum_triangle
#print axioms powerPrimes
#print axioms reciprocal_prime_power_limit
#print axioms pair_coefficient_eq_square
end
end LeanLab.Languasco2004.Decomp588b
