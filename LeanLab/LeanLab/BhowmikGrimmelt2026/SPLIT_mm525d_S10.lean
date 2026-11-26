/-
Burst S10 step mm525d, BhowmikGrimmelt2026, stacked on step mm525c. Source: Bhowmik and
Grimmelt 2026, arXiv 2607.27282, Proposition 4.1 and the proof of Lemma 4.2 on page 16, and
display 7.8 on page 27.

What the paper's own argument proves for the parent of the two S10 units, with the cited
Vinogradov Vaughan bound at log power four, display 4.8, in place of the open QUESTION 2
input at power two:

* `ssum_partial_log4_S10d` PROVED: the minor arc bound for every partial sum of S up to X,
  from `minor_dirichlet84`, `vaughan_small_denominator84` and `vaughan_large_denominator84`.
* `prime_minor_multi_log9_S10d` PROVED: the statement of `prime_minor_multi_525` with log X
  to the ninth in place of the fifth, by the chain of step mm525c. This is a variant, not the
  unit statement: it shows the power nine that the displayed proof of Lemma 4.2 gives, also
  for the N dependent smoothed family, with no open input.

No new sorry. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_mm525c_S10

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction NNReal

attribute [local instance] Classical.propDecidable

/-- Page 16, proof of Lemma 4.2, with Proposition 4.1: off the major arcs of length X, every
partial sum of S up to X is at most 48600 times the minor arc size times log X to the fourth. -/
theorem ssum_partial_log4_S10d :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ), 2 ≤ X → ∀ R : ℝ, 1 ≤ R → R ≤ X →
      ∀ (m : ℕ), m ≤ X → ∀ α : ℝ, ¬ MajorArc X R α →
        ‖Ssum m α‖ ≤ C * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) *
          Real.log X ^ 4 := by
  refine ⟨48600, by norm_num, ?_⟩
  intro X hX R hR hRX m hmX α hminor
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hR0 : 0 < R := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hrhs : 0 ≤ (48600 : ℝ) * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) *
      Real.log X ^ 4 := by positivity
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hz : Ssum m α = 0 := by
      interval_cases m <;> simp [Ssum]
    rw [hz, norm_zero]
    exact hrhs
  obtain ⟨a, q, hq, hcop, hRq, hqR, happ⟩ := minor_dirichlet84 hX0 hR0 hRX hminor
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmXr : (m : ℝ) ≤ X := by exact_mod_cast hmX
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
  have hsR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
  have hfirst : (m : ℝ) / Real.sqrt q ≤ (X : ℝ) / Real.sqrt R := by
    calc (m : ℝ) / Real.sqrt q ≤ (X : ℝ) / Real.sqrt q :=
          div_le_div_of_nonneg_right hmXr (Real.sqrt_nonneg _)
      _ ≤ (X : ℝ) / Real.sqrt R :=
          div_le_div_of_nonneg_left hX0.le hsR (Real.sqrt_le_sqrt hRq.le)
  have hmid : (m : ℝ) ^ (4 / 5 : ℝ) ≤ (X : ℝ) ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow hm0.le hmXr (by norm_num)
  have hlast : Real.sqrt ((m : ℝ) * q) ≤ (X : ℝ) / Real.sqrt R := by
    have hprod : (m : ℝ) * q ≤ ((X : ℝ) / Real.sqrt R) ^ 2 := by
      have hqr : (q : ℝ) * R ≤ X := (le_div_iff₀ hR0).mp hqR
      rw [div_pow, hsR2, le_div_iff₀ hR0]
      have h1 : (m : ℝ) * q * R ≤ (X : ℝ) * (q * R) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hmXr (by positivity)
      nlinarith only [h1, mul_le_mul_of_nonneg_left hqr hX0.le]
    exact (Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq (by positivity))
  have hlogm : Real.log m ≤ Real.log X := Real.log_le_log hm0 hmXr
  have hlogm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hexplicit : ‖Ssum m α‖ ≤ 24300 * ((m : ℝ) / Real.sqrt q +
      (m : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt ((m : ℝ) * q)) * Real.log m ^ 4 := by
    rcases le_total q m with hqm | hmq
    · exact vaughan_small_denominator84 hm2 hq hcop happ hqm
    · exact vaughan_large_denominator84 hm2 hmq α
  calc
    _ ≤ 24300 * ((m : ℝ) / Real.sqrt q + (m : ℝ) ^ (4 / 5 : ℝ) +
        Real.sqrt ((m : ℝ) * q)) * Real.log m ^ 4 := hexplicit
    _ ≤ 24300 * (2 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ))) *
        Real.log X ^ 4 := by
      gcongr
      have hpow : 0 ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by positivity
      linarith
    _ = _ := by ring

/-- Display 7.8 page 27 with the log power that the displayed proof of Lemma 4.2 page 16
gives: the statement of `prime_minor_multi_525` with log X to the ninth, PROVED. -/
theorem prime_minor_multi_log9_S10d {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α))‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 9 := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  obtain ⟨C₀, hC₀, h₀⟩ := ssum_partial_log4_S10d
  obtain ⟨K, hK, hfamK⟩ := prime_family_S10c hϕ
  refine ⟨2 * K * ((L : ℝ) * (C₀ + 8)) ^ 2, by positivity, ?_⟩
  intro X hX _hR2
  set R : ℝ := (X : ℝ) ^ ϑ with hRdef
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  set A : ℝ := (X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hlog2 : 0 ≤ Real.log X ^ 2 := by positivity
  have hX45 : (X : ℝ) ^ (4 / 5 : ℝ) ≤ A := by
    have : 0 ≤ (X : ℝ) / Real.sqrt R := by positivity
    linarith
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else 1
  have hW : Measurable W :=
    measurable_const.ite (measurableSet_majorArc84 X R) measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ (1 : ℝ) := by
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  set U : ℝ := (L : ℝ) * ((C₀ + 8) * A * Real.log X ^ 4) with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 →
      ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ U := by
    intro n hn α hne
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W, hh])
    have hBn : 0 ≤ (C₀ + 8) * A * Real.log X ^ 4 := by positivity
    apply leaf_prime_parts_feed1122 hϕ hL hn hBn
    intro m hmn
    have hmX : m ≤ X := hmn.trans hn
    have hS := h₀ X hX R hR1 hRX m hmX α hm
    have hD := nonprime_partial_S10b hX hmX α
    have htri : ‖∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime),
        (vonMangoldt k : ℂ) * ee (α * k)‖ ≤
        ‖Ssum m α‖ + ‖Ssum m α - ∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime),
          (vonMangoldt k : ℂ) * ee (α * k)‖ := by
      have := norm_sub_le (Ssum m α) (Ssum m α -
        ∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime), (vonMangoldt k : ℂ) * ee (α * k))
      simpa using this
    have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
      have h2 : Real.log 2 ≤ Real.log X :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hX)
      linarith [Real.log_two_gt_d9]
    have hl24 : Real.log X ^ 2 ≤ 4 * Real.log X ^ 4 := by
      have hsq : (1 / 4 : ℝ) ≤ Real.log X ^ 2 := by nlinarith
      nlinarith
    have hD' : 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 ≤ 8 * A * Real.log X ^ 4 := by
      have h1 : 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 ≤ 2 * A * Real.log X ^ 2 := by
        gcongr
      have h2 : 2 * A * Real.log X ^ 2 ≤ 2 * A * (4 * Real.log X ^ 4) :=
        mul_le_mul_of_nonneg_left hl24 (by positivity)
      linarith
    have hexp : (C₀ + 8) * A * Real.log X ^ 4 =
        C₀ * A * Real.log X ^ 4 + 8 * A * Real.log X ^ 4 := by ring
    linarith
  have hfam := hfamK X hX W hW 1 U (by norm_num) hU0 hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1,
          (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
            ee (-(N * α))) =
      ∫ α in (0 : ℝ)..1,
          if MajorArc X R α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α _
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  simp_rw [heq] at hfam
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hsq : A ^ 2 ≤ 2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2, hAdef]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hpi := split_leaf_power_identity X hX ϑ
  calc
    _ ≤ K * 1 ^ 2 * U ^ 2 * X * Real.log X := hfam
    _ = K * ((L : ℝ) * (C₀ + 8)) ^ 2 * A ^ 2 * X * Real.log X ^ 9 := by
      rw [hUdef]; ring
    _ ≤ K * ((L : ℝ) * (C₀ + 8)) ^ 2 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 9 := by
      gcongr
    _ = 2 * K * ((L : ℝ) * (C₀ + 8)) ^ 2 *
        (((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * (X : ℝ)) *
          Real.log X ^ 9 := by
      rw [hRdef]; ring
    _ = _ := by
      rw [hpi, hRdef]; ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.ssum_partial_log4_S10d
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_log9_S10d
