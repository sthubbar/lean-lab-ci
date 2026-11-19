/-
Jia 1996 pages 261 and 262, supporting the model counts on page 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Reuse the lab rough density theorem with its fixed positive power cutoff.
The full uniform Lemma 21 and the four target leaves are not asserted here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Buchstab578
import LeanLab.BHP1997.RoughDensity517e
import LeanLab.Languasco2004.Sieve565
import LeanLab.Languasco2004.Decomp578e
namespace LeanLab.Languasco2004.ModelCount583
open Real Filter Finset Buchstab578
noncomputable section

/-- Page 261 display 40: extend the constructed source solution by zero below one.
This auxiliary convention is used by the lab rough density interface. -/
def sourceBuchstab (u : ℝ) : ℝ := if u < 1 then 0 else buchstab u

/-- Page 261 display 40: the zero extension satisfies the lab differential equation interface.
Continuity is required only on the original domain from one onward. -/
theorem sourceBuchstab_isBuchstab :
    LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab sourceBuchstab := by
  refine ⟨buchstab_continuous.continuousOn.congr ?_, ?_, ?_⟩
  · intro u hu
    simp only [sourceBuchstab, ite_eq_right (not_lt.mpr (Set.mem_Ici.mp hu))]
  · intro u hu1 hu2
    simpa only [sourceBuchstab, ite_eq_right (not_lt.mpr hu1)] using
      buchstab_initial u hu1 hu2
  · intro u hu
    have he : (fun v : ℝ => v * sourceBuchstab v) =ᶠ[nhds u]
        (fun v : ℝ => v * buchstab v) := by
      filter_upwards [eventually_gt_nhds (by linarith : (1 : ℝ) < u)] with v hv
      simp only [sourceBuchstab, ite_eq_right (not_lt.mpr hv.le)]
    have hd := (buchstab_weight_derivative u hu).congr_of_eventuallyEq he
    simpa only [sourceBuchstab, ite_eq_right (by linarith : ¬ u - 1 < 1)] using hd

/-- Page 261 support: the chosen auxiliary extension is zero below the source domain. -/
theorem sourceBuchstab_zeroBelowOne :
    LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne sourceBuchstab := by
  intro u hu
  exact ite_eq_left hu

/-- Page 262 Lemma 21 support: the constructed solution supplies the lab rough density input.
The cutoff remains at least a fixed positive power of the ambient bound.
This reuses BHP1997.RoughDensity517e and does not supply the full uniform Lemma 21. -/
theorem rough_density_actual (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Ioc a b, (LeanLab.BHP1997.Task308.roughIndicator n z -
            sourceBuchstab (log n / log z) / log z)| ≤
          C * b * log X ^ (-A) := by
  exact LeanLab.BHP1997.LowerShortC165.rough_interval_density sourceBuchstab
    sourceBuchstab_isBuchstab sourceBuchstab_zeroBelowOne hc A hA

/-- Page 262 definition of S of E and z: the lab rough indicator sum equals
the ordinary rough sieve cardinality at a natural cutoff. No distribution estimate occurs. -/
theorem rough_indicator_sum_eq_sieved_card (s : Finset ℕ) (z : ℕ) :
    (∑ n ∈ s, LeanLab.BHP1997.Task308.roughIndicator n z) =
      ((Sieve565.sieved s 1 (z : ℝ)).card : ℝ) := by
  classical
  rw [show Sieve565.sieved s 1 (z : ℝ) =
      s.filter (fun n => n = 1 ∨ z ≤ n.minFac) from ?_]
  · simp only [LeanLab.BHP1997.Task308.roughIndicator, Finset.sum_boole]
  · ext n
    simp only [Sieve565.sieved, mem_filter]
    apply and_congr_right
    intro hn
    constructor
    · intro h
      apply Nat.le_minFac.mpr
      intro p hp hpn
      by_contra hlt
      exact h p hp (by exact_mod_cast (lt_of_not_ge hlt)) hp.not_dvd_one hpn
    · intro h p hp hpz hp1 hpn
      have hrough := (LeanLab.BHP1997.Task308.rough_indicator_support n z).mp
        (by simp only [LeanLab.BHP1997.Task308.roughIndicator, ite_eq_left h])
      exact hrough p hp (by exact_mod_cast hpz) hpn

/-- Pages 261 and 262 Lemma 20 part iii, supporting the page 285 pair and triple models.
Above the fourth power of the natural cutoff, ordinary rough counts lie between
the constants 0.5612 and 0.5617 times interval cardinality divided by the cutoff logarithm,
with the unchanged bounded power density error. No full Lemma 21 premise is used. -/
theorem rough_count_four (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      2 ≤ z → ∀ a b : ℕ, 1 ≤ a → z ^ 4 ≤ a → (b : ℝ) ≤ X →
        (0.5612 * ((Ioc a b).card : ℝ) / log z - C * b * log X ^ (-A) ≤
          ((Sieve565.sieved (Ioc a b) 1 (z : ℝ)).card : ℝ)) ∧
        (((Sieve565.sieved (Ioc a b) 1 (z : ℝ)).card : ℝ) ≤
          0.5617 * ((Ioc a b).card : ℝ) / log z + C * b * log X ^ (-A)) := by
  obtain ⟨C, hC, hD⟩ := rough_density_actual c A hc hA
  refine ⟨C, hC, ?_⟩
  intro X hX z hz hz2 a b ha hza hb
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (by omega : 1 < z)
  have hlz : 0 < log z := Real.log_pos hz1
  have hpoint : ∀ n ∈ Ioc a b,
      0.5612 ≤ sourceBuchstab (log n / log z) ∧
        sourceBuchstab (log n / log z) ≤ 0.5617 := by
    intro n hn
    have hzn : z ^ 4 ≤ n := hza.trans (mem_Ioc.mp hn).1.le
    have hznR : (z : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hzn
    have hlog := Real.log_le_log (pow_pos hz0 4) hznR
    rw [Real.log_pow] at hlog
    have hu : (4 : ℝ) ≤ log n / log z := by
      rw [le_div_iff₀ hlz]
      simpa only [Nat.cast_ofNat] using hlog
    have hg := Decomp578e.global_four_from_grid (log n / log z) hu
    simpa only [sourceBuchstab, ite_eq_right (by linarith : ¬ log n / log z < 1)] using hg
  have hL := sum_le_sum (s := Ioc a b) (fun n hn =>
    div_le_div_of_nonneg_right (hpoint n hn).1 hlz.le)
  have hU := sum_le_sum (s := Ioc a b) (fun n hn =>
    div_le_div_of_nonneg_right (hpoint n hn).2 hlz.le)
  simp only [sum_const, nsmul_eq_mul] at hL hU
  have hL' : 0.5612 * ((Ioc a b).card : ℝ) / log z ≤
      ∑ n ∈ Ioc a b, sourceBuchstab (log n / log z) / log z := by
    convert hL using 1 <;> ring
  have hU' : (∑ n ∈ Ioc a b, sourceBuchstab (log n / log z) / log z) ≤
      0.5617 * ((Ioc a b).card : ℝ) / log z := by
    convert hU using 1 <;> ring
  have hd := hD X hX z hz a b ha hb
  rw [sum_sub_distrib, rough_indicator_sum_eq_sieved_card] at hd
  obtain ⟨hdL, hdU⟩ := abs_le.mp hd
  constructor <;> linarith

/-- Pages 261 and 262 Lemma 20 part ii, supporting the page 285 triple model.
Above the third power of the natural cutoff, the rough count has the constant 0.5644
upper bound with the unchanged bounded power density error. -/
theorem rough_count_three_upper (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      2 ≤ z → ∀ a b : ℕ, 1 ≤ a → z ^ 3 ≤ a → (b : ℝ) ≤ X →
        ((Sieve565.sieved (Ioc a b) 1 (z : ℝ)).card : ℝ) ≤
          0.5644 * ((Ioc a b).card : ℝ) / log z + C * b * log X ^ (-A) := by
  obtain ⟨C, hC, hD⟩ := rough_density_actual c A hc hA
  refine ⟨C, hC, ?_⟩
  intro X hX z hz hz2 a b ha hza hb
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (by omega : 1 < z)
  have hlz : 0 < log z := Real.log_pos hz1
  have hpoint : ∀ n ∈ Ioc a b,
      sourceBuchstab (log n / log z) ≤ 0.5644 := by
    intro n hn
    have hzn : z ^ 3 ≤ n := hza.trans (mem_Ioc.mp hn).1.le
    have hznR : (z : ℝ) ^ 3 ≤ (n : ℝ) := by exact_mod_cast hzn
    have hlog := Real.log_le_log (pow_pos hz0 3) hznR
    rw [Real.log_pow] at hlog
    have hu : (3 : ℝ) ≤ log n / log z := by
      rw [le_div_iff₀ hlz]
      simpa only [Nat.cast_ofNat] using hlog
    have hg := (Decomp578e.global_three_from_grid (log n / log z) hu).2
    simpa only [sourceBuchstab, ite_eq_right (by linarith : ¬ log n / log z < 1)] using hg
  have hU := sum_le_sum (s := Ioc a b) (fun n hn =>
    div_le_div_of_nonneg_right (hpoint n hn) hlz.le)
  simp only [sum_const, nsmul_eq_mul] at hU
  have hU' : (∑ n ∈ Ioc a b, sourceBuchstab (log n / log z) / log z) ≤
      0.5644 * ((Ioc a b).card : ℝ) / log z := by
    convert hU using 1 <;> ring
  have hd := hD X hX z hz a b ha hb
  rw [sum_sub_distrib, rough_indicator_sum_eq_sieved_card] at hd
  have hdU := (abs_le.mp hd).2
  linarith

#print axioms sourceBuchstab
#print axioms sourceBuchstab_isBuchstab
#print axioms sourceBuchstab_zeroBelowOne
#print axioms rough_density_actual
#print axioms rough_indicator_sum_eq_sieved_card
#print axioms rough_count_four
#print axioms rough_count_three_upper
end
end LeanLab.Languasco2004.ModelCount583
