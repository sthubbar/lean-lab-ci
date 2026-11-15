/-
Jia 1996 page 283 display 60 and page 285 before display 64.
Source https://doi.org/10.4064/aa-77-3-207-287.
Explicit truncation reserve and normalization for the model estimates.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Numeric565
import LeanLab.Languasco2004.Source565

namespace LeanLab.Languasco2004.Reserve578
open Real Finset intervalIntegral Decomp279a Decomp316a Numeric565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 283 display 60: the constant lower model retains the printed exponent truncation. -/
def pairCoefficient : ℝ :=
  (0.5612 * (135 / 16)) *
    ∫ t in (16 / 135 : ℝ)..(89 / 462 - 0.00000001), log ((135 / 16) * t) / t

/-- Page 283 display 60: the truncated constant model still has half a micro unit of reserve.
This bounds the omitted endpoint strip, before any prime sum asymptotic is invoked. -/
theorem pair_coefficient_reserve : mainOne + 0.0000005 ≤ pairCoefficient := by
  let a : ℝ := 16 / 135
  let b : ℝ := 89 / 462
  let c : ℝ := b - 0.00000001
  let f : ℝ → ℝ := fun t => log ((135 / 16) * t) / t
  have hac : a ≤ c := by dsimp [a, b, c]; norm_num
  have hcb : c ≤ b := by dsimp [c]; linarith
  have hf : ContinuousOn f (Set.Icc a b) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by dsimp [a]; norm_num) ht.1
      exact (mul_pos (by norm_num : (0 : ℝ) < 135 / 16) ht0).ne'
    · fun_prop
    · intro t ht
      exact (lt_of_lt_of_le (by dsimp [a]; norm_num) ht.1).ne'
  have hiac : IntervalIntegrable f MeasureTheory.volume a c :=
    (hf.mono (Set.Icc_subset_Icc le_rfl hcb)).intervalIntegrable_of_Icc hac
  have hicb : IntervalIntegrable f MeasureTheory.volume c b :=
    (hf.mono (Set.Icc_subset_Icc hac le_rfl)).intervalIntegrable_of_Icc hcb
  have hsum := integral_add_adjacent_intervals hiac hicb
  have htail : (∫ t in c..b, f t) ≤ 9 * (b - c) := by
    have h := integral_mono_on hcb hicb (intervalIntegrable_const (c := (9 : ℝ)))
      (show ∀ t ∈ Set.Icc c b, f t ≤ 9 by
        intro t ht
        have hta : a ≤ t := hac.trans ht.1
        have ht0 : 0 < t := lt_of_lt_of_le (by dsimp [a]; norm_num) hta
        have hx : 0 < (135 / 16 : ℝ) * t := mul_pos (by norm_num) ht0
        have hl := Real.log_le_sub_one_of_pos hx
        apply (div_le_iff₀ ht0).mpr
        dsimp [a, b] at hta ht
        linarith [ht.2])
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  unfold mainOne pairCoefficient
  simp only [zero_add]
  change (0.5612 * (135 / 16)) * (∫ t in a..b, f t) - 0.000001 + 0.0000005 ≤
    (0.5612 * (135 / 16)) * (∫ t in a..c, f t)
  have hbc : b - c = 0.00000001 := by dsimp [c]; ring
  rw [hbc] at htail
  rw [← hsum]
  nlinarith only [htail]

/-- Pages 262 and 283: normalize an integer model lower estimate by the nonnegative singular factor. -/
theorem normalize_lower (N Y K M : ℝ) (n : ℕ) (hN : 1 ≤ N)
    (hM : K * (Y / log Y) ≤ M) :
    K * scale N Y n ≤ singular n / log N * M := by
  have h := mul_le_mul_of_nonneg_left hM
    (div_nonneg (singular_nonneg n) (Real.log_nonneg hN))
  convert h using 1 <;> simp only [scale, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- Pages 262 and 284: the same normalization preserves an integer model upper estimate. -/
theorem normalize_upper (N Y K M : ℝ) (n : ℕ) (hN : 1 ≤ N)
    (hM : M ≤ K * (Y / log Y)) :
    singular n / log N * M ≤ K * scale N Y n := by
  have h := mul_le_mul_of_nonneg_left hM
    (div_nonneg (singular_nonneg n) (Real.log_nonneg hN))
  convert h using 1 <;> simp only [scale, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- Pages 208 and 283: every large window integer exceeds twice the localized model length.
The same threshold also makes localization exceed any fixed model threshold. -/
theorem localization_model_domain (ε T : ℝ) (hε : 0 < ε) (he : ε < 1 / 100) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      1 ≤ N ∧ 1 ≤ localization N ε ∧ T ≤ localization N ε ∧
        ∀ n ∈ window N ε, 2 * localization N ε ≤ (n : ℝ) := by
  have hp : 0 < 7 / 12 + ε := by linarith
  have hq : 0 < 1 - (7 / 12 + ε) := by linarith
  obtain ⟨N1, h1⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop T))
  obtain ⟨N2, h2⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hq).eventually (Filter.eventually_ge_atTop (2 : ℝ)))
  refine ⟨max 2 (max N1 N2), ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hY : 1 ≤ localization N ε := Real.one_le_rpow hN1 hp.le
  refine ⟨hN1, hY, h1 N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)), ?_⟩
  have hcap := mul_le_mul_of_nonneg_right
    (h2 N ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    (Real.rpow_nonneg (by linarith : 0 ≤ N) (7 / 12 + ε))
  have hid : N ^ (1 - (7 / 12 + ε)) * N ^ (7 / 12 + ε) = N := by
    rw [← Real.rpow_add (by linarith : 0 < N)]
    have heq : (1 - (7 / 12 + ε)) + (7 / 12 + ε) = 1 := by ring
    rw [heq, Real.rpow_one]
  rw [hid] at hcap
  intro n hn
  have hnN : N < (n : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hn).1).1
  exact hcap.trans hnN.le

#print axioms pairCoefficient
#print axioms pair_coefficient_reserve
#print axioms normalize_lower
#print axioms normalize_upper
#print axioms localization_model_domain
end
end LeanLab.Languasco2004.Reserve578
