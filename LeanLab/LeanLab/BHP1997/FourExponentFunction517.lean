/-
P0069, Section 5, page 51, display 5.17.
Supported bounded variation functions on the exponent grid.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentInnerVariation517
import LeanLab.BHP1997.FourExponentScales517

namespace LeanLab.BHP1997.LowerShortC165
open Classical MeasureTheory DecompC165d
open scoped BigOperators

/-- Page 51 display 5.17. Extending a supported exponent integral adds
only zero tails. -/
theorem four_exponent_function_extend (f : ℝ → ℝ)
    (hi : ∀ l r, IntervalIntegrable f volume l r)
    (hz : ∀ t, t ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ t → f t = 0)
    (l r : ℝ) (hl : l ≤ lowerFourGridReal 0) (hr : lowerFourGridReal 128 ≤ r) :
    (∫ t in l..r, f t) = ∫ t in lowerFourGridReal 0..lowerFourGridReal 128, f t := by
  have h0 : (∫ t in l..lowerFourGridReal 0, f t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le hl] at ht
    exact hz t (Or.inl ht.2)
  have h1 : (∫ t in lowerFourGridReal 128..r, f t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le hr] at ht
    exact hz t (Or.inr ht.1.le)
  have ha := intervalIntegral.integral_add_adjacent_intervals (hi l (lowerFourGridReal 0))
    (hi (lowerFourGridReal 0) (lowerFourGridReal 128))
  have hb := intervalIntegral.integral_add_adjacent_intervals (hi l (lowerFourGridReal 128))
    (hi (lowerFourGridReal 128) r)
  rw [h0, zero_add] at ha
  rw [h1, add_zero] at hb
  exact hb.symm.trans ha.symm

/-- Page 51 display 5.17. Every supported bounded variation exponent
function has a full-grid integer quadrature with a lower cutoff saving. -/
theorem four_exponent_function_full_grid (f : ℝ → ℝ)
    (hf : ∀ t, |f t| ≤ (10 : ℝ)^5)
    (hi : ∀ l r, IntervalIntegrable f volume l r)
    (hv : eVariationOn f (Set.Icc 0 1) ≤ ENNReal.ofReal 120100000)
    (hz : ∀ t, t ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ t → f t = 0)
    {Z : ℝ} (hZ : 1 < Z) (L N : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hN : (N : ℝ)+1 ≤ Z)
    (hlo : Real.log ((L : ℝ)+1) / Real.log Z ≤ lowerFourGridReal 0)
    (hhi : lowerFourGridReal 128 ≤ Real.log ((N : ℝ)+1) / Real.log Z) :
    |(∑ n ∈ Finset.Icc 1 N, f (Real.log (n : ℝ) / Real.log Z) / ((n : ℝ)*Real.log Z)) -
      ∫ t in lowerFourGridReal 0..lowerFourGridReal 128, f t| ≤
        200000000 / ((L : ℝ)*Real.log Z) := by
  let g : ℕ → ℝ := fun n => f (Real.log (n : ℝ) / Real.log Z) / ((n : ℝ)*Real.log Z)
  let l := Real.log ((L : ℝ)+1) / Real.log Z
  let r := Real.log ((N : ℝ)+1) / Real.log Z
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hNle : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
  have hl0 : 0 ≤ l := div_nonneg (Real.log_nonneg (by linarith)) hlog.le
  have hr1 : r ≤ 1 := (div_le_one hlog).mpr (Real.log_le_log (by linarith) hN)
  have hlr : l ≤ r := div_le_div_of_nonneg_right
    (Real.log_le_log (by linarith) (by linarith)) hlog.le
  have hsub : Set.Icc l r ⊆ Set.Icc (0 : ℝ) 1 := fun t ht => ⟨hl0.trans ht.1, ht.2.trans hr1⟩
  have hvar := (eVariationOn.mono f hsub).trans hv
  have hvr : (eVariationOn f (Set.Icc l r)).toReal ≤ 120100000 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
    norm_num at h
    exact h
  have hbv : BoundedVariationOn f (Set.Icc l r) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have hend : (L : ℝ)+((N-L : ℕ) : ℝ)+1 = (N : ℝ)+1 := by rw [Nat.cast_sub hLN]; ring
  have hq := four_exponent_log_bv_quadrature f hZ (by norm_num : (0 : ℝ) ≤ 10^5) L (N-L) hL
    (fun i _ => hf _) (by simpa only [hend] using hi l r) (by simpa only [hend] using hbv)
  rw [hend] at hq
  have hq' : |(∑ i ∈ Finset.range (N-L),
      f (Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z) /
        (((L : ℝ)+(i : ℝ)+1)*Real.log Z)) - ∫ t in l..r, f t| ≤
      200000000 / ((L : ℝ)*Real.log Z) := by
    exact hq.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hp : ∑ n ∈ Finset.Ioc 0 L, g n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hn0, hnL⟩ := Finset.mem_Ioc.mp hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hnlt : (n : ℝ) < (L : ℝ)+1 := by exact_mod_cast Nat.lt_succ_of_le hnL
    have hlt := (div_lt_div_iff_of_pos_right hlog).mpr (Real.log_lt_log hnreal hnlt)
    change f (Real.log (n : ℝ) / Real.log Z) / ((n : ℝ)*Real.log Z) = 0
    rw [hz _ (Or.inl (hlt.le.trans hlo)), zero_div]
  have hsum : (∑ n ∈ Finset.Icc 1 N, g n) = ∑ i ∈ Finset.range (N-L),
      f (Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z) /
        (((L : ℝ)+(i : ℝ)+1)*Real.log Z) := by
    have hs := Finset.sum_Ioc_consecutive g (Nat.zero_le L) hLN
    have heq0 : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hp, zero_add, heq0] at hs
    rw [← hs]
    have heq : Finset.Ioc L N = Finset.Ico (L+1) (N+1) := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [heq, Finset.sum_Ico_eq_sum_range, show N+1-(L+1) = N-L by omega]
    apply Finset.sum_congr rfl
    intro i _
    simp only [show L+1+i = L+i+1 by omega, g, Nat.cast_add, Nat.cast_one]
  have hext := four_exponent_function_extend f hi hz l r hlo hhi
  rw [hext] at hq'
  change |(∑ n ∈ Finset.Icc 1 N, g n) - _| ≤ _
  rw [hsum]
  exact hq'

/-- Page 51 display 5.17. A strict ordered exponent fibre adds only its
single equality-index term to the full-grid quadrature error. -/
theorem four_exponent_function_strict_grid (f : ℝ → ℝ)
    (hf : ∀ t, |f t| ≤ (10 : ℝ)^5)
    (hi : ∀ l r, IntervalIntegrable f volume l r)
    (hv : eVariationOn f (Set.Icc 0 1) ≤ ENNReal.ofReal 120100000)
    (hz : ∀ t, t ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ t → f t = 0)
    {Z : ℝ} (hZ : 1 < Z) (L N q : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hq : q ∈ Finset.Icc 1 N) (hN : (N : ℝ)+1 ≤ Z)
    (hlo : Real.log ((L : ℝ)+1) / Real.log Z ≤ lowerFourGridReal 0)
    (hhi : lowerFourGridReal 128 ≤ Real.log ((N : ℝ)+1) / Real.log Z)
    (horder : ∀ t, Real.log (q : ℝ) / Real.log Z < t → f t = 0) :
    |(∑ n ∈ Finset.Icc 1 N, if n < q then
        f (Real.log (n : ℝ) / Real.log Z) / ((n : ℝ)*Real.log Z) else 0) -
      ∫ t in lowerFourGridReal 0..lowerFourGridReal 128, f t| ≤
        200100000 / ((L : ℝ)*Real.log Z) := by
  let B := Finset.Icc 1 N
  let g := fun n : ℕ => f (Real.log (n : ℝ) / Real.log Z) / ((n : ℝ)*Real.log Z)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by have := (Finset.mem_Icc.mp hq).1; omega)
  have hzero : ∀ n ∈ B, q < n → g n = 0 := by
    intro n hn hqn
    have hlt := (div_lt_div_iff_of_pos_right hlog).mpr
      (Real.log_lt_log hq0 (by exact_mod_cast hqn : (q : ℝ) < (n : ℝ)))
    simp only [g, horder _ hlt, zero_div]
  have hs : (∑ n ∈ B, if n < q then g n else 0) = (∑ n ∈ B, g n)-g q := by
    have ha := Finset.sum_erase_add B g hq
    have hb := Finset.sum_erase_add B (fun n => if n < q then g n else 0) hq
    have he : (∑ n ∈ B.erase q, if n < q then g n else 0) = ∑ n ∈ B.erase q, g n := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hnq, hnB⟩ := Finset.mem_erase.mp hn
      by_cases h : n < q
      · simp only [if_pos h]
      · rw [if_neg h, hzero n hnB (by omega)]
    rw [he, if_neg (lt_irrefl q), add_zero] at hb
    linarith
  have hM : |g q| ≤ (10 : ℝ)^5 / ((L : ℝ)*Real.log Z) := by
    by_cases hqL : q ≤ L
    · have hlt := (div_lt_div_iff_of_pos_right hlog).mpr
        (Real.log_lt_log hq0 (by exact_mod_cast Nat.lt_succ_of_le hqL : (q : ℝ) < (L : ℝ)+1))
      simp only [g, hz _ (Or.inl (hlt.le.trans hlo)), zero_div, abs_zero]
      positivity
    · rw [show g q = f (Real.log (q : ℝ) / Real.log Z) / ((q : ℝ)*Real.log Z) from rfl,
        abs_div, abs_of_pos (mul_pos hq0 hlog)]
      calc _ ≤ (10 : ℝ)^5 / ((q : ℝ)*Real.log Z) :=
          div_le_div_of_nonneg_right (hf _) (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (show L ≤ q by omega)) hlog.le)
  have hfull := four_exponent_function_full_grid f hf hi hv hz hZ L N hL hLN hN hlo hhi
  change |(∑ n ∈ B, if n < q then g n else 0) - _| ≤ _
  rw [hs]
  calc _ = |((∑ n ∈ B, g n)-(∫ t in lowerFourGridReal 0..lowerFourGridReal 128, f t))-g q| := by
        congr 1; ring
    _ ≤ |(∑ n ∈ B, g n)-(∫ t in lowerFourGridReal 0..lowerFourGridReal 128, f t)|+|g q| := abs_sub _ _
    _ ≤ 200000000 / ((L : ℝ)*Real.log Z)+10^5 / ((L : ℝ)*Real.log Z) := add_le_add hfull hM
    _ = _ := by ring

#print axioms four_exponent_function_extend
#print axioms four_exponent_function_full_grid
#print axioms four_exponent_function_strict_grid
end LeanLab.BHP1997.LowerShortC165
