/-
Split of the leaf `delay_even_tsum_le` of SPLIT_delay_partial_sums, BJS arXiv 2207.09452v6.
For 2 at most s at most 4 and even n, display 16 gives s f_n of s as the integral of f_{n-1} of
t minus 1 over t above s. Cut at t equal to 4: the part above 4 is 4 f_n of 4 by display 16
again, and on s below t at most 4 the odd function f_{n-1} at t minus 1 in the range 1 to 3 is
3 f_{n-1} of 3 over t minus 1 by display 17, or 3 minus t plus 1 over t minus 1 when n is 2 by
display 15. Summing over even n, the even series at s is controlled by the odd series at 3 and
the even series at 4, and the bound 1 minus f of s of display 14, with f of s equal to
2 e^gamma log of s minus 1 over s by display 8, reduces exactly to its value at s equal to 4
together with the odd value F of 3 equal to 2 e^gamma over 3.

Inputs: the one new LEAF below, the value at s equal to 4, the LEAF
`delay_odd_tsum_at_three_le` of SPLIT_delay_odd_tsum_le,
and the existing summability leaves `delay_odd_summable` and `delay_even_summable` of
SPLIT_delay_partial_sums, used as stated. This file adds no definition and changes no existing
file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_delay_odd_tsum_le

namespace LeanLab.BS2022GRH.Decomp327a
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d MeasureTheory
noncomputable section

/-- 1 over t minus 1 is integrable on s below t at most 4 for s at least 2. -/
theorem integrableOn_one_div_sub_one (s : ℝ) (hs2 : 2 ≤ s) :
    IntegrableOn (fun t : ℝ => 1 / (t - 1)) (Set.Ioc s 4) := by
  have hc : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.Icc s 4) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro x hx
    have h0 : (0 : ℝ) < x - 1 := by linarith [hx.1]
    simpa using h0.ne'
  exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/-- The integral of 1 over t minus 1 over s below t at most 4 is log 3 minus log of s minus 1,
used in BJS display 16 on the lower piece. -/
theorem integral_Ioc_one_div_sub_one (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    ∫ t in Set.Ioc s 4, 1 / (t - 1) = log 3 - log (s - 1) := by
  rw [← intervalIntegral.integral_of_le hs4]
  have h := intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x) (a := s) (b := 4) 1
  beta_reduce at h
  rw [h, integral_one_div_of_pos (by linarith) (by norm_num), Real.log_div (by norm_num)
    (by linarith)]
  norm_num

/-- LEAF: the even delay series at the single point s equal to 4 sums to at most 1 minus f of 4,
BJS display 14 cited from Nathanson Theorem 9.4, with f of 4 equal to 2 e^gamma log 3 over 4 by
display 8. Class HARD, the value of the Rosser lower sieve function at 4, a citation wall.
Faithful piece: it is the s equal to 4 instance, and the range 2 at most s at most 4 is
recovered from it by displays 15 to 17 in `delay_even_tsum_le_split`. -/
theorem delay_even_tsum_at_four_le :
    (∑' n : ℕ, if 0 < n ∧ n % 2 = 0 then delayTerm n 4 else 0) ≤
      1 - 2 * exp eulerMascheroniConstant * log 3 / 4 := by
  sorry

/-- The term f_2, BJS displays 15 and 16: for 2 at most s at most 4,
s f_2 of s is the integral over s below t at most 4 of 4 minus t over t minus 1, which is
3 times log 3 minus log of s minus 1, minus 4 minus s. One explicit integral. -/
theorem delayTerm_two_eq (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    s * delayTerm 2 s = 3 * (log 3 - log (s - 1)) - (4 - s) := by
  have hs0 : 0 < s := by linarith
  rw [delayTerm, if_neg (by norm_num), mul_div_cancel₀ _ hs0.ne']
  simp only [delayTerm]
  set f : ℝ → ℝ := fun t => max (3 - (t - 1)) 0 / (t - 1) with hf
  have hzero : ∀ t ∈ Set.Ioi (4 : ℝ), f t = 0 := by
    intro t ht
    have := Set.mem_Ioi.mp ht
    simp only [hf, max_eq_right (by linarith : 3 - (t - 1) ≤ 0), zero_div]
  have heq : Set.EqOn f (fun t => 3 * (1 / (t - 1)) - 1) (Set.Ioc s 4) := by
    intro t ht
    have h1 := ht.1; have h2 := ht.2
    simp only [hf, max_eq_left (by linarith : (0 : ℝ) ≤ 3 - (t - 1))]
    have : t - 1 ≠ 0 := by linarith
    field_simp
  have hI := integrableOn_one_div_sub_one s hs2
  have hg : IntegrableOn (fun t : ℝ => 3 * (1 / (t - 1)) - 1) (Set.Ioc s 4) :=
    (hI.const_mul 3).sub (integrableOn_const (hs := measure_Ioc_lt_top.ne))
  have hInt1 : IntegrableOn f (Set.Ioc s 4) := hg.congr_fun heq.symm measurableSet_Ioc
  have hInt2 : IntegrableOn f (Set.Ioi 4) :=
    (integrableOn_zero).congr_fun (fun t ht => (hzero t ht).symm) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hs4, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    hInt1 hInt2, setIntegral_eq_zero_of_forall_eq_zero hzero, add_zero,
    setIntegral_congr_fun measurableSet_Ioc heq, integral_sub (hI.const_mul 3)
    (integrableOn_const (hs := measure_Ioc_lt_top.ne)), integral_const_mul, integral_Ioc_one_div_sub_one s hs2 hs4,
    setIntegral_const, Real.volume_real_Ioc_of_le hs4]
  simp

/-- One even term from n at least 4, BJS display 16 cut at t equal to 4 with display 17
on the lower piece: for 2 at most s at most 4, s f_n of s is at most
3 f_{n-1} of 3 times log 3 minus log of s minus 1, plus 4 f_n of 4. In the paper this is an
equality; the inequality form also covers a non integrable integrand, where the Lean integral is
zero. Proved by splitting one improper integral and integrating 1 over t minus 1. -/
theorem delayTerm_even_step_le (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) (s : ℝ) (hs2 : 2 ≤ s)
    (hs4 : s ≤ 4) :
    s * delayTerm n s ≤
      3 * delayTerm (n - 1) 3 * (log 3 - log (s - 1)) + 4 * delayTerm n 4 := by
  have hs0 : 0 < s := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 + 1 := ⟨n - 4, by omega⟩
  have hodd : (k + 3) % 2 = 1 := by omega
  have hd3 : 0 ≤ delayTerm (k + 3) 3 :=
    delayTerm_nonneg (k + 3) 3 (by rw [if_pos hodd]; norm_num)
  have hd4 : 0 ≤ delayTerm (k + 3 + 1) 4 :=
    delayTerm_nonneg (k + 3 + 1) 4 (by rw [if_neg (by omega)]; norm_num)
  have hL0 : 0 ≤ log 3 - log (s - 1) := by
    rw [sub_nonneg]; exact Real.log_le_log (by linarith) (by linarith)
  have hsub : k + 3 + 1 - 1 = k + 3 := by omega
  rw [hsub]
  have hunf : ∀ x : ℝ, delayTerm (k + 3 + 1) x =
      (∫ t in Set.Ioi x, delayTerm (k + 3) (t - 1)) / x := by
    intro x
    rw [show k + 3 + 1 = (k + 2) + 2 by omega, delayTerm, if_neg (by omega)]
  set f : ℝ → ℝ := fun t => delayTerm (k + 3) (t - 1) with hf
  have h4 : 4 * delayTerm (k + 3 + 1) 4 = ∫ t in Set.Ioi 4, f t := by
    rw [hunf]; field_simp
  rw [hunf, mul_div_cancel₀ _ hs0.ne', h4]
  by_cases hint : IntegrableOn f (Set.Ioi s)
  · have heq : Set.EqOn f (fun t => delayTerm (k + 3) 3 * 3 * (1 / (t - 1))) (Set.Ioc s 4) := by
      intro t ht
      have h1 := ht.1; have h2 := ht.2
      simp only [hf]
      rw [show k + 3 = (k + 1) + 2 by omega, delayTerm_odd_flat (k + 1) (t - 1) (by linarith)
        (by linarith) (by omega)]
      field_simp
    rw [← Set.Ioc_union_Ioi_eq_Ioi hs4, setIntegral_union Set.Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hint.mono_set (Set.Ioc_subset_Ioi_self))
      (hint.mono_set (Set.Ioi_subset_Ioi hs4)), setIntegral_congr_fun measurableSet_Ioc heq,
      integral_const_mul, integral_Ioc_one_div_sub_one s hs2 hs4]
    apply le_of_eq; ring
  · rw [integral_undef hint]
    have : 0 ≤ ∫ t in Set.Ioi 4, f t := by
      apply setIntegral_nonneg measurableSet_Ioi
      intro t ht
      have := Set.mem_Ioi.mp ht
      exact delayTerm_nonneg (k + 3) (t - 1) (by rw [if_pos hodd]; linarith)
    positivity

/-- The leaf `delay_even_tsum_le` verbatim. CONDITIONAL ON delay_even_tsum_at_four_le,
delay_odd_tsum_at_three_le, and the existing leaves
delay_odd_summable at 3 and delay_even_summable at s and at 4. -/
theorem delay_even_tsum_le_split (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    (∑' n : ℕ, if 0 < n ∧ n % 2 = 0 then delayTerm n s else 0) ≤
      1 - 2 * exp eulerMascheroniConstant * log (s - 1) / s := by
  have hs0 : 0 < s := by linarith
  set e : ℝ := exp eulerMascheroniConstant with he_def
  set L : ℝ := log 3 - log (s - 1) with hL_def
  have hL0 : 0 ≤ L := by
    rw [hL_def, sub_nonneg]
    exact Real.log_le_log (by linarith) (by linarith)
  set E : ℝ → ℕ → ℝ := fun x n => if 0 < n ∧ n % 2 = 0 then delayTerm n x else 0 with hE_def
  set O : ℕ → ℝ := fun n => if n % 2 = 1 then delayTerm n 3 else 0 with hO_def
  set O' : ℕ → ℝ := fun n => if 0 < n ∧ n % 2 = 0 then delayTerm (n - 1) 3 else 0 with hO'_def
  have hOsum : Summable O := delay_odd_summable 3 (by norm_num) le_rfl
  have hO'shift : (fun n => O' (n + 1)) = O := by
    funext n
    simp only [hO'_def, hO_def, Nat.add_sub_cancel]
    by_cases h : n % 2 = 1
    · rw [if_pos ⟨Nat.succ_pos n, by omega⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hO'sum : Summable O' := by
    rw [← summable_nat_add_iff 1, hO'shift]; exact hOsum
  have hO'tsum : ∑' n, O' n = ∑' n, O n := by
    rw [hO'sum.tsum_eq_zero_add, hO'shift]; simp [hO'_def]
  have hEs : Summable (E s) := delay_even_summable s hs2 hs4
  have hE4 : Summable (E 4) := delay_even_summable 4 (by norm_num) le_rfl
  set c : ℝ := (3 * L - (4 - s)) / s with hc
  set B : ℕ → ℝ := fun n => 1 / s * (3 * L * O' n + 4 * E 4 n) + (if n = 2 then c else 0)
    with hB_def
  have hB : HasSum B (1 / s * (3 * L * (∑' n, O' n) + 4 * (∑' n, E 4 n)) + c) :=
    (((hO'sum.hasSum.mul_left (3 * L)).add (hE4.hasSum.mul_left 4)).mul_left (1 / s)).add
      (hasSum_ite_eq 2 c)
  have hterm : ∀ n, E s n ≤ B n := by
    intro n
    simp only [hE_def, hB_def, hO'_def]
    by_cases hn2 : n = 2
    · subst hn2
      have h1 : delayTerm 1 3 = 0 := by simp [delayTerm]
      have h2 : delayTerm 2 4 = 0 := delayTerm_eq_zero_of_endpoint 2 4 (by norm_num)
      have h3 := delayTerm_two_eq s hs2 hs4
      have hc2 : (0 : ℕ) < 2 ∧ 2 % 2 = 0 := by norm_num
      rw [if_pos hc2, if_pos hc2, if_pos hc2, if_pos rfl, show (2 : ℕ) - 1 = 1 from rfl, h1, h2,
        hc, hL_def, ← h3, mul_div_cancel_left₀ _ hs0.ne']
      simp
    · rw [if_neg hn2, add_zero]
      by_cases hev : 0 < n ∧ n % 2 = 0
      · rw [if_pos hev, if_pos hev, if_pos hev]
        have hn4 : 4 ≤ n := by omega
        have h := delayTerm_even_step_le n hn4 hev.2 s hs2 hs4
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs0, hL_def]
        linarith
      · rw [if_neg hev, if_neg hev, if_neg hev]; simp
  have hle := hasSum_le hterm hEs.hasSum hB
  have hT3 : ∑' n, O n ≤ 2 * e / 3 - 1 := delay_odd_tsum_at_three_le
  have hT4 : ∑' n, E 4 n ≤ 1 - 2 * e * log 3 / 4 := delay_even_tsum_at_four_le
  rw [hO'tsum] at hle
  have hmul : L * (∑' n, O n) ≤ L * (2 * e / 3 - 1) := mul_le_mul_of_nonneg_left hT3 hL0
  have key : 1 / s * (3 * L * (∑' n, O n) + 4 * (∑' n, E 4 n)) + c ≤
      1 - 2 * e * log (s - 1) / s := by
    rw [hc, one_div, ← div_eq_inv_mul, ← add_div, div_le_iff₀ hs0]
    have : (1 - 2 * e * log (s - 1) / s) * s = s - 2 * e * log (s - 1) := by
      field_simp
    rw [this, hL_def] at *
    nlinarith
  exact le_trans hle key

end

end LeanLab.BS2022GRH.Decomp327a

#print axioms LeanLab.BS2022GRH.Decomp327a.integrableOn_one_div_sub_one
#print axioms LeanLab.BS2022GRH.Decomp327a.integral_Ioc_one_div_sub_one
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_tsum_at_four_le
#print axioms LeanLab.BS2022GRH.Decomp327a.delayTerm_two_eq
#print axioms LeanLab.BS2022GRH.Decomp327a.delayTerm_even_step_le
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_tsum_le_split
