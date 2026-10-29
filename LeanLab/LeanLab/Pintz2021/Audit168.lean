import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.PrincipalSeriesTask99
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
Zero frequency audit for P0054 page 6 displays 2.5 to 2.7.
The sealed natural frequency range includes zero.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Audit168

open Finset Filter Topology State1581 CharacterSumsTask53 PrincipalSeriesTask99

attribute [local instance] Classical.propDecidable

/-- The pole induces the principal character at every modulus. -/
theorem lift_pole (q : ℕ) : lift pole q = 1 := by
  unfold lift pole
  simp only [Nat.one_dvd, ↓reduceDIte]
  exact map_one _

/-- The sealed finite sum at a principal character is the earlier finite template. -/
theorem cRam_one (q : ℕ) (m : ℤ) :
    cRam q 1 m = characterSum (principalValue q) q m := by
  unfold cRam characterSum
  apply sum_congr rfl
  intro h _
  congr 1
  by_cases hc : h.Coprime q
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime h q).mpr hc)]
    simp [principalValue, hc]
  · rw [MulChar.map_nonunit _ (fun hu => hc ((ZMod.isUnit_iff_coprime h q).mp hu))]
    simp [principalValue, hc]

/-- The pole coefficient at zero frequency is Mobius squared over totient. -/
theorem coefficient_zero (q : ℕ) :
    cCoef pole pole q 0 =
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) : ℂ) := by
  simp only [cCoef, lift_pole, inv_one, one_mul, Nat.cast_zero, neg_zero]
  rw [cRam_one, principal_zero]
  have ht : tau q 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    exact (cRam_one q 1).trans (gauss_principal q)
  rw [ht]
  push_cast
  by_cases hq : (Nat.totient q : ℂ) = 0
  · simp [hq]
  · field_simp

/-- The zero frequency coefficient sequence is not summable. -/
theorem zero_not_summable :
    ¬ Summable (fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ)) := by
  intro hs
  apply not_summable_one_div_on_primes
  have hdom : ∀ n : ℕ,
      ({p : ℕ | p.Prime}.indicator (fun n => (1 : ℝ) / n)) n ≤
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ) := by
    intro n
    by_cases hn : n.Prime
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hn, ↓reduceIte,
        ArithmeticFunction.moebius_apply_prime hn, Int.cast_neg, Int.cast_one, neg_one_sq]
      exact one_div_le_one_div_of_le
        (by exact_mod_cast Nat.totient_pos.mpr hn.pos)
        (by exact_mod_cast Nat.totient_le n)
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hn, ↓reduceIte]
      positivity
  exact hs.of_nonneg_of_le
    (fun n => Set.indicator_nonneg (fun _ _ => by positivity) n) hdom

/-- The real part of the sealed pole partial sum at zero. -/
theorem partial_zero_re (Q : ℕ) :
    (singPartial pole pole 0 Q).re =
      ∑ q ∈ Icc 1 Q,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) := by
  simp [singPartial, show pole.r = 1 from rfl, coefficient_zero,
    Complex.re_sum, pow_two, Complex.mul_re]

/-- No complex number is the limit of the sealed zero frequency pole series. -/
theorem zero_no_limit (s : ℂ) :
    ¬ Tendsto (singPartial pole pole 0) atTop (𝓝 s) := by
  intro h
  have hr := Complex.continuous_re.tendsto s |>.comp h
  simp only [Function.comp_def, partial_zero_re] at hr
  obtain ⟨B, hB⟩ := hr.bddAbove_range
  apply zero_not_summable
  refine summable_of_sum_range_le (c := B)
    (fun q => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
  intro N
  have heq : Ico 1 (N + 1) = Icc 1 N := by
    ext q
    simp only [mem_Ico, mem_Icc]
    omega
  have hz : ((ArithmeticFunction.moebius 0 : ℤ) : ℝ) ^ 2 /
      (Nat.totient 0 : ℝ) = 0 := by simp
  have he := sum_range_eq_add_Ico
    (fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ))
    (Nat.succ_pos N)
  rw [heq, hz, zero_add] at he
  calc
    _ ≤ ∑ q ∈ range (N + 1),
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) := by
      rw [sum_range_succ]
      exact le_add_of_nonneg_right (by positivity)
    _ = _ := he
    _ ≤ B := hB ⟨N, rfl⟩

/-- The sealed Theorem1_220 is false because its convergence clause includes zero. -/
theorem sealed_target_false : ¬ Theorem1_220 := by
  rintro ⟨ε0, hε0, h⟩
  let ε := min (ε0 / 2) (1 / 9)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε0' : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε4 : ε < 4 / 9 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨c, H0, C, X0, hc, hdata⟩ := h ε hε hε0'
  obtain ⟨H, X, P0, hHyp, _⟩ := thm1Hyp_inhabited hε hε4 H0 X0
  obtain ⟨P, _, _, _, Sg, hconv, _⟩ := hdata H X P0 hHyp
  exact zero_no_limit (Sg pole pole 0)
    (hconv pole (pole_mem_excSet _ _ _ _) pole (pole_mem_excSet _ _ _ _) 0)

end LeanLab.Pintz2021.Audit168

#print axioms LeanLab.Pintz2021.Audit168.lift_pole
#print axioms LeanLab.Pintz2021.Audit168.cRam_one
#print axioms LeanLab.Pintz2021.Audit168.coefficient_zero

#print axioms LeanLab.Pintz2021.Audit168.zero_not_summable
#print axioms LeanLab.Pintz2021.Audit168.partial_zero_re
#print axioms LeanLab.Pintz2021.Audit168.zero_no_limit
#print axioms LeanLab.Pintz2021.Audit168.sealed_target_false
