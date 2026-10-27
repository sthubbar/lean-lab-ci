import LeanLab.Pintz2021.TranslatedTask53
import LeanLab.Pintz2021.CutoffTask53

/-!
P0054 Lemma 2, author copy pages 14 and 15, display 4.9.
The finite estimates of task53 are completed by a uniform parameter choice.
The proof uses proved LPZ2007 arithmetic, not the cited Pintz theorem.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Lemma2Task99

open Finset Filter Topology
open DivisorSumTask53 TranslatedTask53 CutoffTask53

/-- The exact existing Lemma2 predicate, with no cited analytic input. -/
theorem lemma2_proved : Lemma2 := by
  intro η hη
  let δ : ℝ := η / (12 * C0)
  have hC := Applications.C0_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨D₁, hD₁⟩ :=
    (tendsto_order.1 (tendsto_sum_nat_add LeanLab.LPZ2007.seriesTerm)).2 δ hδ
      |>.exists_forall_of_atTop
  let D := max D₁ 4
  have hD : 4 ≤ D := le_max_right _ _
  have htail : ∑' k, LeanLab.LPZ2007.seriesTerm (k + (D + 1)) ≤ δ :=
    (hD₁ (D + 1) (by dsimp [D]; omega)).le
  let N := ⌈Real.exp 27 * Real.log D / δ⌉₊
  let M := max ⌈(6 * Real.exp 27 / δ) ^ 2 + 1⌉₊ 4
  refine ⟨max ((2 : ℝ) ^ N) ((2 : ℝ) ^ M), ?_⟩
  intro X m q hm hq _hsq hlarge
  have hqbig : (2 : ℝ) ^ N < q :=
    (le_max_left _ _).trans_lt (hlarge.trans_le (min_le_left _ _))
  have hXbig : (2 : ℝ) ^ M < X :=
    (le_max_right _ _).trans_lt (hlarge.trans_le (min_le_right _ _))
  have hq0 : 0 < q := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    exact_mod_cast hp.trans hqbig
  have hqpow : 2 ^ N ≤ q := by exact_mod_cast hqbig.le
  have hNlog : N ≤ Nat.log 2 q := Nat.le_log_of_pow_le (by norm_num) hqpow
  have hxi : (Real.exp 27 * Real.log D / δ) ≤ LeanLab.LPZ2007.xi q := by
    have hn : N ≤ LeanLab.LPZ2007.xi q :=
      hNlog.trans (LeanLab.LPZ2007.log_lt_xi hq hq0).le
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hxipos : (0 : ℝ) < LeanLab.LPZ2007.xi q := by
    exact_mod_cast (LeanLab.LPZ2007.xi_odd hq hq0).1
  have hsmall : Real.exp 27 * Real.log D / LeanLab.LPZ2007.xi q ≤ δ := by
    apply (div_le_iff₀ hxipos).mpr
    have hh := (div_le_iff₀ hδ).mp hxi
    nlinarith
  have hM4 : 4 ≤ M := le_max_right _ _
  have hX16 : 16 ≤ X := by
    have hp : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ M :=
      pow_le_pow_right₀ (by norm_num) hM4
    norm_num at hp
    linarith
  have hX1 : 1 ≤ X := by linarith
  have hlogM : (M : ℝ) ≤ Real.logb 2 X := by
    calc
      (M : ℝ) = Real.logb 2 ((2 : ℝ) ^ M) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
      _ ≤ Real.logb 2 X :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hXbig.le
  have hceilM : (⌈(6 * Real.exp 27 / δ) ^ 2 + 1⌉₊ : ℝ) ≤ M := by
    exact_mod_cast (le_max_left _ _ : ⌈(6 * Real.exp 27 / δ) ^ 2 + 1⌉₊ ≤ M)
  have hscale : (6 * Real.exp 27 / δ) ^ 2 + 1 ≤ Real.logb 2 X :=
    (Nat.le_ceil _).trans (hceilM.trans hlogM)
  have hb := lemma2_sum_le_of_parameters m q ⌊Lnu X⌋₊ D hX1 hm
    (floor_Lnu_le_logb hX1) hq hq0 hD hδ hsmall htail hscale
  have hnorm : 6 * C0 * δ = η / 2 := by dsimp [δ]; field_simp; ring
  rw [hnorm] at hb
  exact hb.trans (by nlinarith [(Lnu_bounds hX16).1])

/-- The hypotheses allow a nonempty positive sum above every threshold. -/
theorem nonempty_instance (C : ℝ) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ Squarefree q ∧
      C < min (q : ℝ) ((q + 2 : ℕ) : ℝ) ∧
      1 ∈ eligibleExponents (q + 2) q ⌊Lnu ((q + 2 : ℕ) : ℝ)⌋₊ ∧
      0 < Sing ((q + 2) - 2 ^ 1) := by
  obtain ⟨q, hqbound, hprime⟩ := Nat.exists_infinite_primes (⌈max C 16⌉₊ + 1)
  have hqC : max C 16 < (q : ℝ) := by
    have hc := Nat.le_ceil (max C 16)
    have hqr : (⌈max C 16⌉₊ : ℝ) + 1 ≤ q := by exact_mod_cast hqbound
    linarith
  have hq16 : (16 : ℝ) < q := (le_max_right _ _).trans_lt hqC
  have hq2 : q ≠ 2 := by intro h; subst q; norm_num at hq16
  have hX16 : (16 : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hlog4 : 4 ≤ Real.logb 2 ((q + 2 : ℕ) : ℝ) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).mpr
    convert hX16 using 1 <;> norm_num
  have hcut : 1 ≤ Lnu ((q + 2 : ℕ) : ℝ) := by
    have := (Lnu_bounds hX16).1
    linarith
  refine ⟨q, hprime, hprime.odd_of_ne_two hq2, hprime.squarefree, ?_, ?_,
    Applications.Sing_pos _⟩
  · apply lt_min ((le_max_left _ _).trans_lt hqC)
    have h := (le_max_left _ _).trans_lt hqC
    push_cast
    linarith
  · simp only [eligibleExponents, mem_filter, mem_Icc]
    exact ⟨⟨le_rfl, Nat.le_floor (by simpa using hcut)⟩, by norm_num; omega, by simp⟩

end LeanLab.Pintz2021.Lemma2Task99

#print axioms LeanLab.Pintz2021.Lemma2Task99.lemma2_proved

#print axioms LeanLab.Pintz2021.Lemma2Task99.nonempty_instance
