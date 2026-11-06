/-
Uniform numerical Euler product bound for the weighted smooth moment.
Source https://arxiv.org/abs/0801.0130 page 14 below display 50.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Rankin447
import LeanLab.PNTSieve.MertensUpper

namespace LeanLab.KumchevLiu2007.EulerProduct447
open Real
open scoped BigOperators

/-- Page 14 below display 50, derived local numerical estimate.
The moving exponent keeps p to s minus 1 at least p over 12. -/
theorem fractional_local_bound (Q : ℝ) (hQ : 0 < Q) (p : ℕ)
    (hp : p.Prime) (hpQ : (p : ℝ) ≤ Q) :
    0 < (p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1 ∧
      64 / ((p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1) ≤ 768 / (p : ℝ) := by
  let V := max 1 (Real.log Q)
  let δ := 1 / (2 * V)
  let s := 1 - δ
  have hV1 : 1 ≤ V := le_max_left _ _
  have hVpos : 0 < V := by linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hδ : δ ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by dsimp [V] at *; linarith)
  have hs : (1 / 2 : ℝ) ≤ s := by dsimp [s]; linarith
  have hlog : Real.log (p : ℝ) ≤ V :=
    (Real.log_le_log hp0 hpQ).trans (le_max_right _ _)
  have hδlog : Real.log (p : ℝ) * δ ≤ 1 := by
    dsimp [δ]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * V)).mpr
    linarith
  have hexp : Real.exp (Real.log (p : ℝ) * δ) ≤ 3 := by
    exact (Real.exp_le_exp.mpr hδlog).trans (by linarith [Real.exp_one_lt_d9])
  have hprod : (p : ℝ) ^ s * Real.exp (Real.log (p : ℝ) * δ) = (p : ℝ) := by
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_add]
    have he : Real.log (p : ℝ) * s + Real.log (p : ℝ) * δ = Real.log (p : ℝ) := by
      dsimp [s]
      ring
    rw [he, Real.exp_log hp0]
  have hp3 : (p : ℝ) / 3 ≤ (p : ℝ) ^ s := by
    have hh := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hp0.le s)
    rw [hprod] at hh
    linarith
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hp43 : (4 / 3 : ℝ) ≤ (p : ℝ) ^ s := by
    calc
      _ ≤ Real.sqrt 2 := hsqrt
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
      _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hp2 (by norm_num)
      _ ≤ (p : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have hden : (p : ℝ) / 12 ≤ (p : ℝ) ^ s - 1 := by linarith
  have hdenpos : 0 < (p : ℝ) ^ s - 1 := lt_of_lt_of_le (by positivity) hden
  change 0 < (p : ℝ) ^ s - 1 ∧ 64 / ((p : ℝ) ^ s - 1) ≤ 768 / (p : ℝ)
  refine ⟨hdenpos, ?_⟩
  apply (div_le_div_iff₀ hdenpos hp0).mpr
  nlinarith

/-- Page 14 below display 50, exact Task447c numerical product supply.
The weak lab Mertens bound suffices with C equal to exp 9216 and D equal to 768. -/
theorem fractional_euler_product_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ Q : ℝ, 0 < Q →
      (∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  classical
  refine ⟨Real.exp 9216, 768, Real.exp_pos _, by norm_num, ?_⟩
  intro Q hQ
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
  let s := 1 - 1 / (2 * max 1 (Real.log Q))
  by_cases hQ2 : 2 ≤ Q
  · let N := ⌊Q⌋₊
    have hN2 : 2 ≤ N := Nat.le_floor hQ2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hNQ : (N : ℝ) ≤ Q := Nat.floor_le hQ.le
    have hlocal (p : ℕ) (hp : p ∈ S) :
        0 < 1 + 64 / ((p : ℝ) ^ s - 1) ∧
          Real.log (1 + 64 / ((p : ℝ) ^ s - 1)) ≤ 768 * (1 / (p : ℝ)) := by
      have hprime := (Finset.mem_filter.mp hp).2
      have hpN : p ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hpQ : (p : ℝ) ≤ Q := (Nat.cast_le.mpr hpN).trans hNQ
      obtain ⟨hd, hb⟩ := fractional_local_bound Q hQ p hprime hpQ
      change 0 < (p : ℝ) ^ s - 1 at hd
      change 64 / ((p : ℝ) ^ s - 1) ≤ 768 / (p : ℝ) at hb
      have hpos : 0 < 1 + 64 / ((p : ℝ) ^ s - 1) := by positivity
      refine ⟨hpos, ?_⟩
      have hh := Real.log_le_sub_one_of_pos hpos
      have hh' : Real.log (1 + 64 / ((p : ℝ) ^ s - 1)) ≤ 64 / ((p : ℝ) ^ s - 1) := by linarith
      convert hh'.trans hb using 1 <;> ring
    have hsum : (∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 12 := by
      have hsub : S ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
        intro p hp
        obtain ⟨hpr, hprime⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨hprime.one_le, Nat.lt_succ_iff.mp (Finset.mem_range.mp hpr)⟩, hprime⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hn => by positivity)).trans
        (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN2)
    have hprodpos : 0 < ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1)) :=
      Finset.prod_pos (fun p hp => (hlocal p hp).1)
    have hlogprod : Real.log (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤
        768 * (Real.log (Real.log (N : ℝ)) + 12) := by
      rw [Real.log_prod (fun p hp => (hlocal p hp).1.ne')]
      calc
        _ ≤ ∑ p ∈ S, 768 * (1 / (p : ℝ)) := Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
        _ = 768 * ∑ p ∈ S, 1 / (p : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
    have hprod : (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤
        Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := by
      have hh := (Real.log_le_iff_le_exp hprodpos).mp hlogprod
      have he : Real.exp (768 * (Real.log (Real.log (N : ℝ)) + 12)) =
          Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := by
        rw [mul_add, Real.exp_add, show (768 : ℝ) = ((768 : ℕ) : ℝ) by norm_num,
          Real.exp_nat_mul, Real.exp_log hlogN]
        norm_num
        ring
      exact hh.trans_eq he
    calc
      _ ≤ Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := hprod
      _ ≤ Real.exp 9216 * (max 1 (Real.log Q)) ^ (768 : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ hlogN.le
        exact (Real.log_le_log hNpos hNQ).trans (le_max_right _ _)
      _ = _ := by norm_num
  · have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      have hpN : p ≤ ⌊Q⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hpQ : (p : ℝ) ≤ Q := (Nat.cast_le.mpr hpN).trans (Nat.floor_le hQ.le)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      linarith
    change (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤ _
    rw [hS, Finset.prod_empty]
    have hC : 1 ≤ Real.exp 9216 := Real.one_le_exp (by norm_num)
    have hV : 1 ≤ (max 1 (Real.log Q)) ^ (768 : ℝ) :=
      Real.one_le_rpow (le_max_left _ _) (by norm_num)
    nlinarith

#print axioms fractional_local_bound
#print axioms fractional_euler_product_bound
#print axioms LeanLab.PNTSieve.Mertens.sum_inv_primes_le
end LeanLab.KumchevLiu2007.EulerProduct447
