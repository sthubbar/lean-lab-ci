/-
Proof of the MEDIUM leaf modulus_over_totient491 of SPLIT_mixed_pair_repair491, audit
P1122-0033 of the factor q over phi of q in P0093 page 160 equation 5.5.
phi of q over q is the product of 1 - 1/p over the primes dividing q. The primes up to the cut
Y = floor of log N contribute at least exp of -16 over log Y, by the lab's proved
PNTSieve.Mertens.mertens_product_ge; the primes above Y number at most log q over log Y, so
they contribute at least one half by Bernoulli's inequality, since q is at most N to the one
tenth. Hence q over phi of q is at most 2 exp 16 log log N, below 4 exp 16 times the square root
of log N.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.PNTSieve.MertensProduct
open Finset Real

namespace LeanLab.Linnik1951.TotientRatioS128

lemma tot_prod (q : ℕ) : (q.totient : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - (p:ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  push_cast at h
  exact h

lemma small_part (q Y : ℕ) (hY : 2 ≤ Y) :
    Real.exp (-16) / Real.log Y ≤ ∏ p ∈ q.primeFactors.filter (fun p => p ≤ Y), (1 - (p:ℝ)⁻¹) := by
  have hM := LeanLab.PNTSieve.Mertens.mertens_product_ge Y hY
  set A := q.primeFactors.filter (fun p => p ≤ Y)
  set B := (Icc 1 Y).filter Nat.Prime
  have hsub : A ⊆ B := by
    intro p hp
    simp only [A, B, mem_filter, Nat.mem_primeFactors, mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1.one_lt.le, hp.2⟩, hp.1.1⟩
  have hf : ∀ p ∈ B, (1 : ℝ) / p = (p:ℝ)⁻¹ := fun p _ => one_div _
  rw [prod_congr rfl (fun p hp => by rw [hf p hp])] at hM
  rw [← prod_sdiff hsub] at hM
  have h1 : ∏ p ∈ B \ A, (1 - (p:ℝ)⁻¹) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro p hp
      have : (1:ℝ) ≤ p := by
        have := (mem_filter.mp (mem_sdiff.mp hp).1).2.one_lt.le
        exact_mod_cast this
      have : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      linarith
    · intro p hp
      have : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
      linarith
  have h0 : 0 ≤ ∏ p ∈ A, (1 - (p:ℝ)⁻¹) := by
    apply prod_nonneg
    intro p hp
    have : (1:ℝ) ≤ p := by
      have := (Nat.mem_primeFactors.mp (mem_filter.mp hp).1).1.one_lt.le
      exact_mod_cast this
    have : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
    linarith
  calc Real.exp (-16) / Real.log Y ≤ _ := hM
    _ ≤ 1 * ∏ p ∈ A, (1 - (p:ℝ)⁻¹) := mul_le_mul_of_nonneg_right h1 h0
    _ = _ := one_mul _

lemma large_card (q Y : ℕ) (hq : 1 ≤ q) :
    (Y : ℝ) ^ (q.primeFactors.filter (fun p => ¬ p ≤ Y)).card ≤ q := by
  set C := q.primeFactors.filter (fun p => ¬ p ≤ Y)
  have h1 : Y ^ C.card ≤ ∏ p ∈ C, p := by
    apply Finset.pow_card_le_prod
    intro p hp
    have := (mem_filter.mp hp).2
    omega
  have h2 : (∏ p ∈ C, p) ∣ q :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd q)
  have h3 : Y ^ C.card ≤ q := h1.trans (Nat.le_of_dvd hq h2)
  exact_mod_cast h3

lemma large_part (q Y : ℕ) (hY : 2 ≤ Y) :
    1 - ((q.primeFactors.filter (fun p => ¬ p ≤ Y)).card : ℝ) / Y ≤
      ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ≤ Y), (1 - (p:ℝ)⁻¹) := by
  set C := q.primeFactors.filter (fun p => ¬ p ≤ Y)
  have hY0 : (0:ℝ) < Y := by positivity
  have hY2 : (2:ℝ) ≤ Y := by exact_mod_cast hY
  have hb : ∀ p ∈ C, 0 ≤ 1 - (Y:ℝ)⁻¹ ∧ 1 - (Y:ℝ)⁻¹ ≤ 1 - (p:ℝ)⁻¹ := by
    intro p hp
    have hp' : Y < p := by have := (mem_filter.mp hp).2; omega
    have hpY : (Y:ℝ) ≤ p := by exact_mod_cast hp'.le
    refine ⟨?_, ?_⟩
    · have : (Y:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      linarith
    · have : (p:ℝ)⁻¹ ≤ (Y:ℝ)⁻¹ := inv_anti₀ hY0 hpY
      linarith
  have hpow : (1 - (Y:ℝ)⁻¹) ^ C.card ≤ ∏ p ∈ C, (1 - (p:ℝ)⁻¹) := by
    rw [← prod_const]
    exact Finset.prod_le_prod₀ (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2)
  have hbern := one_add_mul_le_pow (a := -(Y:ℝ)⁻¹) (by
    have : (Y:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith) C.card
  have : (1:ℝ) + C.card * -(Y:ℝ)⁻¹ = 1 - (C.card : ℝ) / Y := by ring
  rw [this, ← sub_eq_add_neg] at hbern
  exact hbern.trans hpow


/-- the ratio bound for a cut Y with log Y ≥ 1 and few large prime factors. -/
lemma ratio_cut (q Y : ℕ) (hq : 1 ≤ q) (hY : 3 ≤ Y)
    (hk : Real.log q ≤ (Y : ℝ) / 2) :
    (q : ℝ) ≤ 2 * Real.exp 16 * Real.log Y * q.totient := by
  have hY2 : 2 ≤ Y := by omega
  have hYr : (3:ℝ) ≤ Y := by exact_mod_cast hY
  have hlY : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; have : Real.exp 1 = Real.exp 1 := rfl; linarith
  set C := q.primeFactors.filter (fun p => ¬ p ≤ Y)
  have hcard := large_card q Y hq
  have hcl : (C.card : ℝ) * Real.log Y ≤ Real.log q := by
    have hpos : (0:ℝ) < (Y:ℝ) ^ C.card := by positivity
    have := Real.log_le_log hpos hcard
    rwa [Real.log_pow] at this
  have hck : (C.card : ℝ) / Y ≤ 1 / 2 := by
    have hc0 : (0:ℝ) ≤ C.card := by positivity
    have : (C.card : ℝ) ≤ Real.log q := by nlinarith
    rw [div_le_iff₀ (by linarith)]; linarith
  have hL := large_part q Y hY2
  have hS := small_part q Y hY2
  have hT := tot_prod q
  rw [← prod_filter_mul_prod_filter_not q.primeFactors (fun p => p ≤ Y)] at hT
  have hS0 : 0 < Real.exp (-16) / Real.log Y := by positivity
  have hprod : Real.exp (-16) / Real.log Y * (1/2) ≤
      (∏ p ∈ q.primeFactors.filter (fun p => p ≤ Y), (1 - (p:ℝ)⁻¹)) *
      ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ≤ Y), (1 - (p:ℝ)⁻¹) :=
    mul_le_mul hS (by linarith) (by norm_num) (hS0.le.trans hS)
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have key : (q:ℝ) * (Real.exp (-16) / Real.log Y * (1/2)) ≤ q.totient := by
    rw [hT]; exact mul_le_mul_of_nonneg_left hprod hq0.le
  have he : Real.exp 16 * Real.exp (-16) = 1 := by rw [← Real.exp_add]; norm_num
  have hlpos : 0 < Real.log Y := by linarith
  have : (q:ℝ) = 2 * Real.exp 16 * Real.log Y * ((q:ℝ) * (Real.exp (-16) / Real.log Y * (1/2))) := by
    field_simp; linear_combination (-1:ℝ) * he
  rw [this]
  have h2 : 0 ≤ 2 * Real.exp 16 * Real.log Y := by positivity
  exact mul_le_mul_of_nonneg_left key h2

theorem modulus_over_totient_S128 :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (q : ℝ) ≤ D * (q.totient : ℝ) * Real.sqrt (Real.log N) := by
  refine ⟨4 * Real.exp 16, by positivity, 100, fun N hN q hq hqN => ?_⟩
  have hN1 : (100:ℝ) < N := by exact_mod_cast hN
  set L := Real.log N with hLdef
  have hL3 : 4 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 4 ≤ (2.7182818286:ℝ) ^ 4 := pow_le_pow_left₀ h0 h.le 4
      _ ≤ 100 := by norm_num
      _ ≤ N := hN1.le
  set Y := ⌊L⌋₊ with hYdef
  have hYle : (Y:ℝ) ≤ L := Nat.floor_le (by linarith)
  have hYgt : L < Y + 1 := Nat.lt_floor_add_one L
  have hY3 : 3 ≤ Y := by
    have : (3:ℝ) < Y + 1 := by linarith
    have : (2:ℝ) < Y := by linarith
    exact_mod_cast this
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hlq : Real.log q ≤ L / 10 := by
    have := Real.log_le_log hq0 hqN
    rw [Real.log_rpow (by linarith)] at this
    linarith [hLdef]
  have hk : Real.log q ≤ (Y:ℝ) / 2 := by linarith
  have hc := ratio_cut q Y hq hY3 hk
  have hYpos : (0:ℝ) < Y := by positivity
  have hlogY : Real.log Y ≤ 2 * Real.sqrt L := by
    have hs : Real.log Y ≤ Real.log L := Real.log_le_log hYpos hYle
    have hsq : Real.log L = 2 * Real.log (Real.sqrt L) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have hsqp : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
    have := Real.log_le_sub_one_of_pos hsqp
    linarith
  have ht : (0:ℝ) ≤ q.totient := by positivity
  calc (q:ℝ) ≤ 2 * Real.exp 16 * Real.log Y * q.totient := hc
    _ ≤ 2 * Real.exp 16 * (2 * Real.sqrt L) * q.totient := by
        gcongr
    _ = 4 * Real.exp 16 * (q.totient : ℝ) * Real.sqrt L := by ring

end LeanLab.Linnik1951.TotientRatioS128
