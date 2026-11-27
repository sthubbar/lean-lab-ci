/-
P0068 Zhan 1991, page 263 display (3.3): the divisor LEAF `perron_fiber_leaf_ps2` of
PerronSum1122d.lean, PROVED. Burst 20261124, session S9, unit A-extra-2. A tuple of display (3.4)
with product `m ≥ 1` is a tuple of divisors of `m`, so there are at most `d(m)^20` of them, and
`d(m) ≪_k m^{1/k}`, Hardy and Wright Theorem 315, with `k ≥ 20/ε`; for `m = 0` there is no tuple.
The divisor bound helpers are copies, renamed with the suffix `_A2`, of the PROVED lemmas of
LeanLab/HeathBrown1985/DivisorEps.lean, since this lab folder may not import that one.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PerronSum1122d

namespace LeanLab.Zhan1991
open Finset Filter Topology Real

noncomputable section


/-- `(a + 1)^k ≤ M 2^a` for all `a`. -/
theorem exists_pow_le_two_pow_A2 (k : ℕ) : ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ℕ, ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) one_lt_two
  have ht' : Tendsto (fun a : ℕ => ((a + 1 : ℕ) : ℝ) ^ k / 2 ^ (a + 1)) atTop (𝓝 0) :=
    ht.comp (tendsto_add_atTop_nat 1)
  obtain ⟨S, hS⟩ := ht'.bddAbove_range
  refine ⟨max 1 (2 * S), le_max_left _ _, fun a => ?_⟩
  have h1 : ((a + 1 : ℕ) : ℝ) ^ k / 2 ^ (a + 1) ≤ S := hS ⟨a, rfl⟩
  have h2 : (0 : ℝ) < 2 ^ (a + 1) := by positivity
  rw [div_le_iff₀ h2] at h1
  push_cast at h1
  have h3 : (0 : ℝ) < 2 ^ a := by positivity
  calc ((a : ℝ) + 1) ^ k ≤ S * 2 ^ (a + 1) := h1
    _ = (2 * S) * 2 ^ a := by ring
    _ ≤ max 1 (2 * S) * 2 ^ a := by gcongr; exact le_max_right _ _

/-- The prime power factor bound behind `d(n)^k ≪ n`. -/
theorem prime_pow_factor_le_A2 (k : ℕ) (M : ℝ) (hM1 : 1 ≤ M)
    (hM : ∀ a : ℕ, ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a) (p a : ℕ) (hp : 2 ≤ p) :
    ((a : ℝ) + 1) ^ k ≤ (if p < 2 ^ k then M else 1) * (p : ℝ) ^ a := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  split_ifs with h
  · calc ((a : ℝ) + 1) ^ k ≤ M * 2 ^ a := hM a
      _ ≤ M * (p : ℝ) ^ a := by gcongr
  · push Not at h
    have ha : (a : ℝ) + 1 ≤ 2 ^ a := by
      have := Nat.lt_two_pow_self (n := a)
      exact_mod_cast this
    have hpk : ((2 : ℝ) ^ k) ≤ p := by exact_mod_cast h
    calc ((a : ℝ) + 1) ^ k ≤ ((2 : ℝ) ^ a) ^ k := by gcongr
      _ = ((2 : ℝ) ^ k) ^ a := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (p : ℝ) ^ a := by gcongr
      _ = 1 * (p : ℝ) ^ a := by ring

/-- The divisor bound `d(n)^k ≤ C_k n`. -/
theorem card_divisors_pow_le_A2 (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ^ k ≤ C * n := by
  obtain ⟨M, hM1, hM⟩ := exists_pow_le_two_pow_A2 k
  refine ⟨M ^ (2 ^ k), one_le_pow₀ hM1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors hn0]
  push_cast
  rw [← prod_pow]
  have hg : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ k ≤
      (if p < 2 ^ k then M else 1) * (p : ℝ) ^ n.factorization p := by
    intro p hp
    exact prime_pow_factor_le_A2 k M hM1 hM p _ (Nat.prime_of_mem_primeFactors hp).two_le
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ k
      ≤ ∏ p ∈ n.primeFactors, ((if p < 2 ^ k then M else 1) * (p : ℝ) ^ n.factorization p) :=
        prod_le_prod₀ (fun p _ => by positivity) hg
    _ = (∏ p ∈ n.primeFactors, (if p < 2 ^ k then M else 1)) *
          ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := prod_mul_distrib
    _ ≤ M ^ (2 ^ k) * n := by
        have hn' : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
          conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
          push_cast; rfl
        rw [← hn']
        gcongr
        rw [← prod_filter, prod_const]
        apply pow_le_pow_right₀ hM1
        calc (n.primeFactors.filter (· < 2 ^ k)).card ≤ (range (2 ^ k)).card := by
              apply card_le_card
              intro p hp
              simp only [mem_filter] at hp
              simpa using hp.2
          _ = 2 ^ k := card_range _

/-- `d(n) ≤ C n^{1/k}`. -/
theorem card_divisors_le_rpow_A2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  obtain ⟨C, hC1, hC⟩ := card_divisors_pow_le_A2 k
  refine ⟨C ^ ((k : ℝ)⁻¹), by positivity, fun n hn => ?_⟩
  have hk0 : k ≠ 0 := by omega
  have hd0 : (0 : ℝ) ≤ n.divisors.card := by positivity
  calc (n.divisors.card : ℝ) = ((n.divisors.card : ℝ) ^ k) ^ ((k : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hd0 hk0).symm
    _ ≤ (C * n) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) (hC n hn) (by positivity)
    _ = C ^ ((k : ℝ)⁻¹) * (n : ℝ) ^ ((k : ℝ)⁻¹) :=
        Real.mul_rpow (by linarith) (by positivity)


/-- The same statement as the LEAF `perron_fiber_leaf_ps2`, page 263 display (3.3). -/
theorem perron_fiber_proof_A2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ)
    (Nv : Fin 20 → ℝ) (m : ℕ), N₀ ≤ N → m ≤ 2 ^ 20 * N →
    ((Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))).filter
      (fun n => ∏ j, n j = m)).card ≤ K * (N : ℝ) ^ ε := by
  intro ε hε
  set k : ℕ := ⌈20 / ε⌉₊ + 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  obtain ⟨C, hC, hCd⟩ := card_divisors_le_rpow_A2 k hk1
  refine ⟨C ^ 20 * ((2 : ℝ) ^ 20) ^ ε, 0, by positivity, ?_⟩
  intro N Nv m _ hm
  have hKN : 0 ≤ C ^ 20 * ((2 : ℝ) ^ 20) ^ ε * (N : ℝ) ^ ε := by positivity
  rcases Nat.eq_zero_or_pos m with h0 | hmpos
  · -- no tuple of positive integers has product `0`
    have : ((Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))).filter
        (fun n => ∏ j, n j = m)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro n hn hprod
      rw [h0, Finset.prod_eq_zero_iff] at hprod
      obtain ⟨j, -, hj⟩ := hprod
      have := Fintype.mem_piFinset.mp hn j
      simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at this
      omega
    rw [this, Finset.card_empty, Nat.cast_zero]
    exact hKN
  -- every tuple with product `m` is a tuple of divisors of `m`
  have hsub : ((Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))).filter
      (fun n => ∏ j, n j = m)) ⊆ Fintype.piFinset (fun _ : Fin 20 => m.divisors) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Fintype.mem_piFinset]
    intro j
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    rw [← hn.2]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hkε : (20 : ℝ) / k ≤ ε := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [div_le_iff₀ hk0]
    have h1 : 20 / ε ≤ (⌈20 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (k : ℝ) = ⌈20 / ε⌉₊ + 1 := by rw [hkdef]; push_cast; ring
    rw [div_le_iff₀ hε] at h1
    nlinarith
  have hd := hCd m hmpos
  have hd0 : (0 : ℝ) ≤ m.divisors.card := by positivity
  have hpow : ((m.divisors.card : ℝ)) ^ 20 ≤ C ^ 20 * (m : ℝ) ^ ε := by
    calc ((m.divisors.card : ℝ)) ^ 20 ≤ (C * (m : ℝ) ^ ((k : ℝ)⁻¹)) ^ 20 := by gcongr
      _ = C ^ 20 * (m : ℝ) ^ ((20 : ℝ) / k) := by
          rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ ((k : ℝ)⁻¹)), ← Real.rpow_mul (by positivity)]
          congr 2
          push_cast
          ring
      _ ≤ C ^ 20 * (m : ℝ) ^ ε := by
          gcongr
  have hmN : (m : ℝ) ^ ε ≤ ((2 : ℝ) ^ 20) ^ ε * (N : ℝ) ^ ε := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    exact_mod_cast hm
  calc (((Fintype.piFinset (fun j : Fin 20 => dyad (Nv j))).filter
        (fun n => ∏ j, n j = m)).card : ℝ) ≤ ((m.divisors.card ^ 20 : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ((m.divisors.card : ℝ)) ^ 20 := by push_cast; rfl
    _ ≤ C ^ 20 * (m : ℝ) ^ ε := hpow
    _ ≤ C ^ 20 * (((2 : ℝ) ^ 20) ^ ε * (N : ℝ) ^ ε) := by gcongr
    _ = C ^ 20 * ((2 : ℝ) ^ 20) ^ ε * (N : ℝ) ^ ε := by ring
end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.card_divisors_le_rpow_A2
#print axioms LeanLab.Zhan1991.perron_fiber_proof_A2
