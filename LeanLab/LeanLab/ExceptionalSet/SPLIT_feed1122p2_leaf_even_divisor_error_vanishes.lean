import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_index_coefficient_domination

/-!
Split of `leaf_even_divisor_error_vanishes` of
`LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_index_coefficient_domination`,
burst-20261122 wave 13, session S132. Source P0082, Brudern and Perelli 1998, page 359,
displays 14 and 15.

Pieces:
* `leaf_divisorError_tau_bound`, displays 14 and 15: for `1 ≤ r ≤ P`, `P ≥ 2`, `m ≥ 1` coprime to
  `r`, the envelope is at most `C τ(m) P^{ε-1}`; the paper has `τ(m) (log log P)^3 log P / P`,
  and the logarithms are absorbed into `P^ε`. LEAF, HARD.
* `leaf_tau_le_rpow`, the divisor bound `τ(n) ≤ C n^ε`, PROVED by a copy of the proof of
  `LeanLab.Akeno2026.Decomp86.card_divisors_le_rpow`.
* `leaf_even_divisor_error_vanishes_of_leaves`, the exact original statement, PROVED from the two
  pieces: with `ε = δ`, `X = F γ N`, `P = X^{6δ}`, the bound is `C X^{δ + 6δ(δ-1)} ≤ C X^{-4δ}`, and
  `X ≥ N` for `N ≥ 3`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF: P0082 page 359 displays 14 and 15, class HARD. For every `ε > 0` there is `C > 0` with
`divisorError r P m ≤ C τ(m) P^{ε - 1}` whenever `P ≥ 2`, `1 ≤ r ≤ P`, `m ≥ 1` and `(m, r) = 1`.
Writing `q = r k`, the finite part is at most `τ(m) (log log P)^2 log P / P` and the tail is at
most `τ(m) (log log P)^3 / P`; the logarithms are absorbed into `P^ε`. -/
theorem leaf_divisorError_tau_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (P : ℝ) (m : ℤ), 2 ≤ P → 1 ≤ r → (r : ℝ) ≤ P → 1 ≤ m → Int.gcd m r = 1 →
        divisorError r P m ≤ C * (m.toNat.divisors.card : ℝ) * P ^ (ε - 1) := by
  sorry

/-- The divisor bound `τ(n) ≤ C n^ε`, used on page 359 to say `τ(m) = X^{o(1)}`. PROVED; the
proof is a copy of `LeanLab.Akeno2026.Decomp86.card_divisors_le_rpow`, copied rather than imported
to keep the build closure inside this folder. -/
theorem leaf_tau_le_rpow :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hc (p : ℕ) : 1 ≤ c p := by dsimp [c]; split_ifs <;> linarith
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)


/-- `F γ N ≥ N` for `γ ≥ 1` and `N ≥ 3`. -/
theorem F_ge_self_p2 (γ : ℝ) (h1 : 1 ≤ γ) (N : ℕ) (hN : 3 ≤ N) : (N : ℝ) ≤ F γ N := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
  calc (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0).symm
    _ ≤ Real.exp (Real.log N ^ γ) := by
      apply Real.exp_le_exp.2
      calc Real.log N = Real.log N ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ Real.log N ^ γ := Real.rpow_le_rpow_of_exponent_le hlog h1

/-- The exact statement of `leaf_even_divisor_error_vanishes`, from the two pieces. -/
theorem leaf_even_divisor_error_vanishes_of_leaves (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            divisorError r (F γ N ^ (6 * δ)) m ≤ η := by
  intro η hη δ hδ hδs
  obtain ⟨C1, hC1, H1⟩ := leaf_divisorError_tau_bound δ hδ
  obtain ⟨C2, hC2, H2⟩ := leaf_tau_le_rpow δ hδ
  set K : ℝ := max (C1 * C2 / η) 2 with hK
  have hK2 : 2 ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  set T : ℝ := K ^ (1 / (4 * δ)) with hT
  refine ⟨max 3 ⌈T⌉₊, ?_⟩
  intro N hN r hr hrP m hm1 hm2 hgcd
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hNT : T ≤ N := le_trans (Nat.le_ceil T) (by exact_mod_cast le_trans (le_max_right _ _) hN)
  set X : ℝ := F γ N with hX
  have hXN : (N : ℝ) ≤ X := F_ge_self_p2 γ h1.le N hN3
  have hTX : T ≤ X := le_trans hNT hXN
  have hX1 : 1 ≤ X := le_trans (by exact_mod_cast (by omega : 1 ≤ N)) hXN
  have hX0 : 0 < X := by linarith
  have hX4 : K ≤ X ^ (4 * δ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le _) hTX (by positivity : 0 ≤ 4 * δ)
    rw [← Real.rpow_mul hK0.le, show 1 / (4 * δ) * (4 * δ) = 1 by field_simp,
      Real.rpow_one] at h
    exact h
  have hX64 : X ^ (4 * δ) ≤ X ^ (6 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hP2 : 2 ≤ X ^ (6 * δ) := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1' : (1 : ℤ) ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hm0
    omega
  have hD := H1 r (X ^ (6 * δ)) m hP2 hr hrP hm1' hgcd
  have hτ := H2 m.toNat
  have hmcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [hmcast] at hτ
  have hmX : (m : ℝ) ^ δ ≤ X ^ δ := Real.rpow_le_rpow hm0.le hm2 hδ.le
  have hPpow : (X ^ (6 * δ)) ^ (δ - 1) = X ^ (6 * δ * (δ - 1)) := by
    rw [← Real.rpow_mul hX0.le]
  have hPp0 : 0 ≤ (X ^ (6 * δ)) ^ (δ - 1) := Real.rpow_nonneg (Real.rpow_nonneg hX0.le _) _
  have hexp : X ^ δ * X ^ (6 * δ * (δ - 1)) ≤ X ^ (-(4 * δ)) := by
    rw [← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    nlinarith
  have hneg : X ^ (-(4 * δ)) = (X ^ (4 * δ))⁻¹ := Real.rpow_neg hX0.le _
  have hX4pos : 0 < X ^ (4 * δ) := Real.rpow_pos_of_pos hX0 _
  calc divisorError r (X ^ (6 * δ)) m
      ≤ C1 * (m.toNat.divisors.card : ℝ) * (X ^ (6 * δ)) ^ (δ - 1) := hD
    _ ≤ C1 * (C2 * (m : ℝ) ^ δ) * (X ^ (6 * δ)) ^ (δ - 1) := by gcongr
    _ ≤ C1 * (C2 * X ^ δ) * (X ^ (6 * δ)) ^ (δ - 1) := by gcongr
    _ = C1 * C2 * (X ^ δ * X ^ (6 * δ * (δ - 1))) := by rw [hPpow]; ring
    _ ≤ C1 * C2 * X ^ (-(4 * δ)) := by gcongr
    _ = C1 * C2 / X ^ (4 * δ) := by rw [hneg]; ring
    _ ≤ η := by
      rw [div_le_iff₀ hX4pos]
      have hK' : C1 * C2 / η ≤ X ^ (4 * δ) := le_trans (le_max_left _ _) hX4
      rw [div_le_iff₀ hη] at hK'
      linarith

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
