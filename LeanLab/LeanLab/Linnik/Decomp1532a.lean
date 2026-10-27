/-
Unit U-1532, run 20261026T0004Z-24325, DECOMPOSE.
Gallagher 1975, Primes and powers of 2, Invent. Math. 29, 125-142, base g = 2.

File a: the powers of 2 modulo q, Section 2 of the paper, pp. 133-136.
* `ordTwo q`, the order `e(q)` of 2 modulo an odd `q`, p. 133.
* `pairs k L`, pairs of exponent tuples `ν, μ ∈ [1, L]^k`, written with `Fin L` and the shift
  `ν i + 1` of `sv`; `dif x = 2^{ν₁} + ... + 2^{ν_k} - (2^{μ₁} + ... + 2^{μ_k})`, so that
  `r_{k,k}(n)` of display (3), p. 134, is the number of `x` with `dif x = n`.
* `Mprod x = ∏_{e ≤ x} (2^e - 1)`, the modulus `M` in the proof of Lemma 4, p. 133.
Leaves: Lemma 3 inputs on `e(q)`, Lemma 4 split into four steps, Lemma 5, Lemma 7, Lemma 8.
Assembly: `lemma4`, Lemma 4 of p. 133, from the four Lemma 4 leaves.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Linnik.U1434Lemma21

namespace LeanLab.Linnik.Decomp1532a

open Finset
open LeanLab.Linnik.U1434Lemma21 (sv)

/-- `e(q)`, the order of 2 modulo `q`, p. 133; for odd `q` it is the least `e ≥ 1` with
`2^e ≡ 1 mod q`. -/
noncomputable def ordTwo (q : ℕ) : ℕ := orderOf (2 : ZMod q)

/-- Pairs of exponent tuples `(ν, μ)`, `ν i + 1, μ i + 1 ∈ [1, L]`. -/
abbrev pairs (k L : ℕ) : Type := (Fin k → Fin L) × (Fin k → Fin L)

/-- `dif (ν, μ) = Σ 2^{ν_i + 1} - Σ 2^{μ_i + 1}`, the integer `n` of display (3), p. 134. -/
def dif {k L : ℕ} (x : pairs k L) : ℤ := (sv x.1 : ℤ) - sv x.2

/-- `M = ∏_{e=1}^{x} (2^e - 1)`, proof of Lemma 4, p. 133. -/
def Mprod (x : ℕ) : ℕ := ∏ e ∈ Icc 1 x, (2 ^ e - 1)

/-- LEAF. Unit U-1532. For odd `q` the order `e(q)` of 2 modulo `q` is positive,
p. 133, definition before Lemma 3. -/
theorem ordTwo_pos {q : ℕ} (hq : Odd q) : 0 < ordTwo q := by
  have h_unit : IsUnit (2 : ZMod q) := by
    apply ZMod.isUnit_prime_of_not_dvd
    · exact Nat.prime_two
    · exact hq.not_two_dvd_nat
  rcases q with _ | q'
  · exfalso; revert hq; decide
  · have h_pos := orderOf_pos h_unit.unit
    have h_eq : orderOf (2 : ZMod (q' + 1)) = orderOf h_unit.unit := by
      exact @orderOf_units _ _ h_unit.unit
    rwa [← h_eq] at h_pos

/-- LEAF. Unit U-1532. For odd `q`, `q` divides `2^{e(q)} - 1`, p. 133, definition of
`e(q)`. -/
theorem dvd_two_pow_ordTwo_sub_one {q : ℕ} (hq : Odd q) : q ∣ 2 ^ ordTwo q - 1 := by
  have h1 : (2 : ZMod q) ^ ordTwo q = 1 := pow_orderOf_eq_one (2 : ZMod q)
  have h2 : ((2 ^ ordTwo q : ℕ) : ZMod q) = 1 := by exact_mod_cast h1
  have h3 : (2 ^ ordTwo q : ℕ) ≡ 1 [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have h4 : (1 : ZMod q) = ((1 : ℕ) : ZMod q) := by simp
    rw [← h4]
    exact h2
  have h3' : 1 ≡ 2 ^ ordTwo q [MOD q] := h3.symm
  have h4 : (q : ℤ) ∣ (2 ^ ordTwo q : ℕ) - (1 : ℤ) := Nat.ModEq.dvd h3'
  apply Int.ofNat_dvd.mp
  have h5 : ((2 ^ ordTwo q - 1 : ℕ) : ℤ) = (2 ^ ordTwo q : ℕ) - (1 : ℤ) := by
    apply Nat.cast_sub
    exact Nat.one_le_pow _ _ (by norm_num)
  rw [h5]
  exact h4

/-- LEAF. Unit U-1532. For odd `q ≥ 1`, `log q ≤ e(q) log 2`, the bound `e(f) ≫ log f` used in
the proof of Lemma 10, p. 137. -/
theorem log_le_ordTwo_mul_log_two {q : ℕ} (hq : Odd q) :
    Real.log q ≤ ordTwo q * Real.log 2 := by
  have h_dvd : q ∣ 2 ^ ordTwo q - 1 := dvd_two_pow_ordTwo_sub_one hq
  have h_pos : 0 < 2 ^ ordTwo q - 1 := by
    have h1 : 2 ^ 1 ≤ 2 ^ ordTwo q := by
      apply Nat.pow_le_pow_right (by norm_num) (ordTwo_pos hq)
    have h_pow : 2 ^ 1 = 2 := by rfl
    rw [h_pow] at h1
    omega
  have h_le : q ≤ 2 ^ ordTwo q - 1 := by
    apply Nat.le_of_dvd h_pos h_dvd
  have h_le2 : q ≤ 2 ^ ordTwo q := by omega
  have h_le3 : (q : ℝ) ≤ ((2 ^ ordTwo q : ℕ) : ℝ) := by exact_mod_cast h_le2
  have h_log : Real.log (q : ℝ) ≤ Real.log ((2 ^ ordTwo q : ℕ) : ℝ) := by
    have hq_pos : 0 < q := by
      rcases q with _ | q'
      · exfalso; revert hq; decide
      · exact Nat.zero_lt_succ _
    apply Real.log_le_log
    · exact_mod_cast hq_pos
    · exact h_le3
  have h_log2 : Real.log ((2 ^ ordTwo q : ℕ) : ℝ) = (ordTwo q : ℝ) * Real.log 2 := by
    have h_pow : ((2 ^ ordTwo q : ℕ) : ℝ) = (2 : ℝ) ^ (ordTwo q : ℕ) := by push_cast; rfl
    rw [h_pow]
    exact Real.log_pow (2 : ℝ) (ordTwo q)
  rwa [h_log2] at h_log

/-- LEAF. Unit U-1532. For odd `q`, `2^a ≡ 2^b mod q` exactly when `a ≡ b mod e(q)`; this is the
periodicity used in the proofs of Lemmas 3 and 5, pp. 133-134. -/
theorem two_pow_modEq_iff {q : ℕ} (hq : Odd q) (a b : ℕ) :
    2 ^ a ≡ 2 ^ b [MOD q] ↔ a ≡ b [MOD ordTwo q] := by
  have h_unit : IsUnit (2 : ZMod q) := by
    apply ZMod.isUnit_prime_of_not_dvd
    · exact Nat.prime_two
    · exact hq.not_two_dvd_nat
  constructor
  · intro h
    have h1 : ((2 ^ a : ℕ) : ZMod q) = ((2 ^ b : ℕ) : ZMod q) := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    have h2 : (2 : ZMod q) ^ a = (2 : ZMod q) ^ b := by
      push_cast at h1
      exact h1
    have h4 : h_unit.unit ^ a = h_unit.unit ^ b := by
      apply Units.ext
      exact h2
    have h5 : a ≡ b [MOD orderOf h_unit.unit] := by
      exact pow_eq_pow_iff_modEq.mp h4
    have h6 : orderOf (2 : ZMod q) = orderOf h_unit.unit := by
      exact @orderOf_units _ _ h_unit.unit
    rwa [← h6] at h5
  · intro h
    have h1 : a ≡ b [MOD orderOf h_unit.unit] := by
      have h6 : orderOf (2 : ZMod q) = orderOf h_unit.unit := by
        exact @orderOf_units _ _ h_unit.unit
      have h7 : ordTwo q = orderOf (2 : ZMod q) := rfl
      rwa [h7, h6] at h
    have h2 : h_unit.unit ^ a = h_unit.unit ^ b := by
      exact pow_eq_pow_iff_modEq.mpr h1
    have h3 : (2 : ZMod q) ^ a = (2 : ZMod q) ^ b := by
      exact congr_arg Units.val h2
    have h4 : ((2 ^ a : ℕ) : ZMod q) = ((2 ^ b : ℕ) : ZMod q) := by
      push_cast
      exact h3
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h4

/-- LEAF. Unit U-1532. For odd `q`, every residue class `c` contains at most `L / e(q) + 1` of
the powers `2^μ`, `1 ≤ μ ≤ L`; the last step of the proof of Lemma 5, p. 134. -/
theorem card_pow_residue_le {q : ℕ} (hq : Odd q) (c L : ℕ) :
    (#{μ ∈ Icc 1 L | 2 ^ μ % q = c} : ℝ) ≤ L / ordTwo q + 1 := by
  sorry

/-- LEAF. Unit U-1532. Every `n` has at most two ordered representations `n = 2^a + 2^b`, the
uniqueness of `n = g^μ (1 + g^δ)` in the proof of Lemma 5, p. 134. -/
theorem card_two_pow_pairs_le (n : ℕ) :
    #{x ∈ range n ×ˢ range n | 2 ^ x.1 + 2 ^ x.2 = n} ≤ 2 := by
  sorry

/-- LEAF. Unit U-1532. Lemma 5, display (4), p. 134, with constant 2: for `k ≥ 2` the number
`r_{k,k}(0)` of pairs with `2^{ν₁} + ... + 2^{ν_k} = 2^{μ₁} + ... + 2^{μ_k}` is at most
`2 L^{2k-2}`. -/
theorem rkk_zero_le {k : ℕ} (hk : 2 ≤ k) (L : ℕ) :
    #{x : pairs k L | dif x = 0} ≤ 2 * L ^ (2 * k - 2) := by
  sorry

/-- LEAF. Unit U-1532. Lemma 5, display (5), p. 134: for odd `q` and `k ≥ 1`, the number of
pairs with `q ∣ n` is at most `L^{2k} / e(q) + L^{2k-1}`. -/
theorem card_dvd_dif_le {q : ℕ} (hq : Odd q) {k : ℕ} (hk : 1 ≤ k) (L : ℕ) :
    (#{x : pairs k L | (q : ℤ) ∣ dif x} : ℝ) ≤
      (L : ℝ) ^ (2 * k) / ordTwo q + (L : ℝ) ^ (2 * k - 1) := by
  sorry

/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133: an odd `q` with `e(q) ≤ x` divides
`M = ∏_{e ≤ x} (2^e - 1)`. -/
theorem dvd_Mprod {q x : ℕ} (hq : Odd q) (hx : ordTwo q ≤ x) : q ∣ Mprod x := by
  have h_dvd : q ∣ 2 ^ ordTwo q - 1 := dvd_two_pow_ordTwo_sub_one hq
  apply dvd_trans h_dvd
  have h_pos : 1 ≤ ordTwo q := ordTwo_pos hq
  have h_mem : ordTwo q ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨h_pos, hx⟩
  exact Finset.dvd_prod_of_mem (fun e => 2 ^ e - 1) h_mem

/-- LEAF. Unit U-1532. For `x ≥ 2`, `M = ∏_{e ≤ x} (2^e - 1) ≥ 3`, so `log log M` is
positive in the proof of Lemma 4, p. 133. -/
theorem three_le_Mprod {x : ℕ} (hx : 2 ≤ x) : 3 ≤ Mprod x := by
  have h_split : Finset.Icc 1 x = Finset.Icc 1 2 ∪ Finset.Icc 3 x := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [Mprod, h_split]
  have h_disj : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 x) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_Icc] at ha hb
    omega
  rw [Finset.prod_union h_disj]
  have h_prod1 : ∏ e ∈ Finset.Icc 1 2, (2 ^ e - 1) = 3 := by rfl
  rw [h_prod1]
  have h_prod2 : 1 ≤ ∏ e ∈ Finset.Icc 3 x, (2 ^ e - 1) := by
    apply Finset.one_le_prod
    intro i hi
    have h_le : 3 ≤ i := (Finset.mem_Icc.mp hi).1
    have h_pow : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h_le
    omega
  omega

/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133: `log M ≤ x² log 2`, the printed
`M ≤ g^{x²}`. -/
theorem log_Mprod_le (x : ℕ) : Real.log (Mprod x) ≤ (x : ℝ) ^ 2 * Real.log 2 := by
  sorry

/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133, the Euler product identity
`Σ_{q ∣ m} μ(q)² q / φ(q)² = ∏_{p ∣ m} (1 + p/(p-1)²)` for `m ≥ 1`. -/
theorem sum_divisors_eq_prod {m : ℕ} (hm : 0 < m) :
    ∑ q ∈ m.divisors, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 =
      ∏ p ∈ m.primeFactors, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
  sorry

/-- LEAF. Unit U-1532. Proof of Lemma 4, p. 133: `∏_{p ∣ m} (1 + p/(p-1)²) ≤ 2 m/φ(m)`, since
the factor over `p/(p-1)` is `1 + 1/(p(p-1))` and the product of these over all primes is below
2. -/
theorem prod_le_two_mul_div_totient {m : ℕ} (hm : 0 < m) :
    ∏ p ∈ m.primeFactors, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ 2 * ((m : ℝ) / m.totient) := by
  sorry

/-- LEAF. Unit U-1532. The bound `m/φ(m) ≪ log log m` for `m ≥ 3`, the last step of the proof of
Lemma 4, p. 133. -/
theorem div_totient_le_loglog :
    ∃ C : ℝ, ∀ m : ℕ, 3 ≤ m → (m : ℝ) / m.totient ≤ C * Real.log (Real.log m) := by
  sorry

/-- LEAF. Unit U-1532. Lemma 7, p. 135, for g = 2: there are `d` and `C` with
`n/φ(n) ≤ C Σ μ(q)²/φ(q)` over odd `q ∣ n`, `q ≤ log^d n`, for every `n ≥ 3`. -/
theorem lemma7 : ∃ d : ℕ, ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
    (n : ℝ) / n.totient ≤
      C * ∑ q ∈ n.divisors.filter (fun q : ℕ => Odd q ∧ (q : ℝ) ≤ Real.log n ^ d),
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / q.totient := by
  sorry

/-- LEAF. Unit U-1532. Lemma 8, p. 136, A. I. Vinogradov's bound: for `1 ≤ k ≤ N`, `N ≥ 2`,
`L = [log₂ N]`, `Σ_{n ≠ 0} r_{k,k}(n) |n|/φ(|n|) ≤ C L^{2k}` with an absolute `C`. -/
theorem lemma8 : ∃ C : ℝ, ∀ k N : ℕ, 1 ≤ k → k ≤ N → 2 ≤ N →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) ≤ C * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  sorry

/-- ASSEMBLY, CONDITIONAL ON the leaves `dvd_Mprod`, `three_le_Mprod`, `log_Mprod_le`,
`sum_divisors_eq_prod`, `prod_le_two_mul_div_totient` and `div_totient_le_loglog`.
Lemma 4, p. 133, for g = 2: `Σ μ(q)² q / φ(q)² ≪ log x` over odd `q` with `e(q) ≤ x`, here over
any finite range `1 ≤ q ≤ Q`, uniformly in `Q`. -/
theorem lemma4 : ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → ∀ Q : ℕ,
    ∑ q ∈ Icc 1 Q with Odd q ∧ ordTwo q ≤ x,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2 ≤
        C * Real.log x := by
  obtain ⟨C, hC⟩ := div_totient_le_loglog
  refine ⟨4 * C, fun x hx Q => ?_⟩
  set M := Mprod x with hMdef
  have hM3 : 3 ≤ M := three_le_Mprod hx
  have hM0 : 0 < M := by omega
  have hsub : (Icc 1 Q).filter (fun q => Odd q ∧ ordTwo q ≤ x) ⊆ M.divisors := by
    intro q hq
    rw [mem_filter] at hq
    exact Nat.mem_divisors.mpr ⟨dvd_Mprod hq.2.1 hq.2.2, hM0.ne'⟩
  have h1 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2)
    (fun q _ _ => by positivity)
  rw [sum_divisors_eq_prod hM0] at h1
  have h2 := prod_le_two_mul_div_totient hM0
  have h3 := hC M hM3
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hlogM1 : 1 < Real.log M := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hll0 : 0 < Real.log (Real.log M) := Real.log_pos hlogM1
  have htot : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM0
  have hratio : 0 < (M : ℝ) / M.totient := div_pos (by linarith) htot
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have : C * Real.log (Real.log M) < 0 := mul_neg_of_neg_of_pos hneg hll0
    linarith
  have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogMle := log_Mprod_le x
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll : Real.log (Real.log M) ≤ 2 * Real.log x := by
    have hle : Real.log M ≤ (x : ℝ) ^ 2 := by
      calc Real.log M ≤ (x : ℝ) ^ 2 * Real.log 2 := hlogMle
        _ ≤ (x : ℝ) ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (x : ℝ) ^ 2 := by ring
    calc Real.log (Real.log M) ≤ Real.log ((x : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) hle
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  calc ∑ q ∈ Icc 1 Q with Odd q ∧ ordTwo q ≤ x,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 * q / (q.totient : ℝ) ^ 2
      ≤ ∏ p ∈ M.primeFactors, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := h1
    _ ≤ 2 * ((M : ℝ) / M.totient) := h2
    _ ≤ 2 * (C * Real.log (Real.log M)) := by linarith
    _ ≤ 2 * (C * (2 * Real.log x)) := by
        have := mul_le_mul_of_nonneg_left hll hC0
        linarith
    _ = 4 * C * Real.log x := by ring

end LeanLab.Linnik.Decomp1532a
