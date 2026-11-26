/-
Re-split of the two leaves `leaf_karL2_core` and `leaf_karJ0_lowdeg` of
`LeanLab.ExceptionalSet.KarLemma2Steps`, Karacuba 1971 Lemma 2 p. 243-244, Vinogradov's
estimate of a Weyl sum, and Lemma 1, Vinogradov's mean value theorem, in degrees `2 ≤ d ≤ 12`.

1. `leaf_karJ0_lowdeg`. Degree padding does NOT reduce it to the case `d ≥ 12` of `KarLemma1`:
   `karJ0 d k M` counts solutions of the `d` equations `Σ u_i^j = Σ v_i^j`, `j ≤ d`; a lower degree
   has fewer equations, so `karJ0 d k M ≥ karJ0 12 k M`, the wrong direction for an upper bound,
   and the exponent of the bound also changes with `d`. Instead the file follows Vinogradov's
   proof of the mean value theorem, induction on `l`:
   * base `l = 1`: PROVED in `karJ0_lowdeg_base` from the trivial count
     `karJ0 d k M ≤ d! (M+1)^{2k-d}`, `leaf_karJ0_trivial_count`, LEAF MEDIUM, Newton's identities:
     the power sums `p_1, ..., p_d` determine the multiset of `v_1, ..., v_d`;
   * step `l → l + 1`: `leaf_karJ0_step`, LEAF HARD, Vinogradov's recursive lemma, which raises
     `k` by `d` and multiplies the defect `d(d+1)/2 (1-1/d)^l` by `1 - 1/d`.
   `karJ0_lowdeg_from_leaves` assembles them, twin of `leaf_karJ0_lowdeg`.
2. `leaf_karL2_core`. PROVED step: Lemma 1 enters only through `KarJ0Bound (n+1)` for `k = b_l`;
   `karL2_core_from_afterJ0` substitutes that bound into the averaged bound of `karL2_reduce` by
   monotonicity. What remains, `leaf_karL2_core_afterJ0`, LEAF HARD, is the choice of `M` and of
   `l`, the sum over `x` of the products of the sums `𝔖_s(m A_s(x))` using the rational
   approximation of `α_r` and Lemma 3, and the exponent arithmetic. No `J_k(0)` occurs in it.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KarLemma2Steps

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Lemma 1 in low degree: base case and induction step -/

/-- LEAF: Vinogradov's mean value theorem, Karacuba's reference [1], the starting count of the
induction on `l`. MEDIUM. For `k ≥ d`, fixing `u_1, ..., u_k` and `v_{d+1}, ..., v_k` fixes the
power sums `p_j = Σ_{i ≤ d} v_i^j`, `j ≤ d`, and by Newton's identities these determine the
multiset `{v_1, ..., v_d}`, so at most `d!` ordered tuples: `J_k(0) ≤ d! (M+1)^{2k-d}`. -/
theorem leaf_karJ0_trivial_count :
    ∀ d k M : ℕ, 1 ≤ d → d ≤ k →
      karJ0 d k M ≤ (d.factorial : ℝ) * ((M : ℝ) + 1) ^ (2 * k - d) := by
  sorry

/-- LEAF: Vinogradov's mean value theorem, Karacuba's reference [1], the induction step on `l`
in its proof, through Vinogradov's recursive lemma, in the degrees `2 ≤ d ≤ 12`. HARD.
From the bound with `k = b_l = d l + ⌊d(d+1)/4 + 1⌋` for every range `M` one gets the bound with
`k = b_{l+1} = b_l + d`, the constant multiplied by `(20d)^{d(d+1)/2}` and the defect
`d(d+1)/2 (1-1/d)^l` multiplied by `1 - 1/d`. -/
theorem leaf_karJ0_step : ∀ d : ℕ, 2 ≤ d → d ≤ 12 → ∀ l : ℕ, 0 < l →
    (∀ M : ℕ,
      karJ0 d (d * l + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M <
        (20 * d : ℝ) ^ (((d * (d + 1) : ℕ) : ℝ) / 2 * l) *
          ((M : ℝ) + 1) ^ ((2 * ((d * l + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) : ℝ)
            - ((d * (d + 1) : ℕ) : ℝ) / 2 + ((d * (d + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (d : ℝ)) ^ l)) →
    ∀ M : ℕ,
      karJ0 d (d * (l + 1) + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M <
        (20 * d : ℝ) ^ (((d * (d + 1) : ℕ) : ℝ) / 2 * ((l + 1 : ℕ) : ℝ)) *
          ((M : ℝ) + 1) ^ ((2 * ((d * (l + 1) + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) : ℝ)
            - ((d * (d + 1) : ℕ) : ℝ) / 2
            + ((d * (d + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (d : ℝ)) ^ (l + 1)) := by
  sorry

/-- PROVED from `leaf_karJ0_trivial_count`: the case `l = 1` of `KarJ0Bound d`, `d ≥ 1`. -/
theorem karJ0_lowdeg_base (d : ℕ) (hd : 1 ≤ d) (M : ℕ) :
    karJ0 d (d * 1 + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M <
      (20 * d : ℝ) ^ (((d * (d + 1) : ℕ) : ℝ) / 2 * ((1 : ℕ) : ℝ)) *
        ((M : ℝ) + 1) ^ ((2 * ((d * 1 + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) : ℝ)
          - ((d * (d + 1) : ℕ) : ℝ) / 2 + ((d * (d + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (d : ℝ)) ^ 1) := by
  set k := d * 1 + ⌊((d * (d + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hkdef
  have hdk : d ≤ k := by rw [hkdef]; omega
  have hJ := leaf_karJ0_trivial_count d k M hd hdk
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set A : ℝ := (M : ℝ) + 1 with hA
  have hA1 : 1 ≤ A := by rw [hA]; have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith
  have hD : (((d * (d + 1) : ℕ) : ℝ)) = (d : ℝ) * ((d : ℝ) + 1) := by push_cast; ring
  -- the constant
  have hfac : (d.factorial : ℝ) < (20 * d : ℝ) ^ (((d * (d + 1) : ℕ) : ℝ) / 2 * ((1 : ℕ) : ℝ)) := by
    have h1 : (d.factorial : ℝ) ≤ (d : ℝ) ^ d := by exact_mod_cast Nat.factorial_le_pow d
    have h2 : (d : ℝ) ^ d < (20 * d : ℝ) ^ d :=
      pow_lt_pow_left₀ (by linarith) hd0.le (by omega)
    have h3 : (20 * d : ℝ) ^ d ≤ (20 * d : ℝ) ^ (((d * (d + 1) : ℕ) : ℝ) / 2 * ((1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      rw [hD]; push_cast
      nlinarith
    linarith
  -- the power of `M + 1`
  have hpow : A ^ (2 * k - d) ≤ A ^ ((2 * ((k : ℕ) : ℝ) : ℝ)
          - ((d * (d + 1) : ℕ) : ℝ) / 2 + ((d * (d + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (d : ℝ)) ^ 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hA1
    rw [Nat.cast_sub (by omega), hD]
    push_cast
    have : (d : ℝ) * ((d : ℝ) + 1) / 2 * (1 - 1 / (d : ℝ)) = ((d : ℝ) + 1) * ((d : ℝ) - 1) / 2 := by
      field_simp
    rw [pow_one, this]
    nlinarith
  have hApos : 0 < A ^ (2 * k - d) := by positivity
  calc karJ0 d k M ≤ (d.factorial : ℝ) * A ^ (2 * k - d) := hJ
    _ < (20 * d : ℝ) ^ (((d * (d + 1) : ℕ) : ℝ) / 2 * ((1 : ℕ) : ℝ)) * A ^ (2 * k - d) :=
        mul_lt_mul_of_pos_right hfac hApos
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- PROVED from the two LEAFs above, by induction on `l`: `KarJ0Bound d` for `2 ≤ d ≤ 12`. -/
theorem karJ0_lowdeg_from_leaves : ∀ d : ℕ, 2 ≤ d → d ≤ 12 → KarJ0Bound d := by
  intro d hd2 hd12 l M hl
  induction l, hl using Nat.le_induction generalizing M with
  | base => simpa using karJ0_lowdeg_base d (by omega) M
  | succ l hl ih =>
    have h := leaf_karJ0_step d hd2 hd12 l hl ih M
    simpa using h

/-- Exact type twin of `leaf_karJ0_lowdeg`. -/
theorem leaf_karJ0_lowdeg_proved : type_of% @leaf_karJ0_lowdeg := karJ0_lowdeg_from_leaves

/-! ### The core: Lemma 1 substituted -/

/-- LEAF: Karacuba Lemma 2 p. 243-244, the end of Vinogradov's proof [2] after Lemma 1 has been
substituted for `J_k(0)` with `k = b_L = (n+1) L + ⌊(n+1)(n+2)/4 + 1⌋`. HARD. One chooses the range
`M` and the integer `L`, sums over `1 ≤ x ≤ P` the products of the sums `𝔖_s(m A_s(x))` using the
approximation `α_r = a/q + θ/q²`, the spacing of the fractional parts of the Taylor coefficients
and Lemma 3, and does the exponent arithmetic giving `ρ = τ/(3 n² l)` and the constant
`(8n)^{0.5 n l}`. Neither an exponential sum nor `J_k(0)` occurs. -/
theorem leaf_karL2_core_afterJ0 :
    ∀ n m P : ℕ, 1 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ∃ M L : ℕ, 0 < L ∧
        (((M : ℝ) + 1) ^ 2)⁻¹ * ∑ x ∈ Finset.Icc 1 P,
          (((M : ℝ) + 1) ^ (8 * ((n + 1) * L + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊) ^ 2
              - 4 * ((n + 1) * L + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) *
            ((20 * ((n + 1 : ℕ) : ℝ) : ℝ) ^ ((((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 2 * L) *
              ((M : ℝ) + 1) ^ ((2 * (((n + 1) * L
                  + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) : ℝ)
                - (((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 2
                + (((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 2 * (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ L)) ^ 2 *
            ∏ s ∈ Finset.Icc 1 (n + 1), karSigma ((n + 1) * L
                + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M s ((m : ℝ) * karL2Coef n α x s))
            ^ (((4 * ((n + 1) * L + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊) ^ 2 : ℕ) : ℝ)⁻¹)
          + 2 * (M : ℝ) ^ 2 <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  sorry

/-- PROVED from `leaf_karL2_core_afterJ0`: the exact statement of `leaf_karL2_core`, with Lemma 1
entering through `KarJ0Bound (n+1)` at `k = b_L` and monotonicity of the averaged bound. -/
theorem karL2_core_from_afterJ0 :
    ∀ n m P : ℕ, 1 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 → KarJ0Bound (n + 1) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ∃ M k : ℕ, 1 ≤ k ∧
        (((M : ℝ) + 1) ^ 2)⁻¹ * ∑ x ∈ Finset.Icc 1 P,
          (((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * karJ0 (n + 1) k M ^ 2 *
            ∏ s ∈ Finset.Icc 1 (n + 1), karSigma k M s ((m : ℝ) * karL2Coef n α x s))
            ^ (((4 * k ^ 2 : ℕ) : ℝ)⁻¹) + 2 * (M : ℝ) ^ 2 <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hJ
  obtain ⟨M, L, hL, hlt⟩ := leaf_karL2_core_afterJ0 n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  refine ⟨M, (n + 1) * L + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊, ?_, ?_⟩
  · have : 1 ≤ (n + 1) * L := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega
  refine lt_of_le_of_lt ?_ hlt
  have hS : ∀ x : ℕ, 0 ≤ ∏ s ∈ Finset.Icc 1 (n + 1), karSigma ((n + 1) * L
      + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M s ((m : ℝ) * karL2Coef n α x s) :=
    fun x => Finset.prod_nonneg fun s _ => karSigma_nonneg _ _ _ _
  have hJ0 := karJ0_nonneg (n + 1) ((n + 1) * L + ⌊(((n + 1) * (n + 1 + 1) : ℕ) : ℝ) / 4 + 1⌋₊) M
  have hJb := (hJ L M hL).le
  gcongr with x hx
  all_goals first
    | exact hS x
    | exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hJ0 2)) (hS x)

/-- Exact type twin of `leaf_karL2_core`. -/
theorem leaf_karL2_core_proved : type_of% @leaf_karL2_core := karL2_core_from_afterJ0

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karJ0_lowdeg_base
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.leaf_karJ0_lowdeg_proved
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.leaf_karL2_core_proved
