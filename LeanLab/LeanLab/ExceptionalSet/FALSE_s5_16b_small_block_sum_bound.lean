import LeanLab.ExceptionalSet.SPLIT_leaf_small_case

/-!
Counterexample to the LEAF `leaf_small_block_sum_bound` of
`LeanLab.ExceptionalSet.SPLIT_leaf_small_case`, found by CLOUD S5 burst-20261127 while
working unit S5-16, a KEEP GOING step.

The LEAF is the p. 248 short block estimate of the small `n` case of Karacuba's Theorem 1,
chapter I section 2: `|Σ_{x ∈ [a, a+m)} e(f x)| ≤ A0 m^(1-ρ)` for every block of length
`1 ≤ m ≤ [P^(c1 - c4/2)]`. As stated it has no lower bound on `m`, and fails for the same
quadratic phase that refutes its sub LEAF `leaf_polynomial_block_sum`: at
`c0 = c1 = 1/2`, `c2 = c4 = 1/8`, `c3 = 1/16`, `n = 2`, `N = a = 0`, `T = {2}`,
`t = 8 k`, `P = t^16`, `f x = t^(-2) x^2`, the block `[0, k)` has sum of norm at least `k/2`,
which exceeds `A0 k^(1-ρ)` once `k^ρ > 2 A0`. The proof does not use `KarLemma2`.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit.FalseS5b

open LeanLab.ExceptionalSet.U1539 Real

private theorem eC_re' (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  rw [eC, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _
theorem quad_deriv (β : ℝ) : deriv (fun x : ℝ => β * x ^ 2) = fun x => 2 * β * x := by
  funext x
  have := ((hasDerivAt_pow 2 x).const_mul β).deriv
  rw [this]
  push_cast
  ring

theorem quad_iter2 (β : ℝ) : iteratedDeriv 2 (fun x : ℝ => β * x ^ 2) = fun _ => 2 * β := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, quad_deriv]
  funext x
  have := ((hasDerivAt_id x).const_mul (2 * β)).deriv
  simp only [id] at this
  rw [show (fun x => 2 * β * x) = (fun x => 2 * β * id x) from rfl]
  rw [((hasDerivAt_id x).const_mul (2 * β)).deriv, mul_one]

theorem quad_iter3 (β : ℝ) : iteratedDeriv 3 (fun x : ℝ => β * x ^ 2) = fun _ => 0 := by
  rw [iteratedDeriv_succ, quad_iter2]
  funext x
  exact deriv_const x _

theorem quad_iter1 (β : ℝ) : iteratedDeriv 1 (fun x : ℝ => β * x ^ 2) = fun x => 2 * β * x := by
  rw [iteratedDeriv_one, quad_deriv]

theorem quad_contDiff (β : ℝ) (k : WithTop ℕ∞) : ContDiff ℝ k (fun x : ℝ => β * x ^ 2) := by
  fun_prop


theorem cos_ge_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 / 2 ≤ Real.cos x := by
  have := Real.one_sub_sq_div_two_le_cos (x := x)
  nlinarith


/-- The conclusion of the LEAF `leaf_small_block_sum_bound` fails: a quadratic phase whose
coefficient is `P^(-1/8)` does not move on a block of length `P^(1/16)/8`. -/
theorem leaf_small_block_sum_bound_concl_false :
    ¬ (∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A0 ρ : ℝ, 0 < A0 ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              m ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ →
              ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ)) := by
  intro hall
  obtain ⟨A0, ρ, hA0, hρ0, hρ1, hmain⟩ :=
    hall (1 / 2) (1 / 2) (1 / 8) (1 / 16) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨k, hk⟩ := exists_nat_gt (max 10 ((2 * A0) ^ (1 / ρ)))
  have hk10 : (10 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkK : (2 * A0) ^ (1 / ρ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hk1 : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
  set t : ℕ := 8 * k with ht
  have htr : (t : ℝ) = 8 * k := by rw [ht]; push_cast; ring
  have ht1 : (1 : ℝ) ≤ t := by rw [htr]; linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  set P : ℕ := t ^ 16 with hPdef
  have hPpow : ∀ r : ℝ, (P : ℝ) ^ r = (t : ℝ) ^ (16 * r) := by
    intro r
    rw [hPdef, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  have hP1 : 1 < P := by
    have : 1 < t := by
      have : (1 : ℝ) < t := by rw [htr]; linarith
      exact_mod_cast this
    rw [hPdef]
    exact Nat.one_lt_pow (by norm_num) this
  set β : ℝ := (t : ℝ) ^ (-(2 : ℝ)) with hβ
  have hβ' : β = 1 / ((t : ℝ) ^ 2) := by
    rw [hβ, Real.rpow_neg ht0, one_div]
    norm_cast
  have hβpos : 0 < β := by rw [hβ']; positivity
  set f : ℝ → ℝ := fun x => β * x ^ 2 with hf
  have hhyp : KarHyp (1 / 2) (1 / 2) (1 / 8) (1 / 16) 0 P 2 f {2} := by
    refine ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, (quad_contDiff β _).contDiffOn⟩, ?_, ?_, ?_, ?_⟩
    · intro x _
      rw [hf, quad_iter3]
      simp only [zero_div, abs_zero]
      positivity
    · intro s hs
      simp only [Finset.mem_singleton] at hs
      simp [hs]
    · simp
    · intro s hs x _
      simp only [Finset.mem_singleton] at hs
      subst hs
      rw [hf, quad_iter2, hPpow, hPpow]
      have e : |2 * β / ((2 : ℕ).factorial : ℝ)| = β := by
        rw [abs_of_pos (by positivity)]
        norm_num
      rw [e, hβ]
      constructor
      · apply Real.rpow_le_rpow_of_exponent_le ht1
        norm_num
      · apply le_of_eq
        congr 1
        norm_num
  have hm : (k : ℝ) ≤ (P : ℝ) ^ ((1 / 2 : ℝ) - (1 / 8) / 2) := by
    rw [hPpow]
    calc (k : ℝ) ≤ (t : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one, htr]; linarith
      _ ≤ (t : ℝ) ^ (16 * ((1 / 2 : ℝ) - (1 / 8) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hkP : 0 + k ≤ 0 + P := by
    have : k ≤ t := by rw [ht]; omega
    have : t ≤ P := by
      rw [hPdef]
      exact Nat.le_self_pow (by norm_num) t
    omega
  have hbound := hmain 0 P 2 (by omega) le_rfl
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) f {2} hhyp 0 k le_rfl hkP hk1
    (Nat.le_floor hm)
  rw [zero_add, ← Finset.range_eq_Ico] at hbound
  have hre : (k : ℝ) / 2 ≤ ‖∑ y ∈ Finset.range k, eC (f (y : ℝ))‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have : ∀ y ∈ Finset.range k, (1 / 2 : ℝ) ≤ (eC (f (y : ℝ))).re := by
      intro y hy
      rw [eC_re', hf]
      rw [Finset.mem_range] at hy
      have hy' : (y : ℝ) ≤ k := by exact_mod_cast hy.le
      have hy0 : (0 : ℝ) ≤ y := by positivity
      have hsq : β * (y : ℝ) ^ 2 ≤ 1 / 64 := by
        rw [hβ', htr]
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith
      apply cos_ge_half
      · positivity
      · have hpi : Real.pi < 3.15 := Real.pi_lt_d2
        have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        linarith
    calc (k : ℝ) / 2 = ∑ y ∈ Finset.range k, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum this
  have hkρ : 2 * A0 < (k : ℝ) ^ ρ := by
    have hK0 : 0 ≤ (2 * A0) ^ (1 / ρ) := Real.rpow_nonneg (by linarith) _
    have := Real.rpow_lt_rpow hK0 hkK hρ0
    rwa [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hρ0.ne', Real.rpow_one] at this
  have hsplit : (k : ℝ) ^ (1 - ρ) = k / (k : ℝ) ^ ρ := by
    rw [Real.rpow_sub hkpos, Real.rpow_one]
  have hkρpos : 0 < (k : ℝ) ^ ρ := Real.rpow_pos_of_pos hkpos _
  have hlt : A0 * (k : ℝ) ^ (1 - ρ) < k / 2 := by
    rw [hsplit, mul_div_assoc', div_lt_iff₀ hkρpos]
    nlinarith
  linarith

/-- The LEAF `leaf_small_block_sum_bound` implies the negation of the cited Lemma 2 as
formalized, so it is false unless `KarLemma2` is. -/
example : type_of% @LeanLab.ExceptionalSet.U1539.KaracubaSplit.leaf_small_block_sum_bound →
    ¬ LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2 :=
  fun hl h2 => leaf_small_block_sum_bound_concl_false (hl h2)

end LeanLab.ExceptionalSet.U1539.KaracubaSplit.FalseS5b
