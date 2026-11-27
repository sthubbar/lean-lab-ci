import LeanLab.ExceptionalSet.SPLIT_leaf_small_block_sum_bound

/-!
Counterexample to the LEAF `leaf_polynomial_block_sum` of
`LeanLab.ExceptionalSet.SPLIT_leaf_small_block_sum_bound`, unit S5-16 of CLOUD S5
burst-20261127.

The LEAF promises one saving `ρ > 0` and one constant `K` for every block of length
`1 ≤ m ≤ P^(c1 - c4/2)`. It has no lower bound on `m`, while the saving of Karacuba's
Lemma 2 at the `s`-th Taylor coefficient needs the denominator `q ≤ P^(c2 s)` to be below
`m^s`, which the split's own comment derives from `m ≥ P^(c1 - c4/2)/2`. Without that bound
the conclusion fails: at `c0 = c1 = 1/2`, `c2 = c4 = 1/8`, `c3 = 1/16`, `n = 2`, `N = a = 0`,
`T = {2}`, `t = 8 k`, `P = t^16` and `f x = t^(-2) x^2`, every hypothesis of the LEAF holds,
the Taylor polynomial of `f` is `f`, every phase `t^(-2) y^2` with `y < k` is at most `1/64`,
so the block sum of length `m = k` has norm at least `k / 2`, which exceeds
`(1/2) K k^(1-ρ)` once `k^ρ > K`.

The theorem below refutes the conclusion of the LEAF outright, without using `KarLemma2`.
So the LEAF holds only if `KarLemma2` is refutable; the twin at the end records that.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit.FalseS5

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

theorem quad_taylor (β : ℝ) (b y : ℝ) (hb : 0 < b) :
    taylorWithinEval (fun x : ℝ => β * x ^ 2) 2 (Set.Icc 0 b) 0 y = β * y ^ 2 := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) b) := uniqueDiffOn_Icc hb
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have e1 : iteratedDerivWithin 1 (fun x : ℝ => β * x ^ 2) (Set.Icc 0 b) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((quad_contDiff β _).contDiffAt) h0, quad_iter1]
    ring
  have e2 : iteratedDerivWithin 2 (fun x : ℝ => β * x ^ 2) (Set.Icc 0 b) 0 = 2 * β := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((quad_contDiff β _).contDiffAt) h0, quad_iter2]
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, taylorWithinEval_succ, taylorWithinEval_succ,
    taylor_within_zero_eval]
  simp only [zero_add] at *
  rw [e1, e2]
  simp
  ring


theorem cos_ge_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 / 2 ≤ Real.cos x := by
  have := Real.one_sub_sq_div_two_le_cos (x := x)
  nlinarith

theorem leaf_polynomial_block_sum_concl_false :
    ¬ (∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ ρ K : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ≤ 3 * c4 / (4 * c1) ∧ 1 ≤ K ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 → 1 < P →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              (m : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) →
              8 * Real.pi * ((n : ℝ) + 1) ≤
                (P : ℝ) ^ ((c4 / 2) * ((n : ℝ) + 1 + ρ) - c1 * ρ) →
              ‖∑ y ∈ Finset.range m,
                eC (taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) (a : ℝ)
                  ((a : ℝ) + (y : ℝ)))‖ ≤ 1 / 2 * (K * (m : ℝ) ^ (1 - ρ))) := by
  intro hall
  obtain ⟨ρ, K, hρ0, hρ1, hρc, hK, hmain⟩ :=
    hall (1 / 2) (1 / 2) (1 / 8) (1 / 16) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hρc' : ρ ≤ 3 / 16 := by
    have : (3 : ℝ) * (1 / 8) / (4 * (1 / 2)) = 3 / 16 := by norm_num
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (max 10 (K ^ (1 / ρ)))
  have hk10 : (10 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkK : K ^ (1 / ρ) < k := lt_of_le_of_lt (le_max_right _ _) hk
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
  have hthr : 8 * Real.pi * (((2 : ℕ) : ℝ) + 1) ≤
      (P : ℝ) ^ ((1 / 8 / 2) * (((2 : ℕ) : ℝ) + 1 + ρ) - 1 / 2 * ρ) := by
    rw [hPpow]
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    calc 8 * Real.pi * (((2 : ℕ) : ℝ) + 1) ≤ (t : ℝ) := by
          rw [htr]; push_cast; nlinarith
      _ = (t : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht1 (by push_cast; nlinarith)
  have hkP : 0 + k ≤ 0 + P := by
    have : k ≤ t := by rw [ht]; omega
    have : t ≤ P := by
      rw [hPdef]
      exact Nat.le_self_pow (by norm_num) t
    omega
  have hbound := hmain 0 P 2 (by omega) le_rfl
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hP1 f {2} hhyp 0 k le_rfl hkP hk1 hm hthr
  -- the Taylor polynomial is f itself
  have htay : ∀ y ∈ Finset.range k,
      taylorWithinEval f 2 (Set.Icc ((0 : ℕ) : ℝ) (((0 : ℕ) : ℝ) + (k : ℝ))) ((0 : ℕ) : ℝ)
        (((0 : ℕ) : ℝ) + (y : ℝ)) = β * (y : ℝ) ^ 2 := by
    intro y _
    simp only [Nat.cast_zero, zero_add]
    exact quad_taylor β k y hkpos
  rw [Finset.sum_congr rfl (fun y hy => by rw [htay y hy])] at hbound
  -- lower bound by the real part
  have hre : (k : ℝ) / 2 ≤ ‖∑ y ∈ Finset.range k, eC (β * (y : ℝ) ^ 2)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have : ∀ y ∈ Finset.range k, (1 / 2 : ℝ) ≤ (eC (β * (y : ℝ) ^ 2)).re := by
      intro y hy
      rw [eC_re']
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
  -- the saving cannot hold for large k
  have hkρ : K < (k : ℝ) ^ ρ := by
    have hK0 : 0 ≤ K ^ (1 / ρ) := Real.rpow_nonneg (by linarith) _
    have := Real.rpow_lt_rpow hK0 hkK hρ0
    rwa [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hρ0.ne', Real.rpow_one] at this
  have hsplit : (k : ℝ) ^ (1 - ρ) = k / (k : ℝ) ^ ρ := by
    rw [Real.rpow_sub hkpos, Real.rpow_one]
  have hkρpos : 0 < (k : ℝ) ^ ρ := Real.rpow_pos_of_pos hkpos _
  have hlt : K * (k : ℝ) ^ (1 - ρ) < k := by
    rw [hsplit, mul_div_assoc', div_lt_iff₀ hkρpos]
    nlinarith
  linarith


/-- The LEAF `leaf_polynomial_block_sum` implies the negation of the cited Lemma 2 as
formalized, so it is false unless `KarLemma2` is. -/
example : type_of% @LeanLab.ExceptionalSet.U1539.KaracubaSplit.leaf_polynomial_block_sum →
    ¬ LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2 :=
  fun hl h2 => leaf_polynomial_block_sum_concl_false (hl h2)

end LeanLab.ExceptionalSet.U1539.KaracubaSplit.FalseS5
