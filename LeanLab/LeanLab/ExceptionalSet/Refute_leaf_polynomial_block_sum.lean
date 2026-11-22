/-
Refutation of the leaf `leaf_polynomial_block_sum` of
`LeanLab.ExceptionalSet.SPLIT_leaf_small_block_sum_bound`.

The leaf asks for one saving `rho > 0` and one constant `K`, depending on `c0, ..., c4` only,
such that every block of length `1 <= m <= P^(c1 - c4/2)` has Taylor polynomial block sum at most
`(1/2) K m^(1-rho)`. Only an upper bound on `m` is assumed. Karacuba's Lemma 2 gives a saving
only when the denominator `Q_s <= P^(c2 s)` of the approximation to the `s`-th coefficient is
below `m^s`, p. 248 `Q_s <= P^(c2 s) < P2^s`, which needs `m` at least about `P^(c2)`.
A block much shorter than `P^(c2)` has no saving at all.

Counterexample: `c0 = c1 = 1/2`, `c2 = c3 = 1/8`, `c4 = 1/4`, so `c2 + c4 = 3/8 < c1`. Take
`n = 2`, `T = {2}`, `N = a = 0`, `P = t^8` with `t = 4u`, and `f x = x^2 / t^2`. Then
`f''/2 = t^(-2) = P^(-2 c2) = P^(-2 c3)`, `f''' = 0`, the Taylor polynomial of order two is `f`
itself, and on the block of length `m = u` every phase `y^2/t^2` is at most `1/16`, so every term
`e(y^2/t^2)` has real part at least `1/2`. The block sum has norm at least `u/2`, while the leaf
asks for at most `(1/2) K u^(1-rho)`; this fails once `u^rho > K`. The threshold hypothesis
`8 pi (n+1) <= P^((c4/2)(n+1+rho) - c1 rho) = t^(3 - 3 rho)` holds for `t >= 400` since
`rho <= 3 c4/(4 c1) = 3/8`.

The same `f` refutes the parent sealed statement `leaf_small_block_sum_bound` too: there the sum
is over `f` itself, which is the same sum.

This file states no new definition. AI wrote this code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_small_block_sum_bound

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- `Re e(t) = cos (2 pi t)`. Standard. -/
theorem refute_pbs_eC_re (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  rw [eC, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- The iterated derivatives of the quadratic `x^2 / t^2` of the counterexample:
the second is the constant `2 / t^2`. -/
theorem refute_pbs_iteratedDeriv_two (t : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => x ^ 2 / t ^ 2) = fun _ => 2 / t ^ 2 := by
  have h1 : deriv (fun x : ℝ => x ^ 2 / t ^ 2) = fun x => 2 * x / t ^ 2 := by
    funext x
    have := ((hasDerivAt_pow 2 x).div_const (t ^ 2)).deriv
    rw [this]; push_cast; ring
  have h2 : deriv (fun x : ℝ => 2 * x / t ^ 2) = fun _ => 2 / t ^ 2 := by
    funext x
    have := (((hasDerivAt_id x).const_mul 2).div_const (t ^ 2)).deriv
    simp only [id] at this
    rw [this]; ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]

/-- The third derivative of `x^2 / t^2` vanishes. -/
theorem refute_pbs_iteratedDeriv_three (t : ℝ) :
    iteratedDeriv 3 (fun x : ℝ => x ^ 2 / t ^ 2) = fun _ => 0 := by
  rw [iteratedDeriv_succ, refute_pbs_iteratedDeriv_two]
  funext x
  exact deriv_const x _

/-- The quadratic is its own Taylor polynomial of order two, on any interval `[0, b]`:
Taylor's bound with a vanishing third derivative. -/
theorem refute_pbs_taylor_eq (t b x : ℝ) (hb : 0 < b) (hx : x ∈ Set.Icc (0 : ℝ) b) :
    taylorWithinEval (fun x : ℝ => x ^ 2 / t ^ 2) 2 (Set.Icc (0 : ℝ) b) 0 x = x ^ 2 / t ^ 2 := by
  have hcd : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 2 / t ^ 2) := (contDiff_id.pow 2).div_const _
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) b) := uniqueDiffOn_Icc hb
  have hC : ∀ y ∈ Set.Icc (0 : ℝ) b,
      ‖iteratedDerivWithin (2 + 1) (fun x : ℝ => x ^ 2 / t ^ 2) (Set.Icc (0 : ℝ) b) y‖ ≤ 0 := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hcd.contDiffAt.of_le le_top) hy,
      show (2 + 1 : ℕ) = 3 from rfl, refute_pbs_iteratedDeriv_three]
    simp
  have h := taylor_mean_remainder_bound (f := fun x : ℝ => x ^ 2 / t ^ 2) (a := 0) (b := b)
    (C := 0) (x := x) (n := 2) hb.le (hcd.contDiffOn.of_le le_top) hx hC
  rw [zero_mul, zero_div, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-- The leaf `leaf_polynomial_block_sum` without its hypothesis `KarLemma2` is false: the
counterexample of the file header, a block much shorter than `P^(c2)` on which the quadratic
`x^2 / t^2` has almost constant phase. -/
theorem leaf_polynomial_block_sum_body_false :
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
  intro H
  obtain ⟨ρ, K, hρ0, _hρ1, hρc, hK1, hB⟩ :=
    H (1 / 2) (1 / 2) (1 / 8) (1 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hρ38 : ρ ≤ 3 / 8 := by
    have : (3 : ℝ) * (1 / 4) / (4 * (1 / 2)) = 3 / 8 := by norm_num
    linarith
  -- the block length `u`
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ, u = ⌈K ^ (1 / ρ)⌉₊ + 100 := ⟨_, rfl⟩
  have hu100 : (100 : ℝ) ≤ (u : ℝ) := by
    rw [hu_def]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈K ^ (1 / ρ)⌉₊]
  have huK : K ^ (1 / ρ) < (u : ℝ) := by
    rw [hu_def]; push_cast; linarith [Nat.le_ceil (K ^ (1 / ρ))]
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ, t = 4 * u := ⟨_, rfl⟩
  have htR : (t : ℝ) = 4 * (u : ℝ) := by rw [ht_def]; push_cast; ring
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by rw [htR]; linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
  obtain ⟨P, hP_def⟩ : ∃ P : ℕ, P = t ^ 8 := ⟨_, rfl⟩
  have hPpow : ∀ r : ℝ, (P : ℝ) ^ r = (t : ℝ) ^ (8 * r) := by
    intro r
    rw [hP_def, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hu1 : 1 ≤ u := by
    have : (1 : ℝ) ≤ (u : ℝ) := by linarith
    exact_mod_cast this
  have ht400 : 400 ≤ t := by
    have : (400 : ℝ) ≤ (t : ℝ) := by rw [htR]; linarith
    exact_mod_cast this
  have hP1 : 1 < P := by
    rw [hP_def]
    calc 1 < 400 := by norm_num
      _ ≤ t := ht400
      _ = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hP0 : 0 < P := by omega
  have hut : u ≤ P := by
    rw [hP_def]
    calc u ≤ t := by rw [ht_def]; omega
      _ = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  -- the hypotheses of the counterexample
  obtain ⟨f, hf_def⟩ : ∃ f : ℝ → ℝ, f = fun x => x ^ 2 / (t : ℝ) ^ 2 := ⟨_, rfl⟩
  have hcd : ContDiff ℝ ⊤ f := hf_def ▸ (contDiff_id.pow 2).div_const _
  have hHyp : KarHyp (1 / 2) (1 / 2) (1 / 8) (1 / 8) 0 P 2 f {2} := by
    refine ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, hcd.contDiffOn.of_le le_top⟩, ?_, ?_, ?_, ?_⟩
    · intro x _
      rw [show (2 + 1 : ℕ) = 3 from rfl, hf_def, refute_pbs_iteratedDeriv_three]
      simp only [zero_div, abs_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro s hs; simp at hs; simp [hs]
    · simp
    · intro s hs x _
      have hs2 : s = 2 := by simpa using hs
      subst hs2
      rw [hf_def, refute_pbs_iteratedDeriv_two, hPpow]
      have hval : |2 / (t : ℝ) ^ 2 / ((2 : ℕ).factorial : ℝ)| = (t : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [abs_of_pos (by positivity)]
        simp [Nat.factorial]
        field_simp
      have he : (8 : ℝ) * -(1 / 8 * ((2 : ℕ) : ℝ)) = -2 := by norm_num
      rw [hval, he]
      exact ⟨le_rfl, le_rfl⟩
  have hthr : 8 * Real.pi * (((2 : ℕ) : ℝ) + 1) ≤
      (P : ℝ) ^ ((1 / 4 / 2) * (((2 : ℕ) : ℝ) + 1 + ρ) - 1 / 2 * ρ) := by
    rw [hPpow]
    have he : (1 : ℝ) ≤ 8 * ((1 / 4 / 2) * (((2 : ℕ) : ℝ) + 1 + ρ) - 1 / 2 * ρ) := by
      push_cast; nlinarith
    have h1 : (t : ℝ) ^ (1 : ℝ) ≤ (t : ℝ) ^ (8 * ((1 / 4 / 2) * (((2 : ℕ) : ℝ) + 1 + ρ) - 1 / 2 * ρ)) :=
      Real.rpow_le_rpow_of_exponent_le ht1 he
    rw [Real.rpow_one] at h1
    have hpi := Real.pi_lt_four
    have : (400 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht400
    push_cast at h1 ⊢
    nlinarith
  have hmP : ((u : ℕ) : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4 / 2) := by
    rw [hPpow]
    have he : (8 : ℝ) * ((1 : ℝ) / 2 - 1 / 4 / 2) = 3 := by norm_num
    rw [he, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hut' : (u : ℝ) ≤ (t : ℝ) := by rw [htR]; linarith
    calc (u : ℝ) ≤ (t : ℝ) := hut'
      _ = (t : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (t : ℝ) ^ 3 := pow_le_pow_right₀ ht1 (by norm_num)
  have hkar : (2 : ℝ) < karN0 (1 / 2) (1 / 8) (1 / 4) := by
    have : (12 : ℝ) ≤ karN0 (1 / 2) (1 / 8) (1 / 4) := le_max_left _ _
    linarith
  have hbound := hB 0 P 2 hP0 le_rfl (by exact_mod_cast hkar) hP1 f {2} hHyp 0 u le_rfl
    (by omega) hu1 hmP hthr
  simp only [Nat.cast_zero, zero_add] at hbound
  -- the lower bound `u / 2` for the block sum
  have hu0 : (0 : ℝ) < (u : ℝ) := by linarith
  have hterm : ∀ y ∈ Finset.range u, (1 : ℝ) / 2 ≤
      (eC (taylorWithinEval f 2 (Set.Icc (0 : ℝ) (u : ℝ)) 0 (y : ℝ))).re := by
    intro y hy
    have hy : (y : ℝ) < (u : ℝ) := by exact_mod_cast Finset.mem_range.1 hy
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    rw [hf_def, refute_pbs_taylor_eq _ _ _ hu0 ⟨hy0, hy.le⟩, refute_pbs_eC_re]
    have hq : (y : ℝ) ^ 2 / (t : ℝ) ^ 2 ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity), htR]
      nlinarith
    have hq0 : 0 ≤ (y : ℝ) ^ 2 / (t : ℝ) ^ 2 := by positivity
    have hpi := Real.pi_pos
    rw [← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith
    · nlinarith
  have hre : (u : ℝ) / 2 ≤
      ‖∑ y ∈ Finset.range u, eC (taylorWithinEval f 2 (Set.Icc (0 : ℝ) (u : ℝ)) 0 (y : ℝ))‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  -- and the upper bound of the leaf is smaller
  have hKu : K < (u : ℝ) ^ ρ := by
    have h := Real.rpow_lt_rpow (Real.rpow_nonneg (by linarith) _) huK hρ0
    rwa [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hρ0.ne', Real.rpow_one] at h
  have hsplit : (u : ℝ) ^ (1 - ρ) * (u : ℝ) ^ ρ = (u : ℝ) := by
    rw [← Real.rpow_add hu0]; simp
  have hupos : 0 < (u : ℝ) ^ (1 - ρ) := Real.rpow_pos_of_pos hu0 _
  have hlt : K * (u : ℝ) ^ (1 - ρ) < (u : ℝ) := by
    calc K * (u : ℝ) ^ (1 - ρ) < (u : ℝ) ^ ρ * (u : ℝ) ^ (1 - ρ) :=
          mul_lt_mul_of_pos_right hKu hupos
      _ = (u : ℝ) := by rw [mul_comm, hsplit]
  linarith

/-- The leaf `leaf_polynomial_block_sum` itself, as stated with the hypothesis `KarLemma2`, can
hold only if `KarLemma2` fails. Since `KarLemma2` is Vinogradov's estimate, Karacuba's reference
[2], which the route takes as true, the leaf is false as stated. -/
theorem leaf_polynomial_block_sum_false
    (hleaf : KarLemma2 →
      ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
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
                  ((a : ℝ) + (y : ℝ)))‖ ≤ 1 / 2 * (K * (m : ℝ) ^ (1 - ρ))) :
    ¬ KarLemma2 :=
  fun h2 => leaf_polynomial_block_sum_body_false (hleaf h2)

/-- The parent sealed statement `leaf_small_block_sum_bound` of
`LeanLab.ExceptionalSet.SPLIT_leaf_small_case`, without its hypothesis `KarLemma2`, is false by
the same counterexample: the block sum over `f x = x^2 / t^2` itself on `[0, u)`, `t = 4u`,
`P = t^8`, has norm at least `u/2`, and `u <= t^3 = P^(3/8) = P^(c1 - c4/2)`. -/
theorem leaf_small_block_sum_bound_body_false :
    ¬ (∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A0 ρ : ℝ, 0 < A0 ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              m ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ →
              ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ)) := by
  intro H
  obtain ⟨A0, ρ, hA0, hρ0, _hρ1, hB⟩ :=
    H (1 / 2) (1 / 2) (1 / 8) (1 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ, u = ⌈(2 * A0) ^ (1 / ρ)⌉₊ + 100 := ⟨_, rfl⟩
  have hu100 : (100 : ℝ) ≤ (u : ℝ) := by
    rw [hu_def]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈(2 * A0) ^ (1 / ρ)⌉₊]
  have huK : (2 * A0) ^ (1 / ρ) < (u : ℝ) := by
    rw [hu_def]; push_cast; linarith [Nat.le_ceil ((2 * A0) ^ (1 / ρ))]
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ, t = 4 * u := ⟨_, rfl⟩
  have htR : (t : ℝ) = 4 * (u : ℝ) := by rw [ht_def]; push_cast; ring
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by rw [htR]; linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
  obtain ⟨P, hP_def⟩ : ∃ P : ℕ, P = t ^ 8 := ⟨_, rfl⟩
  have hPpow : ∀ r : ℝ, (P : ℝ) ^ r = (t : ℝ) ^ (8 * r) := by
    intro r
    rw [hP_def, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hu1 : 1 ≤ u := by
    have : (1 : ℝ) ≤ (u : ℝ) := by linarith
    exact_mod_cast this
  have ht400 : 400 ≤ t := by
    have : (400 : ℝ) ≤ (t : ℝ) := by rw [htR]; linarith
    exact_mod_cast this
  have hP1 : 1 < P := by
    rw [hP_def]
    calc 1 < 400 := by norm_num
      _ ≤ t := ht400
      _ = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hP0 : 0 < P := by omega
  have hut : u ≤ P := by
    rw [hP_def]
    calc u ≤ t := by rw [ht_def]; omega
      _ = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  obtain ⟨f, hf_def⟩ : ∃ f : ℝ → ℝ, f = fun x => x ^ 2 / (t : ℝ) ^ 2 := ⟨_, rfl⟩
  have hcd : ContDiff ℝ ⊤ f := hf_def ▸ (contDiff_id.pow 2).div_const _
  have hHyp : KarHyp (1 / 2) (1 / 2) (1 / 8) (1 / 8) 0 P 2 f {2} := by
    refine ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, hcd.contDiffOn.of_le le_top⟩, ?_, ?_, ?_, ?_⟩
    · intro x _
      rw [show (2 + 1 : ℕ) = 3 from rfl, hf_def, refute_pbs_iteratedDeriv_three]
      simp only [zero_div, abs_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro s hs; simp at hs; simp [hs]
    · simp
    · intro s hs x _
      have hs2 : s = 2 := by simpa using hs
      subst hs2
      rw [hf_def, refute_pbs_iteratedDeriv_two, hPpow]
      have hval : |2 / (t : ℝ) ^ 2 / ((2 : ℕ).factorial : ℝ)| = (t : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [abs_of_pos (by positivity)]
        simp [Nat.factorial]
        field_simp
      have he : (8 : ℝ) * -(1 / 8 * ((2 : ℕ) : ℝ)) = -2 := by norm_num
      rw [hval, he]
      exact ⟨le_rfl, le_rfl⟩
  have hmP : u ≤ ⌊(P : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4 / 2)⌋₊ := by
    rw [hPpow]
    have he : (8 : ℝ) * ((1 : ℝ) / 2 - 1 / 4 / 2) = 3 := by norm_num
    rw [he, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show ((t : ℝ) ^ 3) = ((t ^ 3 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    calc u ≤ t := by rw [ht_def]; omega
      _ = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hkar : (2 : ℝ) < karN0 (1 / 2) (1 / 8) (1 / 4) := by
    have : (12 : ℝ) ≤ karN0 (1 / 2) (1 / 8) (1 / 4) := le_max_left _ _
    linarith
  have hbound := hB 0 P 2 hP0 le_rfl (by exact_mod_cast hkar) f {2} hHyp 0 u le_rfl
    (by omega) hu1 hmP
  rw [Finset.sum_Ico_eq_sum_range, show 0 + u - 0 = u by omega] at hbound
  simp only [zero_add, Nat.cast_zero] at hbound
  have hu0 : (0 : ℝ) < (u : ℝ) := by linarith
  have hterm : ∀ y ∈ Finset.range u, (1 : ℝ) / 2 ≤ (eC (f (y : ℝ))).re := by
    intro y hy
    have hy : (y : ℝ) < (u : ℝ) := by exact_mod_cast Finset.mem_range.1 hy
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    rw [hf_def, refute_pbs_eC_re]
    have hq : (y : ℝ) ^ 2 / (t : ℝ) ^ 2 ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity), htR]
      nlinarith
    have hq0 : 0 ≤ (y : ℝ) ^ 2 / (t : ℝ) ^ 2 := by positivity
    have hpi := Real.pi_pos
    rw [← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith
    · nlinarith
  have hre : (u : ℝ) / 2 ≤ ‖∑ y ∈ Finset.range u, eC (f (y : ℝ))‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hKu : 2 * A0 < (u : ℝ) ^ ρ := by
    have h := Real.rpow_lt_rpow (Real.rpow_nonneg (by linarith) _) huK hρ0
    rwa [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hρ0.ne', Real.rpow_one] at h
  have hsplit : (u : ℝ) ^ (1 - ρ) * (u : ℝ) ^ ρ = (u : ℝ) := by
    rw [← Real.rpow_add hu0]; simp
  have hupos : 0 < (u : ℝ) ^ (1 - ρ) := Real.rpow_pos_of_pos hu0 _
  have hlt : 2 * A0 * (u : ℝ) ^ (1 - ρ) < (u : ℝ) := by
    calc 2 * A0 * (u : ℝ) ^ (1 - ρ) < (u : ℝ) ^ ρ * (u : ℝ) ^ (1 - ρ) :=
          mul_lt_mul_of_pos_right hKu hupos
      _ = (u : ℝ) := by rw [mul_comm, hsplit]
  have hb' : ‖∑ y ∈ Finset.range u, eC (f (y : ℝ))‖ ≤ A0 * (u : ℝ) ^ (1 - ρ) := by
    simpa using hbound
  linarith

/-- The parent sealed statement `leaf_small_block_sum_bound`, with its hypothesis
`KarLemma2`, can hold only if `KarLemma2` fails. -/
theorem leaf_small_block_sum_bound_false
    (hleaf : KarLemma2 →
      ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A0 ρ : ℝ, 0 < A0 ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              m ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ →
              ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ)) :
    ¬ KarLemma2 :=
  fun h2 => leaf_small_block_sum_bound_body_false (hleaf h2)

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
