/-
The conclusion of the leaf `leaf_small_block_sum_bound` of
`ExceptionalSet/SPLIT_leaf_small_case.lean` is FALSE as written.

The leaf asks, under `KarLemma2`, for `A0` and `ρ > 0`, depending on `c0, ..., c4` only, such
that EVERY block `[a, a + m)` inside `[N, N + P]` with `1 ≤ m ≤ [P ^ (c1 - c4 / 2)]` has
`‖∑ e (f x)‖ ≤ A0 m ^ (1 - ρ)`. A block so short that `f` moves by less than `1 / 64` across it
has no cancellation: every term has real part at least `1 / 2`, so the sum has norm at least
`m / 2`, and the bound forces `m ^ ρ ≤ 2 A0`. Nothing bounds `m` from below.

The configuration, for given `A0` and `ρ`: `c0 = c1 = 1 / 2`, `c2 = c3 = c4 = 1 / 8`, `n = 2`,
`T = {2}`, `N = a = 0`, `m ≥ 1000` with `2 A0 < m ^ ρ`, `P = (8 m) ^ 8`, and
`f x = x ^ 2 / (64 m ^ 2)`, so that `f'' / 2 = P ^ (-(1 / 4))` exactly and `f''' = 0`, and
`f y ≤ 1 / 64` for `y < m`. Also `m ≤ (8 m) ^ (7 / 2) = P ^ (7 / 16)`.

Since the conclusion is false, the leaf statement `KarLemma2 → ...` is equivalent to
`¬ KarLemma2`. `KarLemma2` is Vinogradov's estimate as cited by Karacuba and is believed true,
so the leaf is false unless that formalization of Lemma 2 is wrong. Karacuba's p. 248 step uses
blocks of length about `[P ^ (c1 - c4 / 2)]`, and only the last block of a cover is shorter; a
faithful leaf bounds `m` below, or adds a constant to the right side.

Results, all fully proved, nothing admitted:
* `small_block_sum_conclusion_false`, the negation of the conclusion of the leaf, verbatim;
* `leaf_small_block_sum_bound_iff_not_lemma2`, the leaf statement is equivalent to `¬ KarLemma2`.

The leaf statement itself is not changed and this file does not use it.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_small_case

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

private theorem eC_re_sbf (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  rw [eC, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- The derivatives of `x ↦ β x ^ 2`. -/
private theorem deriv_sq_sbf (β : ℝ) :
    deriv (fun x : ℝ => β * x ^ 2) = fun x => 2 * β * x := by
  funext x
  have h : HasDerivAt (fun x : ℝ => β * x ^ 2) (β * (2 * x)) x := by
    have := (hasDerivAt_pow 2 x).const_mul β
    simpa using this
  rw [h.deriv]; ring

private theorem deriv_lin_sbf (β : ℝ) : deriv (fun x : ℝ => 2 * β * x) = fun _ => 2 * β := by
  funext x
  have h : HasDerivAt (fun x : ℝ => 2 * β * x) (2 * β * 1) x :=
    (hasDerivAt_id x).const_mul (2 * β)
  rw [h.deriv]; ring

private theorem iteratedDeriv_two_sbf (β : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => β * x ^ 2) = fun _ => 2 * β := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_sq_sbf, deriv_lin_sbf]

private theorem iteratedDeriv_three_sbf (β : ℝ) :
    iteratedDeriv 3 (fun x : ℝ => β * x ^ 2) = fun _ => 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_sbf]
  funext x
  simp


/-- The main refutation: the conclusion of `leaf_small_block_sum_bound` is false. -/
theorem small_block_sum_conclusion_false :
    ¬ (∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A0 ρ : ℝ, 0 < A0 ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              m ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ →
              ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ)) := by
  intro hall
  obtain ⟨A0, ρ, hA0, hρ, hρ1, hmain⟩ :=
    hall (1 / 2) (1 / 2) (1 / 8) (1 / 8) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set K : ℝ := 2 * A0 with hKdef
  have hK : 0 < K := by positivity
  -- the block length
  obtain ⟨m0, hm0⟩ := exists_nat_gt (K ^ (1 / ρ))
  set m : ℕ := max 1000 m0 with hmdef
  have hm1000 : (1000 : ℝ) ≤ m := by
    have : 1000 ≤ m := le_max_left _ _
    exact_mod_cast this
  have hmK : K < (m : ℝ) ^ ρ := by
    have h1 : K ^ (1 / ρ) < (m : ℝ) := by
      have : m0 ≤ m := le_max_right _ _
      have : (m0 : ℝ) ≤ m := by exact_mod_cast this
      linarith
    have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg hK.le _) h1 hρ
    rwa [← Real.rpow_mul hK.le, one_div, inv_mul_cancel₀ hρ.ne', Real.rpow_one] at h2
  have hm0' : (0 : ℝ) < m := by linarith
  -- the length of the interval
  set P : ℕ := (8 * m) ^ 8 with hPdef
  have hPR : (P : ℝ) = (8 * (m : ℝ)) ^ (8 : ℕ) := by rw [hPdef]; push_cast; ring
  have h8m : (0 : ℝ) < 8 * (m : ℝ) := by linarith
  have hPrpow : ∀ e : ℝ, (P : ℝ) ^ e = (8 * (m : ℝ)) ^ (8 * e) := by
    intro e
    rw [hPR, ← Real.rpow_natCast, ← Real.rpow_mul h8m.le]
    norm_num
  have hP1 : 1 < P := by
    have : (1 : ℝ) < P := by
      rw [hPR]
      have : (1 : ℝ) < 8 * (m : ℝ) := by linarith
      exact one_lt_pow₀ this (by norm_num)
    exact_mod_cast this
  have hP0 : 0 < P := by omega
  -- the phase function
  set β : ℝ := 1 / (64 * (m : ℝ) ^ 2) with hβ
  have hβpos : 0 < β := by positivity
  have hβP : (P : ℝ) ^ (-(1 / 8 * ((2 : ℕ) : ℝ))) = β := by
    rw [hPrpow, hβ]
    have : 8 * (-(1 / 8 * ((2 : ℕ) : ℝ))) = -((2 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg h8m.le, Real.rpow_natCast]
    field_simp
    ring
  set f : ℝ → ℝ := fun x => β * x ^ 2 with hf
  have hfC : ContDiff ℝ ⊤ f := by
    rw [hf]; fun_prop
  have hHyp : KarHyp (1 / 2) (1 / 2) (1 / 8) (1 / 8) 0 P 2 f {2} := by
    refine ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, (hfC.of_le le_top).contDiffOn⟩,
      ?_, ?_, ?_, ?_⟩
    · intro x _
      rw [hf, iteratedDeriv_three_sbf]
      simp only [zero_div, abs_zero]
      exact Real.rpow_nonneg (by positivity) _
    · intro s hs
      simp only [Finset.mem_singleton] at hs
      subst hs
      simp
    · simp
    · intro s hs x _
      simp only [Finset.mem_singleton] at hs
      subst hs
      rw [hf, iteratedDeriv_two_sbf, hβP]
      have : |2 * β / ((2 : ℕ).factorial : ℝ)| = β := by
        rw [Nat.factorial_two]; push_cast
        rw [abs_of_pos (by positivity)]; ring
      rw [this]
      exact ⟨le_rfl, le_rfl⟩
  -- the block sum has norm at least `m / 2`
  have hlow : (m : ℝ) / 2 ≤ ‖∑ x ∈ Finset.Ico 0 (0 + m), eC (f x)‖ := by
    rw [Finset.sum_Ico_eq_sum_range, show 0 + m - 0 = m by omega]
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have hterm : ∀ y ∈ Finset.range m, (1 / 2 : ℝ) ≤ (eC (f ((0 + y : ℕ) : ℝ))).re := by
      intro y hy
      rw [eC_re_sbf, hf]
      simp only [zero_add]
      have hy' : (y : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.1 hy).le
      have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
      have hby : β * (y : ℝ) ^ 2 ≤ 1 / 64 := by
        rw [hβ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have hby0 : 0 ≤ β * (y : ℝ) ^ 2 := by positivity
      have hpi := Real.pi_lt_d2
      have ht : 2 * Real.pi * (β * (y : ℝ) ^ 2) ≤ 1 := by nlinarith [Real.pi_pos]
      have ht0 : 0 ≤ 2 * Real.pi * (β * (y : ℝ) ^ 2) := by positivity
      have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (β * (y : ℝ) ^ 2))
      nlinarith
    have := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  -- the hypotheses of the leaf
  have hmP : m ≤ ⌊(P : ℝ) ^ ((1 / 2 : ℝ) - (1 / 8) / 2)⌋₊ := by
    apply Nat.le_floor
    rw [hPrpow]
    have : (1 : ℝ) ≤ 8 * (m : ℝ) := by linarith
    calc (m : ℝ) ≤ 8 * (m : ℝ) := by linarith
      _ = (8 * (m : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (8 * (m : ℝ)) ^ (8 * ((1 / 2 : ℝ) - (1 / 8) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le this (by norm_num)
  have hkar : ((2 : ℕ) : ℝ) < karN0 (1 / 2) (1 / 8) (1 / 8) := by
    have : (12 : ℝ) ≤ karN0 (1 / 2) (1 / 8) (1 / 8) := le_max_left _ _
    push_cast; linarith
  have hbig := hmain 0 P 2 hP0 le_rfl hkar f {2} hHyp 0 m le_rfl
    (by
      have h1 : m ≤ 8 * m := by omega
      have h2 : 8 * m ≤ (8 * m) ^ 8 := Nat.le_self_pow (by norm_num) _
      rw [hPdef]; omega)
    (le_trans (by norm_num) (le_max_left 1000 m0)) hmP
  -- `m / 2 ≤ A0 m ^ (1 - ρ)` forces `m ^ ρ ≤ 2 A0`
  have hle := le_trans hlow hbig
  have hsplit : (m : ℝ) ^ (1 - ρ) * (m : ℝ) ^ ρ = m := by
    rw [← Real.rpow_add hm0', sub_add_cancel, Real.rpow_one]
  have hpos : 0 < (m : ℝ) ^ (1 - ρ) := Real.rpow_pos_of_pos hm0' _
  have : (m : ℝ) ^ (1 - ρ) * (m : ℝ) ^ ρ ≤ (m : ℝ) ^ (1 - ρ) * K := by
    rw [hsplit, hKdef]; linarith
  have := le_of_mul_le_mul_left this hpos
  linarith

/-- Since the conclusion is false, the leaf statement is equivalent to `¬ KarLemma2`. -/
theorem leaf_small_block_sum_bound_iff_not_lemma2 :
    (KarLemma2 → ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A0 ρ : ℝ, 0 < A0 ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              m ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ →
              ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ)) ↔
      ¬ KarLemma2 :=
  ⟨fun h h2 => small_block_sum_conclusion_false (h h2), fun h h2 => absurd h2 h⟩

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
