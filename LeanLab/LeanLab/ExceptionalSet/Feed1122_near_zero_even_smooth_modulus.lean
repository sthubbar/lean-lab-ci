import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_even_index

/-!
Feed split of `leaf_near_zero_even_smooth_modulus` of
`LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_even_index`.

Source: J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier
48 (1998), P0082, page 358, displays 9 and 10.  Display 10 says the exceptional modulus `r`
is large in terms of `P`: `r (log r)^{-2} ≫ 1 / (1 - β)` and `1 - β ≤ a / log P`.  The
smooth conductor case is the case where that modulus has no prime factor above three; there
the modulus is bounded, so for large `N` no exceptional zero of that modulus can lie in the
interval `[1 - a / log P, 1)`, and the case is empty.

That observation has two elementary inputs.
* `leaf_quadratic_primitive_smooth_conductor_dvd_24`, the one LEAF, MEDIUM: a primitive
  character with `χ ^ 2 = 1` whose modulus has only the prime factors two and three has
  modulus dividing `24`.
* `feed1122_small_conductor_no_real_zero_near_one`, proved here: for the finitely many
  nontrivial characters of modulus at most `24` there is a uniform `ε > 0` with no real zero
  in `[1 - ε, 1)`; this is `L(1, χ) ≠ 0` plus continuity, Davenport chapter 14 as cited on
  page 358.

The assembly proves the target from these leaves: the case `r = 1` contradicts the common
divisor hypothesis, and otherwise the selected zero contradicts the proved helper once
`a / log P < ε`, which holds for large `N` since `log P = 6 δ (log N) ^ γ`.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF: P0082 page 358 display 10, the exceptional modulus is the conductor of a primitive
real character, and a primitive real character whose conductor has no prime factor above
three has conductor dividing `24`: the odd part of a real primitive conductor is squarefree
and its two part is `1`, `4` or `8`.  Class MEDIUM: routine structure of real Dirichlet
characters at the primes two and three. -/
theorem leaf_quadratic_primitive_smooth_conductor_dvd_24 (r : ℕ) (_ : NeZero r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hsq : χ ^ 2 = 1)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ r → p ≤ 3) : r ∣ 24 := by
  sorry

/-- Proved helper: one primitive or not, a nontrivial character `χ` modulo `k + 1` has no
real zero in `[1 - ε, 1)` for all small `ε > 0`, from `L(1, χ) ≠ 0` and continuity. -/
theorem feed1122_char_no_real_zero_near_one (k : ℕ) (χ : DirichletCharacter ℂ (k + 1)) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      χ ≠ 1 → ∀ σ : ℝ, 1 - ε ≤ σ → σ < 1 → χ.LFunction σ ≠ 0 := by
  by_cases hχ : χ = 1
  · exact Filter.Eventually.of_forall (fun _ h => absurd hχ h)
  have hc : Continuous (fun σ : ℝ => χ.LFunction (σ : ℂ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
  have h1 : χ.LFunction ((1 : ℝ) : ℂ) ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hev : ∀ᶠ σ in nhds (1 : ℝ), (fun σ : ℝ => χ.LFunction (σ : ℂ)) σ ≠ 0 :=
    ContinuousAt.eventually_ne (g := fun σ : ℝ => χ.LFunction (σ : ℂ)) hc.continuousAt h1
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < η :=
    nhdsWithin_le_nhds (eventually_lt_nhds hη)
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hε0 _ σ hσ1 hσ2
  apply hball (y := σ)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Proved, P0082 page 358 displays 9 and 10, with Davenport chapter 14 as cited there: for
the finitely many nontrivial characters of modulus at most `24` there is a uniform `ε > 0`
such that no real point of `[1 - ε, 1)` is a zero of their L functions.  This is
`L(1, χ) ≠ 0` with continuity and finiteness of the set of characters. -/
theorem feed1122_small_conductor_no_real_zero_near_one :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (q : ℕ) (_ : NeZero q), q ≤ 24 →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
        ∀ σ : ℝ, 1 - ε ≤ σ → σ < 1 → χ.LFunction σ ≠ 0 := by
  have hall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ k : Fin 24,
      ∀ χ : DirichletCharacter ℂ (k.val + 1),
        χ ≠ 1 → ∀ σ : ℝ, 1 - ε ≤ σ → σ < 1 → χ.LFunction σ ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    rw [Filter.eventually_all]
    intro χ
    exact feed1122_char_no_real_zero_near_one k.val χ
  obtain ⟨ε, hε, hε0⟩ := (hall.and self_mem_nhdsWithin).exists
  refine ⟨ε, hε0, ?_⟩
  intro q hq hq24 χ _ _ hχ σ hσ1 hσ2
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := Nat.exists_eq_succ_of_ne_zero hq.out
  exact hε ⟨k, by omega⟩ χ hχ σ hσ1 hσ2

/-- Proved helper: `log P = 6 δ (log N) ^ γ` for `P = F γ N ^ (6 δ)` grows, so the length
`a / log P` of the exceptional interval falls below any `ε > 0` for large `N`. -/
theorem feed1122_exceptional_interval_short (γ : ℝ) (h1 : 1 < γ) (a δ ε : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 - ε ≤ 1 - a / Real.log (F γ N ^ (6 * δ)) := by
  set M : ℝ := max 1 (a / (6 * δ * ε)) with hM
  refine ⟨⌈Real.exp M⌉₊, fun N hN => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hexp : Real.exp M ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos M) hexp
  have hlogN : M ≤ Real.log N := by
    rw [← Real.log_exp M]
    exact Real.log_le_log (Real.exp_pos M) hexp
  have hlog1 : (1 : ℝ) ≤ Real.log N := hM1.trans hlogN
  have hpow : Real.log N ≤ Real.log N ^ γ := by
    calc Real.log N = Real.log N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log N ^ γ := Real.rpow_le_rpow_of_exponent_le hlog1 h1.le
  have hL : Real.log (F γ N ^ (6 * δ)) = 6 * δ * Real.log N ^ γ := by
    unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
    rw [Real.log_rpow (Real.exp_pos _), Real.log_exp]
  rw [hL]
  have hLpos : 0 < 6 * δ * Real.log N ^ γ := by positivity
  have hkey : a / (6 * δ * ε) ≤ Real.log N ^ γ :=
    (le_max_right _ _).trans (hlogN.trans hpow)
  have hdiv : a / (6 * δ * Real.log N ^ γ) ≤ ε := by
    rw [div_le_iff₀ hLpos]
    rw [div_le_iff₀ (by positivity)] at hkey
    nlinarith [hkey]
  linarith

/-- Proved helper: in the smooth conductor range the selected real zero hypothesis is empty
for large `N`, except for `r = 1`. -/
theorem feed1122_smooth_selected_trivial (γ : ℝ) (h1 : 1 < γ) (a : ℝ) (ha : 0 < a)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ,
      SelectedRealZero a (F γ N ^ (6 * δ)) r →
      (∀ p : ℕ, p.Prime → p ∣ r → p ≤ 3) → r = 1 := by
  obtain ⟨ε, hε, HB⟩ := feed1122_small_conductor_no_real_zero_near_one
  obtain ⟨N₀, hN₀⟩ := feed1122_exceptional_interval_short γ h1 a δ ε ha hδ hε
  refine ⟨N₀, fun N hN r hsel hsmooth => ?_⟩
  rcases hsel with ⟨hr1, _⟩ | ⟨hnz, χ, β, hprim, hsq, hne, _, hβ1, hβ2, hL, _⟩
  · exact hr1
  · exfalso
    have h24 := leaf_quadratic_primitive_smooth_conductor_dvd_24 r hnz χ hprim hsq hsmooth
    have hr24 : r ≤ 24 := Nat.le_of_dvd (by norm_num) h24
    exact HB r hnz hr24 χ hprim hsq hne β (le_trans (hN₀ N hN) hβ1) hβ2 hL

/-- Assembly, statement copied verbatim from `leaf_near_zero_even_smooth_modulus`. -/
theorem leaf_near_zero_even_smooth_modulus_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            (∀ p : ℕ, p.Prime → p ∣ r → p ≤ 3) →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  refine ⟨1, one_pos, fun δ hδ _ => ⟨1, one_pos, fun κ _ _ => ⟨1, 1, one_pos, one_pos, ?_⟩⟩⟩
  obtain ⟨N₀, hN₀⟩ := feed1122_smooth_selected_trivial γ h1 a ha δ hδ
  refine ⟨N₀, fun N hN r _ _ hsel hsmooth n _ _ _ hgcd _ _ => ?_⟩
  exfalso
  have hr1 := hN₀ N hN r hsel hsmooth
  subst hr1
  simp at hgcd

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
