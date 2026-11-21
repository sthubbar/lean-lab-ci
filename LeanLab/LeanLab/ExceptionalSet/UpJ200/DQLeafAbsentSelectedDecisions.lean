import LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-!
Cited wall decision for `Decomp559b.leaf_absent_selected`, run CLOUD-cited-leaf_absent_selected.
Source P0082: J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, doi 10.5802/aif.1621, copy `papers/P0082.pdf`.
Read from the page images: page 358 displays 9, 11 and Lemma 2, page 362 Lemma 7 case i.

VERDICT: NAMED HYPOTHESIS. The leaf is case i of the proof of Lemma 7, page 362: when the
exceptional character does not exist, Lemma 2 page 358 gives
`R₁(m) = m 𝔖(m) + O(m φ(m)⁻¹ X exp(-c₁ log X / log P))` for `m ≤ X`, and `𝔖(m) ≫ m/φ(m)` for
even `m`, so `R₁(ν̃_n) ≫ X`. Lemma 2 is cited by the paper itself as "Combine (6.17) and (7.1)
of Montgomery and Vaughan", P0015, Acta Arith. 27 (1975). It is accepted here as the named
hypothesis `Lemma2NoExcBP`. The elementary lower bound for the singular series, stated without
proof on page 362, is the second named hypothesis `SingularSeriesEvenLowerBP`.

`leaf_absent_selected_of_lemma2` proves the exact statement of the leaf from the two named
hypotheses, sorry free. CONDITIONAL ON `Lemma2NoExcBP` and `SingularSeriesEvenLowerBP`.

Choices that make the hypotheses weaker than the paper, so they stay true if the paper is:
* the threshold `X₀` may depend on the zero free constant `a` and on `δ`; the paper's O is
  absolute. The constants `c₁` and `K` depend on `a` only, as the paper needs.
* "the exceptional character does not exist" is read for an arbitrary zero free constant
  `a > 0` and only real zeros `σ < 1` of primitive characters of modulus at most `P`, exactly
  as `SelectedRealZero a P 1` encodes it. Complex zeros are excluded by the classical region,
  Davenport chapter 14, so this is the paper's condition (9) with constant `min a c`.
* `P = X^{6δ}` with `0 < δ < 1/100`, the paper's range on page 357.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)

/-- The singular series of P0082 page 358 display 11,
`𝔖(m) = ∏_{p ∤ m} (1 - (p-1)⁻²) ∏_{p ∣ m} (1 + (p-1)⁻¹)`, as one product over all primes.
For odd `m` the factor at `p = 2` is zero. -/
noncomputable def singularSeries (m : ℕ) : ℝ :=
  ∏' p : Nat.Primes,
    (if (p : ℕ) ∣ m then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- P0082 page 358 display 9 in the absent case: no primitive character of modulus at most
`P` has a real zero `σ` with `1 - a / log P ≤ σ < 1`. This is the first alternative of
`Decomp559b.SelectedRealZero` with its conductor `r = 1` dropped. -/
def NoExceptionalReal (a P : ℝ) : Prop :=
  ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
    1 ≤ q → (q : ℝ) ≤ P → χ.IsPrimitive →
      ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 → χ.LFunction σ ≠ 0

/-- NAMED HYPOTHESIS. P0082 page 358, Lemma 2, proof "Combine (6.17) and (7.1) of
Montgomery and Vaughan [MV]", P0015 Acta Arith. 27 (1975). For every zero free constant
`a > 0` there are `c₁ > 0` and `K > 0` such that for `0 < δ < 1/100`, `P = X^{6δ}`, all large
`X` with no exceptional character, and every `1 ≤ m ≤ X`,
`|R₁(m) - m 𝔖(m)| ≤ K m φ(m)⁻¹ X exp(-c₁ log X / log P)`. -/
def Lemma2NoExcBP : Prop :=
  ∀ a : ℝ, 0 < a → ∃ c₁ K : ℝ, 0 < c₁ ∧ 0 < K ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 / 100 → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ X →
        ‖R1 (X ^ (6 * δ)) X (m : ℤ) - (((m : ℝ) * singularSeries m : ℝ) : ℂ)‖ ≤
          K * ((m : ℝ) / (m.totient : ℝ)) * X *
            Real.exp (-(c₁ * Real.log X / Real.log (X ^ (6 * δ))))

/-- NAMED HYPOTHESIS. P0082 page 362, Lemma 7 case i: `𝔖(m) ≫ m / φ(m)` for
`m ≡ 0 mod 2`. Elementary; the paper states it without proof. -/
def SingularSeriesEvenLowerBP : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → Even m →
    C * ((m : ℝ) / (m.totient : ℝ)) ≤ singularSeries m

/-- `SelectedRealZero a P 1` is the absent case: the second alternative would need a
nonprincipal character mod 1. PROVED. -/
theorem noExceptionalReal_of_selected_one {a P : ℝ} (h : SelectedRealZero a P 1) :
    NoExceptionalReal a P := by
  rcases h with ⟨_, hfree⟩ | ⟨_, χ, _, _, _, hne, _⟩
  · exact hfree
  · exact absurd (DirichletCharacter.level_one χ) hne

/-- `exp(-x) ≤ 1/x` for `x > 0`. PROVED. -/
theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le hx
  linarith [Real.add_one_le_exp x]

/-- P0082 page 362 Lemma 7 case i, the exact statement of `Decomp559b.leaf_absent_selected`.
CONDITIONAL ON `Lemma2NoExcBP` and `SingularSeriesEvenLowerBP`. -/
theorem leaf_absent_selected_of_lemma2 (hL : Lemma2NoExcBP) (hS : SingularSeriesEvenLowerBP)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨c₁, K, hc₁, hK, hL⟩ := hL a ha
  obtain ⟨Cs, hCs, hS⟩ := hS
  refine ⟨min (1 / 100) (c₁ * Cs / (24 * K)), lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδ₀
  have hδ1 : δ < 1 / 100 := lt_of_lt_of_le hδ₀ (min_le_left _ _)
  have hδ2 : δ < c₁ * Cs / (24 * K) := lt_of_lt_of_le hδ₀ (min_le_right _ _)
  obtain ⟨X₀, hX₀⟩ := hL δ hδ hδ1
  refine ⟨1, one_pos, ?_⟩
  intro κ _ _
  refine ⟨Cs / 4, 1, by positivity, one_pos, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hF.eventually_ge_atTop (max X₀ 2))
  refine ⟨N₀, ?_⟩
  intro N hN r _ _ hs j hj n hn heven hm hr1
  subst hr1
  have hXbig := hN₀ N hN
  have hX₀X : X₀ ≤ F γ N := le_trans (le_max_left _ _) hXbig
  have hX2 : 2 ≤ F γ N := le_trans (le_max_right _ _) hXbig
  have hnoexc := noExceptionalReal_of_selected_one hs
  have hwin := (Finset.mem_filter.mp hn).2
  have hνpos : (0 : ℤ) < nu γ n := by
    have : (0 : ℝ) < (nu γ n : ℝ) := by linarith [hwin.1]
    exact_mod_cast this
  have hj0 : 0 ≤ j := by rcases hj with h | h <;> omega
  have hnn : 0 ≤ nu γ n + j := by omega
  set k : ℕ := (nu γ n + j).toNat with hkdef
  have hk : ((k : ℕ) : ℤ) = nu γ n + j := Int.toNat_of_nonneg hnn
  rw [← hk] at heven hm ⊢
  have hk1 : 1 ≤ k := by omega
  have hkX : (k : ℝ) ≤ F γ N := by exact_mod_cast hm
  have hkeven : Even k := Int.even_coe_nat k |>.mp heven
  have hkhalf : F γ N / 2 < (k : ℝ) := by
    have h1' : (nu γ n : ℤ) ≤ (k : ℤ) := by omega
    have h2' : ((nu γ n : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast h1'
    have h3' : ((k : ℤ) : ℝ) = (k : ℝ) := by push_cast; rfl
    linarith [hwin.1]
  -- the cited asymptotic
  have hbound := hX₀ (F γ N) hX₀X hnoexc k hk1 hkX
  set X := F γ N with hXdef
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogP : Real.log (X ^ (6 * δ)) = 6 * δ * Real.log X := Real.log_rpow hX0 _
  have hratio : c₁ * Real.log X / Real.log (X ^ (6 * δ)) = c₁ / (6 * δ) := by
    rw [hlogP]; field_simp
  rw [hratio] at hbound
  set e := Real.exp (-(c₁ / (6 * δ))) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hKe : K * e ≤ Cs / 4 := by
    have h1' : e ≤ 1 / (c₁ / (6 * δ)) := exp_neg_le_inv (by positivity)
    have h2' : 1 / (c₁ / (6 * δ)) = 6 * δ / c₁ := by field_simp
    rw [h2'] at h1'
    have h3' : K * e ≤ K * (6 * δ / c₁) := mul_le_mul_of_nonneg_left h1' hK.le
    have h4' : K * (6 * δ / c₁) ≤ Cs / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hδ2
      rw [mul_div_assoc', div_le_iff₀ hc₁]
      nlinarith
    linarith
  -- the ratio m / φ(m)
  set ρ := (k : ℝ) / (k.totient : ℝ) with hρ
  have hφ : (0 : ℝ) < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le k
  have hsing := hS k hk1 hkeven
  -- real part of R₁
  have hre : (k : ℝ) * singularSeries k - K * ρ * X * e ≤
      (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ)).re := by
    have h := Complex.abs_re_le_norm
      (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ) - (((k : ℝ) * singularSeries k : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    have := (abs_le.mp (h.trans hbound)).1
    linarith
  have hmain : Cs / 4 * X ≤ (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ)).re := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hA1 : (k : ℝ) * (Cs * ρ) ≤ (k : ℝ) * singularSeries k :=
      mul_le_mul_of_nonneg_left hsing hk0
    have hA2 : K * ρ * X * e ≤ ρ * X * (Cs / 4) := by
      have := mul_le_mul_of_nonneg_left hKe (by positivity : (0 : ℝ) ≤ ρ * X)
      nlinarith
    have hA3 : ρ * (Cs * (X / 2)) ≤ ρ * (Cs * k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkhalf.le hCs.le) (by positivity)
    have hA4 : Cs / 4 * X ≤ ρ * (Cs / 4 * X) := by
      have : 0 ≤ Cs / 4 * X := by positivity
      nlinarith
    nlinarith
  have hP0 : 0 ≤ X ^ (6 * δ) := Real.rpow_nonneg hX0.le _
  have hD : 0 ≤ divisorError 1 (X ^ (6 * δ)) ((k : ℕ) : ℤ) := by
    unfold divisorError
    apply add_nonneg
    · refine mul_nonneg ?_ (sum_nonneg (fun q _ => div_nonneg (by positivity) (by positivity)))
      simpa using div_nonneg zero_le_one hP0
    · refine mul_nonneg ?_ (tsum_nonneg (fun q => by split_ifs <;> positivity))
      simp
  have : 0 ≤ 1 * X * divisorError 1 (X ^ (6 * δ)) ((k : ℕ) : ℤ) := by positivity
  linarith

/-- Twin check: the conditional theorem has exactly the type of the open leaf
`Decomp559b.leaf_absent_selected`. -/
example (hL : Lemma2NoExcBP) (hS : SingularSeriesEvenLowerBP) : True :=
  let _f : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected :=
    leaf_absent_selected_of_lemma2 hL hS
  trivial

end LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected
