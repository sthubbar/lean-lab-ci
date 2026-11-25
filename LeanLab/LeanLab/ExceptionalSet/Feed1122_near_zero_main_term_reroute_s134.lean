import LeanLab.ExceptionalSet.Feed1122_near_zero_even_large_prime_long
import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_selected

/-!
Feed 1122, CLOUD S134: the two LEAFs `leaf_near_zero_even_main_term` of
`Feed1122_near_zero_even_index.lean` and `leaf_near_zero_odd_main_term` of
`Feed1122_near_zero_odd_index.lean`, P0082 page 363 display 20 with page 364 case ii d, both
derived from the single LEAF `leaf_exceptional_main_term_lower` of
`Feed1122_near_zero_even_large_prime_long.lean`, P0082 page 358 Lemma 3 with displays 20, 21
and case ii d.  The three leaves state the same analytic step; the two near zero leaves drop the
factor `log P`, which is at least `1` for large `N`, and replace the uniqueness clause by
`SelectedRealZero`, whose second branch identifies the given character and zero.  The window
`window γ N` already gives `X/2 < ν_n`, so the frequency `ν_n`, or `ν_n + 1` for odd `ν_n`, lies
in `(X/2, X]`.  So both theorems below are CONDITIONAL ON `leaf_exceptional_main_term_lower`.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- `SelectedRealZero` with `1 < gcd(m, r)` gives the uniqueness clause of
`leaf_exceptional_main_term_lower` for any given exceptional character `χ` and zero `β`. -/
theorem selected_uniqueness_s134 (a P : ℝ) (r : ℕ) (m : ℤ)
    (hs : SelectedRealZero a P r) (hg : 1 < Int.gcd m r) (hr : 1 ≤ r) (hrP : (r : ℝ) ≤ P)
    (i : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ) (hprim : χ.IsPrimitive)
    (hβl : 1 - a / Real.log P ≤ β) (hβ1 : β < 1) (hz : χ.LFunction β = 0) :
    ∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
      1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
        ∀ σ : ℝ, 1 - a / Real.log P ≤ σ → σ < 1 →
          ψ.LFunction σ = 0 → q = r ∧ HEq ψ χ ∧ σ = β := by
  rcases hs with ⟨h1, _⟩ | ⟨i', χ', β', _, _, _, _, _, _, _, U⟩
  · subst h1
    simp at hg
  · obtain ⟨_, hχ, hβ⟩ := U r i χ hr hrP hprim β hβl hβ1 hz
    intro q iq ψ hq hqP hψ σ hσl hσ1 hσz
    obtain ⟨hqr, hψ', hσ⟩ := U q iq ψ hq hqP hψ σ hσl hσ1 hσz
    exact ⟨hqr, hψ'.trans hχ.symm, hσ.trans hβ.symm⟩

/-- `log P ≥ 1` eventually, with `P = F γ N ^ (6 δ)`, for `γ > 0`, `δ > 0`. -/
theorem log_P_ge_one_s134 (γ : ℝ) (h1 : 1 < γ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ Real.log (F γ N ^ (6 * δ)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hlog
  have h6 : Tendsto (fun N : ℕ => 6 * δ * Real.log (N : ℝ) ^ γ) atTop atTop :=
    hp.const_mul_atTop (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h6.eventually_ge_atTop 1)
  exact ⟨N₀, fun N hN => by rw [feed1122_log_P]; exact hN₀ N hN⟩

/-- The common step: from `leaf_exceptional_main_term_lower`, for an even frequency `m` in
`(X/2, X]` with the hypotheses of case ii d, `c (1 - β) X ≤ Re R1(m) + A X divisorError`. -/
theorem near_zero_main_term_core_s134 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          SelectedRealZero a (F γ N ^ (6 * δ)) r →
          ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
            χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
            1 - a / Real.log (F γ N ^ (6 * δ)) ≤ β → β < 1 → χ.LFunction β = 0 →
          ∀ m : ℤ, Even m → F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N →
            1 < Int.gcd m r →
            (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) →
              c * (1 - β) * F γ N ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) m).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) m := by
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_exceptional_main_term_lower γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨c, A, hc, hA, N₁, L⟩ := H δ hδ hδlt
  obtain ⟨N₂, hlogP⟩ := log_P_ge_one_s134 γ h1 δ hδ
  refine ⟨c, A, hc, hA, max N₁ N₂, ?_⟩
  intro N hN r hr hrP hs i χ β hprim hsq hne hβ0 hβl hβ1 hz m hm hm1 hm2 hg hnop
  obtain ⟨hN₁, hN₂⟩ := max_le_iff.mp hN
  have U := selected_uniqueness_s134 a _ r m hs hg hr hrP i χ β hprim hβl hβ1 hz
  have hL := L N hN₁ r hr hrP m hm hm1 hm2 hg hnop i χ β hprim hsq hne hβ0 hβl hβ1 hz U
  have hlog := hlogP N hN₂
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hb : 0 ≤ 1 - β := by linarith
  have hk : c * (1 - β) * F γ N ≤ c * (1 - β) * Real.log (F γ N ^ (6 * δ)) * F γ N := by
    have h0 : 0 ≤ c * (1 - β) * F γ N := by positivity
    nlinarith
  exact hk.trans hL

/-- Verbatim statement of `leaf_near_zero_even_main_term`, CONDITIONAL ON
`leaf_exceptional_main_term_lower`. -/
theorem leaf_near_zero_even_main_term_s134 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
              χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
              1 - a / Real.log (F γ N ^ (6 * δ)) ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * (1 - β) * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨δ₀, hδ₀, H⟩ := near_zero_main_term_core_s134 γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ⟨1, one_pos, fun κ _ _ => ?_⟩⟩
  obtain ⟨c, A, hc, hA, N₀, L⟩ := H δ hδ hδlt
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr hrP hs i χ β hprim hsq hne hβ0 hβl hβ1 hz n hn hev hm hg hnop _
  have hw := (Finset.mem_filter.mp hn).2
  exact L N hN r hr hrP hs i χ β hprim hsq hne hβ0 hβl hβ1 hz (nu γ n) hev hw.1 hm hg hnop

/-- Verbatim statement of `leaf_near_zero_odd_main_term`, CONDITIONAL ON
`leaf_exceptional_main_term_lower`. -/
theorem leaf_near_zero_odd_main_term_s134 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
              χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
              1 - a / Real.log (F γ N ^ (6 * δ)) ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * (1 - β) * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, H⟩ := near_zero_main_term_core_s134 γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ⟨1, one_pos, fun κ _ _ => ?_⟩⟩
  obtain ⟨c, A, hc, hA, N₀, L⟩ := H δ hδ hδlt
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr hrP hs i χ β hprim hsq hne hβ0 hβl hβ1 hz n hn hodd hm hg hnop _
  have hw := (Finset.mem_filter.mp hn).2
  have hev : Even (nu γ n + 1) := Int.even_add_one.mpr hodd
  have hlt : F γ N / 2 < ((nu γ n + 1 : ℤ) : ℝ) := by
    push_cast; linarith [hw.1]
  exact L N hN r hr hrP hs i χ β hprim hsq hne hβ0 hβl hβ1 hz (nu γ n + 1) hev hlt hm hg hnop

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
