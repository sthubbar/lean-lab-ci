import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_selected

/-!
Feed 1122, wave 2: a split of `leaf_near_zero_even_index` along the analytic chain of
P0082, Bruedern and Perelli 1998, proof of Lemma 7, case ii d, journal pages 363 and 364.

The existing file `SPLIT_leaf_near_zero_even_index.lean` cuts by conductor range, but its
short modulus leaf is proved from `leaf_near_zero_even_index` itself, so that split does not
carry the parent.  This file makes a different cut, by the steps of the paper proof.

* The branch of `SelectedRealZero` with no exceptional zero has `r = 1`, which contradicts the
  hypothesis `1 < gcd`; this is proved here.
* LEAF HARD: display 20 together with the first display of page 364 gives a lower bound
  `c (1 - beta) X` for the major arc integral up to the divisor error.
* LEAF HARD: display 10, the Page type bound `1 - beta >> r^(-1/2) (log r)^(-2)`.
* LEAF MEDIUM: for `r <= calE^(1/7)` and large `N`, `r^(-1/2) (log r)^(-2)` beats `calE^(-1/10)`.

The assembly chains these and is proved.  AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF: P0082 page 363 display 20 combined with page 364 first display, case ii d. HARD.
With the exceptional real primitive character `χ` of conductor `r` and its zero `β`, the product
of display 21 empty and `1 < gcd`, one has `I(m) ≤ m^β`, so the main term
`m S(m) + I(m) S'(m)` is at least `S(m) (m - m^β) ≫ (1 - β) m`, and display 20 turns this into
a lower bound `c (1 - β) X` for `Re R1` at the even frequency `nu γ n`, the divisor error
carrying the large conductor terms and the remaining Siegel error being at most half the
leading term for small `δ`.  The factors `log P` and `m / φ(m)` of the paper are dropped,
which only weakens the bound. -/
theorem leaf_near_zero_even_main_term (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  sorry

/-- LEAF: P0082 page 358 display 10, citing Davenport chapter 14. HARD.
The zero `β < 1` of the L function of a nonprincipal real primitive character of conductor `r`
satisfies `1 - β ≫ r^(-1/2) (log r)^(-2)`; the logarithm is shifted to `log (r + 2)` so that it
is positive for every conductor. -/
theorem leaf_near_zero_page_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β → β < 1 → χ.LFunction β = 0 →
        c / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) ≤ 1 - β := by
  sorry

/-- LEAF: P0082 page 364 last lines, the step from display 10 to `X calE^(-1/10)`. MEDIUM.
For `1 ≤ r ≤ calE^(1/7)` one has `r^(-1/2) (log r)^(-2) ≥ calE^(-1/14) (log calE)^(-2)`, and this
is at least `calE^(-1/10)` once `N` is large, since `calE` tends to infinity for `γ < 3/2`. -/
theorem leaf_near_zero_conductor_power (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
      calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ 1 / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) := by
  sorry

/-- Proved helper: the branch of `SelectedRealZero` without an exceptional zero has `r = 1`,
which is incompatible with a nontrivial common divisor. -/
theorem near_zero_selected_exceptional (a P : ℝ) (r : ℕ) (m : ℤ)
    (hs : SelectedRealZero a P r) (hg : 1 < Int.gcd m r) :
    ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
      0 < β ∧ 1 - a / Real.log P ≤ β ∧ β < 1 ∧ χ.LFunction β = 0 := by
  rcases hs with ⟨hr, _⟩ | ⟨i, χ, β, h1, h2, h3, h4, h5, h6, h7, _⟩
  · subst hr
    exfalso
    have : Int.gcd m ((1 : ℕ) : ℤ) = 1 := by simp
    omega
  · exact ⟨i, χ, β, h1, h2, h3, h4, h5, h6, h7⟩

/-- Assembly: verbatim statement of `leaf_near_zero_even_index`, proved from the leaves. -/
theorem leaf_near_zero_even_index_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_near_zero_even_main_term γ h1 h2 a ha
  obtain ⟨c₂, hc₂, hpage⟩ := leaf_near_zero_page_bound
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδlt
  obtain ⟨κ₀, hκ₀, K⟩ := H δ hδ hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκle
  obtain ⟨c₁, A, hc₁, hA, N₁, L⟩ := K κ hκ hκle
  obtain ⟨N₂, hpow⟩ := leaf_near_zero_conductor_power γ h1 h2 κ hκ
  refine ⟨c₁ * c₂, A, mul_pos hc₁ hc₂, hA, max N₁ N₂, ?_⟩
  intro N hN r hr hrP hs n hn heven hm hgcd hnop hrE
  obtain ⟨hN₁, hN₂⟩ := max_le_iff.mp hN
  obtain ⟨i, χ, β, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
    near_zero_selected_exceptional a _ r _ hs hgcd
  have hmain := L N hN₁ r hr hrP hs i χ β hp1 hp2 hp3 hp4 hp5 hp6 hp7 n hn heven hm hgcd hnop hrE
  have hβ := hpage r i χ β hp1 hp2 hp3 hp4 hp6 hp7
  have hE := hpow N hN₂ r hr hrE
  set D := Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hβ' : c₂ * (1 / D) ≤ 1 - β := by rw [mul_one_div]; exact hβ
  have k1 : c₁ * c₂ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      c₁ * c₂ * F γ N * (1 / D) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have k2 : c₁ * F γ N * (c₂ * (1 / D)) ≤ c₁ * F γ N * (1 - β) :=
    mul_le_mul_of_nonneg_left hβ' (by positivity)
  calc c₁ * c₂ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
      ≤ c₁ * c₂ * F γ N * (1 / D) := k1
    _ = c₁ * F γ N * (c₂ * (1 / D)) := by ring
    _ ≤ c₁ * F γ N * (1 - β) := k2
    _ = c₁ * (1 - β) * F γ N := by ring
    _ ≤ _ := hmain

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
