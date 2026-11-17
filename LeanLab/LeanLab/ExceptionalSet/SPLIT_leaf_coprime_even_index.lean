import LeanLab.ExceptionalSet.SPLIT_leaf_coprime_selected

/-!
Split of `leaf_coprime_even_index` of `LeanLab.ExceptionalSet.SPLIT_leaf_coprime_selected`.

The statement being split is the even frequency, coprime conductor lower bound: for
`1 < γ < 3/2` and `a > 0` there is a positive cap on the truncation exponent, a positive cap on
the height parameter, a positive constant `c` and a threshold `N₀` such that for every
admissible truncation `F(γ,N)^(6δ)`, every `N ≥ N₀`, every conductor `r` selected by
`SelectedRealZero` with `r ≠ 1`, every index `n` of the floor window with `ν_n` even and
coprime to `r`, the real part of the major arc integral at the single frequency `ν_n` is at
least `c F(γ,N)`.

Two estimates carry the content, and both are strictly weaker than the whole statement.

* `leaf_even_index_coefficient_domination` asks the same lower bound but against the frequency
  itself, `c ν_n`, not against the window height `F(γ,N)`. Since the window pins `ν_n` at most
  `F(γ,N)`, this is the whole statement with the right hand side weakened: it needs no step
  comparing `ν_n` with `F(γ,N)` and it says nothing at all about indices outside the window.
* `leaf_even_index_window_frequency_gap` is the comparison that is dropped from the first leaf:
  on the window the frequency `ν_n` is at least half the window height. It fixes no constant and
  makes no analytic claim; it only reads the floor value against the window bound.

The assembly is arithmetic. The first leaf gives `c ν_n ≤ re R₁(ν_n)`, the second gives
`F(γ,N) ≤ 2 ν_n`, hence `(c/2) F(γ,N) ≤ c ν_n ≤ re R₁(ν_n)`, which is the statement with the
constant `c/2`. The caps and the threshold pass through unchanged, because neither leaf restricts
`δ`, `κ` or `N` beyond what the statement already restricts.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Step one: the major arc integral at the single even frequency `ν_n` dominates the
frequency itself, uniformly over the admissible truncation exponents and height parameters and
over the window indices, in the coprime case with a selected conductor other than one. This
is the analytic content of the statement; it is weaker than the statement because the window
only gives `ν_n ≤ F(γ,N)`, so a bound against `ν_n` is a bound against a smaller quantity, and
no comparison of `ν_n` with `F(γ,N)` is made here. -/
theorem leaf_even_index_coefficient_domination (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n) r = 1 →
                c * ((nu γ n : ℤ) : ℝ) ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re := by
  sorry

/-- LEAF. Step two: on the floor window the frequency is at least half the window height,
`F(γ,N) ≤ 2 ν_n`. This is the comparison between the floor value and the height at which the
window cuts it; it is the only place where the window bound is read, and it carries no analytic
claim, no constant and no threshold. It holds for every `N`, including the degenerate ones:
at `N = 0` the window value satisfies `F(γ,0)/2 < ν_n`, so the half-open inequality is already
strict. -/
theorem leaf_even_index_window_frequency_gap (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ N : ℕ, ∀ n : ℕ, n ∈ window γ N → F γ N ≤ 2 * ((nu γ n : ℤ) : ℝ) := by
  intro N n hn
  rw [window, Finset.mem_filter] at hn
  have hlt : F γ N / 2 < ((nu γ n : ℤ) : ℝ) := hn.2.1
  linarith

/-- Assembly of `leaf_coprime_even_index`: the domination leaf bounds the real part of the
major arc integral by the frequency, the window leaf bounds the frequency below by half the
height, and the constant `c/2` carries the composition. -/
theorem leaf_coprime_even_index_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n) r = 1 →
                c * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := leaf_even_index_coefficient_domination γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδpos hδlt => ?_⟩
  obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδpos hδlt
  refine ⟨κ₀, hκ₀, fun κ hκpos hκle => ?_⟩
  obtain ⟨c, hc, N₀, hN₀⟩ := hκ κ hκpos hκle
  refine ⟨c / 2, by linarith, N₀, ?_⟩
  intro N hN r hr hrP hs n hn heven hm hr1 hgcd
  have hmain : c * ((nu γ n : ℤ) : ℝ) ≤
      (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re :=
    hN₀ N hN r hr hrP hs n hn heven hm hr1 hgcd
  have hgap : F γ N ≤ 2 * ((nu γ n : ℤ) : ℝ) :=
    leaf_even_index_window_frequency_gap γ h1 h2 N n hn
  have hhalf : c / 2 * F γ N ≤ c * ((nu γ n : ℤ) : ℝ) := by
    have h1' : c / 2 * F γ N ≤ c / 2 * (2 * ((nu γ n : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hgap (by linarith : (0 : ℝ) ≤ c / 2)
    have h2' : c / 2 * (2 * ((nu γ n : ℤ) : ℝ)) = c * ((nu γ n : ℤ) : ℝ) := by ring
    linarith only [h1', h2']
  exact le_trans hhalf hmain

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
