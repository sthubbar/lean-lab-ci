import LeanLab.ExceptionalSet.SPLIT_leaf_even_coefficient_lower
import LeanLab.ExceptionalSet.Decomp465b
import LeanLab.ExceptionalSet.Endpoint465
import LeanLab.ExceptionalSet.LargeGcd465
import LeanLab.ExceptionalSet.Decomp465c

/-!
Explicit smaller inputs for the two parity pieces of the even major coefficient.
Source: P0082 pages 359 to 364, displays 14, 15, 20 and 22.
The pointwise input contains no exceptional count. The moment input contains
no major coefficient. The gcd input contains neither a prime sum nor a coefficient.
Only the pointwise input remains OPEN.
Both divisor means and the gcd count use the cited Lemma4. AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

noncomputable section

/-- The sum of the explicit positive envelopes for Gamma1 and Gamma2.
P0082 page 359 displays 14 and 15. The implicit constants belong in the
pointwise estimate. The integer m is allowed to have either parity. -/
def divisorError (r : ℕ) (P : ℝ) (m : ℤ) : ℝ :=
  (r : ℝ) / P *
    ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
      (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) +
  (r : ℝ) * ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0

/-- LEAF. P0082 pages 362 to 364, the pointwise cases of Lemma7,
display 20 with the Gamma errors retained, and display 21.
For one conductor r the lower bound holds unless r is large and its gcd
with the even integer is at least r divided by 24. No counting estimate
or first moment estimate is included. Shift j chooses the adjacent integer. -/
theorem leaf_pointwise (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              ((r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) ∨
                (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24) →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- LEAF. P0082 pages 360 to 362, Lemma5 and displays 17 to 19.
Only the first moment of the explicit divisor envelopes is asserted.
There is no coefficient estimate and no exceptional count. -/
theorem leaf_error_mean (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N,
                divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
                  C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  simpa only [divisorError, gammaOne, gammaTwo] using error_mean_from_parts γ h1 h2

/-- LEAF. P0082 page 364 display 22 and its following sentence.
This is only the large conductor gcd count. It is CONDITIONAL ON Lemma4.
It has no major arc integral,
no prime sum, no coefficient threshold, and no divisor error. -/
theorem leaf_large_gcd (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 7 : ℝ) < (r : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              (((window γ N).filter (fun n =>
                (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ))).card : ℝ) ≤
                  B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  exact large_gcd_from_lemma4 LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2

end
end LeanLab.ExceptionalSet.Supply465

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page 359 displays 14 and 15 are nonnegative error envelopes. -/
theorem divisorError_nonneg (r : ℕ) (P : ℝ) (m : ℤ) (hP : 0 ≤ P) :
    0 ≤ divisorError r P m := by
  unfold divisorError
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    exact sum_nonneg (fun q _ => by positivity)
  · apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun q => by split_ifs <;> positivity)

end LeanLab.ExceptionalSet.Supply465

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 pages 363 and 364. The three smaller inputs supply the even
coefficient count for each adjacent shift. CONDITIONAL ON the pointwise leaf and the cited Lemma4. -/
theorem adjacent_count (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            ((((window γ N).filter (fun n => Even (nu γ n + j))).filter (fun n =>
              (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                  B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δp, hδp, hp⟩ := leaf_pointwise γ h1 h2
  obtain ⟨δm, hδm, hm⟩ := leaf_error_mean γ h1 h2
  obtain ⟨δg, hδg, hg⟩ := leaf_large_gcd γ h1 h2
  refine ⟨min δp (min δm δg), lt_min hδp (lt_min hδm hδg), fun δ hδ hδsmall => ?_⟩
  obtain ⟨κp, hκp, hp⟩ := hp δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κm, hκm, hm⟩ := hm δ hδ
    (hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨κg, hκg, hg⟩ := hg δ hδ
    (hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨min 1 (min κp (min κm κg)), lt_min zero_lt_one (lt_min hκp (lt_min hκm hκg)),
    fun κ hκ hκsmall => ?_⟩
  have hκ1 : κ ≤ 1 := hκsmall.trans (min_le_left _ _)
  have hκrest : κ ≤ min κp (min κm κg) := hκsmall.trans (min_le_right _ _)
  obtain ⟨c, A, hc, hA, Np, hp⟩ := hp κ hκ (hκrest.trans (min_le_left _ _))
  obtain ⟨C, hC, Nm, hm⟩ := hm κ hκ
    (hκrest.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨B, hB, Ng, hg⟩ := hg κ hκ
    (hκrest.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨c / 2, B + 1 + 2 * A * C / c, by positivity, by positivity,
    max 16 (max Np (max Nm Ng)), fun N hN j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNm : Nm ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNg : Ng ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨r, hr, hrP, hp⟩ := hp N hNp
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let s := (window γ N).filter (fun n => Even (nu γ n + j))
  let g := fun n => divisorError r P (nu γ n + j)
  let rare := if (r : ℝ) ≤ E ^ (1 / 7 : ℝ) then ∅ else
    (window γ N).filter (fun n => (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ))
  let t := rare ∪ {N}
  have hX : 0 < X := Real.exp_pos _
  have hE : 1 ≤ E := by
    apply Real.one_le_exp
    apply mul_nonneg hκ.le
    apply Real.rpow_nonneg
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hg0 : ∀ n ∈ window γ N, 0 ≤ g n := fun n _ =>
    divisorError_nonneg r P _ (Real.rpow_nonneg hX.le _)
  have hmean : ∑ n ∈ s, g n ≤ C * N * E ^ (-(1 / 2 : ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ => hg0 n hn)).trans
      (hm N hNm r hr hrP j hj)
  have hrare : (rare.card : ℝ) ≤ B * N * E ^ (-(1 / 12 : ℝ)) := by
    dsimp only [rare]
    split_ifs with hsmall
    · simp only [card_empty, Nat.cast_zero]
      positivity
    · exact hg N hNg r hr hrP (lt_of_not_ge hsmall) j hj
  have ht : (t.card : ℝ) ≤ (B + 1) * N * E ^ (-(1 / 12 : ℝ)) := by
    have hu : (t.card : ℝ) ≤ (rare.card : ℝ) + 1 := by
      exact_mod_cast (card_union_le rare {N}).trans_eq (by simp)
    have hscale := one_le_count_scale γ κ h1 hκ.le hκ1 N (by omega)
    change 1 ≤ (N : ℝ) * E ^ (-(1 / 12 : ℝ)) at hscale
    nlinarith
  apply count_coefficient s t
    (fun n => (R1 P X (nu γ n + j)).re) g c A C (B + 1) X E N
    hc hA hC.le hX hE (fun n hn => hg0 n (mem_filter.mp hn).1) hmean ht
  intro n hn hnt
  obtain ⟨hnw, hne⟩ := mem_filter.mp hn
  have hnnot : n ≠ N := by
    intro heq
    apply hnt
    exact mem_union.mpr (Or.inr (mem_singleton.mpr heq))
  have hnN : n < N := lt_of_le_of_ne (Decomp371a.window_upper γ h1 N (by omega) n hnw) hnnot
  have hrange := adjacent_le_X γ h1 N n hN16 hnw hnN j (by rcases hj with rfl | rfl <;> norm_num)
  apply hp j hj n hnw hne (by exact_mod_cast hrange)
  by_cases hsmall : (r : ℝ) ≤ E ^ (1 / 7 : ℝ)
  · exact Or.inl hsmall
  · apply Or.inr
    have : ¬ (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ) := by
      intro hlarge
      apply hnt
      apply mem_union.mpr
      apply Or.inl
      dsimp only [rare]
      rw [if_neg hsmall]
      exact mem_filter.mpr ⟨hnw, hlarge⟩
    exact lt_of_not_ge this

end LeanLab.ExceptionalSet.Supply465

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- Exact sealed even index statement from P0082 Lemma7 pages 362 to 364.
CONDITIONAL ON the pointwise leaf and the cited Lemma4. -/
theorem even_index_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, B, hc, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, B, hc, hB, N₀, fun N hN => ?_⟩
  simpa only [add_zero] using h N hN 0 (Or.inl rfl)

/-- Exact sealed odd index statement from P0082 Lemma7 pages 362 to 364.
CONDITIONAL ON the pointwise leaf and the cited Lemma4. -/
theorem odd_index_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, B, hc, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, B, hc, hB, N₀, fun N hN => ?_⟩
  simpa only [Int.even_add_one, Int.not_even_iff_odd] using h N hN 1 (Or.inr rfl)

end LeanLab.ExceptionalSet.Supply465
