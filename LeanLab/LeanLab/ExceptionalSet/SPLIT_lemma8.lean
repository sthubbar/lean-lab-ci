/-
Split of `lemma8` of this folder into the three steps of its proof in section 5 of the
article the statement comes from.

The statement counts the `n` of the window whose major arc integral is small. The proof
splits that set. Away from the fractional boundary of `F(n)` the major arc integral is the
sum of the two adjacent integer coefficients; those coefficients are large outside their own
sparse exceptional set; and the indices on the fractional boundary are few.

`lemma8_split` below states `Lemma8` unchanged and is assembled from the three leaves, so it
carries no `sorry` of its own. Each leaf carries exactly one step, and each is strictly
weaker than the split's main statement.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step of the proof, the plateau identity for the kernel weight, with no counting in
it. For `0 < Δ < 1` with `Δ = ℰ(γ,κ,N)^(-1/8)`, an index `n` whose value `F(n)` has
fractional part between `Δ` and `1 - Δ` lies on the plateau of the kernel, so the real part
of the major arc integral at `F(n)` is the real part of the sum of the two coefficients
adjacent to `F(n)`. One identity, for every `δ`, every `N` and every `n`; it is not an
estimate and it contains no exceptional set. The two fractional hypotheses are satisfied by
every `n` with `F(n)` an integer away from the boundary, so none of them is vacuous. -/
theorem leaf_major_identity (γ δ κ : ℝ) (N n : ℕ)
    (hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)))
    (hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hleft : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ Int.fract (F γ n))
    (hright : Int.fract (F γ n) ≤ 1 - calE γ κ N ^ (-(1 / 8 : ℝ))) :
    (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
        Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
          * eC (-(α * F γ n))).re =
      (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re := by
  sorry

/-- LEAF. Step of the proof, the sparse exceptional set of the coefficients, with no major
arc integral in it. For `1 < γ < 3/2` and small `δ`, and for `κ` below a positive cap that
does not depend on `κ` itself, all but `O(N ℰ^(-1/12))` indices of the window have the sum of
the two adjacent integer coefficients at least `c₀ F(N) ℰ^(-1/10)` in real part. This is the
coefficient lower bound of Lemma 7 and display 20, a count of indices of the window, and it
is strictly weaker than the split's statement because the quantity counted is a sum of two
coefficients rather than an integral. -/
theorem leaf_coefficient_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
              F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter (fun n : ℕ =>
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
                  R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                    c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- LEAF. Step of the proof, the fractional boundary count of display 23, purely a count of
indices. For `1 < γ < 3/2` and `κ` below a positive cap, the indices of the window whose
value `F(n)` is within `ℰ^(-1/8)` of an integer are at most `O(N ℰ^(-1/8))` in number. No
coefficient and no integral occurs, so this is strictly weaker than the split's statement.
At `N = 0` and `N = 1` the window is empty and the count is `0`, and the linear bound has a
positive right side, so the inequality is not vacuous there. -/
theorem leaf_fractional_boundary (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ((((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
            F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)).filter (fun n : ℕ =>
              Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
                1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  sorry

/-! ### Assembly -/

/-- Lemma 8 from the three leaves above: the unchanged statement of `lemma8`. The indices of
the window whose integral is small are either on the fractional boundary, counted by the
boundary leaf, or off it, where the identity leaf rewrites the integral into the sum of the
two adjacent coefficients, which is then small only on the exceptional set counted by the
coefficient leaf. The two counts are added, and `ℰ^(-1/8) ≤ ℰ^(-1/12)` absorbs the boundary
count into the exponent of the statement. -/
theorem lemma8_split : Lemma8 := by
  classical
  intro γ h1 h2
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := leaf_coefficient_lower γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := leaf_fractional_boundary γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, hcoeff⟩ := hcoeff δ hδ hδsmall
  let κ := min κa κb
  have hκ : 0 < κ := lt_min hκa hκb
  obtain ⟨c₀, Ba, hc₀, hBa, Na, ha⟩ := hcoeff κ hκ (min_le_left _ _)
  obtain ⟨Bb, hBb, Nb, hb⟩ := hboundary κ hκ (min_le_right _ _)
  refine ⟨κ, c₀, Ba + Bb, hκ, hc₀, max 2 (max Na Nb), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE : 1 < calE γ κ N := by
    unfold calE
    exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos hlog _))
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hE) _
  have hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hE)]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (Real.log_pos hE) (by norm_num))
  let W := (Finset.range (2 * N + 1)).filter (fun n : ℕ =>
    F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)
  let A := W.filter (fun n : ℕ =>
    (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
        c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
  let B := W.filter (fun n : ℕ =>
    Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
      1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))
  have hsubset : (Finset.range (2 * N + 1)).filter (fun n : ℕ =>
      F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N ∧
      (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
          Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
            * eC (-(α * F γ n))).re
        < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) ⊆ A ∪ B := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn0, hnA, hnBv, hnmajor⟩
    have hnW : n ∈ W := Finset.mem_filter.mpr ⟨hn0, hnA, hnBv⟩
    by_cases hnB : n ∈ B
    · exact Finset.mem_union_right _ hnB
    · have hgood : ¬ (Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) := by
        intro hbad
        exact hnB (Finset.mem_filter.mpr ⟨hnW, hbad⟩)
      have hid := leaf_major_identity γ δ κ N n hΔ hΔ1
        (le_of_not_gt (fun h => hgood (Or.inl h)))
        (le_of_not_gt (fun h => hgood (Or.inr h)))
      refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnW, ?_⟩)
      rw [hid] at hnmajor
      exact hnmajor
  have hcard : (((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
      F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N ∧
      (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
          Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
            * eC (-(α * F γ n))).re
        < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      (A.card : ℝ) + B.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le A B)
  have hpow : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ calE γ κ N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)
  calc (((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
      F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N ∧
      (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
          Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
            * eC (-(α * F γ n))).re
        < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ)
      ≤ (A.card : ℝ) + B.card := hcard
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
          Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := add_le_add (ha N hNa) (hb N hNb)
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
          Bb * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by gcongr
    _ = (Ba + Bb) * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by ring

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma8_split
