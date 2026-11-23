/-
Split of `leaf_even_moment` of `SPLIT_lemma6`, display 29 of Brudern-Perelli 1998,
P0082, section 6, p. 367-369, into the steps of its proof.

The paper applies Lemma 1 with the kernel `K_e` of display 31, so that for every `n`
whose fractional part `{F(n)}` lies in `[Δ/2, 1 - Δ/2]` the coefficient `R₁(ν_n + 1)`
is the major arc integral of display 32; the remaining `n`, counted by Lemma 4, are
handled by the trivial bound `|R₁(m)| ≪ X log X` in display 33; the good `n` are then
bounded through displays 35 to 39 with Lemma 9. Display 33 loses a factor `(log X)²`
against the target, which the paper calls acceptable; we absorb it by taking
`Δ = ℰ^(-1/3) / (log X)²` in place of display 34, so the boundary count carries the
saving and no constant has to swallow a power of `log X`.

Leaves:
* `leaf_R1_trivial_bound`, the trivial bound before display 33, now proved in
  `Feed1122LeafR1TrivialBound` from its MEDIUM leaf `leaf_R1_le_sum_log_sq`.
* `leaf_boundary_count`, the Lemma 4 count after display 32, MEDIUM.
* `leaf_even_good_moment`, displays 31, 32 and 35 to 39 on the good `n`, HARD.
`leaf_even_moment_of_leaves` restates `leaf_even_moment` exactly and is proved from them.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.Feed1122LeafR1TrivialBound

namespace LeanLab.ExceptionalSet.U1539

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- Formerly a LEAF, now proved from `Feed1122LeafR1TrivialBound`, which carries the
analytic half as the MEDIUM leaf `leaf_R1_le_sum_log_sq`. The trivial bound stated before
display 33 of P0082, p. 368,
`|R₁(m)| ≤ ∫_0^1 |S(α)|² dα ≪ X log X`, here with the explicit constant `2`, since
`∫_0^1 |S|² = Σ_{P<p≤X} (log p)² ≤ log X · θ(X) ≤ (log 4) X log X`. Class MEDIUM: Parseval
for a trigonometric polynomial and a Chebyshev bound. Valid for every real `P`, every
integer `m` and every `X ≥ 2`. -/
theorem leaf_R1_trivial_bound (P X : ℝ) (hX : 2 ≤ X) (m : ℤ) :
    ‖R1 P X m‖ ≤ 2 * X * Real.log X :=
  leaf_R1_trivial_bound_of_leaves P X hX m

/-- LEAF: the count after display 32 of P0082, p. 368, by Lemma 4 with `α = 1`: the `n`
of the window whose fractional part `{F(n)}` lies below `Δ/2` or above `1 - Δ/2` number
`O(NΔ + N exp(-κ̃ (log N)^(3-2γ)))`. Here the second term is written as
`N ℰ^(-1/3) / (log X)²` with `ℰ = calE γ κ N`, which it does not exceed eventually for every
`κ` below a cap, because `ℰ^(-1/3)` with a smaller `κ` beats any power of `log N`. Class
MEDIUM: Lemma 4 is the stated `Lemma4` of this folder, plus a growth comparison. For `Δ ≥ 1`
the bound is trivial; it is not vacuous for small `Δ`. -/
theorem leaf_boundary_count (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ : ℝ, 0 < Δ →
        (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
            Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ)
          ≤ B * N * (Δ + calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2) := by
  sorry

/-- LEAF: displays 31, 32 and 35 to 39 of P0082, p. 367-369, on the good `n`. For the `n`
of the window with `ν_n` even and `{F(n)} ∈ [Δ/2, 1 - Δ/2]`, where
`Δ = ℰ^(-1/3) / (log X)²`, the kernel `W_e` of display 31 equals `1` at `{F(n)} - 1`, so by
Lemma 1 the coefficient `R₁(ν_n + 1)` is the major arc integral of `S² K_e e(-αF(n))`; the
tail beyond `|α| ≤ Y` is removed, display 35, the square is opened, display 37, and the
two ranges of `Φ_e(β - α)` are bounded by display 38 and by Lemma 9 with Vinogradov's
estimate, display 39. Class HARD. It bounds a sub-sum of the parent's sum only, so it is
strictly weaker than `leaf_even_moment`. -/
theorem leaf_even_good_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n))).filter
              (fun n : ℕ => ¬ (Int.fract (F γ n) <
                  calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 ∨
                1 - calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 <
                  Int.fract (F γ n))),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-! ### Glue, no sorry -/

/-- A sum of squares over `s` is its good part plus at most the number of bad indices of a
superset times a uniform bound on the squares. -/
theorem moment_good_bad_glue (s t : Finset ℕ) (bad : ℕ → Prop) [DecidablePred bad]
    (g : ℕ → ℝ) (M G c : ℝ) (hst : s ⊆ t) (hg : ∀ n ∈ s, g n ^ 2 ≤ M)
    (hgood : (∑ n ∈ s.filter (fun n => ¬ bad n), g n ^ 2) ≤ G)
    (hcount : ((t.filter bad).card : ℝ) ≤ c) (hM : 0 ≤ M) :
    (∑ n ∈ s, g n ^ 2) ≤ G + c * M := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s := s) (p := bad)]
  have hb : (∑ n ∈ s.filter bad, g n ^ 2) ≤ ((s.filter bad).card : ℝ) * M := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun n hn => hg n (Finset.mem_filter.mp hn).1)
  have hsub : ((s.filter bad).card : ℝ) ≤ ((t.filter bad).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hst)
  have h3 : ((s.filter bad).card : ℝ) * M ≤ c * M :=
    mul_le_mul_of_nonneg_right (hsub.trans hcount) hM
  linarith

/-- For `N ≥ 3` the size `X = F(γ,N)` is at least `2` and `log X = (log N)^γ ≥ 1`. -/
theorem F_ge_two_and_log (γ : ℝ) (h1 : 1 < γ) (N : ℕ) (hN : 3 ≤ N) :
    2 ≤ F γ N ∧ 1 ≤ Real.log (F γ N) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hpow : 1 ≤ Real.log (N : ℝ) ^ γ := Real.one_le_rpow hlogN (by linarith)
  have hlogF : Real.log (F γ N) = Real.log (N : ℝ) ^ γ := by
    simp [F, Real.log_exp]
  refine ⟨?_, hlogF ▸ hpow⟩
  have : Real.exp 1 ≤ F γ N := by
    unfold F
    exact Real.exp_le_exp.mpr hpow
  have := Real.exp_one_gt_d9
  linarith

/-- The common assembly of the two parity branches of display 29 and display 30: a good
part bounded at `B₁ N X² ℰ^(-1/3)` and a boundary count at `B₂ N (Δ + Δ)` with
`Δ = ℰ^(-1/3) / (log X)²` give the whole branch at `(B₁ + 8 B₂) N X² ℰ^(-1/3)`. -/
theorem branch_moment_assemble (γ : ℝ) (h1 : 1 < γ) (pred : ℕ → Prop) [DecidablePred pred]
    (arg : ℕ → ℤ) (δ κ B₁ B₂ : ℝ) (_hB₂ : 0 < B₂) (N : ℕ) (hN : 3 ≤ N)
    (hgood : (∑ n ∈ ((Finset.Icc ((N + 1) / 2) N).filter pred).filter
        (fun n : ℕ => ¬ (Int.fract (F γ n) <
            calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 ∨
          1 - calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 <
            Int.fract (F γ n))),
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (arg n)‖ ^ 2) ≤
          B₁ * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)))
    (hbad : (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
        Int.fract (F γ n) < calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 ∨
        1 - calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 <
          Int.fract (F γ n))).card : ℝ)
        ≤ B₂ * N * (calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 +
          calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2)) :
    (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter pred,
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (arg n)‖ ^ 2) ≤
      (B₁ + 8 * B₂) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨hX2, hL1⟩ := F_ge_two_and_log γ h1 N hN
  set X := F γ N with hXdef
  set L := Real.log X with hLdef
  set E := calE γ κ N ^ (-(1 / 3 : ℝ)) with hEdef
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by linarith
  have hM : ∀ n ∈ (Finset.Icc ((N + 1) / 2) N).filter pred,
      ‖R1 (X ^ (6 * δ)) X (arg n)‖ ^ 2 ≤ (2 * X * L) ^ 2 := by
    intro n _
    have hb := leaf_R1_trivial_bound (X ^ (6 * δ)) X hX2 (arg n)
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hglue := moment_good_bad_glue ((Finset.Icc ((N + 1) / 2) N).filter pred)
    (Finset.Icc ((N + 1) / 2) N)
    (fun n : ℕ => Int.fract (F γ n) < E / L ^ 2 / 2 ∨ 1 - E / L ^ 2 / 2 < Int.fract (F γ n))
    (fun n => ‖R1 (X ^ (6 * δ)) X (arg n)‖) ((2 * X * L) ^ 2)
    (B₁ * N * X ^ 2 * E) (B₂ * N * (E / L ^ 2 + E / L ^ 2))
    (Finset.filter_subset _ _) hM hgood hbad (sq_nonneg _)
  refine hglue.trans (le_of_eq ?_)
  have hL2 : L ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### Assembly -/

/-- `leaf_even_moment` of `SPLIT_lemma6`, statement unchanged, from the three leaves above. -/
theorem leaf_even_moment_of_leaves (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hgood⟩ := leaf_even_good_moment γ h1 h2
  obtain ⟨κb, hκb, hbad⟩ := leaf_boundary_count γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κa, hκa, hgood⟩ := hgood δ hδ hδs
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκle => ?_⟩
  obtain ⟨B₁, hB₁, N₁, hgood⟩ := hgood κ hκ (hκle.trans (min_le_left _ _))
  obtain ⟨B₂, hB₂, N₂, hbad⟩ := hbad κ hκ (hκle.trans (min_le_right _ _))
  refine ⟨B₁ + 8 * B₂, by linarith, max (max N₁ N₂) 3, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hL := (F_ge_two_and_log γ h1 N hN3).2
  have hΔ : 0 < calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 := by
    have : 0 < calE γ κ N := Real.exp_pos _
    have : 0 < Real.log (F γ N) := by linarith
    positivity
  exact branch_moment_assemble γ h1 (fun n : ℕ => Even (nu γ n)) (fun n => nu γ n + 1)
    δ κ B₁ B₂ hB₂ N hN3 (hgood N hN1) (hbad N hN2 _ hΔ)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_R1_trivial_bound
#print axioms LeanLab.ExceptionalSet.U1539.moment_good_bad_glue
#print axioms LeanLab.ExceptionalSet.U1539.F_ge_two_and_log
#print axioms LeanLab.ExceptionalSet.U1539.branch_moment_assemble
#print axioms LeanLab.ExceptionalSet.U1539.leaf_even_moment_of_leaves
