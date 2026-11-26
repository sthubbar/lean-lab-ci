/-
Feed 1122 split of `leaf_window_count` of `LeanLab.ExceptionalSet.SPLIT_lu`.

P0095 W. C. Lu, Exceptional set of Goldbach number, J. Number Theory 130 (2010) 2359-2392.

`leaf_window_count` is the local count of Lu's Section 10: on the window `|k - N| ≤ N^0.99979`
of Lemma 1, p. 2360, the even non-Goldbach `k` number `≪ N^0.8787026`.  The lab already proves
this CONDITIONAL ON Lu's analytic bundle, as `Lu2010Assembly.window_count`, and the bundle has
since been reduced, by the proved files Lu2010Lemma1, Lu2010Orth, Lu2010Arcs, Lu2010Sec9,
Lu2010Minor, Lu2010Dirichlet, Lu2010Bound12 and Lu2010Main63, to two analytic displays only:
* the major arc lower bound (84) or (85), p. 2391, for the concrete expression (63),
  the structure `Lu2010Main63.MajorInputs63`;
* the zero mass display (39), `Lu2010Formula63.Mass39`, which yields (86).

This file states that pair as one LEAF and proves `leaf_window_count_of_leaves`, whose statement
is the statement of `leaf_window_count` verbatim.  The glue proved here: the conversion chain
of the bundles, the identification `rad N = ⌊N^0.99979⌋`, and the two exceptional even indices
`0` and `2` that `Pintz2018Reduction.Exc` leaves out because it asks `4 ≤ k`.

The pair is one leaf, not two, because both displays speak about the same family of zeros, and
the lab has no definition of Lu's zero family yet: `MajorInputs63` and `Mass39` take the family as
a parameter.  Splitting further needs that definition first, see the burst note.

AI wrote this Lean code.  Binary Goldbach is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.Statements
import LeanLab.ExceptionalSet.Lu2010Main63

namespace LeanLab.ExceptionalSet.Feed1122WindowCount
open LeanLab.ExceptionalSet
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010Formula63
open LeanLab.ExceptionalSet.Lu2010Main63

attribute [local instance] Classical.propDecidable

/-- The expression 63 over the empty family vanishes identically, since `pairs N ∅ M` is empty. -/
theorem printed63_empty (N : ℕ) (M : ℝ) (k : ℕ) :
    Lu2010Eq63.printed63 N (∅ : Finset Exponent) M k = 0 := by
  unfold Lu2010Eq63.printed63 Lu2010Formula63.pairs
  simp

/-- Reduction helper, proved.  Display (84) of Lu 2010, p. 2391, for the concrete major arc
integral `Lu2010Arcs.D1c` and the concrete singular product `BG2026.Sing`, on Lemma 1's window,
implies the leaf's existence statement.  The zero mass display (39) is trivial for the empty
family, because its weight sum over an empty set is zero, and `printed63` over the empty family
vanishes by `printed63_empty`.  This isolates the exact missing analytic input of the leaf: the
major arc lower bound (84) for the printed expression 63.  The empty family is the strongest
choice for (63), since it makes the error term `‖printed63‖` zero; any nonempty family makes
both (39) and (84) harder. -/
theorem leaf_of_major84
    (h84 : ∃ Cerr : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ k ∈ Win N, Even k →
      LeanLab.ExceptionalSet.BG2026.Sing k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-2⁻¹ : ℝ))
        < (Lu2010Arcs.D1c N k).re) :
    ∃ (family : ℕ → Finset Exponent) (M : ℕ → ℝ),
      Mass39 family ∧ Nonempty (MajorInputs63 family M) := by
  refine ⟨fun _ => ∅, fun _ => 0, ⟨0, by norm_num, 0, fun N _ _ => by simp⟩, ?_⟩
  obtain ⟨Cerr, N0, h⟩ := h84
  refine ⟨⟨N0, Cerr, 1, one_pos, ?_⟩⟩
  intro N hN
  refine Or.inl (fun k hk hke => ?_)
  have h63 : Lu2010Eq63.printed63 N (∅ : Finset Exponent) 0 k = 0 := printed63_empty N 0 k
  rw [h63]
  simp
  exact h N hN k hk hke

/-- LEAF: Lu 2010, p. 2391 displays (84) or (85) together with display (39). HARD.
There are a family of exponents and a cutoff `M` for which the zero mass display (39) holds and
the major arc lower bound (84), in the case without an exceptional zero, or (85), in the case
with one, holds on Lemma 1's window for the concrete expression (63) and the singular product.
This is the analytic heart of Lu's Sections 4 to 8: zero density estimates, the exceptional zero
repulsion and the singular series lower bound.  It says nothing about Goldbach numbers by itself;
the lab proves everything from it to the window count. -/

theorem leaf_lu_major_and_mass39 :
    ∃ (family : ℕ → Finset Exponent) (M : ℕ → ℝ),
      Mass39 family ∧ Nonempty (MajorInputs63 family M) := by
  sorry

/-- Lu's full analytic bundle `Inputs` of `Lu2010Assembly`, built from the leaf through the
proved reduction chain of the lab. -/
theorem inputs_nonempty : Nonempty Inputs := by
  obtain ⟨family, M, h39, ⟨J⟩⟩ := leaf_lu_major_and_mass39
  exact ⟨((((((J.toInputsL h39).toInputsS Lu2010Bound12.bound12_proved).toInputsM).toInputsC
    ).toInputsO).toInputsT).toInputs⟩

/-- `rad N = ⌊N^0.99979⌋` for `N ≥ 1`, from `rad_eq`. -/
theorem rad_eq_floor (N : ℕ) (hN : 0 < N) : rad N = ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊ := by
  unfold rad
  rw [rad_eq N hN]

/-- The even non-Goldbach indices of the window lie in `bad N` or in `{0, 2}`. -/
theorem filter_subset (N : ℕ) (hN : 0 < N) :
    (Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n) ⊆ bad N ∪ {0, 2} := by
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hwin, hev, hng⟩ := hn
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · apply Finset.mem_union_right
    obtain ⟨m, hm⟩ := hev
    have : n = 0 ∨ n = 2 := by omega
    rcases this with h | h <;> simp [h]
  · apply Finset.mem_union_left
    unfold bad
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold Win
      rw [rad_eq_floor N hN]
      exact hwin
    · exact ⟨h4, hev, hng⟩

/-- `leaf_window_count` of `SPLIT_lu`, statement verbatim, from the leaf. -/
theorem leaf_window_count_of_leaves :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := by
  obtain ⟨I⟩ := inputs_nonempty
  obtain ⟨N2, K, hK, hwin⟩ := window_count I
  refine ⟨K + 2, max N2 1, by linarith, le_max_right _ _, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : 0 < N := hN1
  have hb := hwin N (le_trans (le_max_left _ _) hN)
  have hθ : θw = 0.8787026 := rfl
  rw [hθ] at hb
  have hcard := Finset.card_le_card (filter_subset N hN0)
  have hu := Finset.card_union_le (bad N) ({0, 2} : Finset ℕ)
  have h2 : ({0, 2} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  have hnat : ((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
      (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card ≤ (bad N).card + 2 := by omega
  have hreal : (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
      (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) ≤ ((bad N).card : ℝ) + 2 := by
    exact_mod_cast hnat
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (0.8787026 : ℝ) := Real.one_le_rpow hNR (by norm_num)
  nlinarith

end LeanLab.ExceptionalSet.Feed1122WindowCount

#print axioms LeanLab.ExceptionalSet.Feed1122WindowCount.inputs_nonempty
#print axioms LeanLab.ExceptionalSet.Feed1122WindowCount.rad_eq_floor
#print axioms LeanLab.ExceptionalSet.Feed1122WindowCount.filter_subset
#print axioms LeanLab.ExceptionalSet.Feed1122WindowCount.leaf_window_count_of_leaves
