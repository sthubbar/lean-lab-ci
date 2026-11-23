/-
Split of `major_arc_count_power` of `LeanLab.ExceptionalSet.SPLIT_theorem51`, burst-20261122,
session S91. Source: P0015, Montgomery and Vaughan 1975, section 8, displays 8.1 to 8.3, page 367:
`R(n) ≥ R₁(n) - |R₂(n)|`, the minor arc part `R₂` is discarded for few `n` by the mean value
bound 3.2, and what remains is a lower bound for the main term.

Here the order is reversed, on the lab's discrete data `M = 2x + 1`, `Φ = logPrimes x`, minor
arcs at `Q = x^{1/10}`. By `sum_dft_sq` the major part plus the minor part is `M R(n)`, with
`R(n) = ∑_j Φ(j) Φ(n - j)` the weighted Goldbach count. So a small major part forces either a
large minor part, counted by `minor_arc_l4_power` of the parent file, PROVED, or a small
Goldbach count `R(n) ≤ 3x/8`. The latter is the one LEAF.

* LEAF `goldbach_count_window_power`, HARD: at most `C x^θ`, `θ < 1`, even `n` in `(x/2, x]`
  have `‖R(n)‖ ≤ 3x/8`.
* `minor_large_count_power`, PROVED from `minor_arc_l4_power` and Markov's inequality
  `card_large_minor_le`.
* `major_le_goldbach_add_minor`, PROVED: the pointwise identity.
* `major_arc_count_power_of_leaves`, PROVED from the above, statement identical to the parent.

QUESTION recorded in the burst note: Montgomery and Vaughan prove only `R₁(n) > X P^{-1/3}` at
8.3, not a lower bound of order `X`; in the exceptional character case `R₁(n)` can be of order
`(1 - β̃) n log P`. The fixed threshold `3x/8` here, like the parent's `M x/4`, asks more than
8.3 and seems to need the absence of exceptional zeros of modulus at most `x^{1/10}` close to `1`.

The parent's proved minor arc input lives in the parent file, so this file imports the parent
and the parent keeps its sorry. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_theorem51

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction
open ZMod
open LeanLab.ExceptionalSet.MV
open LeanLab.Routes.R0001

noncomputable section

/-- LEAF: P0015 section 8, displays 8.1 to 8.3 page 367, the lower bound for the Goldbach count
off a power-small set, in the form with a fixed threshold. HARD. On `M = 2x + 1` and
`Φ = logPrimes x`, the weighted count `R(n) = ∑_j Φ(j) Φ(n - j)` of ordered prime pairs with
sum `n` has modulus at most `3x/8` for at most `C x^θ` even `n` in `(x/2, x]`, some `θ < 1`.
Heuristically `R(n) ~ 𝔖(n) n ≥ 1.32 x/2`. See the QUESTION in the header on the exceptional
zero case. -/
theorem goldbach_count_window_power :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖∑ j : ZMod (Mx x), logPrimes x j * logPrimes x ((n : ZMod (Mx x)) - j)‖
                ≤ 3 * (x : ℝ) / 8)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) ^ θ := by
  sorry

/-- The minor arc part is at least `M x / 8` for at most `C x^θ` of the `n` in `(x/2, x]`:
Markov's inequality `card_large_minor_le` against the fourth moment of `minor_arc_l4_power`,
P0015 display 3.2 in its discrete form. -/
theorem minor_large_count_power :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ =>
              (Mx x : ℝ) * x / 8 ≤ ‖minorPart (logPrimes x)
                (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10))) (n : ZMod (Mx x))‖)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) ^ θ := by
  classical
  obtain ⟨θ, C, X0, hθ0, hθ1, hC, hX0, h⟩ := minor_arc_l4_power
  refine ⟨θ, 4 * C, X0, hθ0, hθ1, by positivity, hX0, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans hX0 hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hMpos : (0 : ℝ) < (Mx x : ℝ) := by
    have : 0 < Mx x := by unfold Mx; omega
    exact_mod_cast this
  set m := minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10))
  set T : ℝ := (Mx x : ℝ) * x / 8 with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  set S4 : ℝ := ∑ k ∈ m, ‖𝓕 (logPrimes x) k‖ ^ 4
  have hcard : ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ =>
      T ≤ ‖minorPart (logPrimes x) m (n : ZMod (Mx x))‖)).card : ℕ) : ℝ)
      ≤ ((univ.filter fun n : ZMod (Mx x) => T ≤ ‖minorPart (logPrimes x) m n‖).card : ℝ) := by
    gcongr
    refine Finset.card_le_card_of_injOn (fun n => (n : ZMod (Mx x))) ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hn
      simp [hn.2]
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
      have := (ZMod.natCast_eq_natCast_iff' a b (Mx x)).1 hab
      have ha' : a < Mx x := by unfold Mx; omega
      have hb' : b < Mx x := by unfold Mx; omega
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  have hmk := card_large_minor_le (logPrimes x) m T hTpos.le
  have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => by positivity
  have hb := h x hx
  have hkey : ((univ.filter fun n : ZMod (Mx x) => T ≤ ‖minorPart (logPrimes x) m n‖).card : ℝ)
      ≤ 4 * ((Mx x : ℝ) * S4 / ((Mx x : ℝ) * x / 4) ^ 2) := by
    have hT2 : T ^ 2 = ((Mx x : ℝ) * x / 4) ^ 2 / 4 := by rw [hT]; ring
    have hpos : 0 < ((Mx x : ℝ) * x / 4) ^ 2 := by positivity
    rw [hT2] at hmk
    rw [mul_div_assoc', le_div_iff₀ hpos]
    nlinarith
  calc _ ≤ _ := hcard
    _ ≤ 4 * ((Mx x : ℝ) * S4 / ((Mx x : ℝ) * x / 4) ^ 2) := hkey
    _ ≤ 4 * (C * (x : ℝ) ^ θ) := by gcongr
    _ = 4 * C * (x : ℝ) ^ θ := by ring

/-- The pointwise step, P0015 display 8.1 read backwards on the discrete data: the major part
plus the minor part is `M R(n)`, so a major part at most `M x/4` and a minor part below `M x/8`
give `‖R(n)‖ ≤ 3x/8`. -/
theorem major_le_goldbach_add_minor (x : ℕ) (hx : 1 ≤ x) (m : Finset (ZMod (Mx x)))
    (n : ZMod (Mx x))
    (hmaj : ‖majorPart (logPrimes x) m n‖ ≤ (Mx x : ℝ) * x / 4)
    (hmin : ‖minorPart (logPrimes x) m n‖ < (Mx x : ℝ) * x / 8) :
    ‖∑ j : ZMod (Mx x), logPrimes x j * logPrimes x (n - j)‖ ≤ 3 * (x : ℝ) / 8 := by
  have hid : majorPart (logPrimes x) m n + minorPart (logPrimes x) m n
      = (Mx x : ℂ) * ∑ j : ZMod (Mx x), logPrimes x j * logPrimes x (n - j) := by
    unfold majorPart minorPart
    rw [add_comm, Finset.sum_add_sum_compl, sum_dft_sq]
  have hMpos : (0 : ℝ) < (Mx x : ℝ) := by
    have : 0 < Mx x := by unfold Mx; omega
    exact_mod_cast this
  have hnorm : (Mx x : ℝ) * ‖∑ j : ZMod (Mx x), logPrimes x j * logPrimes x (n - j)‖
      ≤ ‖majorPart (logPrimes x) m n‖ + ‖minorPart (logPrimes x) m n‖ := by
    have := norm_add_le (majorPart (logPrimes x) m n) (minorPart (logPrimes x) m n)
    rw [hid, norm_mul, Complex.norm_natCast] at this
    exact this
  have h3 : (Mx x : ℝ) * ‖∑ j : ZMod (Mx x), logPrimes x j * logPrimes x (n - j)‖
      ≤ (Mx x : ℝ) * (3 * (x : ℝ) / 8) := by
    nlinarith
  exact le_of_mul_le_mul_left h3 hMpos

/-- `major_arc_count_power` assembled from the LEAF `goldbach_count_window_power` and the
PROVED `minor_large_count_power`; statement identical to the parent. -/
theorem major_arc_count_power_of_leaves :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖majorPart (logPrimes x) (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)))
                (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) ^ θ := by
  classical
  obtain ⟨θ₁, C₁, X₁, hθ₁0, hθ₁1, hC₁, hX₁, h₁⟩ := goldbach_count_window_power
  obtain ⟨θ₂, C₂, X₂, hθ₂0, hθ₂1, hC₂, hX₂, h₂⟩ := minor_large_count_power
  refine ⟨max θ₁ θ₂, C₁ + C₂, max X₁ X₂, lt_of_lt_of_le hθ₁0 (le_max_left _ _),
    max_lt hθ₁1 hθ₂1, by positivity, le_trans hX₁ (le_max_left _ _), ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (le_trans hX₁ (le_max_left _ _)) hx
  have hx1r : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  set m := minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10))
  set W := Finset.Icc (x / 2 + 1) x
  set A := W.filter (fun n : ℕ => Even n ∧
    ‖∑ j : ZMod (Mx x), logPrimes x j * logPrimes x ((n : ZMod (Mx x)) - j)‖
      ≤ 3 * (x : ℝ) / 8)
  set B := W.filter (fun n : ℕ =>
    (Mx x : ℝ) * x / 8 ≤ ‖minorPart (logPrimes x) m (n : ZMod (Mx x))‖)
  have hsub : W.filter (fun n : ℕ => Even n ∧
      ‖majorPart (logPrimes x) m (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4) ⊆ A ∪ B := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnW, he, hmaj⟩ := hn
    rcases le_or_gt ((Mx x : ℝ) * x / 8) ‖minorPart (logPrimes x) m (n : ZMod (Mx x))‖ with
      hmin | hmin
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnW, hmin⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnW, he,
        major_le_goldbach_add_minor x hx1 m _ hmaj hmin⟩)
  have hA := h₁ x (le_trans (le_max_left _ _) hx)
  have hB := h₂ x (le_trans (le_max_right _ _) hx)
  have hp1 : (x : ℝ) ^ θ₁ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_left _ _)
  have hp2 : (x : ℝ) ^ θ₂ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_right _ _)
  have hcu : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ) + B.card := by
    exact_mod_cast Finset.card_union_le A B
  calc (((W.filter (fun n : ℕ => Even n ∧
          ‖majorPart (logPrimes x) m (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
      ≤ ((A ∪ B).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (A.card : ℝ) + B.card := hcu
    _ ≤ C₁ * (x : ℝ) ^ θ₁ + C₂ * (x : ℝ) ^ θ₂ := add_le_add hA hB
    _ ≤ C₁ * (x : ℝ) ^ max θ₁ θ₂ + C₂ * (x : ℝ) ^ max θ₁ θ₂ := by gcongr
    _ = (C₁ + C₂) * (x : ℝ) ^ max θ₁ θ₂ := by ring

end

#print axioms minor_large_count_power
#print axioms major_le_goldbach_add_minor
#print axioms major_arc_count_power_of_leaves

end LeanLab.ExceptionalSet.BG2026
