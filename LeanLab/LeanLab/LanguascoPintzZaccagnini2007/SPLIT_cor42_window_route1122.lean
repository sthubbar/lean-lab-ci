import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218

/-!
Route for `cor42_window_extension131` of DecompJ218.lean through Lemma 4.1 of P0045, LPZ 2007,
page 5, and the printed proof of Corollary 4.2 on page 6, carried to the window [X/2, X].
This file adds new declarations only; the parent keeps its sorry.

The implication's hypothesis on J(X) is not used: the window conclusion follows from Lemma 4.1
for even n of size X, since every prime of p1 + p2 = n with n at most X is at most X, and the
error terms of Lemma 4.1 are at most a small multiple of n S(n) for n at least X/2. E is the set
of generalised exceptional moduli of Lemma 4.1, chosen per X; the statement leaves E existential,
so it is not quantified too broadly.

Steps:
1. LEAF, HARD: Lemma 4.1 on the window with Corollary 4.2's choices of H, T and epsilon, the
   exceptional moduli satisfying the raw bound r much larger than L squared from Pintz and
   Goldfeld-Schinzel, and the structure of the moduli used on page 6: a real primitive character
   mod r has r = A r' with A in 1, 4, 8, Davenport chapter 5, and a non-real one has
   log r' much larger than L by Iwaniec's zero free region.
2. Proved here: the printed proof of Corollary 4.2, page 6, passing from r to r', display 10.
3. Proved here: the assembly with the exact statement of the parent.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Lemma 4.1 of P0045 page 5 on the window [X/2, X], with the Corollary 4.2 choices, page 6.
Class: HARD.
Source: Pintz ELAZ 2004 Theorem 10; Jutila for K at most C0 e^(4H); Pintz and Goldfeld-Schinzel
for r much larger than L^2; page 6, Davenport chapter 5 for r = A r', A in 1, 4, 8, for a real
character, Iwaniec for log r' much larger than L otherwise. Lemma 4.1 with n in [X/2, X] in
place of J(X); the explicit formula proof is the same for n of size X. -/
theorem leaf_lemma41_window1122 :
    ∀ η : ℝ, 0 < η →
      ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ E.card ≤ K₁ ∧
          (∀ r ∈ E, c * Lg X ^ 2 ≤ r ∧
            (r ∣ 8 * oddRad131 r ∨ c * Lg X ≤ Real.log (oddRad131 r))) ∧
          (∀ n ∈ evenWindow131 X, Nonexceptional131 Cstar E n →
            |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
          (∀ n ∈ evenWindow131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  sorry

/-- The odd radical is positive. -/
theorem oddRad131_pos1122 (r : ℕ) : 0 < oddRad131 r := by
  unfold oddRad131
  rcases Finset.eq_empty_or_nonempty (r.primeFactors.filter (fun p => 2 < p)) with h | ⟨p, hp⟩
  · rw [h, Finset.prod_empty]
    exact Nat.zero_lt_one
  · exact Finset.prod_pos
      (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos)

/-- P0045 page 6, proof of Corollary 4.2: condition 10 refers to r' in place of r. If r is
much larger than L squared and either r = A r' with A dividing 8, or log r' is much larger
than L, then r' is much larger than L squared, with constant min of c/8 and c^2/2. -/
theorem oddRad_lower_of_alternatives1122 {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L) {r : ℕ}
    (hr : c * L ^ 2 ≤ r) (halt : r ∣ 8 * oddRad131 r ∨ c * L ≤ Real.log (oddRad131 r)) :
    min (c / 8) (c ^ 2 / 2) * L ^ 2 ≤ oddRad131 r := by
  have hpos : (0 : ℝ) < oddRad131 r := by exact_mod_cast oddRad131_pos1122 r
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  rcases halt with hd | hlog
  · have hle : r ≤ 8 * oddRad131 r := Nat.le_of_dvd (by have := oddRad131_pos1122 r; omega) hd
    have hle' : (r : ℝ) ≤ 8 * oddRad131 r := by exact_mod_cast hle
    calc min (c / 8) (c ^ 2 / 2) * L ^ 2 ≤ c / 8 * L ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hL2
      _ ≤ oddRad131 r := by linarith
  · have hcl : 0 ≤ c * L := mul_nonneg hc.le hL
    have hexp : Real.exp (c * L) ≤ oddRad131 r := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hlog
    have hq := Real.quadratic_le_exp_of_nonneg hcl
    calc min (c / 8) (c ^ 2 / 2) * L ^ 2 ≤ c ^ 2 / 2 * L ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hL2
      _ ≤ 1 + c * L + (c * L) ^ 2 / 2 := by nlinarith
      _ ≤ oddRad131 r := hq.trans hexp

/-- The parent `cor42_window_extension131` of DecompJ218.lean, same statement text, from the
Lemma 4.1 window leaf and the proved page 6 step from r to r'. The hypothesis on J(X) is not
used. The parent theorem is neither used nor restated. -/
theorem cor42_window_extension_route1122 :
    Cor42OnWindow131 evenJ131 → Cor42OnWindow131 evenWindow131 := by
  intro _ η hη
  obtain ⟨K₁, Cstar, c, A, hCs, hc, hA, X₀, hX₀⟩ := leaf_lemma41_window1122 η hη
  refine ⟨K₁, Cstar, min (c / 8) (c ^ 2 / 2), A, hCs, lt_min (by positivity) (by positivity),
    hA, max X₀ 1, fun X hX => ?_⟩
  obtain ⟨P, E, hP, hcard, hmod, hrel, hup⟩ := hX₀ X ((le_max_left _ _).trans hX)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (le_max_right X₀ 1).trans hX
  have hLg : 0 ≤ Lg X := by
    unfold Lg
    exact Real.logb_nonneg (by norm_num) hX1
  refine ⟨P, E, hP, ⟨hcard, fun r hr => ?_⟩, hrel, hup⟩
  exact oddRad_lower_of_alternatives1122 hc hLg (hmod r hr).1 (hmod r hr).2

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.oddRad_lower_of_alternatives1122
#print axioms LeanLab.LPZ2007.cor42_window_extension_route1122
