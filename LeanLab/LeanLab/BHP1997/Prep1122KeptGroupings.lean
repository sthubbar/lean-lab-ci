/-
P0069 Baker Harman Pintz 1997, page 53 with Lemma 33 on page 48. Burst S51 burst-20261122, wave 3,
the leaf upK_box_51 of branch claude/BHP1997-kept51, file Prep1122KeptBoxes.lean.

The page 53 sentence is: we obtain b1 from psi(m, Y^c4) by deleting from k_m the terms for which
Lemma 33 does not apply to any arrangement of the variables. A kept term is therefore one for which
some arrangement works, and upperPrimeCovered lists the twelve arrangements: the ordered pairs of
disjoint nonempty groups of the three primes p1, p2, p3, the group exponents playing beta1 and
beta2 of Lemma 33, the remaining factor going into L. To apply Lemma 33 to one fixed arrangement,
each kept term is assigned to the FIRST arrangement in that list for which the pair lies in the
Lemma 33 region. This partitions the kept part of one dyadic box into twelve pieces, and the
pieces are recombined by the Cauchy Schwarz step upK_window_cs, at the cost of the constant 144.

This file proves upK_box_51, as upK_box_51_of_groups with the identical statement, from the
LEAF upK_group8_51, display 5.1 for one dyadic box and one first arrangement. Four arrangements,
g = 1, 3, 5, 7, put the smaller exponent first and never occur since p3 < p2 < p1; their pieces
are zero, upK_group_vanish. The partition identity, the vanishing and the recombination are PROVED.
The leaf upK_group8_51 is the paper's single application of Lemma 33 to one of the eight remaining
arrangements on one box.

New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122KeptBoxes

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- Summing over the first index of a finite list of conditions: for P on Fin n, the indicator
that some P g holds equals the sum over g of the indicator that g is the first index where P holds.
This is the partition of the kept terms by their first Lemma 33 arrangement, page 53. PROVED. -/
theorem upK_first_sum {n : ℕ} (P : Fin n → Prop) (r : ℝ) :
    (∑ g : Fin n, if P g ∧ ∀ j < g, ¬ P j then r else 0) = if ∃ g, P g then r else 0 := by
  by_cases h : ∃ g, P g
  · rw [if_pos h]
    have hne : (Finset.univ.filter P).Nonempty := by
      obtain ⟨g, hg⟩ := h
      exact ⟨g, by simp [hg]⟩
    set g0 := (Finset.univ.filter P).min' hne with hg0def
    have hg0 : P g0 := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    have hmin : ∀ j < g0, ¬ P j := fun j hj hPj =>
      absurd (Finset.min'_le _ j (by simp [hPj])) (not_le.mpr hj)
    rw [Finset.sum_eq_single g0]
    · rw [if_pos ⟨hg0, hmin⟩]
    · intro g _ hgne
      rw [if_neg]
      rintro ⟨hPg, hlt⟩
      rcases lt_trichotomy g g0 with h1 | h1 | h1
      · exact hmin g h1 hPg
      · exact hgne h1
      · exact hlt g0 h1 hg0
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun g _ => if_neg fun hg => h ⟨g, hg.1⟩

/-- Page 53: upperPrimeCovered is the statement that one of the twelve arrangements of the
exponents a, b, c lies in the Lemma 33 region of page 48, listed in the order of its definition.
PROVED. -/
theorem upK_covered_iff (ε a b c : ℝ) :
    upperPrimeCovered ε a b c ↔ ∃ g : Fin 12,
      upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
        (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) := by
  unfold upperPrimeCovered
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩, ⟨6, h⟩, ⟨7, h⟩, ⟨8, h⟩, ⟨9, h⟩,
      ⟨10, h⟩, ⟨11, h⟩]
  · rintro ⟨g, hg⟩
    fin_cases g <;> simp_all

/-- Page 53, the partition of one dyadic box of the kept part of k_m by the first Lemma 33
arrangement. For each m, the box coefficient of upK_kept_dyadic equals the sum over the twelve
arrangements g of the coefficient whose terms have g as their first arrangement. PROVED. -/
theorem upK_box_groupings (ε Y : ℝ) (i : ℕ × ℕ × ℕ) (m : ℕ) :
    (∑ p1 ∈ m.primeFactors.filter
        (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < Y ^ upperC4 ε),
      ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
          (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
        ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
            (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
          if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
              upperPrimeCovered ε (Real.log p1 / Real.log Y) (Real.log p2 / Real.log Y)
                (Real.log p3 / Real.log Y)
            then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) =
      ∑ g : Fin 12,
        ∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < Y ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  (fun a b c : ℝ =>
                    upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                    ∀ j < g, ¬ upperPairRegion ε
                      (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                    (Real.log p1 / Real.log Y) (Real.log p2 / Real.log Y)
                    (Real.log p3 / Real.log Y)
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0 := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p2 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p3 _ => ?_
  set a := Real.log p1 / Real.log Y
  set b := Real.log p2 / Real.log Y
  set c := Real.log p3 / Real.log Y
  by_cases hB : (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i
  · simp only [hB, true_and]
    rw [upK_first_sum (fun g : Fin 12 =>
      upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
        (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g)), upK_covered_iff]
    split_ifs <;> rfl
  · simp only [hB, false_and, ite_false, Finset.sum_const_zero]

/-- Page 53: four of the twelve arrangements of upperPrimeCovered never occur in k_m. Since
p3 < p2 < p1 and Y > 1, the exponents satisfy 0 < c < b < a, while upperPairRegion ε m n needs
n <= m; so the pairs (b, a), (c, a), (c, b) and (c, a + b), g = 1, 3, 5, 7, fail, and the
coefficient of such a first arrangement vanishes. PROVED. -/
theorem upK_group_vanish (ε Y : ℝ) (hY : 1 < Y) (i : ℕ × ℕ × ℕ) (g : Fin 12)
    (hg : g = 1 ∨ g = 3 ∨ g = 5 ∨ g = 7) (m : ℕ) :
    (∑ p1 ∈ m.primeFactors.filter
        (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < Y ^ upperC4 ε),
      ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
          (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
        ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
            (fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
          if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
              (fun a b c : ℝ =>
                upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                  (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                ∀ j < g, ¬ upperPairRegion ε
                  (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                  (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                (Real.log p1 / Real.log Y) (Real.log p2 / Real.log Y)
                (Real.log p3 / Real.log Y)
            then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun p1 hp1 => Finset.sum_eq_zero fun p2 hp2 =>
    Finset.sum_eq_zero fun p3 hp3 => ?_
  rw [if_neg]
  rintro ⟨_, hG, _⟩
  have hp1' := Finset.mem_filter.mp hp1
  have hp2' := Finset.mem_filter.mp hp2
  have hp3' := Finset.mem_filter.mp hp3
  have h3prime : (2 : ℝ) ≤ p3 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp3'.1).two_le
  have hlY : 0 < Real.log Y := Real.log_pos hY
  have hc0 : 0 < Real.log p3 / Real.log Y :=
    div_pos (Real.log_pos (by linarith)) hlY
  have hcb : Real.log p3 / Real.log Y < Real.log p2 / Real.log Y :=
    div_lt_div_of_pos_right (Real.log_lt_log (by linarith) hp3'.2.2) hlY
  have hba : Real.log p2 / Real.log Y < Real.log p1 / Real.log Y :=
    div_lt_div_of_pos_right (Real.log_lt_log (by linarith) hp2'.2.2) hlY
  rcases hg with rfl | rfl | rfl | rfl <;> simp only [upperPairRegion] at hG <;>
    simp at hG <;> linarith [hG.1]

/-- LEAF: P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43, for one dyadic box and
one arrangement g of upperPrimeCovered other than the impossible g = 1, 3, 5, 7: the box terms
whose FIRST arrangement in the Lemma 33 region is g. One E for all boxes and arrangements, constant
uniform. Paper: Lemma 33 for g, M and N the two prime groups of g, 3.2 by Lemma 5, L the rest
times n4; removing the cross conditions is implicit. CONDITIONAL on Theorem 4 and Lemma 9. HARD. -/
theorem upK_group8_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ i : ℕ × ℕ × ℕ, ∀ g : Fin 12, g ≠ 1 → g ≠ 3 → g ≠ 5 → g ≠ 7 →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  (fun a b c : ℝ =>
                    upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                    ∀ j < g, ¬ upperPairRegion ε
                      (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                    (Real.log p1 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
            C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
              Real.log x ^ (-A') := by
  sorry

/-- P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43, for one dyadic box of the
kept part of k_m and one arrangement g of the twelve in upperPrimeCovered: the terms whose FIRST
arrangement in the Lemma 33 region is g. One set E for all boxes and arrangements. PROVED from the
LEAF upK_group8_51 for the eight arrangements that occur, and from upK_group_vanish for g = 1, 3,
5, 7, whose pieces are zero. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem upK_group_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ i : ℕ × ℕ × ℕ, ∀ g : Fin 12,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  (fun a b c : ℝ =>
                    upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                    ∀ j < g, ¬ upperPairRegion ε
                      (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                    (Real.log p1 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
            C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
              Real.log x ^ (-A') := by
  obtain ⟨E, hE⟩ := upK_group8_51 h4 h9 hε hε8
  refine ⟨E, fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA A' hA'
  refine ⟨max C 2, fun x hx q hq hqQ => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hcard, hg8⟩ := hC x (le_trans (le_max_left _ _) hx) q hq hqQ
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hLA : 0 ≤ Real.log x ^ (-A') := Real.rpow_nonneg hL0 _
  have hW : 0 ≤ x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 := by
    have := Real.rpow_pos_of_pos hx0 (11 / 20 + ε)
    positivity
  refine ⟨le_trans hcard (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg hL0 _)), fun i g => ?_⟩
  by_cases hg : g = 1 ∨ g = 3 ∨ g = 5 ∨ g = 7
  · have hY : 1 < x ^ (11 / 20 + ε) := Real.one_lt_rpow (by linarith) (by positivity)
    have hv := fun m => upK_group_vanish ε (x ^ (11 / 20 + ε)) hY i g hg m
    simp only [hv, Complex.ofReal_zero, zero_mul, zero_div, Finset.sum_const_zero, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      intervalIntegral.integral_zero, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) hW) hLA
  · push Not at hg
    exact le_trans (hg8 i g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hW) hLA)

/-- P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43, for one dyadic box: the exact
statement of the LEAF upK_box_51 of Prep1122KeptBoxes.lean. PROVED from the LEAF upK_group_51 by
the partition upK_box_groupings into the twelve first arrangements and Cauchy Schwarz
upK_window_cs over them, with constant 144 C. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem upK_box_51_of_groups (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ i : ℕ × ℕ × ℕ,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log (x ^ (11 / 20 + ε))) (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
            C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
              Real.log x ^ (-A') := by
  obtain ⟨E, hE⟩ := upK_group_51 h4 h9 hε hε8
  refine ⟨E, fun A hA A' hA' => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA A' hA'
  refine ⟨max (max C 1) (144 * max C 0), fun x hx q hq hqQ => ?_⟩
  have hxC : C ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hCout : 144 * max C 0 ≤ max (max C 1) (144 * max C 0) := le_max_right _ _
  have hCC : C ≤ max (max C 1) (144 * max C 0) := le_trans (le_max_left _ _) (le_max_left _ _)
  obtain ⟨hcard, hgroup⟩ := hC x hxC q hq hqQ
  have hx0 : 0 < x := by linarith
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hQ1 : 1 ≤ sieveQ ε x := le_trans hq hqQ
  have hqQpos : (0 : ℝ) < (q : ℝ) * (sieveQ ε x : ℝ) := by
    have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h2 : (1 : ℝ) ≤ sieveQ ε x := by exact_mod_cast hQ1
    positivity
  have hT : 0 < x ^ (11 / 20 + ε) / ((q : ℝ) * (sieveQ ε x : ℝ)) := div_pos hY0 hqQpos
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hW : 0 ≤ x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 := by positivity
  have hLA : 0 ≤ Real.log x ^ (-A') := Real.rpow_nonneg hL0 _
  refine ⟨le_trans hcard (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg hL0 _)), fun i => ?_⟩
  have hJ : ∀ m ∈ rightInterval ε x, m ≠ 0 := by
    intro m hm
    have h := Finset.mem_Ioc.mp hm
    omega
  have hrw : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  upperPrimeCovered ε (Real.log p1 / Real.log (x ^ (11 / 20 + ε))) (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
        ∑ m ∈ rightInterval ε x, (∑ g : Fin 12, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  (fun a b c : ℝ =>
                    upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                    ∀ j < g, ¬ upperPairRegion ε
                      (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                    (Real.log p1 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q)) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    intro χ t
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [upK_box_groupings ε (x ^ (11 / 20 + ε)) i m, ← Finset.sum_mul]
    push_cast
    rfl
  calc _ = ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (∑ g : Fin 12, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  (fun a b c : ℝ =>
                    upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                    ∀ j < g, ¬ upperPairRegion ε
                      (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                    (Real.log p1 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q)) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [hrw χ t]
    _ ≤ ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ((Finset.univ : Finset (Fin 12)).card : ℝ) * ∑ g : Fin 12,
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  (fun a b c : ℝ =>
                    upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                    ∀ j < g, ¬ upperPairRegion ε
                      (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                    (Real.log p1 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) :=
        Finset.sum_le_sum fun χ _ => upK_window_cs _ _ hJ _ hT (neg_le_self hY0.le)
    _ = ((Finset.univ : Finset (Fin 12)).card : ℝ) * ∑ g : Fin 12,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
              ‖∑ m ∈ rightInterval ε x, (((∑ p1 ∈ m.primeFactors.filter
            (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC4 ε),
          ∑ p2 ∈ (m / p1 : ℕ).primeFactors.filter
              (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p1 : ℝ)),
            ∑ p3 ∈ (m / p1 / p2 : ℕ).primeFactors.filter
                (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ (p : ℝ) ∧ (p : ℝ) < (p2 : ℝ)),
              if (Nat.log 2 p1, Nat.log 2 p2, Nat.log 2 p3) = i ∧
                  (fun a b c : ℝ =>
                    upperPairRegion ε (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] g)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] g) ∧
                    ∀ j < g, ¬ upperPairRegion ε
                      (![a, b, a, c, b, c, a + b, c, a + c, b, b + c, a] j)
                      (![b, a, c, a, c, b, c, a + b, b, a + c, a, b + c] j))
                    (Real.log p1 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p2 / Real.log (x ^ (11 / 20 + ε)))
                    (Real.log p3 / Real.log (x ^ (11 / 20 + ε)))
                then upperRough (m / p1 / p2 / p3 : ℕ) (p3 : ℝ) else 0) : ℝ) : ℂ) *
                  χ (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((Finset.univ : Finset (Fin 12)).card : ℝ) * ∑ _g : Fin 12,
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hgroup i g) (Nat.cast_nonneg _)
    _ = 144 * C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        push_cast
        ring
    _ ≤ max (max C 1) (144 * max C 0) *
          (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A') := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hW) hLA
        exact le_trans (by linarith [le_max_left C 0]) hCout

end LeanLab.BHP1997.DecompC165d
