/-
P0069 Baker Harman Pintz 1997, page 53 with Lemma 33 on page 48 and display 5.1 on page 43.
Burst S129 burst-20261122, wave 13, step kept51-p3, on the LEAF upK_group8_51 of
Prep1122KeptGroupings.lean, which is on main.

The leaf upK_group8_51 asks for ONE exceptional set E of characters serving all eight first
arrangements g = 0, 2, 4, 6, 8, 9, 10, 11 at once. In the paper, page 53, Lemma 33 is applied to
each arrangement separately, and each application calls Theorem 4 with its own exceptional set,
of size at most C q^(1/2) L^(-2A). This file cuts that one step off: the new LEAF upK_one_group_51
is display 5.1 for ONE fixed arrangement g, with an exceptional set allowed to depend on g. The
union of the eight sets is the common set, of size at most eight times the bound, and the
character sum outside the union is at most the sum outside each set since every term is a
nonnegative integral. upK_group8_51_split, with the identical statement of upK_group8_51, is
PROVED from the new LEAF through the abstract union step upK_union_exc, which is PROVED.

New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122KeptGroupings

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- Page 53, the union of the exceptional sets of the separate Lemma 33 applications, in
abstract form. For a finite family of arrangements g with V g, each with its own exceptional set
F g of size at most C_g K and its own bound C_g R for a sum of nonnegative terms over the
characters outside F g, the union of the F g serves all g at once, with one constant. PROVED. -/
theorem upK_union_exc {ι : Type} [Fintype ι] (V : ι → Prop) [DecidablePred V]
    (Q : ℝ → ℕ) (K : ℝ → ℝ → ℕ → ℝ) (R : ℝ → ℝ → ℕ → ℝ)
    (Φ : ι → ℕ × ℕ × ℕ → ℝ → (q : ℕ) → DirichletCharacter ℂ q → ℝ)
    (hK : ∀ A x q, 1 ≤ x → 0 ≤ K A x q) (hR : ∀ A' x q, 1 ≤ x → 0 ≤ R A' x q)
    (hΦ : ∀ g i x q χ, 1 ≤ x → 0 ≤ Φ g i x q χ)
    (h : ∀ g, V g → ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ Q x → ((E A x q).card : ℝ) ≤ C * K A x q ∧
        ∀ i : ℕ × ℕ × ℕ,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            Φ g i x q χ ≤ C * R A' x q) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ Q x → ((E A x q).card : ℝ) ≤ C * K A x q ∧
        ∀ i : ℕ × ℕ × ℕ, ∀ g, V g →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            Φ g i x q χ ≤ C * R A' x q := by
  have h' : ∀ g, ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q), V g →
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ Q x → ((E A x q).card : ℝ) ≤ C * K A x q ∧
        ∀ i : ℕ × ℕ × ℕ,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
            Φ g i x q χ ≤ C * R A' x q := by
    intro g
    by_cases hg : V g
    · obtain ⟨E, hE⟩ := h g hg
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ _ => ∅, fun h' => absurd h' hg⟩
  choose F hF using h'
  refine ⟨fun A x q => (Finset.univ.filter V).biUnion fun g => F g A x q,
    fun A hA A' hA' => ?_⟩
  have hC : ∀ g, ∃ C : ℝ, V g → ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ Q x → ((F g A x q).card : ℝ) ≤ C * K A x q ∧
        ∀ i : ℕ × ℕ × ℕ,
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ F g A x q).filter (· ≠ 1),
            Φ g i x q χ ≤ C * R A' x q := by
    intro g
    by_cases hg : V g
    · obtain ⟨C, hC⟩ := hF g hg A hA A' hA'
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => absurd h' hg⟩
  choose Cg hCg using hC
  refine ⟨1 + ∑ g, |Cg g|, fun x hx q hq hqQ => ?_⟩
  have hS0 : 0 ≤ ∑ g, |Cg g| := Finset.sum_nonneg fun g _ => abs_nonneg _
  have hle : ∀ g, Cg g ≤ 1 + ∑ g, |Cg g| := fun g =>
    le_trans (le_abs_self _) (le_trans
      (Finset.single_le_sum (f := fun g => |Cg g|) (fun g _ => abs_nonneg _) (Finset.mem_univ g))
      (by linarith))
  have hx1 : 1 ≤ x := le_trans (by linarith) hx
  have hK0 := hK A x q hx1
  have hR0 := hR A' x q hx1
  constructor
  · calc (((Finset.univ.filter V).biUnion fun g => F g A x q).card : ℝ)
        ≤ ∑ g ∈ Finset.univ.filter V, ((F g A x q).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ g ∈ Finset.univ.filter V, |Cg g| * K A x q := by
          refine Finset.sum_le_sum fun g hg => ?_
          have hgV := (Finset.mem_filter.mp hg).2
          exact le_trans ((hCg g hgV x (le_trans (hle g) hx) q hq hqQ).1)
            (mul_le_mul_of_nonneg_right (le_abs_self _) hK0)
      _ ≤ ∑ g, |Cg g| * K A x q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun g _ _ => mul_nonneg (abs_nonneg _) hK0
      _ = (∑ g, |Cg g|) * K A x q := by rw [Finset.sum_mul]
      _ ≤ (1 + ∑ g, |Cg g|) * K A x q := mul_le_mul_of_nonneg_right (by linarith) hK0
  · intro i g hg
    have hgo := (hCg g hg x (le_trans (hle g) hx) q hq hqQ).2 i
    refine le_trans ?_ (le_trans hgo (mul_le_mul_of_nonneg_right (hle g) hR0))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun χ _ _ => hΦ g i x q χ hx1
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_biUnion, not_exists, not_and] at hχ ⊢
    exact ⟨fun h' => hχ.1 g hg h', hχ.2⟩

/-- LEAF: P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43: ONE application of
Lemma 33 to ONE fixed first arrangement g of upperPrimeCovered, g not one of the impossible
1, 3, 5, 7, on every dyadic box, with an exceptional set E that may depend on g. Paper: M and N
the two prime groups of g, 3.2 for them by Lemma 5, L the rest times n4, Theorem 4 for the
exceptional characters; removing the cross conditions is implicit. CONDITIONAL on Theorem 4 and
Lemma 9. HARD. -/
theorem upK_one_group_51 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (g : Fin 12) (hg1 : g ≠ 1) (hg3 : g ≠ 3) (hg5 : g ≠ 5) (hg7 : g ≠ 7)
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

/-- P0069 page 53 with Lemma 33 on page 48, display 5.1 on page 43: the exact statement of the
LEAF upK_group8_51 of Prep1122KeptGroupings.lean. PROVED from the LEAF upK_one_group_51, one per
arrangement, by the union step upK_union_exc. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem upK_group8_51_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
  have key := upK_union_exc (fun g : Fin 12 => g ≠ 1 ∧ g ≠ 3 ∧ g ≠ 5 ∧ g ≠ 7) (sieveQ ε)
    (fun A x q => (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A))
    (fun A' x q => (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
      Real.log x ^ (-A'))
    (fun g i x q χ =>
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
                ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2))
    ?_ ?_ ?_
    (fun g hg => ?_)
  · obtain ⟨E, hE⟩ := key
    refine ⟨E, fun A hA A' hA' => ?_⟩
    obtain ⟨C, hC⟩ := hE A hA A' hA'
    refine ⟨C, fun x hx q hq hqQ => ?_⟩
    obtain ⟨h1, h2⟩ := hC x hx q hq hqQ
    refine ⟨by simpa only [mul_assoc] using h1, fun i g hg1 hg3 hg5 hg7 => ?_⟩
    simpa only [mul_assoc] using h2 i g ⟨hg1, hg3, hg5, hg7⟩
  · intro A x q hx
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Real.log_nonneg hx) _)
  · intro A' x q hx
    have hx0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx) _)
  · intro g i x q χ hx
    have hx0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    refine intervalIntegral.integral_nonneg (by linarith) fun t _ => ?_
    positivity
  · obtain ⟨E, hE⟩ := upK_one_group_51 h4 h9 g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 hε hε8
    refine ⟨E, fun A hA A' hA' => ?_⟩
    obtain ⟨C, hC⟩ := hE A hA A' hA'
    refine ⟨C, fun x hx q hq hqQ => ?_⟩
    obtain ⟨h1, h2⟩ := hC x hx q hq hqQ
    exact ⟨by simpa only [mul_assoc] using h1, fun i => by simpa only [mul_assoc] using h2 i⟩
