/-
DQ7 decisions for BHP1997, Baker Harman Pintz 1997, design queue item DQ7,
run 20261119T0802Z-29270. Source: P0069 pages 22 to 27, 41 and 42.

Part A. Re-cut of `lower_mean_value_supply` of Decomp312a. The old split asked for an
auxiliary family for EVERY sifted family with a divisor bound, and `c0 = 0` refutes that
leaf in Refute_leaf_auxiliary_family_supply. The new cut keeps the sifted family and the
auxiliary family existential together, and moves the analytic content to a separate
universal leaf over an admissibility class `P` of auxiliary families. The combinatorial
leaf asks for `c0` and `b` with `P ε b` and every conjunct of the claim except the mean
value 4.1, and the analytic leaf asks that every admissible family obeys 4.1. The
assembly is proved for every `P`. Taking `P` to be 4.1 itself shows the cut loses
nothing, so neither leaf is false whenever the sealed claim is true. The intended `P`
is the Type I and Type II bilinear class of Lemma 10 and Lemmas 13 to 16.

Part B. Restatement of `upper_mean_value_supply` of Decomp312b as a new sealed Prop
`UpperMeanValueSupplyStrictDQ7` with the density constant strictly between 1 and the
paper's 1.0001, so the reading u1 = 1 is excluded. It implies the sealed statement.
A vacuity instance shows the numeric range is nonempty.

Part C. Route row for `perron_input`. The Decomp132b copy is a sealed duplicate of
DecompC165a.perron_input. The names `DecompC165a.all_character_fourth_moment` and
`DecompC165a.Contour230.horizontal_convexity_input` exist. Match theorems check them,
and `perron_input_of_fourth_moment_dq7` proves the perron_input statement from the
fourth moment as an explicit argument, through the sealed contour step, which still
uses the horizontal convexity leaf internally.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312b
import LeanLab.BHP1997.DecompC165a

namespace LeanLab.BHP1997.DQ7
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132

/-! ## Part A. Re-cut of the lower supply -/

/-- The conclusion of the sealed `Decomp312a.lower_mean_value_supply`, P0069 pages 24
to 41. Plain math: there are B0, η such that for small ε a density u0 in (0.9953, 1],
a sifted family below the primes on I and an auxiliary family with 4.1, the I1 density
u0 over log x and small L1 distance on I exist. -/
def LowerSupplyDQ7 : Prop :=
  ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∃ (u0 : ℝ) (c0 b : ℝ → ℕ → ℝ),
      0.9953 < u0 ∧ u0 ≤ 1 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u0 b ∧
      ShortApproximation ε (section4SiftedFamily c0) b ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k

/-- Match check: the sealed claim concludes exactly `LowerSupplyDQ7`. Depends on the
sealed open leaf and only checks the match. -/
theorem lower_supply_match_dq7 (h4 : Thm4.Theorem4Paper) : LowerSupplyDQ7 :=
  lower_mean_value_supply h4

/-- New LEAF A, the combinatorial step, P0069 pages 26 to 41, for an admissibility
class `P`. Plain math: a sifted family below the primes on I and an admissible
auxiliary family with the I1 density and small L1 distance on I, without 4.1. -/
def LowerCombinatorialDQ7 (P : ℝ → (ℝ → ℕ → ℝ) → Prop) : Prop :=
  ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∃ (u0 : ℝ) (c0 b : ℝ → ℕ → ℝ),
      0.9953 < u0 ∧ u0 ≤ 1 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      P ε b ∧ ReferenceDensity u0 b ∧
      ShortApproximation ε (section4SiftedFamily c0) b ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k

/-- New LEAF B, the analytic step, P0069 pages 23 to 27, Lemma 10 with display 4.1.
Plain math: every admissible family satisfies the mean value 4.1. -/
def LowerAnalyticDQ7 (P : ℝ → (ℝ → ℕ → ℝ) → Prop) : Prop :=
  ∀ (ε : ℝ) (b : ℝ → ℕ → ℝ), 0 < ε → P ε b → MeanValue41 ε b

/-- The re-cut assembly, proved for every admissibility class. -/
theorem lower_supply_of_cut_dq7 (P : ℝ → (ℝ → ℕ → ℝ) → Prop)
    (hA : LowerCombinatorialDQ7 P) (hB : LowerAnalyticDQ7 P) : LowerSupplyDQ7 := by
  obtain ⟨B0, η, hB0, hη, h⟩ := hA
  refine ⟨B0, η, hB0, hη, fun ε hε hεη => ?_⟩
  obtain ⟨u0, c0, b, hu, hu1, hc, hb, hP, hd, happ, hlo⟩ := h ε hε hεη
  exact ⟨u0, c0, b, hu, hu1, hc, hb, hB ε b hε hP, hd, happ, hlo⟩

/-- The cut loses nothing: with `P` the mean value 4.1 itself, both leaves follow from
the claim, the analytic one trivially. So the cut is never false where the claim holds,
unlike the refuted universal auxiliary leaf. -/
theorem lower_cut_complete_dq7 (h : LowerSupplyDQ7) :
    LowerCombinatorialDQ7 (fun ε b => MeanValue41 ε b) ∧
      LowerAnalyticDQ7 (fun ε b => MeanValue41 ε b) :=
  ⟨h, fun _ _ _ hb => hb⟩

/-! ## Part B. Strict restatement of the upper supply -/

/-- New sealed Prop, P0069 pages 41 and 42, Lemma 28 and the density computation of
page 42. Plain math: there are B0, η such that for small ε a density u1 with
1 < u1 < 1.0001, a sifted family above the primes on I and an auxiliary family with
4.1, the I1 density u1 over log x and small L1 distance on I exist. -/
def UpperMeanValueSupplyStrictDQ7 : Prop :=
  ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
      1 < u1 ∧ u1 < 1.0001 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
      ShortApproximation ε (section4SiftedFamily c1) b ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k

/-- The strict restatement implies the conclusion of the sealed
`Decomp312b.upper_mean_value_supply`. -/
theorem upper_supply_of_strict_dq7 (h : UpperMeanValueSupplyStrictDQ7) :
    ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k := by
  obtain ⟨B0, η, hB0, hη, h⟩ := h
  refine ⟨B0, η, hB0, hη, fun ε hε hεη => ?_⟩
  obtain ⟨u, c, b, hu, hu1, rest⟩ := h ε hε hεη
  exact ⟨u, c, b, hu.le, hu1, rest⟩

/-- Vacuity instance: the numeric constraints of the restatement are satisfiable,
with B0 = 1, η = 1/10 and u1 = 1.00005. -/
theorem upper_strict_constants_nonempty_dq7 :
    ∃ B0 η u1 : ℝ, 0 < B0 ∧ 0 < η ∧ 1 < u1 ∧ u1 < 1.0001 :=
  ⟨1, 1 / 10, 1.00005, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Part C. The perron_input route row -/

/-- Named hypothesis, P0069 page 22, Lemma 7, Ramachandra reference 26. CITED. -/
def AllCharacterFourthMomentDQ7 : Prop := MeanValue132.Lemma7

/-- Named hypothesis, P0069 page 22, Lemma 8 at ε equal to one over log x. CITED.
Plain math: |L(1/2 + σ + iτ, χ)| ≤ C log x ((q(|τ|+1))^(1/2 + 1/log x - σ) + 1). -/
def HorizontalConvexityDQ7 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
    ∀ χ : DirichletCharacter ℂ q, ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 + 1 / Real.log x →
      1 / 4 ≤ |τ| → |τ| ≤ 2 * x →
      ‖χ.LFunction (((1 / 2 + σ : ℝ) : ℂ) + τ * I)‖ ≤
        C * Real.log x *
          (((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) + 1)

/-- Match check for `DecompC165a.all_character_fourth_moment`. -/
theorem fourth_moment_match_dq7 : AllCharacterFourthMomentDQ7 :=
  DecompC165a.all_character_fourth_moment

/-- Match check for `DecompC165a.Contour230.horizontal_convexity_input`. -/
theorem horizontal_match_dq7 : HorizontalConvexityDQ7 :=
  DecompC165a.Contour230.horizontal_convexity_input

/-- The perron_input statement of pages 22 and 23, from the fourth moment as an
explicit argument. Same proof as DecompC165a.perron_input. The contour step
`contour_holder rademacher_strip_bound` is sealed and still uses its own open leaves,
so this is CONDITIONAL on those too. -/
theorem perron_input_of_fourth_moment_dq7 (h7 : AllCharacterFourthMomentDQ7) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x N T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        ∃ J : ℝ × DirichletCharacter ℂ q → ℂ,
          (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C * ((q : ℝ) * T * Real.log x ^ B) ∧
          ∀ p ∈ S, ‖MeanValue132.partialSum N p.2 p.1‖ ≤ ‖J p‖ +
            C * Real.log x * (Real.sqrt q / Real.sqrt T) +
            C * Real.log x * (Real.sqrt N / T) +
            C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) := by
  obtain ⟨C0, hC0, hcontour⟩ :=
    DecompC165a.contour_holder DecompC165a.rademacher_strip_bound
  obtain ⟨B, C1, hB, hC1, hmoment⟩ := DecompC165a.spaced_weighted_moment h7
  let C := max C0 (C0 * C1)
  have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  refine ⟨B + 3, C, by linarith, hC, ?_⟩
  intro x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨J, hJ, hpoint⟩ := hcontour x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  refine ⟨J, ?_, ?_⟩
  · have hW := hmoment x T q S hx hT hTx hq hqx hspace htimes
    have hprod : Real.log x ^ (3 : ℝ) * Real.log x ^ B = Real.log x ^ (B + 3) := by
      rw [← Real.rpow_add hlog]
      congr 1
      ring
    calc
      (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C0 * Real.log x ^ (3 : ℝ) *
          DecompC165a.weightedMoment T S := hJ
      _ ≤ C0 * Real.log x ^ (3 : ℝ) * (C1 * ((q : ℝ) * T * Real.log x ^ B)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (C0 * C1) * ((q : ℝ) * T * Real.log x ^ (B + 3)) := by
        calc
          _ = (C0 * C1) * ((q : ℝ) * T *
              (Real.log x ^ (3 : ℝ) * Real.log x ^ B)) := by ring
          _ = _ := by rw [hprod]
      _ ≤ C * ((q : ℝ) * T * Real.log x ^ (B + 3)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · intro p hp
    have h0 : C0 ≤ C := le_max_left _ _
    have h1 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt q / Real.sqrt T) by positivity)
    have h2 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt N / T) by positivity)
    have h3 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) by
        split_ifs <;> positivity)
    have hpbound := hpoint p hp
    simp only [mul_assoc] at hpbound ⊢
    by_cases hχ : p.2 = 1
    · simp only [hχ, ite_true] at hpbound h3 ⊢
      exact hpbound.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)
    · simp only [hχ, ite_false] at hpbound h3 ⊢
      exact hpbound.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)

/-- The Decomp132b copy and the DecompC165a theorem state the same Prop. -/
theorem perron_input_duplicate_dq7 :
    (type_of% @Decomp132b.perron_input) = (type_of% @DecompC165a.perron_input) := rfl

end LeanLab.BHP1997.DQ7
