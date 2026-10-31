import Mathlib

/-!
P0098 Granville 2007 Theorem 2, page 162, and Proposition 3.1, pages 165 to 167.
The random selection step remains cited. The finite repair and theorem reduction are elementary.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp124
open Finset Set MeasureTheory
open Classical

/-- Ordered prime representations, the function g on P0098 pages 159 and 165. -/
def primePairs (n : ℕ) : ℕ :=
  ((range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (n - p)).card

/-- The counting function P x on P0098 pages 162 and 167. -/
def count (P : Set ℕ) (x : ℝ) : ℕ :=
  ((range (⌊x⌋₊ + 1)).filter fun p => p ∈ P).card

/-- N gamma in Proposition 3.1, page 165, written with the even integer n as variable. -/
def richEven (γ : ℝ) : Set ℕ :=
  {n | Even n ∧ 2 < n ∧ 2 * γ * n / Real.log n ^ 2 < primePairs n}

/-- CITED. P0098 Theorem 2, page 162. The implicit lower range is x at least two.
The even integers to be represented are greater than two, as in its hypothesis. -/
def GranvilleTheorem2 : Prop :=
  (∃ γ : ℝ, 0 < γ ∧ ∀ n : ℕ, Even n → 2 < n →
    γ * n / Real.log n ^ 2 < primePairs n) →
  ∃ (η : ℝ) (P : Set ℕ), 0 < η ∧ P.Infinite ∧
    (∀ p ∈ P, Nat.Prime p) ∧
    (∀ x : ℝ, 2 ≤ x → (count P x : ℝ) ≤ η * Real.sqrt (x * Real.log x)) ∧
    ∀ n : ℕ, Even n → 2 < n → ∃ p ∈ P, ∃ q ∈ P, p + q = n

/-- The random prime subset defined by the prime selectors on P0098 page 166. -/
def coinSet (ω : ℕ → Bool) : Set ℕ := {p | Nat.Prime p ∧ ω p = true}

/-- LEAF. P0098 pages 166 and 167, eq. 3.3 and the bound for W x.
The independent prime sampling construction supplies a probability measure with summable
failure probabilities and almost surely an infinite subset satisfying the sparse bound.
The source uses the standard Chernoff bound and the prime number theorem.
The simultaneous conclusion over all cutoffs is included explicitly in this cited leaf. -/
theorem random_model (γ : ℝ) (hγ : 0 < γ) :
    ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (∀ᵐ ω ∂μ, (coinSet ω).Infinite ∧ ∃ η : ℝ, 0 < η ∧
        ∀ x : ℝ, 2 ≤ x → (count (coinSet ω) x : ℝ) ≤
          η * Real.sqrt (x * Real.log x)) ∧
      (∑' n : ℕ, μ {ω | n ∈ richEven γ ∧
        ¬ ∃ p ∈ coinSet ω, ∃ q ∈ coinSet ω, p + q = n}) ≠ ⊤ := by
  sorry

/-- LEAF. P0098 page 166, the summable failure probabilities give finitely many exceptions.
This is the Borel Cantelli selection step with the simultaneous sparse event.
CONDITIONAL ON random_model. -/
theorem sparse_almost_cover (γ : ℝ) (hγ : 0 < γ) :
    ∃ (η : ℝ) (P : Set ℕ) (E : Finset ℕ), 0 < η ∧ P.Infinite ∧
      (∀ p ∈ P, Nat.Prime p) ∧
      (∀ x : ℝ, 2 ≤ x → (count P x : ℝ) ≤ η * Real.sqrt (x * Real.log x)) ∧
      ∀ n ∈ richEven γ, n ∉ E → ∃ p ∈ P, ∃ q ∈ P, p + q = n := by
  obtain ⟨μ, hμ, hgood, hsum⟩ := random_model γ hγ
  letI : IsProbabilityMeasure μ := hμ
  have hf := ae_finite_setOfPred_mem hsum
  obtain ⟨ω, hω, hωf⟩ := (hgood.and hf).exists
  obtain ⟨hωi, η, hη, hb⟩ := hω
  refine ⟨η, coinSet ω, hωf.toFinset, hη, hωi, fun p hp => hp.1, hb, ?_⟩
  intro n hn hne
  by_contra hnot
  apply hne
  exact hωf.mem_toFinset.mpr ⟨hn, hnot⟩

/-- LEAF. P0098 page 166, the last paragraph. A rich even integer has a prime pair. -/
theorem rich_has_pair {γ : ℝ} (hγ : 0 < γ) {n : ℕ} (hn : n ∈ richEven γ) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  have hnonneg : 0 ≤ 2 * γ * (n : ℝ) / Real.log n ^ 2 := by positivity
  have hpos : 0 < primePairs n := by
    exact_mod_cast lt_of_le_of_lt hnonneg hn.2.2
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  obtain ⟨hpn, hpp, hpq⟩ := mem_filter.mp hp
  have hle : p ≤ n := by have := mem_range.mp hpn; omega
  exact ⟨p, n - p, hpp, hpq, by omega⟩

/-- LEAF. P0098 pages 166 and 167, finite repair of the missed integers.
For a finite collection of representable integers a finite prime set contains a pair for each. -/
theorem finite_patch (E : Finset ℕ)
    (hE : ∀ n ∈ E, ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) :
    ∃ F : Finset ℕ, (∀ p ∈ F, Nat.Prime p) ∧
      ∀ n ∈ E, ∃ p ∈ F, ∃ q ∈ F, p + q = n := by
  choose p q hp hq heq using hE
  let F : Finset ℕ := E.attach.biUnion (fun n => {p n n.property, q n n.property})
  refine ⟨F, ?_, ?_⟩
  · intro r hr
    obtain ⟨n, _, hr⟩ := mem_biUnion.mp hr
    rcases mem_insert.mp hr with hr | hr
    · rw [hr]; exact hp n n.property
    · have hr' := mem_singleton.mp hr
      rw [hr']; exact hq n n.property
  · intro n hn
    refine ⟨p n hn, ?_, q n hn, ?_, heq n hn⟩
    · exact mem_biUnion.mpr ⟨⟨n, hn⟩, mem_attach _ _, by simp⟩
    · exact mem_biUnion.mpr ⟨⟨n, hn⟩, mem_attach _ _, by simp⟩

/-- LEAF. P0098 page 167, P prime differs from P by finitely many primes.
Adding a finite set preserves the square root x log x upper bound with a larger constant. -/
theorem count_finite_extension (P : Set ℕ) (F : Finset ℕ) (η : ℝ)
    (hb : ∀ x : ℝ, 2 ≤ x → (count P x : ℝ) ≤ η * Real.sqrt (x * Real.log x)) :
    ∀ x : ℝ, 2 ≤ x → (count (P ∪ (F : Set ℕ)) x : ℝ) ≤
      (η + F.card) * Real.sqrt (x * Real.log x) := by
  intro x hx
  have hl : (1 : ℝ) / 2 ≤ Real.log x := by
    have h2 := Real.log_two_gt_d9
    have hx2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hs : 1 ≤ Real.sqrt (x * Real.log x) :=
    Real.one_le_sqrt.mpr (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hl)])
  have hc : count (P ∪ (F : Set ℕ)) x ≤ count P x + F.card := by
    unfold count
    simp only [Set.mem_union, Finset.filter_or]
    have hcard : ((Finset.range (⌊x⌋₊ + 1)).filter
        (fun p => p ∈ (F : Set ℕ))).card ≤ F.card := by
      apply Finset.card_le_card
      intro p hp
      exact (mem_filter.mp hp).2
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hcard _)
  have hcr : (count (P ∪ (F : Set ℕ)) x : ℝ) ≤ (count P x : ℝ) + F.card :=
    by exact_mod_cast hc
  have hf : (F.card : ℝ) ≤ F.card * Real.sqrt (x * Real.log x) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hs
  nlinarith [hb x hx]

/-- Proposition 3.1 on page 165 assembled from the random sample and the finite repair.
CONDITIONAL ON sparse_almost_cover. No sorry occurs in the assembly. -/
theorem proposition31_assembled (γ : ℝ) (hγ : 0 < γ) :
    ∃ (η : ℝ) (P : Set ℕ), 0 < η ∧ P.Infinite ∧
      (∀ p ∈ P, Nat.Prime p) ∧
      (∀ x : ℝ, 2 ≤ x → (count P x : ℝ) ≤ η * Real.sqrt (x * Real.log x)) ∧
      ∀ n ∈ richEven γ, ∃ p ∈ P, ∃ q ∈ P, p + q = n := by
  obtain ⟨η, P, E, hη, hPi, hPp, hPb, hPc⟩ := sparse_almost_cover γ hγ
  let E' := E.filter (fun n => n ∈ richEven γ)
  have hE' : ∀ n ∈ E', ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
    intro n hn
    exact rich_has_pair hγ (mem_filter.mp hn).2
  obtain ⟨F, hFp, hFc⟩ := finite_patch E' hE'
  refine ⟨η + F.card, P ∪ (F : Set ℕ), by positivity,
    hPi.mono Set.subset_union_left, ?_, count_finite_extension P F η hPb, ?_⟩
  · intro p hp
    rcases hp with hp | hp
    · exact hPp p hp
    · exact hFp p hp
  · intro n hn
    by_cases he : n ∈ E
    · obtain ⟨p, hp, q, hq, heq⟩ := hFc n (mem_filter.mpr ⟨he, hn⟩)
      exact ⟨p, Or.inr hp, q, Or.inr hq, heq⟩
    · obtain ⟨p, hp, q, hq, heq⟩ := hPc n hn he
      exact ⟨p, Or.inl hp, q, Or.inl hq, heq⟩

/-- Theorem 2, page 162, with exactly the cited proposition as its type.
CONDITIONAL ON the cited random selection leaf. No sorry occurs in the assembly. -/
theorem granville_theorem2_assembled : GranvilleTheorem2 := by
  rintro ⟨γ, hγ, hcount⟩
  obtain ⟨η, P, hη, hPi, hPp, hPb, hPc⟩ :=
    proposition31_assembled (γ / 2) (by positivity)
  refine ⟨η, P, hη, hPi, hPp, hPb, fun n hn hn2 => hPc n ?_⟩
  refine ⟨hn, hn2, ?_⟩
  convert hcount n hn hn2 using 1 <;> ring

end LeanLab.GoldbachAverage.Decomp124
