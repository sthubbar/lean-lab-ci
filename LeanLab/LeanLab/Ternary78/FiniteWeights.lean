import LeanLab.Ternary78.BennettLower

/-
AI wrote this Lean code. Binary Goldbach is open.
Elementary finite sum accounting for the Bennett lower bound.
No zero-free hypothesis or gamma estimate is used.
-/

namespace LeanLab.Ternary78.Bennett

/-- Finite nested sets convert count increments to lower bounds for weights. -/
theorem weightedCount_card_le_sum {ι : Type*} [DecidableEq ι]
    (s : ℕ → Finset ι) (w : ι → ℝ) (f : ℕ → ℝ)
    (hs0 : s 0 = ∅) (hs : ∀ i, s i ⊆ s (i + 1))
    (hw : ∀ i a, a ∈ s (i + 1) \ s i → f (i + 1) ≤ w a) (k : ℕ) :
    weightedCount (fun i => ((s i).card : ℝ)) f k ≤ ∑ a ∈ s k, w a := by
  induction k with
  | zero => simp [weightedCount, hs0]
  | succ k ih =>
    have hcard : ((s (k + 1)).card : ℝ) - (s k).card =
        ((s (k + 1) \ s k).card : ℝ) := (Finset.cast_card_sdiff (hs k)).symm
    have hinc : (((s (k + 1)).card : ℝ) - (s k).card) * f (k + 1) ≤
        ∑ a ∈ s (k + 1) \ s k, w a := by
      rw [hcard]
      calc ((s (k + 1) \ s k).card : ℝ) * f (k + 1) =
          ∑ _a ∈ s (k + 1) \ s k, f (k + 1) := by simp
        _ ≤ ∑ a ∈ s (k + 1) \ s k, w a := Finset.sum_le_sum (fun a ha => hw k a ha)
    change (∑ i ∈ Finset.range (k + 1), _) ≤ _
    rw [Finset.sum_range_succ]
    calc weightedCount (fun i => ((s i).card : ℝ)) f k +
          (((s (k + 1)).card : ℝ) - (s k).card) * f (k + 1) ≤
          (∑ a ∈ s k, w a) + ∑ a ∈ s (k + 1) \ s k, w a := add_le_add ih hinc
      _ = ∑ a ∈ s (k + 1), w a := by
        rw [add_comm, Finset.sum_sdiff (hs k)]

/-- Nonvacuity with a nonempty shell and positive weight. -/
example : weightedCount (fun i => if i = 0 then 0 else 1) (fun _ => 2) 1 ≤
    ∑ _a ∈ ({0} : Finset ℕ), (2 : ℝ) := by
  norm_num [weightedCount]

#print axioms weightedCount_card_le_sum

/-- Indices in z encode zeros with multiplicity. The initial set is empty. -/
noncomputable def heightSet {ι : Type*} [DecidableEq ι] (z : Finset ι)
    (γ : ι → ℝ) (t : ℕ → ℝ) (i : ℕ) : Finset ι := by
  classical
  exact if i = 0 then ∅ else z.filter (fun a => |γ a| ≤ t i)

/-- Increasing heights give nested finite zero sets, including the empty anchor. -/
theorem heightSet_mono {ι : Type*} [DecidableEq ι] (z : Finset ι)
    (γ : ι → ℝ) (t : ℕ → ℝ) (ht : Monotone t) (i : ℕ) :
    heightSet z γ t i ⊆ heightSet z γ t (i + 1) := by
  classical
  by_cases hi : i = 0
  · simp [heightSet, hi]
  · simp only [heightSet, hi, Nat.add_one_ne_zero, ite_false]
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.trans (ht (Nat.le_succ i))⟩

#print axioms heightSet_mono

/-- CONDITIONAL ON BennettThm1_1. Count agreement is required only through k.
The finite indices represent the zeros in that height range, with multiplicity. -/
theorem finite_weighted_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (z : Finset ι) (γ w : ι → ℝ)
    (t f : ℕ → ℝ) (ht : Monotone t)
    (hf : ∀ i, f (i + 1) ≤ f i) (hf0 : ∀ i, 0 ≤ f i) (k : ℕ)
    (hcount : ∀ i, 0 < i → i ≤ k →
      N q χ (t i) = (heightSet z γ t i).card)
    (hw : ∀ i a, 0 < i → a ∈ z → |γ a| ≤ t i → f i ≤ w a) :
    weightedCount (gridLower χ t) f k ≤ ∑ a ∈ heightSet z γ t k, w a := by
  classical
  have heq (i : ℕ) (hi : i ≤ k) :
      gridCount N χ t i = ((heightSet z γ t i).card : ℝ) := by
    by_cases hi0 : i = 0
    · simp [gridCount, heightSet, hi0]
    · simp only [gridCount, hi0, ite_false]
      rw [hcount i (Nat.pos_of_ne_zero hi0) hi]
  have hsum : weightedCount (gridCount N χ t) f k =
      weightedCount (fun i => ((heightSet z γ t i).card : ℝ)) f k := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    rw [heq (i + 1) (by omega), heq i (by omega)]
  calc weightedCount (gridLower χ t) f k ≤ weightedCount (gridCount N χ t) f k :=
      weightedCount_lower_of_bennett hB hq hq1 χ hχ t f hf hf0 k
    _ = weightedCount (fun i => ((heightSet z γ t i).card : ℝ)) f k := hsum
    _ ≤ ∑ a ∈ heightSet z γ t k, w a := by
      apply weightedCount_card_le_sum
      · simp [heightSet]
      · exact heightSet_mono z γ t ht
      · intro i a ha
        have ha' := (Finset.mem_sdiff.mp ha).1
        simp only [heightSet, Nat.add_one_ne_zero, ite_false, Finset.mem_filter] at ha'
        exact hw (i + 1) a (by omega) ha'.1 ha'.2

#print axioms finite_weighted_lower_of_bennett

/-- CONDITIONAL ON BennettThm1_1. A decreasing nonnegative height weight supplies
all weight hypotheses of the finite bridge. This is not a gamma monotonicity claim. -/
theorem height_weighted_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (z : Finset ι) (γ : ι → ℝ)
    (t : ℕ → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i)
    (g : ℝ → ℝ) (hg : AntitoneOn g (Set.Ici 0))
    (hg0 : ∀ u, 0 ≤ u → 0 ≤ g u) (k : ℕ)
    (hcount : ∀ i, 0 < i → i ≤ k →
      N q χ (t i) = (heightSet z γ t i).card) :
    weightedCount (gridLower χ t) (fun i => g (t i)) k ≤
      ∑ a ∈ heightSet z γ t k, g |γ a| := by
  apply finite_weighted_lower_of_bennett hB hq hq1 χ hχ z γ
    (fun a => g |γ a|) t (fun i => g (t i)) ht
  · intro i
    exact hg (ht0 i) (ht0 (i + 1)) (ht (Nat.le_succ i))
  · exact fun i => hg0 (t i) (ht0 i)
  · exact hcount
  · intro i a _ _ ha
    exact hg (show |γ a| ∈ Set.Ici (0 : ℝ) from abs_nonneg (γ a)) (ht0 i) ha

/-- A positive antitone weight and increasing nonnegative grid. -/
example : AntitoneOn (fun _ : ℝ => (1 : ℝ)) (Set.Ici 0) ∧
    Monotone (fun i : ℕ => (i : ℝ)) ∧ (∀ i : ℕ, (0 : ℝ) ≤ (i : ℝ)) := by
  exact ⟨fun _ _ _ _ _ => le_rfl, fun _ _ h => Nat.cast_le.mpr h, Nat.cast_nonneg⟩

#print axioms height_weighted_lower_of_bennett

end LeanLab.Ternary78.Bennett
