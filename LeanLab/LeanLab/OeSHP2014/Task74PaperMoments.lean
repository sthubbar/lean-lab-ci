import LeanLab.OeSHP2014.Task74Moments

/-! The prime gap moment definition and conjecture in section 2.3, pages 2056 and 2057.
The conjecture below is stated only for positive integer orders and integer cutoffs.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- Consecutive prime pairs with their upper endpoint at most x. -/
def primeGapPairs (x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (x + 1)).product (Finset.range (x + 1))).filter fun r =>
    r.1.Prime ∧ r.2.Prime ∧ r.1 < r.2 ∧ ∀ n ∈ Finset.Ioo r.1 r.2, ¬ n.Prime

/-- The paper's unnormalized kth moment at an integer cutoff. -/
def paperMomentNat (k x : ℕ) : ℕ :=
  ∑ r ∈ primeGapPairs x, (r.2 - r.1)^k

/-- The integer order and integer cutoff form of the conjecture after Table 12. -/
def NaturalMomentConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → Asymptotics.IsEquivalent Filter.atTop
    (fun x : ℕ => (paperMomentNat k x : ℝ))
    (fun x : ℕ => (Nat.factorial k : ℝ) * x * Real.log (x : ℝ)^(k - 1))

/-- A concrete check of the moment definition, not a range extension. -/
theorem paperMomentNat_ten :
    paperMomentNat 1 10 = 5 ∧ paperMomentNat 2 10 = 9 ∧
    paperMomentNat 3 10 = 17 ∧ paperMomentNat 4 10 = 33 := by
  decide +kernel

/-- Both adjacent moment inequalities hold for the actual finite prime gap moments. -/
theorem paperMomentNat_cauchy (x : ℕ) :
    (paperMomentNat 2 x : ℝ)^2 ≤ (paperMomentNat 1 x : ℝ) * paperMomentNat 3 x ∧
    (paperMomentNat 3 x : ℝ)^2 ≤ (paperMomentNat 2 x : ℝ) * paperMomentNat 4 x := by
  let g : ℕ × ℕ → ℝ := fun r => (r.2 - r.1 : ℕ)
  constructor
  · simpa [gapMoment, paperMomentNat, g] using
      moment2_sq_le_moment1_mul_moment3 (primeGapPairs x) g
        (by intro i hi; exact Nat.cast_nonneg _)
  · simpa [gapMoment, paperMomentNat, g] using
      moment3_sq_le_moment2_mul_moment4 (primeGapPairs x) g

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.paperMomentNat_ten

#print axioms LeanLab.OeSHP2014.Task74.paperMomentNat_cauchy
