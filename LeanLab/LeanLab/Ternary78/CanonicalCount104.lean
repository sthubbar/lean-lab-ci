import LeanLab.Ternary78.CanonicalZeros104
/-
AI wrote this Lean code. Binary Goldbach is open.
The natural count uses actual analytic L-function zeros with their multiplicities.
Source: https://arxiv.org/abs/2005.02989 pages 1 and 2.
No Bennett analytic estimate is proved in this file.
-/

namespace LeanLab.Ternary78.Bennett
/-- The count N of T and chi from Bennett page 2.
The modulus zero branch is a totalization outside the cited theorem domain. -/
noncomputable def canonicalCount (q : ℕ) (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    Nat.card {w : zeroOccurrences χ // |w.val.1.im| ≤ T}
/-- The canonical count is exactly the cardinality of bounded zero occurrences,
for every choice of their finite type enumeration. -/
theorem canonicalCount_eq_card {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    [Fintype {w : zeroOccurrences χ // |w.val.1.im| ≤ T}] :
    canonicalCount q χ T = Fintype.card {w : zeroOccurrences χ // |w.val.1.im| ≤ T} := by
  simp [canonicalCount, NeZero.ne q, Nat.card_eq_fintype_card]

#print axioms canonicalCount_eq_card

/-- Increasing the height cannot decrease the actual natural zero count.
Source: Bennett page 2, definition of N. -/
theorem canonicalCount_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {S T : ℝ} (hST : S ≤ T) : canonicalCount q χ S ≤ canonicalCount q χ T := by
  have : Finite {w : zeroOccurrences χ // |w.val.1.im| ≤ T} :=
    zeroOccurrences_bounded_finite χ hχ T
  simp only [canonicalCount, NeZero.ne q, dite_false]
  apply Nat.card_le_card_of_injective (fun w => ⟨w.val, w.property.trans hST⟩)
  intro w v h
  exact Subtype.ext (congrArg (fun w : {w : zeroOccurrences χ // |w.val.1.im| ≤ T} => w.val) h)

#print axioms canonicalCount_mono

/-- A complete finite cutoff list computes every lower height count by filtering.
Source: Bennett page 2, zero count definition, and the finite grid interface. -/
theorem canonicalCount_eq_card_filter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (z : Finset (zeroOccurrences χ)) {U T : ℝ}
    (hz : ∀ w, w ∈ z ↔ |w.val.1.im| ≤ U) (hTU : T ≤ U) :
    canonicalCount q χ T = (z.filter (fun w => |w.val.1.im| ≤ T)).card := by
  classical
  have : Finite {w : zeroOccurrences χ // |w.val.1.im| ≤ T} :=
    zeroOccurrences_bounded_finite χ hχ T
  let : Fintype {w : zeroOccurrences χ // |w.val.1.im| ≤ T} := Fintype.ofFinite _
  let e : {w : zeroOccurrences χ // |w.val.1.im| ≤ T} ≃
      {w // w ∈ z.filter (fun w => |w.val.1.im| ≤ T)} :=
    { toFun := fun w => ⟨w.val, Finset.mem_filter.mpr ⟨(hz w.val).mpr (w.property.trans hTU), w.property⟩⟩
      invFun := fun w => ⟨w.val, (Finset.mem_filter.mp w.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [canonicalCount, NeZero.ne q, dite_false, Nat.card_eq_fintype_card]
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

#print axioms canonicalCount_eq_card_filter

/-- The canonical count equals the finite sum of actual analytic orders.
Source: Bennett pages 1 and 2, counting the multiset of zeros with multiplicity. -/
theorem canonicalCount_eq_sum_orders {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    canonicalCount q χ T =
      ∑ z ∈ (lfunction_strip_zeros_finite χ hχ T).toFinset,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) z := by
  classical
  let Z := (lfunction_strip_zeros_finite χ hχ T).toFinset
  have hz (z : ℂ) : z ∈ Z ↔
      0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ DirichletCharacter.LFunction χ z = 0 := by
    simp [Z]
  have : Finite {w : zeroOccurrences χ // |w.val.1.im| ≤ T} :=
    zeroOccurrences_bounded_finite χ hχ T
  let : Fintype {w : zeroOccurrences χ // |w.val.1.im| ≤ T} := Fintype.ofFinite _
  let e : {w : zeroOccurrences χ // |w.val.1.im| ≤ T} ≃
      Σ z : Z, Fin (analyticOrderNatAt (DirichletCharacter.LFunction χ) z) :=
    { toFun := fun w =>
        ⟨⟨w.val.val.1, (hz _).mpr
          ⟨w.val.property.1, w.val.property.2.1, w.property, w.val.property.2.2.1⟩⟩,
          ⟨w.val.val.2, w.val.property.2.2.2⟩⟩
      invFun := fun w =>
        ⟨⟨⟨w.1.val, w.2.val⟩,
          (hz _).mp w.1.property |>.1,
          (hz _).mp w.1.property |>.2.1,
          (hz _).mp w.1.property |>.2.2.2,
          w.2.isLt⟩,
          (hz _).mp w.1.property |>.2.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [canonicalCount_eq_card χ T, Fintype.card_congr e]
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact Finset.sum_coe_sort Z _

#print axioms canonicalCount_eq_sum_orders

end LeanLab.Ternary78.Bennett
