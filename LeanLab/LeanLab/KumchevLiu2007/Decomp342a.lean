/-
Reality of the coefficient in page 13 display 45, used on page 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp292b

namespace LeanLab.KumchevLiu2007.Task342a

open Real Complex
open scoped BigOperators

/-- Page 13 display 45. Reindex reduced natural residues as units modulo q. -/
theorem reduced_sum_zmod (q : ℕ) [NeZero q] (g : ℕ → ℂ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), g a) =
      ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y), g y.val := by
  classical
  refine Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at ha ⊢
    rw [ZMod.isUnit_iff_coprime]
    exact ha.2
  · intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    have h := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt ha1.1, ZMod.val_natCast_of_lt ha2.1] at h
  · intro y hy
    refine ⟨y.val, ?_, ZMod.natCast_zmod_val y⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt y, ?_⟩
    have hy' : IsUnit y := (Finset.mem_filter.mp hy).2
    rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime] at hy'
    exact hy'
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rw [ZMod.val_natCast_of_lt ha.1]

/-- Page 13 display 45. The coefficient is a real scalar times a double unit sum. -/
theorem A2_zmod_formula (n q : ℕ) [NeZero q] :
    U1534.A2 n q =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) ^ 2 *
        ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
            ZMod.stdAddChar (N := q) (a * (x * x - (n : ZMod q))) := by
  classical
  unfold U1534.A2 U1534.gaussS
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  rw [reduced_sum_zmod]
  apply Finset.sum_congr rfl
  intro x hx
  rw [reduced_sum_zmod]
  apply Finset.sum_congr rfl
  intro a ha
  unfold U1534.ee
  rw [← Complex.exp_add]
  rw [show a * (x * x - (n : ZMod q)) =
      (((a.val : ℤ) * ((x.val : ℤ) ^ 2 - (n : ℤ)) : ℤ) : ZMod q) by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- Page 13 display 45 and page 15 second display. Negation permutes unit residues. -/
theorem unit_character_sum_conj (q : ℕ) [NeZero q] (t : ZMod q) :
    (starRingEnd ℂ) (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * t)) =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        ZMod.stdAddChar (N := q) (a * t) := by
  classical
  rw [map_sum]
  simp_rw [AddChar.starComp_apply (by rw [ZMod.ringChar_zmod_n]; exact NeZero.pos q : 0 < ringChar (ZMod q)),
    AddChar.inv_apply, ← neg_mul]
  refine Finset.sum_bij (fun (a : ZMod q) _ => -a) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.neg
  · intro a ha b hb hab
    exact neg_injective hab
  · intro a ha
    refine ⟨-a, ?_, neg_neg a⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.neg
  · intro a ha
    rfl

/-- Page 13 display 45 and page 15 second display. Exact A2_conj supply. -/
theorem A2_conj (n q : ℕ) :
    (starRingEnd ℂ) (U1534.A2 n q) = U1534.A2 n q := by
  classical
  by_cases hq : q = 0
  · subst q
    simp [U1534.A2]
  letI : NeZero q := ⟨hq⟩
  rw [A2_zmod_formula, map_mul, map_div₀, map_pow, map_intCast, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact unit_character_sum_conj q (x * x - (n : ZMod q))

end LeanLab.KumchevLiu2007.Task342a
