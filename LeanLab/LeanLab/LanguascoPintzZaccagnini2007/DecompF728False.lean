import LeanLab.LanguascoPintzZaccagnini2007.DecompF728

/-!
FALSIFY unit `LanguascoPintzZaccagnini2007/DecompF728`, burst prove-20261117.

The statement of `LEAF_Sg_smallness` in `DecompF728.lean` is FALSE as written. Its only
hypothesis on `Sg` is `hSgZero`, which forces `Sg i j n = 0` off the pole pair `(0, 0)` and says
nothing about `Sg 0 0 n`. The conclusion nevertheless bounds `‖Sg 0 0 n‖` by `ε`.

Counterexample: `X = 2`, `K = 0`, every conductor `(z i).1 = 3`, `Sg` constantly `1`,
`ε₀ = 1`, `Cε` constantly `1`, `ε = 1/2`, `n = 2`. Then `2 ∈ evenJ131 2`, `3 ∤ 1 * 2`, and
`‖Sg 0 0 2‖ = 1 > 1/2`. With `K = 0` the index type is `Fin 1`, so `hSgZero` is vacuous.

The theorem below proves the negation of the universally quantified statement. It does not use
`LEAF_Sg_smallness` and does not change it. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

/-- `2` lies in `evenJ131 2`: it is in `[1, 2]`, even, and `2 * 2 / 3 ≤ 2`. -/
theorem two_mem_evenJ131_two : (2 : ℕ) ∈ evenJ131 2 := by
  unfold evenJ131
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨by norm_num, le_refl 2⟩, by decide, by norm_num⟩

/-- The statement of `LEAF_Sg_smallness`, word for word, is false: the hypotheses do not
constrain `Sg 0 0 n`. Witness `X = 2`, `K = 0`, conductor `3`, `Sg = 1`, `ε = 1/2`, `n = 2`. -/
theorem LEAF_Sg_smallness_false :
    ¬ (∀ (X K : ℕ)
        (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
        (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ)
        (_hSgZero : ∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0)
        (ε₀ : ℝ) (_hε₀ : 0 < ε₀)
        (Cε : ℝ → ℕ) (_hC : ∀ ε, 0 < Cε ε),
        (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
          (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε)) := by
  intro h
  have hzero : ∀ (i j : Fin (0 + 1)) (n : ℕ), (i ≠ 0 ∨ j ≠ 0) →
      (fun (_ _ : Fin (0 + 1)) (_ : ℕ) => (1 : ℂ)) i j n = 0 := by
    intro i j n hij
    rcases hij with hi | hj
    · exact absurd (Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)) hi
    · exact absurd (Fin.ext (by have := j.isLt; simp only [Fin.val_zero]; omega)) hj
  have hdvd : ¬ (3 : ℕ) ∣ 1 * 2 := by decide
  have key := h 2 0 (fun _ => ⟨3, (1, 0)⟩) (fun _ _ _ => (1 : ℂ)) hzero
    1 one_pos (fun _ => 1) (fun _ => Nat.one_pos)
    (1 / 2) (by norm_num) (by norm_num) 0 0 2 two_mem_evenJ131_two (Or.inl hdvd)
  norm_num at key

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.two_mem_evenJ131_two
#print axioms LeanLab.LPZ2007.LEAF_Sg_smallness_false
