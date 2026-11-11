import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
Split of `real_zero_bound481` of `Decomp481b`, the real zero lower bound of preprint page 5.

The target asserts one positive constant `a` such that every real zero `1 - δ` of every real
character of modulus `r` satisfies `a * r ^ (-(1 / 2)) ≤ δ`.

The statement has two independent axes and the file cuts along both.

The size of `δ`. The lower bound is an assertion about zeros close to one only: once `1 / 2 ≤ δ`,
the conclusion follows from `a ≤ 1 / 4` together with `r ^ (-(1 / 2)) ≤ 1`, valid for `1 ≤ r`.
That step is elementary and is carried out in the assembly below, not left as a leaf.

The character. A character of modulus one is the trivial character, whose L function is the
Riemann zeta function, so the zeros near one there are a statement about zeta alone: that is
`leaf_real_zero_modulus_one481`. A real primitive character of modulus at least two is the
quadratic case, and the lower bound for it is `leaf_real_zero_primitive_large481`. An
imprimitive real character is the remaining case: the Euler factors at the ramified primes
remove zeros rather than add them, so a zero of the imprimitive L function need not come from
any primitive one, and the lower bound must be stated for that class on its own, which is
`leaf_real_zero_imprimitive481`.

Every leaf is the target with one case restriction and with `δ < 1 / 2`, so every leaf is
strictly weaker than the target and none of them restates it. The three case conditions `r ≤ 1`,
`2 ≤ r` with a primitive character, and a non-primitive character are exhaustive under the
target's `1 ≤ r`. `real_zero_bound481_split` below combines the three constants and the large
`δ` step into the target statement with no `sorry`, and it does not use `real_zero_bound481`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF. The modulus one case of the real zero lower bound. For the trivial character, whose
L function is the Riemann zeta function, a zero at `1 - δ` with `0 < δ < 1 / 2` costs at least a
fixed positive multiple of `1 ^ (-(1 / 2))`, uniformly in the character of modulus one. -/
theorem leaf_real_zero_modulus_one481 :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → r ≤ 1 → ∀ χ : DirichletCharacter ℂ r,
      (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ := by
  sorry

/-- LEAF. The quadratic case of the real zero lower bound. For a real primitive character of
modulus at least two, a zero at `1 - δ` with `0 < δ < 1 / 2` costs at least a fixed positive
multiple of `r ^ (-(1 / 2))`. The constant is uniform over the modulus and the character. -/
theorem leaf_real_zero_primitive_large481 :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → 2 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ.IsPrimitive → (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ := by
  sorry

/-- LEAF. The imprimitive case of the real zero lower bound. For a real character that is not
primitive, a zero of its L function at `1 - δ` with `0 < δ < 1 / 2` costs at least a fixed
positive multiple of `r ^ (-(1 / 2))`. No restriction to zeros induced from a primitive
character is made here, since the Euler factors at the ramified primes do not remove them all. -/
theorem leaf_real_zero_imprimitive481 :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      ¬ χ.IsPrimitive → (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ := by
  sorry

/-- The real zero lower bound from its three cases and the elementary step for large `δ`. -/
theorem real_zero_bound481_split : RealZeroStatement481 := by
  classical
  obtain ⟨a₁, ha₁pos, ha₁⟩ := leaf_real_zero_modulus_one481
  obtain ⟨a₂, ha₂pos, ha₂⟩ := leaf_real_zero_primitive_large481
  obtain ⟨a₃, ha₃pos, ha₃⟩ := leaf_real_zero_imprimitive481
  refine ⟨min (1 / 4) (min a₁ (min a₂ a₃)), ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min ha₁pos (lt_min ha₂pos ha₃pos))
  · intro r hr χ hreal δ hδ hzero
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    have hrpow : (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
    have hpowpos : (0 : ℝ) ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hrpos _)
    have hA1 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ a₁ := le_trans (min_le_right _ _) (min_le_left _ _)
    have hA2 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ a₂ :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hA3 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ a₃ :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hA0 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ 1 / 4 := min_le_left _ _
    by_cases hbig : (1 / 2 : ℝ) ≤ δ
    · have hmul : min (1 / 4) (min a₁ (min a₂ a₃)) * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 := by
        have hstep : min (1 / 4) (min a₁ (min a₂ a₃)) * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (1 / 4) * 1 :=
          mul_le_mul hA0 hrpow hpowpos (by norm_num)
        linarith
      linarith
    · have hsmall : δ < 1 / 2 := lt_of_not_ge hbig
      by_cases hrle : r ≤ 1
      · have h1 := ha₁ r hr hrle χ hreal δ hδ hsmall hzero
        exact le_trans (mul_le_mul_of_nonneg_right hA1 hpowpos) h1
      · have hr2 : 2 ≤ r := by omega
        by_cases hprim : χ.IsPrimitive
        · have h2 := ha₂ r hr hr2 χ hprim hreal δ hδ hsmall hzero
          exact le_trans (mul_le_mul_of_nonneg_right hA2 hpowpos) h2
        · have h3 := ha₃ r hr χ hprim hreal δ hδ hsmall hzero
          exact le_trans (mul_le_mul_of_nonneg_right hA3 hpowpos) h3

end

end LeanLab.LPZ2007
