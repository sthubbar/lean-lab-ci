import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
Split of `real_exceptional_conductor481` of `Decomp481b`.

The target bounds the conductor of every zero of the box `zeroBox481 X H T P` that belongs to a
real primitive character from below by `c * Lg X ^ 2`, at bounded height `T`, in the strip
`1 - H / log X ≤ re ≤ 1`, uniformly in the major arc parameter `P`.

Two cases are needed, and they are not the same argument.

Real zeros. `RealZeroStatement481`, the hypothesis `hzero` of the target, gives `a > 0` with
`a * r ^ (-1/2) ≤ δ` for a zero of a real character at the real point `1 - δ`. A zero of the box
has `1 - re ≤ H / log X`, so `a / √r ≤ H / log X`, that is `r ≥ (a log X / H) ^ 2`, which is
`c * Lg X ^ 2` with a constant that works for every `X`. `leaf_real_zero_conductor481` is that
estimate from `hzero` alone and `leaf_real_zero_box481` puts it into the shape of the box.

Nonreal zeros of real characters. `hzero` says nothing about those, and the box does not exclude
them: membership only requires the character to take real values, not the zero to be real. Off the
real axis one needs the classical zero free region for real characters, which is
`leaf_real_nonreal_threshold481`: the radius `b / log (r (|t| + 2))` is at most `H / log X` for
any zero of the box with nonzero imaginary part, since otherwise the zero would sit inside the
region where the L function does not vanish. `leaf_real_nonreal_conductor481` turns that inequality
into the quadratic conductor bound, which is an exponential lower bound in `X` cut down by
`|im| ≤ T`, hence beats `Lg X ^ 2` for all large `X`.

`real_exceptional_conductor481_split` below is proved from the four leaves with no `sorry`,
does not use `real_exceptional_conductor481`, and keeps the statement of the target.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF. The real zero case, from the real zero lower bound alone: for a modulus `r ≥ 1`, a
character with real values, and a genuine zero of the L function at the real point `1 - δ` with
`0 < δ ≤ H / log X`, the modulus is at least `c * Lg X ^ 2`, with one constant `c` for all `X`.
This is the lower bound `a * r ^ (-1/2) ≤ δ` rearranged, with `Lg X = log X / log 2`. -/
theorem leaf_real_zero_conductor481 (hzero : RealZeroStatement481)
    (H : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      (∀ a, (χ a).im = 0) → ∀ δ : ℝ, 0 < δ → δ ≤ H / Real.log X →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → c * Lg X ^ 2 ≤ (r : ℝ) := by
  sorry

/-- LEAF. The zero free region for real characters off the real axis, in the form the box uses:
some `b > 0` has `b / log (r (|t| + 2)) ≤ H / log X` for every zero of the box with real character
and nonzero imaginary part. Such a zero cannot sit inside `re ≥ 1 - b / log (r (|t| + 2))`, where
the L function does not vanish, and the box puts it at `re ≥ 1 - H / log X`, so the two radii are
ordered. -/
theorem leaf_real_nonreal_threshold481 :
    ∃ b : ℝ, 0 < b ∧ ∀ X : ℕ, 1 < X → ∀ H T P : ℝ,
      ∀ z ∈ zeroBox481 X H T P, (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 →
        b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ H / Real.log X := by
  sorry

/-- LEAF. From that radius to the conductor bound: for a fixed `H ≥ 1` and `T ≥ 1`, if every
nonreal zero of the box satisfies the radius inequality at every height, then the modulus of such
a zero is at least `c * Lg X ^ 2` for all large `X`, uniformly in the major arc parameter `P`.
The box gives `|im| ≤ T`, so `r ≥ X ^ (b / H) / (T + 2)`, and an exponential in `X` beats
`Lg X ^ 2` for large `X`. -/
theorem leaf_real_nonreal_conductor481 (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∀ b : ℝ, 0 < b →
      (∀ X : ℕ, 1 < X → ∀ P : ℝ, ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 →
          b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ H / Real.log X) →
      ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
        AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
          (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  sorry

/-- LEAF. The real zero case inside the box: a zero of the box whose imaginary part vanishes is the
real point `1 - δ` with `δ = 1 - re`, `0 < δ` and `δ ≤ H / log X`, so the real zero case applies to
it with one constant and with a threshold that does not depend on the character, the height, the
major arc parameter or the modulus. -/
theorem leaf_real_zero_box481 (hzero : RealZeroStatement481) (H T : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → z.2.2.im = 0 → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  sorry

/-- The split target: the statement of `real_exceptional_conductor481`, proved from the four leaves
by the case distinction `im = 0` or `im ≠ 0`, with the smaller constant and the larger threshold. -/
theorem real_exceptional_conductor481_split (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨c₁, hc₁, X₁, hreal⟩ := leaf_real_zero_box481 hzero H T hH
  obtain ⟨b, hb, hthr⟩ := leaf_real_nonreal_threshold481
  obtain ⟨c₂, hc₂, X₂, hnonreal⟩ := leaf_real_nonreal_conductor481 H T hH hT b hb
    (fun X hX P z hz him hIm => hthr X hX H T P z hz him hIm)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max X₁ X₂, ?_⟩
  intro X hX P hAdm z hz him
  have hle₁ : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hle₂ : X₂ ≤ X := le_trans (le_max_right _ _) hX
  have hsq : (0 : ℝ) ≤ Lg X ^ 2 := sq_nonneg (Lg X)
  by_cases hIm : z.2.2.im = 0
  · have h := hreal X hle₁ P hAdm z hz him hIm
    have hmin : min c₁ c₂ * Lg X ^ 2 ≤ c₁ * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hsq
    linarith
  · have h := hnonreal X hle₂ P hAdm z hz him hIm
    have hmin : min c₁ c₂ * Lg X ^ 2 ≤ c₂ * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hsq
    linarith

end

end LeanLab.LPZ2007
