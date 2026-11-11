import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
Split of `nonreal_exceptional_radical481` of `Decomp481b`.

The target bounds the odd radical of the conductor of every zero of the box `zeroBox481 X H T P`
whose character takes a nonreal value from below by `c * Lg X ^ 2`, at bounded height `T`, in the
strip `1 - H / log X ≤ re < 1`, uniformly in the major arc parameter `P` in its admissible range.

The proof has three steps, and they are separate estimates.

The zero region. The hypothesis `hiw` forbids zeros of a nonreal primitive character in
`re > 1 - 1 / iwaniecDenom481 r t`. A zero of the box sits at `re ≥ 1 - H / log X`, so the two
inequalities can both hold only if `log X / H ≤ iwaniecDenom481 r t`. That is
`leaf_iwaniec_bound481`, and it is all the analytic input used.

The size of the denominator. A zero of the box has conductor `r ≤ P ≤ X ^ (41 / 100)` and
`|im| ≤ T`, so the argument of the denominator is at most a constant times `log X`, and the
denominator itself is at most `C * (log X) ^ (7 / 8)`, with a constant that depends on `T` only.
That is `leaf_denom_upper_bound481`.

The growth comparison. For fixed `C` and `H` the bound `log X / H ≤ C * (log X) ^ (7 / 8)` fails
for every large enough `X`, because the seventh-eighth power of `log X` is smaller than `log X`
by an unbounded factor. That is `leaf_log_growth_excludes481`.

Together the three leaves make a zero of the box with a nonreal character impossible once `X` is
large enough, so the conclusion holds for any positive constant, and in particular for one. The
threshold absorbs the small scales, where the box is not excluded.

`nonreal_exceptional_radical481_split` below is proved from the three leaves with no `sorry`,
does not use `nonreal_exceptional_radical481`, and keeps the statement of the target.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF. The zero free region in the shape the box uses. From the hypothesis `hiw`, a zero of a
nonreal primitive character that lies in the box, whose real part is at least `1 - H / log X`,
cannot sit inside `re > 1 - 1 / iwaniecDenom481 r t`; hence the two radii are ordered, that is
`log X / H ≤ iwaniecDenom481 r t` for its height `t = im`. -/
theorem leaf_iwaniec_bound481 (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∀ X : ℕ, 2 ≤ X → ∀ P : ℝ, ∀ z ∈ zeroBox481 X H T P,
      (∃ a, (z.2.1 a).im ≠ 0) →
        Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im := by
  sorry

/-- LEAF. The size of the denominator. A zero of the box has conductor at most `P` and height at
most `T`, and an admissible `P` is at most `X ^ (41 / 100)`; therefore the logarithm
`log (r (|t| + 2))` in the denominator is at most a constant times `log X`, so the denominator is
at most `C * (log X) ^ (7 / 8)` once `X ≥ 2`, with one constant `C` that depends on `T` only. -/
theorem leaf_denom_upper_bound481 (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → ∀ P H : ℝ, AdmissibleP131 X P →
      ∀ z ∈ zeroBox481 X H T P,
        iwaniecDenom481 z.1 z.2.2.im ≤ C * (Real.log X) ^ (7 / 8 : ℝ) := by
  sorry

/-- LEAF. The growth comparison. For a fixed positive constant `C` and a fixed `H ≥ 1`, the
seventh-eighth power of `log X` falls below `log X / (C H)` once `X` is large, that is
`C * (log X) ^ (7 / 8) < log X / H` for every `X` at least the threshold. -/
theorem leaf_log_growth_excludes481 (C : ℝ) (hC : 0 < C) (H : ℝ) (hH : 1 ≤ H) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      C * (Real.log X) ^ (7 / 8 : ℝ) < Real.log X / H := by
  sorry

/-- The split target: the statement of `nonreal_exceptional_radical481`, proved from the three
leaves by the contradictory pair of estimates, with constant one and the threshold of the growth
comparison. -/
theorem nonreal_exceptional_radical481_split (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨C, hC, hden⟩ := leaf_denom_upper_bound481 T hT
  obtain ⟨X₁, hX₁⟩ := leaf_log_growth_excludes481 C hC H hH
  refine ⟨1, one_pos, max X₁ 2, ?_⟩
  intro X hX P hP z hz him
  have h2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hle : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hlow : Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im :=
    leaf_iwaniec_bound481 hiw H T hH hT X h2 P z hz him
  have hup : iwaniecDenom481 z.1 z.2.2.im ≤ C * (Real.log X) ^ (7 / 8 : ℝ) :=
    hden X h2 P H hP z hz
  have hbig : C * (Real.log X) ^ (7 / 8 : ℝ) < Real.log X / H := hX₁ X hle
  exfalso
  exact absurd (hlow.trans hup) (not_le.mpr hbig)

end

end LeanLab.LPZ2007
