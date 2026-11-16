import LeanLab.HelfgottMajor.SPLIT_leaf_moment_full_mass_plancherel

/-!
Split of the open leaf `leaf_moment_low_mass_le` of
`SPLIT_leaf_moment_full_mass_plancherel.lean`.

The leaf bounds the low band of the discrete Plancherel mass: the zeros of `L χ` in the strip
`0 < re ρ < 1` with `|im ρ| ≤ T`, kept only when `|im ρ| ≤ 1`, each weighted by its
multiplicity and the squared norm of the Gaussian Mellin profile there, are bounded by the
squared `L2` energy `Sec45.nTwo` of the profile, uniformly in the conductor `q` and in `T`.

The split has three steps.  First, the height window `|im ρ| ≤ T` and the indicator `|im ρ| ≤ 1`
are both harmless: the surviving zeros are exactly those with `|im ρ| ≤ 1` and `|im ρ| ≤ T`,
all summands are nonnegative, and converting the index set from `|im ρ| ≤ T` to the fixed band
`|im ρ| ≤ 1` can only add terms (every such zero has `|im ρ| ≤ 1`, and dropping the restriction
`|im ρ| ≤ T` never removes one).  Second and third, the fixed band is cut at the critical line
into the half with `re ρ ≤ 1/2` and the half with `1/2 < re ρ`; each of the two halves is one
leaf, and its bound is the tightened constant `Sec45.nTwo / 2`.

Every step is a separate leaf ending in `sorry`; the assembly `leaf_moment_low_mass_le_split`
below uses only those leaves and no `sorry`.  The two half-strip leaves carry the whole
analytic content: they are one inequality each about the Plancherel mass on a fixed
half-strip of unit height.  Nothing here is proved about the number of zeros in the band.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- Monotonicity of a nonnegative index-type sum in its index set, stated in the shape the
window-removal leaf needs: the mass carried by the sub-index `{P ∧ R}` inside the index `{P}`
is at most the mass of the index `{Q}`, provided `P ∧ R` implies `Q` and the `Q`-index is
finite.  Nothing is assumed about the summands beyond nonnegativity. -/
private theorem tsum_subtype_indicator_le {Ω : Type*} {P Q R : Ω → Prop} (f : Ω → ℝ)
    (hnn : ∀ x, 0 ≤ f x) (hRQ : ∀ x, P x → R x → Q x) (hQ : {x | Q x}.Finite) :
    (∑' x : {x // P x}, Set.indicator {y : {x // P x} | R (y : Ω)} (fun y => f (y : Ω)) x) ≤
      ∑' x : {x // Q x}, f (x : Ω) := by
  classical
  -- the indicator sum is the sum over the filtered index
  have h1 : (∑' x : {x // P x},
        Set.indicator {y : {x // P x} | R (y : Ω)} (fun y => f (y : Ω)) x)
      = ∑' y : {y : {x // P x} | R (y : Ω)}, f ((y : {x // P x}) : Ω) :=
    (tsum_subtype {y : {x // P x} | R (y : Ω)} (fun y : {x // P x} => f (y : Ω))).symm
  rw [h1]
  -- re-index the iterated subtype as the conjunction
  let e : {y : {x // P x} | R (y : Ω)} ≃ {z : Ω // P z ∧ R z} :=
    { toFun := fun y => ⟨(y.val : Ω), y.val.property, y.property⟩
      invFun := fun z => ⟨⟨z.val, z.property.1⟩, z.property.2⟩
      left_inv := fun y => by ext <;> rfl
      right_inv := fun z => by ext <;> rfl }
  have h2 : (∑' y : {y : {x // P x} | R (y : Ω)}, f ((y : {x // P x}) : Ω))
      = ∑' z : {z : Ω // P z ∧ R z}, f (z : Ω) :=
    Equiv.tsum_eq e (fun z : {z : Ω // P z ∧ R z} => f (z : Ω))
  rw [h2]
  -- inject the conjunction index into the `Q`-index
  haveI : Fintype {z : Ω // Q z} := hQ.fintype
  have hsum : Summable (fun z : {z : Ω // Q z} => f (z : Ω)) := Summable.of_finite
  have hinj : Function.Injective
      (fun z : {z : Ω // P z ∧ R z} => (⟨z.val, hRQ z.val z.property.1 z.property.2⟩ :
        {z : Ω // Q z})) := by
    intro a b hab
    have h : (a : Ω) = (b : Ω) := congrArg (fun w : {z : Ω // Q z} => (w : Ω)) hab
    exact Subtype.ext h
  have hle := tsum_comp_le_tsum_of_inj (f := fun z : {z : Ω // Q z} => f (z : Ω)) hsum
    (fun z => hnn z.val) hinj
  simpa only [Function.comp_def] using hle

/-- LEAF. Window removal.  The height window `|im ρ| ≤ T` and the indicator `|im ρ| ≤ 1` can
both be dropped: every zero that survives them satisfies `|im ρ| ≤ 1`, the summands —
a natural multiplicity times a squared norm — are nonnegative, and re-indexing the surviving
zeros by the fixed band `|im ρ| ≤ 1` only adds the zeros of the band whose height exceeds `T`.
This step estimates nothing about the Mellin norms; it moves the index set and nothing else,
and it is the step that removes the height `T` from the statement. -/
theorem leaf_moment_low_mass_window_restrict (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2) :=
  tsum_subtype_indicator_le (Ω := ℂ)
    (P := fun z : ℂ =>
      DirichletCharacter.LFunction χ z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T)
    (Q := fun z : ℂ =>
      DirichletCharacter.LFunction χ z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ 1)
    (R := fun z : ℂ => |z.im| ≤ 1)
    (f := fun z : ℂ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) *
      ‖gaussianMellin δ z‖ ^ 2)
    (fun z => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (fun z hP hR => ⟨hP.1, hP.2.1, hP.2.2.1, hR⟩)
    (leaf_moment_window_finite q χ 1)

/-- LEAF. Lower half of the fixed low band.  On the zeros of `L χ` in the strip with
`|im ρ| ≤ 1` and `re ρ ≤ 1/2`, the multiplicity-weighted squared Mellin mass is at most half
of the squared `L2` energy `Sec45.nTwo` of the profile.  The index set is the low band only,
cut at the critical line from below, and the constant is tightened from `Sec45.nTwo` to
`Sec45.nTwo / 2`; this is one estimate about a fixed half-strip of unit height, and it says
nothing about the half with `re ρ > 1/2`. -/
theorem leaf_moment_low_mass_lower_half (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 2 := by
  sorry

/-- LEAF. Upper half of the fixed low band.  On the zeros of `L χ` in the strip with
`|im ρ| ≤ 1` and `1/2 < re ρ`, the multiplicity-weighted squared Mellin mass is at most half
of the squared `L2` energy `Sec45.nTwo` of the profile.  The index set is the low band only,
cut at the critical line from above, and the constant is tightened from `Sec45.nTwo` to
`Sec45.nTwo / 2`; this is one estimate about a fixed half-strip of unit height, and it says
nothing about the half with `re ρ ≤ 1/2`. -/
theorem leaf_moment_low_mass_upper_half (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 2 := by
  sorry

/-- Assembly of the split: drop the height window and the indicator to reach the fixed band
`|im ρ| ≤ 1`, split that band at the critical line into `re ρ ≤ 1/2` and `1/2 < re ρ`, and
bound the two halves by `Sec45.nTwo / 2` each. -/
theorem leaf_moment_low_mass_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := (leaf_moment_window_finite q χ 1).fintype
  have hsplit :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2)
        = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
              |ρ.im| ≤ 1},
            Set.indicator {ρ | ρ.val.re ≤ 1 / 2}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
          + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
                |ρ.im| ≤ 1},
              Set.indicator {ρ | 1 / 2 < ρ.val.re}
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                  ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : (ρ : ℂ).re ≤ 1 / 2
    · rw [if_pos h, if_neg (by linarith)]
      ring
    · rw [if_neg h, if_pos (lt_of_not_ge h)]
      ring
  have h1 := leaf_moment_low_mass_window_restrict q χ δ T
  have h2 := leaf_moment_low_mass_lower_half q χ δ T
  have h3 := leaf_moment_low_mass_upper_half q χ δ T
  have h4 :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ≤ Sec45.nTwo := by
    rw [hsplit]
    linarith
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
