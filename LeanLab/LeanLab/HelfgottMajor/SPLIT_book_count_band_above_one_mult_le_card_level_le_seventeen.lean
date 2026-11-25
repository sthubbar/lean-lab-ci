import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le

/-!
# Split of `book_count_band_above_one_mult_le_card_level_le_seventeen`

The parent block covers the conductors `13` to `17` at the top height `2πe / q` of the band:
the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / q]` number at most one. It is split by modulus,
as burst S97 split the block `2` to `6`.

* `q = 14`: there is no primitive character modulo `14`, since reduction of units to `ZMod 7`
  is injective. Proved here, no input.
* the other moduli: the window `(1, 2πe / q]` holds no strip zero at all. One LEAF zero free
  rectangle per modulus, the content of Platt's verification [Pla11] cited in Helfgott arXiv
  1305.2897v4 Section 4.6 page 56. Numerically, burst S126 with mpmath, winding number `0` on the
  boundary of `[10^(-4), 1 - 10^(-4)] × (1, 2πe / q]` for every primitive character of these moduli.
  An empty window is stronger than the parent conclusion.

The assembly is the case analysis on `q`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- No primitive character modulo `14`: units of `ZMod 14` are odd, so reduction of units to
`ZMod 7` is injective, checked by `decide` on residues below `14`; every character modulo `14`
factors through `7` and its conductor is at most `7`. Proved, no input. This is the fact used
tacitly in Section 4.6 of arXiv 1305.2897v4 when Platt's verification is indexed by conductor. -/
theorem cardhi_no_primitive_fourteen (χ : DirichletCharacter ℂ q) (hq : q = 14) : ¬ χ.IsPrimitive := by
  subst hq
  intro hχ
  have hmn : (7 : ℕ) ∣ 14 := by norm_num
  have hinj : Function.Injective (ZMod.unitsMap hmn) := by
    intro a b hab
    have hcast : ((a : ZMod 14).cast : ZMod 7) = ((b : ZMod 14).cast : ZMod 7) := by
      have h := congrArg (fun u : (ZMod 7)ˣ => ((u : ZMod 7))) hab
      simpa only [ZMod.unitsMap_val] using h
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at hcast
    have hmod : a.val.val % 7 = b.val.val % 7 := by
      rw [← ZMod.natCast_eq_natCast_iff']
      exact hcast
    have hcop : ∀ u : (ZMod 14)ˣ, Nat.Coprime u.val.val 14 := by
      intro u
      have hu : IsUnit ((u.val.val : ZMod 14)) := by
        rw [ZMod.natCast_zmod_val]
        exact u.isUnit
      exact (ZMod.isUnit_iff_coprime _ _).mp hu
    have hres : ∀ x, x < 14 → ∀ y, y < 14 → Nat.Coprime x 14 → Nat.Coprime y 14 →
        x % 7 = y % 7 → x = y := by decide
    exact Units.ext (ZMod.val_injective 14
      (hres _ (ZMod.val_lt _) _ (ZMod.val_lt _) (hcop a) (hcop b) hmod))
  have hFT : DirichletCharacter.FactorsThrough χ 7 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hmn]
    intro x hx
    have hx1 : x = 1 := hinj (by rw [hx, map_one])
    simp [hx1]
  have hcond : χ.conductor ≤ 7 :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hFT)
  have hone : χ.conductor = 14 := (DirichletCharacter.isPrimitive_def χ).mp hχ
  omega

/-- LEAF: zero free window for the primitive characters modulo `13`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 13]` of the band at
conductor `13` holds no strip zero of `L(·, χ)`, for each of the 11 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 13]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_thirteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 13) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free window for the primitive characters modulo `15`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 15]` of the band at
conductor `15` holds no strip zero of `L(·, χ)`, for each of the 3 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 15]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_fifteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 15) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free window for the primitive characters modulo `16`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 16]` of the band at
conductor `16` holds no strip zero of `L(·, χ)`, for each of the 4 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 16]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_sixteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 16) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free window for the primitive characters modulo `17`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 17]` of the band at
conductor `17` holds no strip zero of `L(·, χ)`, for each of the 15 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 17]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_seventeen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 17) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_card_level_le_seventeen` from the leaves: case
analysis on `q` in `13` to `17`; the modulus `14` carries no primitive character and the other
moduli have an empty window. -/
theorem book_count_band_above_one_mult_le_card_level_le_seventeen_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 13 ≤ q) (hhi : q ≤ 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have hcases : q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
  rcases hcases with h | h | h | h | h
  · have h := cardhi_window_empty_thirteen χ hχ h
    rw [h]; simp
  · exact absurd hχ (cardhi_no_primitive_fourteen χ h)
  · have h := cardhi_window_empty_fifteen χ hχ h
    rw [h]; simp
  · have h := cardhi_window_empty_sixteen χ hχ h
    rw [h]; simp
  · have h := cardhi_window_empty_seventeen χ hχ h
    rw [h]; simp

end LeanLab.HelfgottMajor.ZeroCount1623
