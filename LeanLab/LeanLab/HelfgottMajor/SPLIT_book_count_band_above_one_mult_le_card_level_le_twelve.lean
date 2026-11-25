import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le

/-!
# Split of `book_count_band_above_one_mult_le_card_level_le_twelve`

The parent block covers the conductors `7` to `12` at the top height `2πe / q` of the band:
the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / q]` number at most one. It is split by modulus,
as burst S97 split the block `2` to `6`.

* `q = 10`: there is no primitive character modulo `10`, since reduction of units to `ZMod 5`
  is injective. Proved here, no input.
* `q = 11`: the window is not empty. Numerically one primitive character modulo `11` has a
  simple zero at `1/2 + 1.2311882409… i`, so this LEAF keeps the parent bound for that modulus.
* `q = 7, 8, 9, 12`: the window `(1, 2πe / q]` holds no strip zero at all. One LEAF zero free
  rectangle per modulus, the content of Platt's verification [Pla11] cited in Helfgott arXiv
  1305.2897v4 Section 4.6 page 56. Numerically, burst S126 with mpmath, winding number `0` on the
  boundary of `[10^(-4), 1 - 10^(-4)] × (1, 2πe / q]` for every primitive character of these four moduli.
  An empty window is stronger than the parent conclusion.

The assembly is the case analysis on `q`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- No primitive character modulo `10`: units of `ZMod 10` are odd, so reduction of units to
`ZMod 5` is injective, checked by `decide` on residues below `10`; every character modulo `10`
factors through `5` and its conductor is at most `5`. Proved, no input. This is the fact used
tacitly in Section 4.6 of arXiv 1305.2897v4 when Platt's verification is indexed by conductor. -/
theorem cardhi_no_primitive_ten (χ : DirichletCharacter ℂ q) (hq : q = 10) : ¬ χ.IsPrimitive := by
  subst hq
  intro hχ
  have hmn : (5 : ℕ) ∣ 10 := by norm_num
  have hinj : Function.Injective (ZMod.unitsMap hmn) := by
    intro a b hab
    have hcast : ((a : ZMod 10).cast : ZMod 5) = ((b : ZMod 10).cast : ZMod 5) := by
      have h := congrArg (fun u : (ZMod 5)ˣ => ((u : ZMod 5))) hab
      simpa only [ZMod.unitsMap_val] using h
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at hcast
    have hmod : a.val.val % 5 = b.val.val % 5 := by
      rw [← ZMod.natCast_eq_natCast_iff']
      exact hcast
    have hcop : ∀ u : (ZMod 10)ˣ, Nat.Coprime u.val.val 10 := by
      intro u
      have hu : IsUnit ((u.val.val : ZMod 10)) := by
        rw [ZMod.natCast_zmod_val]
        exact u.isUnit
      exact (ZMod.isUnit_iff_coprime _ _).mp hu
    have hres : ∀ x, x < 10 → ∀ y, y < 10 → Nat.Coprime x 10 → Nat.Coprime y 10 →
        x % 5 = y % 5 → x = y := by decide
    exact Units.ext (ZMod.val_injective 10
      (hres _ (ZMod.val_lt _) _ (ZMod.val_lt _) (hcop a) (hcop b) hmod))
  have hFT : DirichletCharacter.FactorsThrough χ 5 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hmn]
    intro x hx
    have hx1 : x = 1 := hinj (by rw [hx, map_one])
    simp [hx1]
  have hcond : χ.conductor ≤ 5 :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hFT)
  have hone : χ.conductor = 10 := (DirichletCharacter.isPrimitive_def χ).mp hχ
  omega

/-- LEAF: zero free window for the primitive characters modulo `7`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 7]` of the band at
conductor `7` holds no strip zero of `L(·, χ)`, for each of the 5 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 7]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_seven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 7) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free window for the primitive characters modulo `8`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 8]` of the band at
conductor `8` holds no strip zero of `L(·, χ)`, for each of the 2 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 8]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_eight (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 8) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: zero free window for the primitive characters modulo `9`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 9]` of the band at
conductor `9` holds no strip zero of `L(·, χ)`, for each of the 4 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 9]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_nine (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 9) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- LEAF: the window `(1, 2πe / 11]` of the band at conductor `11`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]. This window is NOT empty: numerically, burst
S126 with mpmath at 30 digits, the primitive character modulo `11` with `χ(2) = exp(-3πi/5)` has a
simple zero at `1/2 + 1.2311882409… i`, with `|L| < 10^(-30)` and winding number `1` on a square of
side `0.02` around it; every other primitive character modulo `11` has winding number `0` on the
window. So the leaf keeps the parent bound for this modulus, one zero, simple. Class HARD: a
certified zero count on a rectangle together with a simplicity check. -/
theorem cardhi_window_eleven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 11) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF: zero free window for the primitive characters modulo `12`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, Platt's verification [Pla11]: the window `(1, 2πe / 12]` of the band at
conductor `12` holds no strip zero of `L(·, χ)`, for each of the 1 primitive characters. Numerically,
burst S126 with mpmath, the argument principle on `[10^(-4), 1 - 10^(-4)] × (1, 2πe / 12]` gives
winding number `0` for every one of them. Class HARD: a certified zero verification on a rectangle. -/
theorem cardhi_window_empty_twelve (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 12) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_card_level_le_twelve` from the leaves: case
analysis on `q` in `7` to `12`; the modulus `10` carries no primitive character, the modulus `11`
is its own leaf, and the other moduli have an empty window. -/
theorem book_count_band_above_one_mult_le_card_level_le_twelve_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 7 ≤ q) (hhi : q ≤ 12) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have hcases : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 := by omega
  rcases hcases with h | h | h | h | h | h
  · have h := cardhi_window_empty_seven χ hχ h
    rw [h]; simp
  · have h := cardhi_window_empty_eight χ hχ h
    rw [h]; simp
  · have h := cardhi_window_empty_nine χ hχ h
    rw [h]; simp
  · exact absurd hχ (cardhi_no_primitive_ten χ h)
  · exact cardhi_window_eleven χ hχ h
  · have h := cardhi_window_empty_twelve χ hχ h
    rw [h]; simp

end LeanLab.HelfgottMajor.ZeroCount1623
