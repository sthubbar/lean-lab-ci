import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le

/-!
# Split of `book_count_band_above_one_mult_le_one_level_le_seventeen`

The parent block covers the conductors `13` to `17` at the top height `2πe / q` of the band.
It is split by modulus, the same pattern as the proved split of the block `2` to `6`.

* `q = 14`: there is no primitive character modulo `14`, since `(ZMod 14)ˣ → (ZMod 7)ˣ` is injective, so every character modulo `14` factors through modulus `7`. Proved here, no input.
* the remaining moduli `13`, `15`, `16`, `17`: one LEAF each, the parent conclusion restricted to that one modulus, a finite certified zero verification of the primitive `L`-functions of that conductor on one short window.

The assembly is the case analysis on `q`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Reduction of units of `ZMod 14` to units of `ZMod 7` is injective: a unit of `ZMod 14` is
odd, so two units with equal residues modulo `7` and both below `14` coincide. Proved, no
input. -/
private lemma one17_unitsMap_seven_fourteen_injective :
    Function.Injective (ZMod.unitsMap (show 7 ∣ 14 by norm_num)) := by
  intro a b hab
  have hcast : ((a : ZMod 14).cast : ZMod 7) = ((b : ZMod 14).cast : ZMod 7) := by
    have h := congrArg (fun u : (ZMod 7)ˣ => ((u : ZMod 7))) hab
    simpa only [ZMod.unitsMap_val] using h
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at hcast
  have hmod : a.val.val % 7 = b.val.val % 7 := by
    rw [← ZMod.natCast_eq_natCast_iff']
    exact hcast
  have halt : a.val.val < 14 := ZMod.val_lt _
  have hblt : b.val.val < 14 := ZMod.val_lt _
  have hcopa : Nat.Coprime a.val.val 14 := by
    have hu : IsUnit ((a.val.val : ZMod 14)) := by
      rw [ZMod.natCast_zmod_val]
      exact a.isUnit
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  have hcopb : Nat.Coprime b.val.val 14 := by
    have hu : IsUnit ((b.val.val : ZMod 14)) := by
      rw [ZMod.natCast_zmod_val]
      exact b.isUnit
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  have hodd_a : a.val.val % 2 = 1 := by
    have h2 : Nat.Coprime a.val.val 2 := hcopa.coprime_dvd_right (by norm_num)
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp h2
    omega
  have hodd_b : b.val.val % 2 = 1 := by
    have h2 : Nat.Coprime b.val.val 2 := hcopb.coprime_dvd_right (by norm_num)
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp h2
    omega
  have hvals : a.val.val = b.val.val := by omega
  exact Units.ext (ZMod.val_injective 14 hvals)

/-- No primitive character modulo `14`: every character of that modulus factors through
modulus `7`, since the reduction of unit groups is injective, so its conductor is at most `7`.
Proved, no input. -/
theorem one17_no_primitive_fourteen (χ : DirichletCharacter ℂ q) (hq : q = 14) : ¬ χ.IsPrimitive := by
  subst hq
  intro hχ
  have hFT : DirichletCharacter.FactorsThrough χ 7 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show 7 ∣ 14 by norm_num)]
    intro x hx
    have hx1 : x = 1 := one17_unitsMap_seven_fourteen_injective (by rw [hx, map_one])
    simp [hx1]
  have hcond : χ.conductor ≤ 7 :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hFT)
  have hone : χ.conductor = 14 := (DirichletCharacter.isPrimitive_def χ).mp hχ
  omega

/-- LEAF: modulus `13` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `13`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 13]` has multiplicity at most one. The window height `2πe / 13` is below `1.32`, so
this is one finite check over the primitive characters of conductor `13`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one17_thirteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 13) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: modulus `15` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `15`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 15]` has multiplicity at most one. The window height `2πe / 15` is below `1.14`, so
this is one finite check over the primitive characters of conductor `15`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one17_fifteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 15) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: modulus `16` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `16`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 16]` has multiplicity at most one. The window height `2πe / 16` is below `1.07`, so
this is one finite check over the primitive characters of conductor `16`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one17_sixteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 16) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: modulus `17` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `17`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 17]` has multiplicity at most one. The window height `2πe / 17` is below `1.01`, so
this is one finite check over the primitive characters of conductor `17`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one17_seventeen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_one_level_le_seventeen` from the leaves: case analysis on `q` in `13` to `17`; the
modulus `14` carries no primitive character and each other modulus is its own leaf. -/
theorem book_count_band_above_one_mult_le_one_level_le_seventeen_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 13 ≤ q) (hhi : q ≤ 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  have hcases : q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
  rcases hcases with h | h | h | h | h
  · exact one17_thirteen χ hχ h
  · exact absurd hχ (one17_no_primitive_fourteen χ h)
  · exact one17_fifteen χ hχ h
  · exact one17_sixteen χ hχ h
  · exact one17_seventeen χ hχ h

end LeanLab.HelfgottMajor.ZeroCount1623
