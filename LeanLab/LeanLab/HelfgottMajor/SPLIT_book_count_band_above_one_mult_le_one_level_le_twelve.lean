import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le

/-!
# Split of `book_count_band_above_one_mult_le_one_level_le_twelve`

The parent block covers the conductors `7` to `12` at the top height `2πe / q` of the band.
It is split by modulus, the same pattern as the proved split of the block `2` to `6`.

* `q = 10`: there is no primitive character modulo `10`, since `(ZMod 10)ˣ → (ZMod 5)ˣ` is injective, so every character modulo `10` factors through modulus `5`. Proved here, no input.
* the remaining moduli `7`, `8`, `9`, `11`, `12`: one LEAF each, the parent conclusion restricted to that one modulus, a finite certified zero verification of the primitive `L`-functions of that conductor on one short window.

The assembly is the case analysis on `q`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Reduction of units of `ZMod 10` to units of `ZMod 5` is injective: a unit of `ZMod 10` is
odd, so two units with equal residues modulo `5` and both below `10` coincide. Proved, no
input. -/
private lemma one12_unitsMap_five_ten_injective :
    Function.Injective (ZMod.unitsMap (show 5 ∣ 10 by norm_num)) := by
  intro a b hab
  have hcast : ((a : ZMod 10).cast : ZMod 5) = ((b : ZMod 10).cast : ZMod 5) := by
    have h := congrArg (fun u : (ZMod 5)ˣ => ((u : ZMod 5))) hab
    simpa only [ZMod.unitsMap_val] using h
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at hcast
  have hmod : a.val.val % 5 = b.val.val % 5 := by
    rw [← ZMod.natCast_eq_natCast_iff']
    exact hcast
  have halt : a.val.val < 10 := ZMod.val_lt _
  have hblt : b.val.val < 10 := ZMod.val_lt _
  have hcopa : Nat.Coprime a.val.val 10 := by
    have hu : IsUnit ((a.val.val : ZMod 10)) := by
      rw [ZMod.natCast_zmod_val]
      exact a.isUnit
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  have hcopb : Nat.Coprime b.val.val 10 := by
    have hu : IsUnit ((b.val.val : ZMod 10)) := by
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
  exact Units.ext (ZMod.val_injective 10 hvals)

/-- No primitive character modulo `10`: every character of that modulus factors through
modulus `5`, since the reduction of unit groups is injective, so its conductor is at most `5`.
Proved, no input. -/
theorem one12_no_primitive_ten (χ : DirichletCharacter ℂ q) (hq : q = 10) : ¬ χ.IsPrimitive := by
  subst hq
  intro hχ
  have hFT : DirichletCharacter.FactorsThrough χ 5 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show 5 ∣ 10 by norm_num)]
    intro x hx
    have hx1 : x = 1 := one12_unitsMap_five_ten_injective (by rw [hx, map_one])
    simp [hx1]
  have hcond : χ.conductor ≤ 5 :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hFT)
  have hone : χ.conductor = 10 := (DirichletCharacter.isPrimitive_def χ).mp hχ
  omega

/-- LEAF: modulus `7` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `7`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 7]` has multiplicity at most one. The window height `2πe / 7` is below `2.45`, so
this is one finite check over the primitive characters of conductor `7`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one12_seven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 7) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: modulus `8` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `8`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 8]` has multiplicity at most one. The window height `2πe / 8` is below `2.14`, so
this is one finite check over the primitive characters of conductor `8`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one12_eight (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 8) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: modulus `9` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `9`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 9]` has multiplicity at most one. The window height `2πe / 9` is below `1.90`, so
this is one finite check over the primitive characters of conductor `9`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one12_nine (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 9) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: modulus `11` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `11`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 11]` has multiplicity at most one. The window height `2πe / 11` is below `1.56`, so
this is one finite check over the primitive characters of conductor `11`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one12_eleven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 11) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: modulus `12` case of the conductor block of the band split, Helfgott, The ternary
Goldbach problem, the finite low height zero verification behind the band bound: for a primitive
character of modulus exactly `12`, every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 12]` has multiplicity at most one. The window height `2πe / 12` is below `1.43`, so
this is one finite check over the primitive characters of conductor `12`, a certified zero
verification of those `L`-functions on one short rectangle, argument principle or Turing method.
Class HARD. -/
theorem one12_twelve (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 12) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Assembly of `book_count_band_above_one_mult_le_one_level_le_twelve` from the leaves: case analysis on `q` in `7` to `12`; the
modulus `10` carries no primitive character and each other modulus is its own leaf. -/
theorem book_count_band_above_one_mult_le_one_level_le_twelve_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 7 ≤ q) (hhi : q ≤ 12) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  have hcases : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 := by omega
  rcases hcases with h | h | h | h | h | h
  · exact one12_seven χ hχ h
  · exact one12_eight χ hχ h
  · exact one12_nine χ hχ h
  · exact absurd hχ (one12_no_primitive_ten χ h)
  · exact one12_eleven χ hχ h
  · exact one12_twelve χ hχ h

end LeanLab.HelfgottMajor.ZeroCount1623
