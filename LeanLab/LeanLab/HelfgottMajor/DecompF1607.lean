import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card

/-!
# Split of `book_count_band_above_one_mult_le_card_level_le_seventeen`, FREE-nv-minimax2 task1607

The target bounds the number of strip zeros of `L(·, χ)` whose imaginary part lies in
`(1, 2πe / q]` by one, for a primitive character `χ` of modulus `q` with `13 ≤ q ≤ 17`.
The band height `2πe / q` is at most `2πe / 13 < 1.32`, so the window is a very short
interval just above height `1`. The proof is a finite verification over the five possible
conductors, and each leaf handles one conductor. The assembly dispatches the five cases
with `omega`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Conductor thirteen: for a primitive character of modulus exactly `13` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 13]` number at most one, counted
without multiplicity. The window height is below `1.32`, so this is one finite check
over the primitive characters of conductor `13`. -/
theorem book_count_band_above_one_mult_le_card_level_thirteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 13) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Reduction of units of `ZMod 14` to units of `ZMod 7` is injective: a unit of `ZMod 14` is
odd, so two units with equal residues modulo `7` and both below `14` coincide. This is the
group-theoretic content of the absence of primitive characters of modulus `14`. -/
private lemma unitsMap_seven_fourteen_injective :
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

/-- There is no primitive character of modulus `14`: every character of that level factors
through level `7`, since the reduction of unit groups is an isomorphism, so its conductor is
at most `7`. -/
private lemma not_primitive_level_fourteen (χ : DirichletCharacter ℂ 14) : ¬ χ.IsPrimitive := by
  intro hχ
  have hFT : DirichletCharacter.FactorsThrough χ 7 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show 7 ∣ 14 by norm_num)]
    intro x hx
    have hx1 : x = 1 := unitsMap_seven_fourteen_injective (by rw [hx, map_one])
    simp [hx1]
  have hcond : χ.conductor ≤ 7 :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hFT)
  have hone : χ.conductor = 14 := (DirichletCharacter.isPrimitive_def χ).mp hχ
  omega

/-- LEAF. Conductor fourteen: for a primitive character of modulus exactly `14` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 14]` number at most one, counted
without multiplicity. The window height is below `1.23`, so this is one finite check
over the primitive characters of conductor `14`. -/
theorem book_count_band_above_one_mult_le_card_level_fourteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 14) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_level_fourteen χ)

/-- LEAF. Conductor fifteen: for a primitive character of modulus exactly `15` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 15]` number at most one, counted
without multiplicity. The window height is below `1.15`, so this is one finite check
over the primitive characters of conductor `15`. -/
theorem book_count_band_above_one_mult_le_card_level_fifteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 15) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Conductor sixteen: for a primitive character of modulus exactly `16` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 16]` number at most one, counted
without multiplicity. The window height is below `1.07`, so this is one finite check
over the primitive characters of conductor `16`. -/
theorem book_count_band_above_one_mult_le_card_level_sixteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Conductor seventeen: for a primitive character of modulus exactly `17` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 17]` number at most one, counted
without multiplicity. The window height is below `1.01`, the shortest of the five blocks,
so this is one finite check over the primitive characters of conductor `17`. -/
theorem book_count_band_above_one_mult_le_card_level_seventeen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Assembly of the split, FREE-nv-minimax2 task1607. The statement of
`book_count_band_above_one_mult_le_card_level_le_seventeen` character for character,
proved from the five conductor leaves with no gap of its own: the modulus `q` lies in
`{13, 14, 15, 16, 17}`, and each case is dispatched to its leaf. -/
theorem book_count_band_above_one_mult_le_card_level_le_seventeen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq13 : 13 ≤ q) (hq17 : q ≤ 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have h_cases : q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl
  · exact book_count_band_above_one_mult_le_card_level_thirteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_fourteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_fifteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_sixteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_seventeen_F1607 χ hχ rfl

end LeanLab.HelfgottMajor.ZeroCount1623
