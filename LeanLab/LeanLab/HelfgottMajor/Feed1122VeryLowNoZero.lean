import LeanLab.HelfgottMajor.SPLIT_book_count_band_very_low_mult_le

/-!
# `very_low_no_zero_of_im_pos_le_one` is FALSE; repaired split, burst 20261122

The target, in `SPLIT_book_count_band_very_low_mult_le`, says that on the band `1 ≤ T`,
`q * T ≤ 2πe` a strip zero of a primitive `L`-function with positive imaginary part has
imaginary part above `1`. It is FALSE. Counterexample: `q = 13`, `T = 1`, which is on the
band since `13 ≤ 2πe ≈ 17.08`, and `χ` the odd primitive character of order `12` modulo `13`
with `χ(2) = exp(5πi/6)`. Its `L`-function has a simple zero at `ρ ≈ 1/2 + 0.883960309509930 i`,
found by mpmath at 40 digits from the Hurwitz zeta formula `L(s, χ) = 13^(-s) Σ χ(a) ζ(s, a/13)`,
with `|L(ρ)| < 10^(-41)` and winding number `1` around a circle of radius `0.01`; a second
independent run through `mpmath.dirichlet` gives the same zero and winding number `1` on the
boundary of `[0,1] × [10^(-6), 1]`. So `ρ ∈ stripZeros χ 1`, `0 < Im ρ`, and `Im ρ ≤ 1`.
This is a numerical counterexample; no Lean refutation is given here, since it needs a rigorous
enclosure of a complex zero.

What survives: for every other conductor up to `17` the argument principle check on the boundary
of `[0,1] × [10^(-6), 1]` gives winding number `0`, so the statement with the extra hypothesis
`q ≠ 13` is numerically supported. This file proves that repaired statement from per conductor
leaves. The parent `book_count_band_very_low_mult_le` may still hold, since the conductor `13`
zero is simple and alone in the box and the real axis carries no zero, giving a sum of exactly
`1`; that needs a separate conductor `13` leaf and is not attempted here.

The source of the low zero facts in Helfgott, Major arcs for Goldbach's problem, arXiv
1305.2897v4, is Section 4.6, page 56, "A verification of zeros and its consequences", which
takes as input Platt's rigorous interval arithmetic computation for every primitive
`L`-function of small conductor, thesis [Pla11] and preprint [Plab]. The count `N(T, χ)` of
display 4.26 on page 38 is the set `stripZeros`.

Leaves: one per conductor `k ∈ {1, 3, 4, 5, 7, 8, 9, 11, 12, 15, 16, 17}`, each a rigorous zero
free rectangle `(0,1) × (0,1]` check. `not_isPrimitive_of_two_mod_four`, for the moduli
`2, 6, 10, 14`, is PROVED here. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122VeryLowNoZero
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 1. HARD.
The Riemann zeta function has no zero `ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 1`; its lowest
nontrivial zero has height about `14.13`. -/
theorem noLowZero_level_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 1) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 3. HARD.
The primitive character of conductor `3` has no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_three (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 3) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 4. HARD.
The primitive character of conductor `4` has no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_four (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 4) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 5. HARD.
The three primitive characters of conductor `5` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_five (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 5) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 7. HARD.
The five primitive characters of conductor `7` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_seven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 7) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 8. HARD.
The two primitive characters of conductor `8` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_eight (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 8) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 9. HARD.
The four primitive characters of conductor `9` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_nine (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 9) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 11. HARD.
The nine primitive characters of conductor `11` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_eleven (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 11) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 12. HARD.
The primitive character of conductor `12` has no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_twelve (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 12) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 15. HARD.
The primitive characters of conductor `15` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_fifteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 15) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 16. HARD.
The primitive characters of conductor `16` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_sixteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 16) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- LEAF: Section 4.6 page 56 of arXiv 1305.2897v4, Platt's verification [Pla11], conductor 17. HARD.
The fifteen primitive characters of conductor `17` have no zero in `(0,1) × (0,1]`. -/
theorem noLowZero_level_seventeen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- A character of modulus `n` is not primitive when reduction of unit groups from `n` to a
proper divisor `m` is injective: the character then factors through `m`, so its conductor is at
most `m < n`. This is the argument of `DecompF1607` for modulus `14`. -/
private lemma not_isPrimitive_of_unitsMap_injective {n m : ℕ} [NeZero n] (hmn : m ∣ n)
    (hlt : m < n) (hinj : Function.Injective (ZMod.unitsMap hmn))
    (χ : DirichletCharacter ℂ n) : ¬ χ.IsPrimitive := by
  intro hχ
  have hFT : DirichletCharacter.FactorsThrough χ m := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hmn]
    intro x hx
    have hx1 : x = 1 := hinj (by rw [hx, map_one])
    simp [hx1]
  have hcond : χ.conductor ≤ m :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hFT)
  have hone : χ.conductor = n := (DirichletCharacter.isPrimitive_def χ).mp hχ
  omega

/-- Injectivity of reduction of unit groups from `n` to `m` from a statement about residues:
two numbers below `n` coprime to `n` with equal residues modulo `m` coincide. -/
private lemma unitsMap_injective_of_nat {n m : ℕ} [NeZero n] (hmn : m ∣ n)
    (hres : ∀ a, a < n → ∀ b, b < n → Nat.Coprime a n → Nat.Coprime b n → a % m = b % m →
      a = b) :
    Function.Injective (ZMod.unitsMap hmn) := by
  intro a b hab
  have hcast : ((a : ZMod n).cast : ZMod m) = ((b : ZMod n).cast : ZMod m) := by
    have h := congrArg (fun u : (ZMod m)ˣ => ((u : ZMod m))) hab
    simpa only [ZMod.unitsMap_val] using h
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at hcast
  have hmod : a.val.val % m = b.val.val % m := by
    rw [← ZMod.natCast_eq_natCast_iff']
    exact hcast
  have hcopa : Nat.Coprime a.val.val n := by
    have hu : IsUnit ((a.val.val : ZMod n)) := by
      rw [ZMod.natCast_zmod_val]
      exact a.isUnit
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  have hcopb : Nat.Coprime b.val.val n := by
    have hu : IsUnit ((b.val.val : ZMod n)) := by
      rw [ZMod.natCast_zmod_val]
      exact b.isUnit
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  have hvals : a.val.val = b.val.val :=
    hres _ (ZMod.val_lt _) _ (ZMod.val_lt _) hcopa hcopb hmod
  exact Units.ext (ZMod.val_injective n hvals)

/-- No modulus `≡ 2 mod 4` up to `17` is a conductor: for `q ∈ {2, 6, 10, 14}` reduction of
unit groups from `q` to `q / 2` is injective, since units of `ZMod q` are odd, checked by
`decide` on residues, so every character of modulus `q` factors through `q / 2`. This is the
classical fact used tacitly in Section 4.6 of arXiv 1305.2897v4 when Platt's verification is
indexed by conductor. -/
theorem not_isPrimitive_of_two_mod_four (χ : DirichletCharacter ℂ q)
    (hq : q = 2 ∨ q = 6 ∨ q = 10 ∨ q = 14) : ¬ χ.IsPrimitive := by
  rcases hq with rfl | rfl | rfl | rfl
  · exact not_isPrimitive_of_unitsMap_injective (show 1 ∣ 2 by norm_num) (by norm_num)
      (unitsMap_injective_of_nat _ (by decide)) χ
  · exact not_isPrimitive_of_unitsMap_injective (show 3 ∣ 6 by norm_num) (by norm_num)
      (unitsMap_injective_of_nat _ (by decide)) χ
  · exact not_isPrimitive_of_unitsMap_injective (show 5 ∣ 10 by norm_num) (by norm_num)
      (unitsMap_injective_of_nat _ (by decide)) χ
  · exact not_isPrimitive_of_unitsMap_injective (show 7 ∣ 14 by norm_num) (by norm_num)
      (unitsMap_injective_of_nat _ (by decide)) χ

/-- Assembly of the REPAIRED statement: `very_low_no_zero_of_im_pos_le_one` with the extra
hypothesis `q ≠ 13`. On the band `1 ≤ T`, `q * T ≤ 2πe`, for a primitive character of modulus
other than `13`, every strip zero with positive imaginary part has imaginary part above `1`.
The band forces `q ≤ 17`, and the conductor leaves cover each remaining modulus. The original
statement without `q ≠ 13` is FALSE, see the module doc. -/
theorem very_low_no_zero_of_im_pos_le_one_of_ne_thirteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h13 : q ≠ 13)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ ∈ stripZeros χ T, 0 < ρ.im → 1 < ρ.im := by
  intro ρ hρ him
  have hq17 : q ≤ 17 := LeanLab.HelfgottMajor.RealAxisKernel.modulus_le_seventeen_of_band hT hband
  have hq0 : q ≠ 0 := NeZero.ne q
  have key : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → 1 < ρ.im := by
    have hcases : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨
        q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact noLowZero_level_one χ hχ h
    · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inl h))
    · exact noLowZero_level_three χ hχ h
    · exact noLowZero_level_four χ hχ h
    · exact noLowZero_level_five χ hχ h
    · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inr (Or.inl h)))
    · exact noLowZero_level_seven χ hχ h
    · exact noLowZero_level_eight χ hχ h
    · exact noLowZero_level_nine χ hχ h
    · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inr (Or.inr (Or.inl h))))
    · exact noLowZero_level_eleven χ hχ h
    · exact noLowZero_level_twelve χ hχ h
    · exact absurd h h13
    · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inr (Or.inr (Or.inr h))))
    · exact noLowZero_level_fifteen χ hχ h
    · exact noLowZero_level_sixteen χ hχ h
    · exact noLowZero_level_seventeen χ hχ h
  exact key ρ hρ.1 hρ.2.1 hρ.2.2.1 him

end LeanLab.HelfgottMajor.Feed1122VeryLowNoZero


