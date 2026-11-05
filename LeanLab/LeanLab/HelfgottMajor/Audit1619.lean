import LeanLab.HelfgottMajor.DecompJ1124

/-!
U-1619 audit of HelfgottMajor/DecompJ1124 `explicit_formula_remainder_E`, filed FALSE by
omos_tick 20261105T0544Z, and of its repair.
AI wrote this Lean code. Binary Goldbach is open.

What is proved here:
* `exists_ball_escape`: any point can be pushed out of a ball by a free R of norm B.
* `leafE_forbids_zero_hypothesis`: the leaf contradicts `hzeros` at every primitive character.
  So the leaf is refuted in Lean only relative to one instance of `hzeros`.
* `not_leafE_of_zeta100`: the leaf is false if every zero of zeta with 0 < Re < 1 and |Im| <= 100
  has Re = 1/2. That input is a known numerical fact and is NOT formalized in the lab or in Mathlib.
  So this is a CONDITIONAL refutation, not a proved FALSE.
* `exists_ball_split` and `assembly_iff_bound`: the assembly's conclusion is equivalent to the
  repaired leaf, a plain bound on the norm, and the assembly closes from it.
-/

namespace LeanLab.HelfgottMajor.Audit1619
open Real LeanLab.HelfgottArcs Decomp123 Decomp269a DecompJ1124

/-- The statement of the leaf `explicit_formula_remainder_E`, verbatim. -/
def LeafE : Prop :=
  ∀ (x : ℝ) (_ : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (_ : χ.IsPrimitive) (δ T : ℝ)
    (_ : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (_ : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) (R : ℂ) (_ : ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695),
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
      (log q + 6.01) * (1 + 6 * |δ|) / sqrt x

/-- A free R of norm B pushes any point out to norm at least B. -/
theorem exists_ball_escape (A : ℂ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R : ℂ, ‖R‖ ≤ B ∧ B ≤ ‖A + R‖ := by
  by_cases hA : A = 0
  · refine ⟨(B : ℂ), ?_, ?_⟩ <;> simp [hA, abs_of_nonneg hB]
  · have hn : 0 < ‖A‖ := norm_pos_iff.mpr hA
    refine ⟨((B / ‖A‖ : ℝ) : ℂ) * A, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
      exact le_rfl
    · have he : A + ((B / ‖A‖ : ℝ) : ℂ) * A = ((1 + B / ‖A‖ : ℝ) : ℂ) * A := by
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have : (1 + B / ‖A‖) * ‖A‖ = ‖A‖ + B := by field_simp
      rw [this]
      linarith

/-- The leaf contradicts the zero hypothesis at every primitive character: at the instance,
take x so large that the right side is below 1 and R aligned with the rest. -/
theorem leafE_forbids_zero_hypothesis (h : LeafE) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) : False := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : 0 ≤ log q := Real.log_nonneg hq
  set C₀ : ℝ := (log q + 6.01) * (1 + 6 * |δ|) with hC₀
  have hC0 : 0 ≤ C₀ := by positivity
  set x : ℝ := (C₀ + 1) ^ 2 with hx
  have hx1 : 1 ≤ x := by rw [hx]; nlinarith
  have hsq : sqrt x = C₀ + 1 := by rw [hx]; exact Real.sqrt_sq (by linarith)
  set B : ℝ := 3 * log q + 13.347 * |δ| + 16.695 with hB
  have hB0 : 16.695 ≤ B := by rw [hB]; have := abs_nonneg δ; nlinarith
  set A : ℂ := Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T with hA
  obtain ⟨R, hR, hesc⟩ := exists_ball_escape A (by linarith : 0 ≤ B)
  have hle := h x hx1 q χ hχ δ T hT hzeros R hR
  rw [← hC₀, hsq] at hle
  have hlt : C₀ / (C₀ + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

/-- The refutation at modulus 1, CONDITIONAL on the zeros of zeta up to height 100 lying on the
line, a hypothesis no lab or Mathlib theorem supplies. -/
theorem not_leafE_of_zeta100
    (h100 : ∀ s : ℂ, DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 →
      0 < s.re → s.re < 1 → |s.im| ≤ 100 → s.re = 1 / 2) : ¬ LeafE := fun h =>
  leafE_forbids_zero_hypothesis h 1 1 DirichletCharacter.isPrimitive_one_level_one 0 100
    (by simp) h100

/-- A point of norm at most B + C is within C of a point of the B ball. -/
theorem exists_ball_split (A : ℂ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (h : ‖A‖ ≤ B + C) :
    ∃ R : ℂ, ‖R‖ ≤ B ∧ ‖A + R‖ ≤ C := by
  by_cases hAB : ‖A‖ ≤ B
  · exact ⟨-A, by simpa using hAB, by simpa using hC⟩
  · have hlt : B < ‖A‖ := not_le.mp hAB
    have hn : 0 < ‖A‖ := by linarith
    refine ⟨((-(B / ‖A‖) : ℝ) : ℂ) * A, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      field_simp
      exact le_rfl
    · have he : A + ((-(B / ‖A‖) : ℝ) : ℂ) * A = ((1 - B / ‖A‖ : ℝ) : ℂ) * A := by
        push_cast
        ring
      have hfrac : B / ‖A‖ ≤ 1 := by
        rw [div_le_one hn]
        exact hlt.le
      rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have : (1 - B / ‖A‖) * ‖A‖ = ‖A‖ - B := by field_simp
      rw [this]
      linarith

/-- The assembly's existential is equivalent to the plain norm bound, so the repaired leaf loses
nothing and also says nothing beyond the assembly. -/
theorem assembly_iff_bound (A : ℂ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∃ R : ℂ, ‖R‖ ≤ B ∧ ‖A + R‖ ≤ C) ↔ ‖A‖ ≤ B + C := by
  refine ⟨?_, exists_ball_split A hB hC⟩
  rintro ⟨R, hR, hAR⟩
  have : ‖A‖ ≤ ‖A + R‖ + ‖R‖ := by
    simpa using norm_sub_le (A + R) R
  linarith

/-- The proposed repaired leaf, stated here as a Prop only. -/
def RepairedLeafE : Prop :=
  ∀ (x : ℝ) (_ : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (_ : χ.IsPrimitive) (δ T : ℝ)
    (_ : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (_ : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2),
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      (3 * log q + 13.347 * |δ| + 16.695) + (log q + 6.01) * (1 + 6 * |δ|) / sqrt x

/-- The assembly `explicit_formula_remainder`, character for character, from the repaired leaf.
So the repair leaves the target statement unchanged and the assembly closes. -/
theorem assembly_of_repairedLeafE (hE : RepairedLeafE)
    (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : 0 ≤ log q := Real.log_nonneg hq
  exact exists_ball_split _ (by have := abs_nonneg δ; positivity) (by positivity)
    (hE x hx q χ hχ δ T hT hzeros)

/-- `explicit_formula_remainder_R` is closed by R = 0, so that leaf says nothing. -/
theorem R_leaf_hollow (q : ℕ) [NeZero q] (δ : ℝ) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : 0 ≤ log q := Real.log_nonneg hq
  exact ⟨0, by simp only [norm_zero]; positivity⟩

end LeanLab.HelfgottMajor.Audit1619

#print axioms LeanLab.HelfgottMajor.Audit1619.leafE_forbids_zero_hypothesis
#print axioms LeanLab.HelfgottMajor.Audit1619.not_leafE_of_zeta100
#print axioms LeanLab.HelfgottMajor.Audit1619.assembly_iff_bound
#print axioms LeanLab.HelfgottMajor.Audit1619.assembly_of_repairedLeafE
#print axioms LeanLab.HelfgottMajor.Audit1619.R_leaf_hollow
