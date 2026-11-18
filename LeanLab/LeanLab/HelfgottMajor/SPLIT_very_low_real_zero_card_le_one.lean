import LeanLab.HelfgottMajor.SPLIT_book_count_band_very_low_mult_le
import LeanLab.PNTPort.DirichletZF.SiegelSigns

/-!
# Split of `very_low_real_zero_card_le_one`

The target bounds by one the number of strip zeros of one primitive `L`-function whose
imaginary part vanishes, on the band `1 ≤ T`, `q * T ≤ 2πe`. Two features of the band matter.
The height enters only through `T ≥ 1`, which puts every real part in the open unit interval
below the truncation height, so the truncation itself is invisible. And the band bounds the
conductor, `q ≤ 2πe`, so only the finitely many `L`-functions of conductor at most seventeen
are consulted.

The count is cut along the character into three cases, each stated for a real argument instead
of for a finite set of points of the complex plane, and each keeping the band:

* `very_low_real_zero_modulus_one`: the conductor is one, so the `L`-function is the zeta
  function, which has no zero on the open unit interval of the real axis; the count is zero.
* `very_low_real_zero_real_valued`: the character takes real values and the conductor is at
  least two; two real arguments of the open unit interval at which the `L`-function vanishes
  are equal, so at most one point is counted.
* `very_low_real_zero_not_real_valued`: the character takes a value with non-zero imaginary
  part and the conductor is at least two; then the open unit interval carries no zero at all,
  and nothing is counted.

The transfer from the finite set of points to the real line is elementary and is carried out
below instead of being left as a leaf: a strip zero with vanishing imaginary part is the
coercion of its real part, so two such zeros with equal real parts coincide, and a finite set
whose elements are pairwise equal has at most one element.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Case of conductor one. On the band `1 ≤ T`, `q * T ≤ 2πe`, if the conductor is one
then the `L`-function is the zeta function, and the strip carries no zero of vanishing
imaginary part: the count of such zeros is empty. Nothing is assumed about zeros off the real
axis, and the statement is only about the one `L`-function of conductor one. -/
theorem very_low_real_zero_modulus_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) (hq : q = 1) :
    ∀ ρ ∈ stripZeros χ T, ρ.im = 0 → False := by
  intro ρ hρ him
  subst hq
  have hcast : ρ = ((ρ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have hL : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by
    rw [← hcast]
    exact hρ.1
  rw [DirichletCharacter.LFunction_modOne_eq] at hL
  have hneg := (LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg hρ.2.1 hρ.2.2.1).2
  rw [hL] at hneg
  simp at hneg

/-- LEAF. Case of a real valued character of conductor at least two. On the band `1 ≤ T`,
`q * T ≤ 2πe`, a primitive character taking only real values has at most one zero of the open
unit interval of the real axis: two real arguments there at which the `L`-function vanishes
are equal. The band is kept, so only conductors at most `2πe` are concerned. The multiplicity of
a zero and the position of the zeros off the real axis are not part of the statement. -/
theorem very_low_real_zero_real_valued (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    ∀ σ₁ σ₂ : ℝ, 0 < σ₁ → σ₁ < 1 → 0 < σ₂ → σ₂ < 1 →
      DirichletCharacter.LFunction χ (σ₁ : ℂ) = 0 →
      DirichletCharacter.LFunction χ (σ₂ : ℂ) = 0 → σ₁ = σ₂ := by
  sorry

/-- LEAF. Case of a character that is not real valued, of conductor at least two. On the band
`1 ≤ T`, `q * T ≤ 2πe`, a primitive character taking a value with non-zero imaginary part has
no zero at all on the open unit interval of the real axis: every real argument there at which
the `L`-function vanishes gives a contradiction. Nothing is assumed about zeros off the real
axis. -/
theorem very_low_real_zero_not_real_valued (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1)
    (hval : ∃ a : ZMod q, (χ a).im ≠ 0) :
    ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) = 0 → False := by
  sorry

/-- A point of the plane with vanishing imaginary part is the coercion of its real part. -/
private lemma eq_ofReal_re_of_im_eq_zero {ρ : ℂ} (him : ρ.im = 0) :
    ρ = ((ρ.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [him]

/-- A finite set of points all of whose elements are equal has at most one element, applied to
the strip zeros of vanishing imaginary part: two of them have the same real part, by the three
cases of the character, and then they coincide. -/
private lemma card_filter_im_eq_zero_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ₁ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im = 0),
      ∀ ρ₂ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im = 0), ρ₁ = ρ₂ := by
  classical
  intro ρ₁ h₁ ρ₂ h₂
  obtain ⟨h₁s, him₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨h₂s, him₂⟩ := Finset.mem_filter.mp h₂
  have hmem₁ : ρ₁ ∈ stripZeros χ T := (stripZeros_finite χ T).mem_toFinset.mp h₁s
  have hmem₂ : ρ₂ ∈ stripZeros χ T := (stripZeros_finite χ T).mem_toFinset.mp h₂s
  have hcast₁ : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero him₁
  have hcast₂ : ρ₂ = ((ρ₂.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero him₂
  have hL₁ : DirichletCharacter.LFunction χ ((ρ₁.re : ℝ) : ℂ) = 0 := by
    rw [← hcast₁]
    exact hmem₁.1
  have hL₂ : DirichletCharacter.LFunction χ ((ρ₂.re : ℝ) : ℂ) = 0 := by
    rw [← hcast₂]
    exact hmem₂.1
  have h0₁ : 0 < ρ₁.re := hmem₁.2.1
  have hlt₁ : ρ₁.re < 1 := hmem₁.2.2.1
  have h0₂ : 0 < ρ₂.re := hmem₂.2.1
  have hlt₂ : ρ₂.re < 1 := hmem₂.2.2.1
  by_cases hq : q = 1
  · exact (very_low_real_zero_modulus_one (q := q) χ hχ hT hband hq ρ₁ hmem₁ him₁).elim
  · by_cases hreal : ∀ a : ZMod q, (χ a).im = 0
    · have hre : ρ₁.re = ρ₂.re :=
        very_low_real_zero_real_valued (q := q) χ hχ hT hband hreal ρ₁.re ρ₂.re h0₁ hlt₁ h0₂ hlt₂ hL₁ hL₂
      rw [hcast₁, hcast₂, hre]
    · have hval : ∃ a : ZMod q, (χ a).im ≠ 0 := by
        by_contra h
        exact hreal fun a => by
          by_contra ha
          exact h ⟨a, ha⟩
      exact (very_low_real_zero_not_real_valued (q := q) χ hχ hT hband hval ρ₁.re h0₁ hlt₁ hL₁).elim

/-- Assembly: on the band `1 ≤ T`, `q * T ≤ 2πe`, the strip zeros of a primitive character
with vanishing imaginary part number at most one. Any two of them are equal by the three cases
of the character, and a finite set with pairwise equal elements has at most one element. -/
theorem very_low_real_zero_card_le_one_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ((stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im = 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  exact card_filter_im_eq_zero_le_one χ hχ hT hband

end LeanLab.HelfgottMajor.ZeroCount1623
