/-
P0069, pages 11 and 12, reduction of a finite twisted polynomial to its primitive character.
These are elementary preparation steps for display 3.3, not the hybrid mean value estimate.
The Montgomery analytic proof is not available in the checked sources.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.Decomp492a
open Classical Complex MeanSquareC165

/-- Pages 11 and 12, auxiliary primitive reduction. A character is its primitive character
on indices coprime to the full modulus, and zero at the other indices.
Uses Mathlib primitiveCharacter_apply_of_isCoprime and apply_eq_zero_iff. -/
theorem character_eq_primitive_mask {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ (n : ZMod q) =
      if n.Coprime q then χ.primitiveCharacter (n : ZMod χ.conductor) else 0 := by
  split_ifs with hn
  · simpa only [Int.cast_natCast] using
      (χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime).symm
  · simpa only [Int.cast_natCast] using
      (χ.apply_eq_zero_iff (n : ℤ)).mpr (by simpa only [Nat.isCoprime_iff_coprime] using hn)

/-- Pages 11 and 12, auxiliary primitive reduction. Removing coefficients not coprime to q
preserves the existing divisor bound with the same exponent. -/
theorem coeffBound_coprime_mask {q : ℕ} {a : ℕ → ℂ} {B : ℝ}
    (ha : Thm4.CoeffBound a B) :
    Thm4.CoeffBound (fun n => if n.Coprime q then a n else 0) B := by
  intro n
  dsimp only
  split_ifs with hn
  · exact ha n
  · simp only [norm_zero]
    positivity

/-- Pages 11 and 12, auxiliary primitive reduction. Removing coefficients not coprime to q
can only decrease the coefficient energy G. -/
theorem energy_coprime_mask_le (q : ℕ) (a : ℕ → ℂ) (c1 c2 F : ℝ) :
    energy (fun n => if n.Coprime q then a n else 0) c1 c2 F ≤ energy a c1 c2 F := by
  apply Finset.sum_le_sum
  intro n hn
  dsimp only
  split_ifs with h
  · exact le_rfl
  · simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    positivity

/-- Pages 11 and 12, auxiliary primitive reduction. The polynomial twisted by an arbitrary
character equals the polynomial twisted by its primitive character after the full-modulus
coprimality mask is applied to the coefficients. No analytic estimate is used. -/
theorem dirPoly_eq_primitive_mask {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (c1 c2 F : ℝ) (s : ℂ) :
    Thm4.dirPoly a c1 c2 F χ s =
      Thm4.dirPoly (fun n => if n.Coprime q then a n else 0)
        c1 c2 F χ.primitiveCharacter s := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [character_eq_primitive_mask]
  dsimp only
  split_ifs <;> simp_all

/-- BHP page 11, displays 3.3 and 3.4, auxiliary zero energy case.
On a support bounded below by a positive number, zero energy forces the entire polynomial
at every complex point to vanish. -/
theorem dirPoly_eq_zero_of_energy_eq_zero {a : ℕ → ℂ} {c1 c2 F : ℝ}
    (hlo : 0 < c1 * F) (henergy : energy a c1 c2 F = 0)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Thm4.dirPoly a c1 c2 F χ s = 0 := by
  classical
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun n (_ : n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
      (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)) =>
      show 0 ≤ ‖a n‖ ^ 2 / (n : ℝ) by positivity)).mp henergy
  apply Finset.sum_eq_zero
  intro n hn
  have hnpos : 0 < (n : ℝ) := hlo.trans (Finset.mem_filter.mp hn).2.1
  have hz : ‖a n‖ ^ 2 = 0 :=
    (div_eq_zero_iff.mp (hterms n hn)).resolve_right hnpos.ne'
  have ha : a n = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  simp [ha]

/-- BHP page 11, display 3.4, auxiliary zero energy case with the required positive threshold.
A set on which every polynomial value has norm at least V is empty when G is zero and V is
positive. No cited analytic estimate is used. -/
theorem large_values_empty_of_zero_energy {a : ℕ → ℂ} {c1 c2 F V : ℝ}
    (hlo : 0 < c1 * F) (henergy : energy a c1 c2 F = 0) (hV : 0 < V)
    {q : ℕ} (S : Finset (ℝ × DirichletCharacter ℂ q))
    (hpoint : ∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := hpoint p hp
  rw [dirPoly_eq_zero_of_energy_eq_zero hlo henergy, norm_zero] at h
  exact (not_le_of_gt hV) h

/-- BHP pages 11 and 12, auxiliary primitive reduction. Keeping the conductor together with
the primitive character loses no character of a fixed positive modulus. -/
theorem conductor_primitive_injective {q : ℕ} [NeZero q] :
    Function.Injective (fun χ : DirichletCharacter ℂ q =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ d : ℕ, DirichletCharacter ℂ d)) := by
  intro χ ψ h
  have heval (n : ℕ) : χ.primitiveCharacter (n : ZMod χ.conductor) =
      ψ.primitiveCharacter (n : ZMod ψ.conductor) :=
    congrArg (fun p : Σ d : ℕ, DirichletCharacter ℂ d => p.2 (n : ZMod p.1)) h
  apply MulChar.ext'
  intro x
  rw [← ZMod.natCast_zmod_val x, character_eq_primitive_mask χ x.val,
    character_eq_primitive_mask ψ x.val]
  split_ifs
  · exact heval x.val
  · rfl

/-- BHP pages 11 and 12, auxiliary primitive reduction at the square-sum level.
The same full-modulus mask is used for every conductor. The image is injective, so this
reindexing preserves the sampling cardinality and gives equality without a divisor loss. -/
theorem square_sum_eq_primitive {q : ℕ} [NeZero q]
    (S : Finset (ℝ × DirichletCharacter ℂ q)) (a : ℕ → ℂ) (c1 c2 F : ℝ) :
    (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ 2) =
      ∑ p ∈ S.image (fun p =>
          (p.1, (⟨p.2.conductor, p.2.primitiveCharacter⟩ : Σ d : ℕ, DirichletCharacter ℂ d))),
        ‖Thm4.dirPoly (fun n => if n.Coprime q then a n else 0)
          c1 c2 F p.2.2 (Thm4.half p.1)‖ ^ 2 := by
  classical
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [dirPoly_eq_primitive_mask]
  · intro p hp r hr h
    have h1 : p.1 = r.1 :=
      congrArg (fun u : ℝ × (Σ d : ℕ, DirichletCharacter ℂ d) => u.1) h
    have h2 : (⟨p.2.conductor, p.2.primitiveCharacter⟩ : Σ d : ℕ, DirichletCharacter ℂ d) =
        ⟨r.2.conductor, r.2.primitiveCharacter⟩ :=
      congrArg (fun u : ℝ × (Σ d : ℕ, DirichletCharacter ℂ d) => u.2) h
    exact Prod.ext h1 (conductor_primitive_injective h2)

end LeanLab.BHP1997.Decomp492a



