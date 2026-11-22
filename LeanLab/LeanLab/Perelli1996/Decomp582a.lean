/-
Perelli 1996, pages 484, 485 and 487, equations 18 through 25 and 31 through 32.
Supply the shorter window through explicit character and density inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Definitions582
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanLab.PNTPort.DirichletZF.U1482Jensen
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import LeanLab.PNTPort.LargeSieve.Multiplicative
import LeanLab.PNTPort.BV.Helpers
import LeanLab.Perelli1996.Ramanujan103
import LeanLab.Perelli1996.Decomp582b

namespace LeanLab.Perelli1996.Decomp582a
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp289a
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 484 below equation 15. The character sum W with the existing inclusive
zero endpoint and the unweighted geometric principal kernel. -/
def twistedRemainder (M : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  (∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
    if χ = 1 then Kernel.T 0 (M + 1) η else 0

/-- Page 487 equation 31. The normalized character energy for one modulus.
The normalization is q divided by phi q. -/
def characterEnergy (M q : ℕ) (Q : ℝ) : ℝ :=
  (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q,
    ∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
      ‖twistedRemainder M χ η‖ ^ 2

/-- Page 484 definition of W. Each finite character remainder is continuous. -/
theorem continuous_twistedRemainder (M : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (twistedRemainder M χ) := by
  classical
  unfold twistedRemainder
  split_ifs <;> simp only [Kernel.T, Kernel.e] <;> fun_prop

/-- Page 487 equation 31. The normalized character energy is nonnegative. -/
theorem characterEnergy_nonneg (M q : ℕ) (Q : ℝ) : 0 ≤ characterEnergy M q Q := by
  unfold characterEnergy
  positivity

/-- Pages 484 and 487. At modulus one the two inclusive remainders agree exactly. -/
theorem twistedRemainder_one (M : ℕ) (η : ℝ) :
    twistedRemainder M (1 : DirichletCharacter ℂ 1) η =
      characterRemainder M 1 0 η := by
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    have hz : (n : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hz]
    exact map_one _
  simp [twistedRemainder, characterRemainder, primeSum, hχ]

/-- Page 484 definition of W, inclusive endpoint variant.
At cutoff zero the principal remainder is minus one. -/
theorem twistedRemainder_zero (η : ℝ) : twistedRemainder 0 (1 : DirichletCharacter ℂ 1) η = -1 := by
  simp [twistedRemainder, Kernel.T, Kernel.e]

/-- Pages 484 and 487, character expansion for equation 31.
Group the prime coefficients by residue and subtract the uniform principal coefficient. -/
def residueCoefficient (M q : ℕ) (η : ℝ) (b : ZMod q) : ℂ :=
  (∑ n ∈ range (M + 1),
    if (n : ZMod q) = b then (Λ n : ℂ) * Kernel.e ((n : ℝ) * η) else 0) -
      Kernel.T 0 (M + 1) η / (q.totient : ℂ)

/-- Pages 484 and 487, character expansion for equation 31.
The multiplicative transform of the residue coefficients equals W exactly. -/
theorem character_transform (M q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (η : ℝ) :
    (∑ b : ZMod q, χ b * residueCoefficient M q η b) =
      twistedRemainder M χ η := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hfinite :
      (∑ b : ZMod q, χ b * ∑ n ∈ range (M + 1),
        if (n : ZMod q) = b then (Λ n : ℂ) * Kernel.e ((n : ℝ) * η) else 0) =
      ∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η) := by
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp [mul_comm, mul_assoc]
  have hprincipal : (∑ b : ZMod q, χ b *
      (Kernel.T 0 (M + 1) η / (q.totient : ℂ))) =
      if χ = 1 then Kernel.T 0 (M + 1) η else 0 := by
    rw [← Finset.sum_mul]
    by_cases hχ : χ = 1
    · subst χ
      rw [ite_eq_left rfl, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
      field_simp
    · rw [ite_eq_right hχ, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]
  unfold residueCoefficient twistedRemainder
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hfinite, hprincipal]

/-- Page 487 equation 31. Character Parseval for the centered residue coefficients.
This uses the existing finite character Parseval theorem from PNTPort. -/
theorem character_parseval (M q : ℕ) [NeZero q] (η : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, ‖twistedRemainder M χ η‖ ^ 2) =
      q.totient * ∑ b : ZMod q,
        if IsUnit b then ‖residueCoefficient M q η b‖ ^ 2 else 0 := by
  simp_rw [← character_transform M q]
  exact LeanLab.PNTPort.LargeSieve.sum_chars_normSq _

/-- Page 487 equation 31. The normalized character energy equals the
integrated squared centered residue coefficients with factor q. -/
theorem characterEnergy_eq_residue (M q : ℕ) [NeZero q] (Q : ℝ) :
    characterEnergy M q Q = (q : ℝ) *
      ∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
        ∑ b : ZMod q, if IsUnit b then ‖residueCoefficient M q η b‖ ^ 2 else 0 := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  unfold characterEnergy
  rw [← integral_finsetSum]
  · simp_rw [character_parseval]
    rw [integral_const_mul]
    field_simp
  · intro χ hχ
    exact ((continuous_twistedRemainder M χ).norm.pow 2).integrableOn_Icc

/-- Page 487 equation 31, derived finite additive normalization.
The complete residue transform has squared norm q times the coefficient energy.
This is the finite additive Parseval step used before restricting the numerator to units. -/
theorem additive_parseval {q : ℕ} [NeZero q] (S : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ b : ZMod q, S b * ZMod.stdAddChar (a * b)‖ ^ 2) =
      q * ∑ b : ZMod q, ‖S b‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.ofReal_pow, LeanLab.PNTPort.LargeSieve.ofReal_normSq_sum]
  have hexp : ∀ a x y : ZMod q,
      S x * ZMod.stdAddChar (a * x) *
        (starRingEnd ℂ) (S y * ZMod.stdAddChar (a * y)) =
      S x * (starRingEnd ℂ) (S y) * ZMod.stdAddChar (a * (x - y)) := by
    intro a x y
    rw [(starRingEnd ℂ).map_mul, LeanLab.PNTPort.LargeSieve.conj_stdAddChar, mul_sub, sub_eq_add_neg,
      AddChar.map_add_eq_mul]
    ring
  simp_rw [hexp]
  rw [sum_comm]
  refine (sum_congr rfl (fun x _ => sum_comm)).trans ?_
  have hsum : ∀ x y : ZMod q,
      (∑ a : ZMod q, S x * (starRingEnd ℂ) (S y) * ZMod.stdAddChar (a * (x - y))) =
      if x = y then (q : ℂ) * (S x * (starRingEnd ℂ) (S x)) else 0 := by
    intro x y
    rw [← mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
    by_cases hxy : x = y
    · rw [ite_eq_left (sub_eq_zero.mpr hxy), ite_eq_left hxy, hxy]; ring
    · rw [ite_eq_right (fun h => hxy (sub_eq_zero.mp h)), ite_eq_right hxy, Nat.cast_zero, mul_zero]
  simp_rw [hsum, sum_ite_eq, mem_univ, ite_true]
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
  rw [mul_sum]

/-- Pages 484 and 487, finite expansion for equation 31.
The unit residue transform equals the coprime prime sum minus its principal kernel. -/
theorem residue_fourier_eq (M q a : ℕ) [NeZero q]
    (hcop : Nat.Coprime q a) (η : ℝ) :
    (∑ b : ZMod q, (if IsUnit b then residueCoefficient M q η b else 0) *
      ZMod.stdAddChar ((a : ZMod q) * b)) =
      (∑ n ∈ (range (M + 1)).filter (fun n => Nat.Coprime n q),
        (Λ n : ℂ) * Kernel.e ((n : ℝ) * ((a : ℝ) / q + η))) -
        ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ) * Kernel.T 0 (M + 1) η := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let ψ := ZMod.stdAddChar (N := q)
  have he (n : ℕ) : ψ ((a : ZMod q) * (n : ZMod q)) =
      Kernel.e ((n : ℝ) * a / q) := by
    rw [show (a : ZMod q) * (n : ZMod q) = ((a : ℤ) : ZMod q) * (n : ZMod q) by simp]
    rw [LeanLab.PNTPort.LargeSieve.stdAddChar_mul_natCast]
    change Kernel.e ((a : ℤ) * ((n : ℝ) / q)) = _
    congr 1
    push_cast
    ring
  have hram : (∑ b : ZMod q, if IsUnit b then ψ ((a : ZMod q) * b) else 0) =
      (ArithmeticFunction.moebius q : ℂ) := by
    rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range]
    have hh : (∑ c ∈ range q, if IsUnit (c : ZMod q) then ψ ((a : ZMod q) * (c : ZMod q)) else 0) =
        Ramanujan103.ramanujanSum q a := by
      rw [Ramanujan103.ramanujanSum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c hc
      simp only [ZMod.isUnit_iff_coprime]
      split_ifs
      · rw [he]
        congr 1
        ring
      · rfl
    rw [hh, Ramanujan103.ramanujanSum_coprime q a hq hcop]
  have hfinite :
      (∑ b : ZMod q, if IsUnit b then
        (∑ n ∈ range (M + 1), if (n : ZMod q) = b then
          (Λ n : ℂ) * Kernel.e ((n : ℝ) * η) else 0) * ψ ((a : ZMod q) * b) else 0) =
      (∑ n ∈ (range (M + 1)).filter (fun n => Nat.Coprime n q),
        (Λ n : ℂ) * Kernel.e ((n : ℝ) * ((a : ℝ) / q + η))) := by
    have hb (b : ZMod q) :
        (if IsUnit b then
          (∑ n ∈ range (M + 1), if (n : ZMod q) = b then
            (Λ n : ℂ) * Kernel.e ((n : ℝ) * η) else 0) * ψ ((a : ZMod q) * b) else 0) =
        ∑ n ∈ range (M + 1), if (n : ZMod q) = b ∧ IsUnit b then
          (Λ n : ℂ) * Kernel.e ((n : ℝ) * η) * ψ ((a : ZMod q) * b) else 0 := by
      rw [Finset.sum_mul]
      by_cases hu : IsUnit b
      · simp [hu, ite_mul]
      · simp [hu]
    simp_rw [hb]
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      ZMod.isUnit_iff_coprime]
    split_ifs
    · rw [he, mul_assoc, ← Parseval103.e_add]
      congr 2
      ring
    · rfl
  change (∑ b : ZMod q, (if IsUnit b then residueCoefficient M q η b else 0) *
      ψ ((a : ZMod q) * b)) = _
  have hsplit :
      (∑ b : ZMod q, (if IsUnit b then residueCoefficient M q η b else 0) * ψ ((a : ZMod q) * b)) =
      (∑ b : ZMod q, if IsUnit b then
        (∑ n ∈ range (M + 1), if (n : ZMod q) = b then
          (Λ n : ℂ) * Kernel.e ((n : ℝ) * η) else 0) * ψ ((a : ZMod q) * b) else 0) -
      (Kernel.T 0 (M + 1) η / (q.totient : ℂ)) *
        (∑ b : ZMod q, if IsUnit b then ψ ((a : ZMod q) * b) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hu : IsUnit b
    · simp only [ite_eq_left hu, residueCoefficient]
      ring
    · simp [hu]
  rw [hsplit, hfinite, hram]
  push_cast
  ring
/-- Page 487 equation 31, finite energy comparison.
Restricting the additive frequencies to units is bounded by normalized character energy. -/
theorem unit_residue_energy_le (M q : ℕ) [NeZero q] (η : ℝ) :
    (∑ a : ZMod q, if IsUnit a then
      ‖∑ b : ZMod q, (if IsUnit b then residueCoefficient M q η b else 0) *
        ZMod.stdAddChar (a * b)‖ ^ 2 else 0) ≤
      (q : ℝ) / q.totient *
        ∑ χ : DirichletCharacter ℂ q, ‖twistedRemainder M χ η‖ ^ 2 := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  rw [character_parseval]
  calc
    _ ≤ ∑ a : ZMod q,
        ‖∑ b : ZMod q, (if IsUnit b then residueCoefficient M q η b else 0) *
          ZMod.stdAddChar (a * b)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs
      · exact le_rfl
      · positivity
    _ = (q : ℝ) * ∑ b : ZMod q,
        ‖if IsUnit b then residueCoefficient M q η b else 0‖ ^ 2 := additive_parseval _
    _ = (q : ℝ) / q.totient *
        ((q.totient : ℝ) * ∑ b : ZMod q,
          if IsUnit b then ‖residueCoefficient M q η b‖ ^ 2 else 0) := by
      have heq : (∑ b : ZMod q, ‖if IsUnit b then residueCoefficient M q η b else 0‖ ^ 2) =
          ∑ b : ZMod q, if IsUnit b then ‖residueCoefficient M q η b‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        split_ifs <;> simp
      rw [heq]
      field_simp
/-- Pages 484 and 487, coprimality error in equation 31.
The difference between the principal remainder and the unit residue transform
is bounded by the von Mangoldt weight on noncoprime integers. -/
theorem norm_residue_error_le (M q a : ℕ) [NeZero q]
    (hcop : Nat.Coprime q a) (η : ℝ) :
    ‖characterRemainder M q (a : ℤ) η -
      ∑ b : ZMod q, (if IsUnit b then residueCoefficient M q η b else 0) *
        ZMod.stdAddChar ((a : ZMod q) * b)‖ ≤ LeanLab.PNTPort.BV.psiBad (M : ℝ) q := by
  rw [residue_fourier_eq M q a hcop η]
  unfold characterRemainder primeSum
  simp only [Int.cast_natCast]
  let v : ℕ → ℂ := fun n => (Λ n : ℂ) * Kernel.e ((n : ℝ) * ((a : ℝ) / q + η))
  have hs : (∑ n ∈ range (M + 1), v n) -
      (∑ n ∈ (range (M + 1)).filter (fun n => Nat.Coprime n q), v n) =
      ∑ n ∈ (range (M + 1)).filter (fun n => ¬ Nat.Coprime n q), v n := by
    have hh := Finset.sum_filter_add_sum_filter_not (range (M + 1))
      (fun n => Nat.Coprime n q) v
    linear_combination -hh
  have heq :
      (∑ n ∈ range (M + 1), v n) -
        ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ) * Kernel.T 0 (M + 1) η -
        ((∑ n ∈ (range (M + 1)).filter (fun n => Nat.Coprime n q), v n) -
          ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ) * Kernel.T 0 (M + 1) η) =
      ∑ n ∈ (range (M + 1)).filter (fun n => ¬ Nat.Coprime n q), v n := by
    rw [show (∑ n ∈ range (M + 1), v n) -
        ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ) * Kernel.T 0 (M + 1) η -
        ((∑ n ∈ (range (M + 1)).filter (fun n => Nat.Coprime n q), v n) -
          ((ArithmeticFunction.moebius q : ℝ) / q.totient : ℂ) * Kernel.T 0 (M + 1) η) =
      (∑ n ∈ range (M + 1), v n) -
        (∑ n ∈ (range (M + 1)).filter (fun n => Nat.Coprime n q), v n) by ring, hs]
  change ‖(∑ n ∈ range (M + 1), v n) - _ - _‖ ≤ _
  rw [heq]
  have hsum : (∑ n ∈ (range (M + 1)).filter (fun n => ¬ Nat.Coprime n q), (Λ n : ℝ)) =
      LeanLab.PNTPort.BV.psiBad (M : ℝ) q := by
    unfold LeanLab.PNTPort.BV.psiBad
    rw [Nat.floor_natCast]
    simp only [Finset.sum_filter]
    have hr : range (M + 1) = insert 0 (Icc 1 M) := by ext n; simp; omega
    rw [hr, Finset.sum_insert (by simp)]
    simp
  calc
    _ ≤ ∑ n ∈ (range (M + 1)).filter (fun n => ¬ Nat.Coprime n q), ‖v n‖ := norm_sum_le _ _
    _ = ∑ n ∈ (range (M + 1)).filter (fun n => ¬ Nat.Coprime n q), (Λ n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [v, Kernel.e, Complex.norm_exp, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ = _ := hsum
/-- Page 487 equation 31, derived fixed eta comparison.
The sum over unit numerator residues of the squared principal remainder
is bounded by twice the normalized character energy plus the squared coprimality error. -/
theorem pointwise_arc_comparison (M q : ℕ) [NeZero q] (η : ℝ) :
    (∑ a : ZMod q, if IsUnit a then
      ‖characterRemainder M q (a.val : ℤ) η‖ ^ 2 else 0) ≤
      2 * ((q : ℝ) / q.totient *
        ∑ χ : DirichletCharacter ℂ q, ‖twistedRemainder M χ η‖ ^ 2) +
        2 * q.totient * (LeanLab.PNTPort.BV.psiBad (M : ℝ) q) ^ 2 := by
  let E := LeanLab.PNTPort.BV.psiBad (M : ℝ) q
  let V : ZMod q → ℂ := fun a =>
    ∑ b : ZMod q, (if IsUnit b then residueCoefficient M q η b else 0) *
      ZMod.stdAddChar (a * b)
  have hE : 0 ≤ E := LeanLab.PNTPort.BV.psiBad_nonneg _ _
  have hpoint (a : ZMod q) :
      (if IsUnit a then ‖characterRemainder M q (a.val : ℤ) η‖ ^ 2 else 0) ≤
        2 * (if IsUnit a then ‖V a‖ ^ 2 else 0) + 2 * (if IsUnit a then E ^ 2 else 0) := by
    by_cases hu : IsUnit a
    · simp only [ite_eq_left hu]
      have hcop : Nat.Coprime q a.val :=
        ((ZMod.isUnit_iff_coprime a.val q).mp (by simpa using hu)).symm
      have herr := norm_residue_error_le M q a.val hcop η
      simp only [ZMod.natCast_zmod_val] at herr
      have hh : ‖characterRemainder M q (a.val : ℤ) η‖ ≤ ‖V a‖ + E := by
        calc
          _ = ‖(characterRemainder M q (a.val : ℤ) η - V a) + V a‖ := by congr 1; ring
          _ ≤ ‖characterRemainder M q (a.val : ℤ) η - V a‖ + ‖V a‖ := norm_add_le _ _
          _ ≤ E + ‖V a‖ := add_le_add herr le_rfl
          _ = _ := by ring
      have hsq := pow_le_pow_left₀ (norm_nonneg (characterRemainder M q (a.val : ℤ) η)) hh 2
      nlinarith [sq_nonneg (‖V a‖ - E)]
    · simp [hu]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (ZMod q))) => hpoint a)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hcount : (∑ a : ZMod q, if IsUnit a then E ^ 2 else 0) = (q.totient : ℝ) * E ^ 2 := by
    have hh := congrArg (fun x : ℝ => x * E ^ 2)
      (LeanLab.PNTPort.LargeSieve.sum_isUnit_eq_totient (q := q))
    simpa only [Finset.sum_mul, ite_mul, one_mul, zero_mul] using hh
  rw [hcount] at hsum
  have hmodel := unit_residue_energy_le M q η
  change (∑ a : ZMod q, if IsUnit a then ‖V a‖ ^ 2 else 0) ≤ _ at hmodel
  change _ ≤ 2 * _ + 2 * q.totient * E ^ 2
  linarith

/-- Page 487 equation 31, derived single modulus integral comparison.
The short arc integral is at most twice the character energy plus
four times the squared noncoprime prime weight divided by Q. -/
theorem integrated_arc_comparison (M q : ℕ) [NeZero q]
    (Q : ℝ) (hQ : 0 < Q) :
    (∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
      ∑ a : ZMod q, if IsUnit a then
        ‖characterRemainder M q (a.val : ℤ) η‖ ^ 2 else 0) ≤
      2 * characterEnergy M q Q +
        4 * (LeanLab.PNTPort.BV.psiBad (M : ℝ) q) ^ 2 / Q := by
  let r := 1 / ((q : ℝ) * Q)
  let E := LeanLab.PNTPort.BV.psiBad (M : ℝ) q
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hr : 0 < r := by dsimp [r]; positivity
  have hleft : Continuous (fun η : ℝ => ∑ a : ZMod q, if IsUnit a then
      ‖characterRemainder M q (a.val : ℤ) η‖ ^ 2 else 0) := by
    apply continuous_finsetSum
    intro a ha
    by_cases hu : IsUnit a
    · simp only [ite_eq_left hu, characterRemainder, primeSum, Kernel.T, Kernel.e]
      fun_prop
    · simp only [ite_eq_right hu]
      exact continuous_const
  have hc : Continuous (fun η : ℝ =>
      ∑ χ : DirichletCharacter ℂ q, ‖twistedRemainder M χ η‖ ^ 2) := by
    apply continuous_finsetSum
    intro χ hχ
    exact (continuous_twistedRemainder M χ).norm.pow 2
  have hright : Continuous (fun η : ℝ =>
      2 * ((q : ℝ) / q.totient *
        ∑ χ : DirichletCharacter ℂ q, ‖twistedRemainder M χ η‖ ^ 2) +
        2 * q.totient * E ^ 2) :=
    ((hc.const_mul _).const_mul _).add continuous_const
  have hi := setIntegral_mono_on (μ := volume) (s := Set.Icc (-r) r) hleft.integrableOn_Icc hright.integrableOn_Icc
    measurableSet_Icc (fun η (_ : η ∈ Set.Icc (-r) r) => pointwise_arc_comparison M q η)
  have hCE : (∫ η in Set.Icc (-r) r, (q : ℝ) / q.totient *
      ∑ χ : DirichletCharacter ℂ q, ‖twistedRemainder M χ η‖ ^ 2) = characterEnergy M q Q := by
    unfold characterEnergy
    rw [integral_const_mul]
    congr 1
    exact integral_finsetSum _ (fun χ _ =>
      ((continuous_twistedRemainder M χ).norm.pow 2).integrableOn_Icc)
  rw [integral_add ((hc.const_mul _).const_mul _).integrableOn_Icc
      continuous_const.integrableOn_Icc, integral_const_mul, hCE,
    setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -r ≤ r), smul_eq_mul] at hi
  have herror : (r - -r) * (2 * q.totient * E ^ 2) ≤ 4 * E ^ 2 / Q := by
    have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    calc
      _ = 4 * q.totient * E ^ 2 / ((q : ℝ) * Q) := by dsimp [r]; field_simp; ring
      _ ≤ 4 * q * E ^ 2 / ((q : ℝ) * Q) := by gcongr
      _ = 4 * E ^ 2 / Q := by field_simp
  exact hi.trans (add_le_add le_rfl herror)
/-- Pages 486 and 487 equations 27 and 31, derived representative identity.
The paper representatives from one through q give the same integrated
remainder energy as the unit residues in ZMod q. -/
theorem remainder_arc_eq_zmod (M q : ℕ) [NeZero q] (Q : ℝ) :
    (∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      ∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
        ‖characterRemainder M q (a : ℤ) η‖ ^ 2) =
    (∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
      ∑ a : ZMod q, if IsUnit a then
        ‖characterRemainder M q (a.val : ℤ) η‖ ^ 2 else 0) := by
  let s := Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q))
  let g : ℕ → ℝ := fun a => ∫ η in s, ‖characterRemainder M q (a : ℤ) η‖ ^ 2
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hends : g 0 = g q := by
    dsimp [g]
    apply integral_congr_ae
    filter_upwards [] with η
    simp only [characterRemainder, Int.cast_zero, zero_div, zero_add,
      Int.cast_natCast, div_self hqR]
    rw [add_comm 1 η, Decomp533a.primeSum_periodic M η]
  have hcont (a : ZMod q) : Continuous (fun η : ℝ => if IsUnit a then
      ‖characterRemainder M q (a.val : ℤ) η‖ ^ 2 else 0) := by
    by_cases hu : IsUnit a
    · simp only [ite_eq_left hu, characterRemainder, primeSum, Kernel.T, Kernel.e]
      fun_prop
    · simp only [ite_eq_right hu]
      exact continuous_const
  symm
  calc
    _ = ∑ a : ZMod q, ∫ η in s, if IsUnit a then
        ‖characterRemainder M q (a.val : ℤ) η‖ ^ 2 else 0 := by
      exact integral_finsetSum _ (fun a _ => (hcont a).integrableOn_Icc)
    _ = ∑ a : ZMod q, if IsUnit a then g a.val else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hu : IsUnit a <;> simp [hu, g]
    _ = ∑ a ∈ range q, if Nat.Coprime a q then g a else 0 := by
      rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range]
      apply Finset.sum_congr rfl
      intro a ha
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)]
      simp only [ZMod.isUnit_iff_coprime]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Decomp533a.sum_reduced_range_eq_Icc q hq g hends


/-- Page 485 equation 21, derived multiplicity fact for all characters. -/
theorem lfunction_zero_order_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hz : χ.LFunction ρ = 0) (hρ : ρ ≠ 1) :
    1 ≤ analyticOrderNatAt χ.LFunction ρ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (χ.differentiableAt_LFunction z (Or.inl hz)).differentiableWithinAt)
      isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (1 : ℂ)).isPreconnected
  have ht : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    apply ha.analyticOrderAt_ne_top_of_isPreconnected hconn
      (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) hρ
    simp [(ha 2 (by norm_num)).analyticOrderAt_eq_zero.mpr
      (χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num))]
  have hn : analyticOrderAt χ.LFunction ρ ≠ 0 :=
    (ha ρ hρ).analyticOrderAt_ne_zero.mpr hz
  simp only [Nat.one_le_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
  exact ⟨hn, ht⟩

/-- Pages 484 and 485 equations 18 and 22, derived finite counting form.
Every character in S has a strip zero. A bound on finite zero families bounds S.
CONDITIONAL ON the displayed finite family density bound K. -/
theorem bad_character_count_le {q : ℕ} [NeZero q] (T σ K : ℝ)
    (hDensity : ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
      (∀ χ ρ, ρ ∈ Z χ → χ.LFunction ρ = 0 ∧
        σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      (∑ χ : DirichletCharacter ℂ q,
        ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ K)
    (S : Finset (DirichletCharacter ℂ q))
    (hS : ∀ χ ∈ S, ∃ ρ : ℂ, χ.LFunction ρ = 0 ∧
      σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) : (S.card : ℝ) ≤ K := by
  classical
  have hex : ∀ χ : DirichletCharacter ℂ q, ∃ ρ : ℂ,
      χ ∈ S → χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
    intro χ
    by_cases hχ : χ ∈ S
    · obtain ⟨ρ, hρ⟩ := hS χ hχ
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨0, fun h => (hχ h).elim⟩
  choose r hr using hex
  let Z : DirichletCharacter ℂ q → Finset ℂ := fun χ => if χ ∈ S then {r χ} else ∅
  have hZ : ∀ χ ρ, ρ ∈ Z χ → χ.LFunction ρ = 0 ∧
      σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
    intro χ ρ hρ
    by_cases hχ : χ ∈ S
    · have he : ρ = r χ := by simpa [Z, hχ] using hρ
      subst ρ
      exact hr χ hχ
    · simp [Z, hχ] at hρ
  have heq : (∑ χ : DirichletCharacter ℂ q,
      ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) =
      ∑ χ ∈ S, (analyticOrderNatAt χ.LFunction (r χ) : ℝ) := by
    have hi (χ : DirichletCharacter ℂ q) :
        (∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) =
          if χ ∈ S then (analyticOrderNatAt χ.LFunction (r χ) : ℝ) else 0 := by
      by_cases hχ : χ ∈ S <;> simp [Z, hχ]
    simp_rw [hi]
    exact Finset.sum_ite_mem_eq S _
  calc
    (S.card : ℝ) = ∑ χ ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ χ ∈ S, (analyticOrderNatAt χ.LFunction (r χ) : ℝ) := by
      apply Finset.sum_le_sum
      intro χ hχ
      have hh := hr χ hχ
      have hne : r χ ≠ 1 := by
        intro he
        have := hh.2.2.1
        simp [he] at this
      exact_mod_cast lfunction_zero_order_pos χ hh.1 hne
    _ = _ := heq.symm
    _ ≤ K := hDensity Z hZ

/-- Page 485 equation 21, auxiliary comparison with Huxley page 435 equation 1.1.
A fixed positive exponent loss cannot be replaced by a fixed logarithmic loss.
This compares numerical majorants and asserts nothing about actual zeros. -/
theorem power_loss_exceeds_log_loss (a b d C : ℝ) (hba : b < a) (hC : 0 ≤ C) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      C * x ^ b * Real.log x ^ d < x ^ a := by
  have hb := (isLittleO_log_rpow_rpow_atTop d (sub_pos.mpr hba)).bound
    (show 0 < 1 / (C + 1) by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hh := hX x ((le_max_right _ _).trans hx)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0 _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hh
  have hratio : C / (C + 1) < 1 := by
    apply (div_lt_one (by positivity : 0 < C + 1)).mpr
    linarith
  have hstrict : C * Real.log x ^ d < x ^ (a - b) := by
    calc
      _ ≤ C * (1 / (C + 1) * x ^ (a - b)) := mul_le_mul_of_nonneg_left hh hC
      _ = C / (C + 1) * x ^ (a - b) := by ring
      _ < 1 * x ^ (a - b) := mul_lt_mul_of_pos_right hratio (Real.rpow_pos_of_pos hx0 _)
      _ = _ := one_mul _
  calc
    _ = x ^ b * (C * Real.log x ^ d) := by ring
    _ < x ^ b * x ^ (a - b) := mul_lt_mul_of_pos_left hstrict (Real.rpow_pos_of_pos hx0 _)
    _ = x ^ a := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- Page 487 below equation 31 using page 484 equations 19 and 20.
For logarithmically small moduli the strong region is wider than the good rectangle.
This is numerical and does not assert an analytic zero free region. -/
theorem small_modulus_region_gap (c A B : ℝ) (hc : 0 < c) (hA : 0 < A) (hB : 0 < B) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N q t : ℝ, N₀ ≤ N → 0 < q →
      q ≤ Real.log N ^ B → |t| ≤ N →
      A * Real.log (Real.log N) / Real.log N <
        c / max (q ^ (1 / (4 * B))) (Real.log (|t| + 1) ^ (4 / 5 : ℝ)) := by
  obtain ⟨N₁, hN₁, hgap⟩ := Decomp88.bad_modulus_lower c A (1 / (4 * B))
    hc hA (by positivity)
  refine ⟨max N₁ (Real.exp 2), hN₁.trans (le_max_left _ _), ?_⟩
  intro N q t hN hq hqsmall ht
  have hL2 : 2 ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hN)
    simpa using hh
  have hL1 : 1 < Real.log N := by linarith
  apply lt_of_not_ge
  intro hbad
  have hlarge := hgap N q t ((le_max_left _ _).trans hN) hq ht hbad
  have he : 1 / (2 * (1 / (4 * B))) = 2 * B := by field_simp; ring
  rw [he] at hlarge
  have hstrict : Real.log N ^ B < Real.log N ^ (2 * B) :=
    Real.rpow_lt_rpow_of_exponent_lt hL1 (by linarith)
  exact (not_lt_of_ge (hlarge.trans hqsmall)) hstrict

/-- Pages 485 and 487 through Perelli and Pintz 1993 page 47 equation 21.
The exact normalized character energy is bounded by finite short window variances.
The rounded windows lie between q Q over four and q Q over two.
The inclusive zero endpoint and principal centering are retained. -/
theorem characterEnergy_gallagher (M q : ℕ) (hq : 0 < q)
    (Q : ℝ) (hQ : 0 < Q) (horder : 2 ≤ (q : ℝ) * Q) :
    ∃ L : DirichletCharacter ℂ q → ℕ,
      (∀ χ, 0 < L χ ∧ (q : ℝ) * Q / 4 ≤ L χ ∧ (L χ : ℝ) ≤ (q : ℝ) * Q / 2) ∧
      characterEnergy M q Q ≤
        ((q : ℝ) / q.totient) * (4 * Real.pi ^ 2 / ((q : ℝ) * Q) ^ 2) *
          ∑ χ : DirichletCharacter ℂ q, ∑ m ∈ range (M + 1 + L χ),
            ‖LeanLab.PNTPort.Gallagher.win
              (fun n => (Λ n : ℂ) * χ n - if χ = 1 then 1 else 0)
              (M + 1) (L χ) m‖ ^ 2 := by
  classical
  have hall (χ : DirichletCharacter ℂ q) :=
    Decomp88.character_gallagher_real_order M q hq Q hQ horder χ
      (if χ = 1 then 1 else 0)
  choose L hL hlo hhi hbound using hall
  refine ⟨L, fun χ => ⟨hL χ, hlo χ, hhi χ⟩, ?_⟩
  have hqQ : 0 < (q : ℝ) * Q := mul_pos (by exact_mod_cast hq) hQ
  have henergy (χ : DirichletCharacter ℂ q) :
      (∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
        ‖twistedRemainder M χ η‖ ^ 2) ≤
        (4 * Real.pi ^ 2 / ((q : ℝ) * Q) ^ 2) *
          ∑ m ∈ range (M + 1 + L χ),
            ‖LeanLab.PNTPort.Gallagher.win
              (fun n => (Λ n : ℂ) * χ n - if χ = 1 then 1 else 0)
              (M + 1) (L χ) m‖ ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [one_div_pos.mpr hqQ])]
    have he (η : ℝ) : twistedRemainder M χ η =
        (∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
          (if χ = 1 then 1 else 0) * Kernel.T 0 (M + 1) η := by
      by_cases hχ : χ = 1 <;> simp [twistedRemainder, hχ]
    simp_rw [he]
    exact hbound χ
  unfold characterEnergy
  calc
    _ ≤ ((q : ℝ) / q.totient) * ∑ χ : DirichletCharacter ℂ q,
        (4 * Real.pi ^ 2 / ((q : ℝ) * Q) ^ 2) *
          ∑ m ∈ range (M + 1 + L χ),
            ‖LeanLab.PNTPort.Gallagher.win
              (fun n => (Λ n : ℂ) * χ n - if χ = 1 then 1 else 0)
              (M + 1) (L χ) m‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => henergy χ)
      positivity
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Page 485 equation 21, derived principal character normalization.
The extra Euler factors preserve zeros and their multiplicities in the positive
half plane away from the pole at one. -/
theorem principal_zero_transfer (q : ℕ) [NeZero q] (ρ : ℂ)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    ((1 : DirichletCharacter ℂ q).LFunction ρ = 0 ↔ riemannZeta ρ = 0) ∧
      analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) ρ =
        analyticOrderNatAt riemannZeta ρ := by
  let E : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))
  have hE : E ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    have hn : ‖(p : ℂ) ^ (-ρ)‖ < 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0,
        Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    intro he
    have he' : (p : ℂ) ^ (-ρ) = 1 := (sub_eq_zero.mp he).symm
    rw [he', norm_one] at hn
    exact (lt_irrefl 1) hn
  have hFact (z : ℂ) (hz : z ≠ 1) :
      (1 : DirichletCharacter ℂ q).LFunction z = E z * riemannZeta z := by
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hz
  refine ⟨?_, ?_⟩
  · rw [hFact ρ hρ1, mul_eq_zero, or_iff_right hE]
  · have hEa : AnalyticAt ℂ E ρ := by
      apply Finset.analyticAt_fun_prod
      intro p hp
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      have hps : (p : ℂ) ∈ Complex.slitPlane := Complex.natCast_mem_slitPlane.mpr
        (Nat.prime_of_mem_primeFactors hp).ne_zero
      fun_prop
    have hZa : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
    have he : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds ρ]
        (fun z => E z * riemannZeta z) := by
      filter_upwards [eventually_ne_nhds hρ1] with z hz
      exact hFact z hz
    unfold analyticOrderNatAt
    congr 1
    rw [analyticOrderAt_congr he]
    change analyticOrderAt (E * riemannZeta) ρ = _
    rw [analyticOrderAt_mul hEa hZa,
      analyticOrderAt_eq_zero.mpr (Or.inr hE), zero_add]

/-- Page 485 equation 21, derived local total zero count.
The existing Jensen estimate covers every character after the principal
Euler factors are removed. This is not a saving in the real part. -/
theorem zero_order_window_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (τ : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧
      ρ.re < 1 ∧ |ρ.im - τ| ≤ 1 / 2) :
    (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      Real.log (24 * LeanLab.PNTPort.DirichletZF.Z * q * (|τ| + 4) ^ 2) /
        Real.log (7 / 6) := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    have htr (ρ : ℂ) (hρ : ρ ∈ S) := principal_zero_transfer q ρ
      (by linarith [(hS ρ hρ).2.1])
      (by intro he; have hh := (hS ρ hρ).2.2.1; simp [he] at hh)
    have heq : (∑ ρ ∈ S,
        (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) ρ : ℝ)) =
        ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact_mod_cast (htr ρ hρ).2
    rw [heq]
    have hmem : ∀ ρ ∈ S, ρ ∈ LeanLab.PNTPort.DirichletZF.U1482.RW riemannZeta τ := by
      intro ρ hρ
      exact ⟨(htr ρ hρ).1.mp (hS ρ hρ).1, (hS ρ hρ).2⟩
    have hb := (LeanLab.PNTPort.DirichletZF.U1482.rw_count_zeta τ).2 S hmem
    apply hb.trans
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 7 / 6)).le
    have hZ := LeanLab.PNTPort.DirichletZF.Z_pos
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    apply Real.log_le_log (by positivity)
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hq1
        (show 0 ≤ 24 * LeanLab.PNTPort.DirichletZF.Z by positivity))
      (sq_nonneg (|τ| + 4))
    simpa only [mul_one] using hm
  · exact (LeanLab.PNTPort.DirichletZF.U1482.rw_count_L hχ τ).2 S hS

/-- Page 485 equation 21, auxiliary total count from the local Jensen bound.
All characters and analytic multiplicities are included. No saving depending
on the real part is claimed by this total count. -/
theorem zero_order_total_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T : ℝ), 2 ≤ T →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → χ.LFunction ρ = 0 ∧
          1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
            C * (q : ℝ) * T * Real.log ((q : ℝ) * T) := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hZpos := LeanLab.PNTPort.DirichletZF.Z_pos
  let A := |Real.log (384 * LeanLab.PNTPort.DirichletZF.Z)| / Real.log 2 + 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨3 * (A / Real.log (7 / 6)), by positivity, ?_⟩
  intro q _ T hT Z hZeros
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hT0 : 0 < T := by linarith
  have hqT2 : 2 ≤ (q : ℝ) * T := by
    have hh := mul_le_mul_of_nonneg_right hq1 hT0.le
    nlinarith
  let L := Real.log ((q : ℝ) * T)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqT2
  have hL0 : 0 < L := hl2.trans_le hL2
  have hlog (τ : ℝ) (hτ : |τ| ≤ T + 1) :
      Real.log (24 * LeanLab.PNTPort.DirichletZF.Z * q * (|τ| + 4) ^ 2) /
        Real.log (7 / 6) ≤ A / Real.log (7 / 6) * L := by
    have hs : (|τ| + 4) ^ 2 ≤ (4 * T) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hqSq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have harg : 24 * LeanLab.PNTPort.DirichletZF.Z * q * (|τ| + 4) ^ 2 ≤
        384 * LeanLab.PNTPort.DirichletZF.Z * ((q : ℝ) * T) ^ 2 := by
      calc
        _ ≤ 24 * LeanLab.PNTPort.DirichletZF.Z * q * (4 * T) ^ 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ ≤ 24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) ^ 2 * (4 * T) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hqSq (by positivity)) (sq_nonneg _)
        _ = _ := by ring
    have hn := Real.log_le_log (by positivity) harg
    have he : Real.log (384 * LeanLab.PNTPort.DirichletZF.Z * ((q : ℝ) * T) ^ 2) =
        Real.log (384 * LeanLab.PNTPort.DirichletZF.Z) + 2 * L := by
      calc
        _ = Real.log (384 * LeanLab.PNTPort.DirichletZF.Z) +
            Real.log (((q : ℝ) * T) ^ 2) := Real.log_mul (by positivity) (by positivity)
        _ = _ := by simp only [Real.log_pow, Nat.cast_ofNat, L]
    rw [he] at hn
    have hab : |Real.log (384 * LeanLab.PNTPort.DirichletZF.Z)| ≤
        (|Real.log (384 * LeanLab.PNTPort.DirichletZF.Z)| / Real.log 2) * L := by
      calc
        _ = (|Real.log (384 * LeanLab.PNTPort.DirichletZF.Z)| / Real.log 2) *
            Real.log 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hL2 (by positivity)
    have hnum : Real.log (24 * LeanLab.PNTPort.DirichletZF.Z * q * (|τ| + 4) ^ 2) ≤ A * L := by
      calc
        _ ≤ Real.log (384 * LeanLab.PNTPort.DirichletZF.Z) + 2 * L := hn
        _ ≤ |Real.log (384 * LeanLab.PNTPort.DirichletZF.Z)| + 2 * L :=
          by linarith [le_abs_self (Real.log (384 * LeanLab.PNTPort.DirichletZF.Z))]
        _ ≤ (|Real.log (384 * LeanLab.PNTPort.DirichletZF.Z)| / Real.log 2) * L + 2 * L :=
          by linarith [hab]
        _ = _ := by dsimp [A]; ring
    calc
      _ ≤ (A * L) / Real.log (7 / 6) := div_le_div_of_nonneg_right hnum hl76.le
      _ = _ := by ring
  let J : ℕ := ⌊2 * T⌋₊ + 1
  let f : ℂ → ℕ := fun ρ => ⌊ρ.im + T⌋₊
  let center : ℕ → ℝ := fun j => (j : ℝ) - T + 1 / 2
  have hJ : (J : ℝ) ≤ 3 * T := by
    have hf := Nat.floor_le (show 0 ≤ 2 * T by positivity)
    dsimp [J]
    push_cast
    linarith
  have hχBound (χ : DirichletCharacter ℂ q) :
      (∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
        3 * T * (A / Real.log (7 / 6) * L) := by
    have hmap : ∀ ρ ∈ Z χ, f ρ ∈ range J := by
      intro ρ hρ
      have him := (hZeros χ ρ hρ).2.2.2
      have hf : f ρ ≤ ⌊2 * T⌋₊ := Nat.floor_mono (by linarith [(abs_le.mp him).2])
      apply Finset.mem_range.mpr
      dsimp [J]
      omega
    have hp := Finset.sum_fiberwise_of_maps_to hmap
      (fun ρ : ℂ => (analyticOrderNatAt χ.LFunction ρ : ℝ))
    calc
      _ = ∑ j ∈ range J, ∑ ρ ∈ (Z χ).filter (fun ρ => f ρ = j),
          (analyticOrderNatAt χ.LFunction ρ : ℝ) := hp.symm
      _ ≤ ∑ j ∈ range J, A / Real.log (7 / 6) * L := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN : j ≤ ⌊2 * T⌋₊ := by
          have hh := Finset.mem_range.mp hj
          dsimp [J] at hh
          omega
        have hjR : (j : ℝ) ≤ 2 * T :=
          (show (j : ℝ) ≤ (⌊2 * T⌋₊ : ℝ) by exact_mod_cast hjN).trans
            (Nat.floor_le (by positivity))
        have hc : |center j| ≤ T + 1 := by
          apply abs_le.mpr
          dsimp [center]
          constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]
        have hmem : ∀ ρ ∈ (Z χ).filter (fun ρ => f ρ = j),
            χ.LFunction ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧
              |ρ.im - center j| ≤ 1 / 2 := by
          intro ρ hρ
          obtain ⟨hρZ, hfj⟩ := Finset.mem_filter.mp hρ
          have hz := hZeros χ ρ hρZ
          refine ⟨hz.1, hz.2.1, hz.2.2.1, ?_⟩
          have hlo : (f ρ : ℝ) ≤ ρ.im + T :=
            Nat.floor_le (by linarith [(abs_le.mp hz.2.2.2).1])
          have hhi : ρ.im + T < (f ρ : ℝ) + 1 := Nat.lt_floor_add_one _
          rw [hfj] at hlo hhi
          apply abs_le.mpr
          dsimp [center]
          constructor <;> linarith
        exact (zero_order_window_bound q χ (center j) _ hmem).trans (hlog _ hc)
      _ = (J : ℝ) * (A / Real.log (7 / 6) * L) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hJ (by positivity)
  have hcard : Fintype.card (DirichletCharacter ℂ q) ≤ q := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
    exact Nat.totient_le q
  change _ ≤ (3 * (A / Real.log (7 / 6))) * (q : ℝ) * T * L
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q, 3 * T * (A / Real.log (7 / 6) * L) :=
      Finset.sum_le_sum (fun χ _ => hχBound χ)
    _ = (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
        (3 * T * (A / Real.log (7 / 6) * L)) := by simp
    _ ≤ (q : ℝ) * (3 * T * (A / Real.log (7 / 6) * L)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

/-- Page 485 equation 21, proved restricted range.
The total Jensen count gives the stated twelve fifths power when sigma is
between one half and seven twelfths, with logarithmic exponent one.
The full sealed density leaf retains its larger sigma range. -/
theorem zero_density_left_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ),
      2 ≤ T → 1 / 2 ≤ σ → σ ≤ 7 / 12 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → χ.LFunction ρ = 0 ∧
          σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
          C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) * Real.log ((q : ℝ) * T) := by
  obtain ⟨C, hC, htotal⟩ := zero_order_total_bound
  refine ⟨C, hC, ?_⟩
  intro q _ T σ hT hσ hσmax Z hZeros
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hbase : 1 ≤ (q : ℝ) * T := by
    have hh := mul_le_mul_of_nonneg_right hq1 (show 0 ≤ T by linarith)
    nlinarith
  have hexp : (1 : ℝ) ≤ 12 * (1 - σ) / 5 := by linarith
  have hpow : (q : ℝ) * T ≤ ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hlog : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg hbase
  calc
    _ ≤ C * (q : ℝ) * T * Real.log ((q : ℝ) * T) :=
      htotal q T hT Z (fun χ ρ hρ =>
        ⟨(hZeros χ ρ hρ).1, hσ.trans (hZeros χ ρ hρ).2.1,
          (hZeros χ ρ hρ).2.2⟩)
    _ = C * ((q : ℝ) * T) * Real.log ((q : ℝ) * T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hlog

/-- LEAF. Page 485 equation 21. The Huxley and Ramachandra density estimate.
This finite subset formulation counts zeros with analytic multiplicity.
It includes all characters modulo q and only nontrivial strip zeros.
The paper cites the estimate rather than proving it. -/
theorem leaf_zero_density :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
      ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → DirichletCharacter.LFunction χ ρ = 0 ∧
          σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
          C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
            Real.log ((q : ℝ) * T) ^ d := by
  sorry

/-- LEAF. Pages 484 and 485 equations 18 through 25, applied on page 487
below equation 31. The short interval explicit formula and the zero free
region turn the density estimate into an all character energy bound.
This is a single modulus statement on the exact Theorem 2 window.
CONDITIONAL ON the displayed density estimate. -/
theorem leaf_short_character_mean (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d)
    (hDensity : ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → DirichletCharacter.LFunction χ ρ = 0 ∧
          σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
          C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
            Real.log ((q : ℝ) * T) ^ d)
    (c B D ε : ℝ) (hc : 0 < c) (hB : 0 < B) (hD : 0 < D) (hε : 0 < ε) :
    ∃ K N₀ : ℝ, 0 < K ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
        characterEnergy ⌊c * N⌋₊ q (meanOrder F N H B) ≤
          K * N * Real.log N ^ (-D) := by
  sorry

/-- LEAF. Pages 484 and 487, the character expansion before equation 16
and character orthogonality in equation 31. This is only the finite
character comparison at one modulus. It includes the coprimality error
and the inclusive zero endpoint. No density saving is asserted here. -/
theorem leaf_arc_orthogonality (c B : ℝ) (hc : 0 < c) (hB : 0 < B) :
    ∃ K N₀ : ℝ, 0 < K ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B → ∀ Q : ℝ, 0 < Q →
        (∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          ∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
            ‖characterRemainder ⌊c * N⌋₊ q (a : ℤ) η‖ ^ 2) ≤
          K * (characterEnergy ⌊c * N⌋₊ q Q + Real.log N ^ (4 : ℕ) / Q) := by
  let K := B * (|Real.log c| + 1) / Real.log 2
  have hK : 0 < K := by dsimp [K]; positivity
  let N₀ := max 3 (max (Real.exp 1) (1 / c))
  refine ⟨2 + 4 * K ^ 2, N₀, by positivity, le_max_left _ _, ?_⟩
  intro N hN q hq1 hqP Q hQ
  let : NeZero q := ⟨by omega⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNE : Real.exp 1 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNC : 1 / c ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL : 0 < Real.log N := by linarith
  have hcN : 1 ≤ c * N := by
    have hh := (div_le_iff₀ hc).mp hNC
    nlinarith
  let M := ⌊c * N⌋₊
  have hM1 : 1 ≤ M := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hcN
  have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMR0 : (0 : ℝ) < M := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have hlogq : Real.log q ≤ B * Real.log N := by
    have hh := Real.log_le_log hqR hqP
    rw [Real.log_rpow hL] at hh
    have hl := Real.log_le_sub_one_of_pos hL
    nlinarith
  have hlogM : Real.log M ≤ (|Real.log c| + 1) * Real.log N := by
    have hh := Real.log_le_log hMR0 (Nat.floor_le (by positivity : 0 ≤ c * N))
    rw [Real.log_mul hc.ne' hN0.ne'] at hh
    have hlogc := le_abs_self (Real.log c)
    have hmul := mul_le_mul_of_nonneg_left hL1 (abs_nonneg (Real.log c))
    nlinarith
  have hE : LeanLab.PNTPort.BV.psiBad (M : ℝ) q ≤ K * Real.log N ^ 2 := by
    calc
      _ ≤ Real.log q / Real.log 2 * Real.log M := LeanLab.PNTPort.BV.psiBad_le hMR1 hq1
      _ ≤ (B * Real.log N) / Real.log 2 * ((|Real.log c| + 1) * Real.log N) := by gcongr
      _ = _ := by dsimp [K]; ring
  have hsq := pow_le_pow_left₀ (LeanLab.PNTPort.BV.psiBad_nonneg (M : ℝ) q) hE 2
  have hmass := integrated_arc_comparison M q Q hQ
  rw [← remainder_arc_eq_zmod M q Q] at hmass
  have heq : (K * Real.log N ^ 2) ^ 2 = K ^ 2 * Real.log N ^ (4 : ℕ) := by ring
  rw [heq] at hsq
  have hnon := characterEnergy_nonneg M q Q
  have herr : 0 ≤ Real.log N ^ (4 : ℕ) / Q := by positivity
  calc
    _ ≤ 2 * characterEnergy M q Q + 4 * (LeanLab.PNTPort.BV.psiBad (M : ℝ) q) ^ 2 / Q := hmass
    _ ≤ 2 * characterEnergy M q Q + 4 * (K ^ 2 * Real.log N ^ (4 : ℕ)) / Q := by gcongr
    _ ≤ (2 + 4 * K ^ 2) * (characterEnergy M q Q + Real.log N ^ (4 : ℕ) / Q) := by
      have hx : 0 ≤ K ^ 2 * characterEnergy M q Q := mul_nonneg (sq_nonneg K) hnon
      have he : 4 * (K ^ 2 * Real.log N ^ (4 : ℕ)) / Q = 4 * K ^ 2 * (Real.log N ^ (4 : ℕ) / Q) := by ring
      rw [he]
      nlinarith

/-- Page 487 after equation 31. Summing a uniform nonnegative bound
through the natural floor of P costs at most P copies of that bound. -/
theorem sum_moduli_bound (P x : ℝ) (hP : 0 ≤ P) (hx : 0 ≤ x)
    (g : ℕ → ℝ) (hg : ∀ q ∈ Icc 1 ⌊P⌋₊, g q ≤ x) :
    (∑ q ∈ Icc 1 ⌊P⌋₊, g q) ≤ P * x := by
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, x := Finset.sum_le_sum hg
    _ = (⌊P⌋₊ : ℝ) * x := by simp
    _ ≤ P * x := mul_le_mul_of_nonneg_right (Nat.floor_le hP) hx

/-- Page 487 equation 32. The exact remainder leaf follows from the
single modulus character comparison, the shorter character mean and
trivial summation over moduli. CONDITIONAL ON the two analytic LEAF inputs.
There is no sorry in this assembly. -/
theorem remainder_mean (F : ℤ[X]) (hF : Admissible F)
    (c B A ε : ℝ) (hc : 0 < c) (hB : 0 < B) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      remainderMass F c N H B ≤ C * N * Real.log N ^ (-2 * A - 1) := by
  let D := 2 * A + 1 + B
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨CD, d, hCD, hd, hDensity⟩ := leaf_zero_density
  obtain ⟨CW, NW, hCW, hNW, hw⟩ :=
    leaf_short_character_mean F hF CD d hCD hd hDensity c B D ε hc hB hD hε
  obtain ⟨CO, NO, hCO, hNO, ho⟩ := leaf_arc_orthogonality c B hc hB
  let δ := 1 / (12 * (F.natDegree : ℝ)) + ε / 2
  have hk : 0 < (F.natDegree : ℝ) := by
    exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NQ, hNQ, hq⟩ := Section3.power_error_log_saving δ B hδ
  have ht := (isLittleO_log_rpow_rpow_atTop (D + 4) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨NL, hl⟩ := Filter.eventually_atTop.mp ht
  let N₀ := max (max NW NO) (max NQ (max NL (Real.exp 1)))
  refine ⟨CO * (CW + 1), N₀, by positivity,
    hNW.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu
  have hNW' : NW ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNO' : NO ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNQ' : NQ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNL' : NL ≤ N := ((le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hNE : Real.exp 1 ≤ N := ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hN3 : 3 ≤ N := hNW.trans hNW'
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL : 0 < Real.log N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  have hQ1 : 1 ≤ meanOrder F N H B := by
    have hh : N ^ (2 * δ) ≤ H := by
      convert hH using 1
      dsimp [δ]
      congr 1
      ring
    calc
      1 ≤ N ^ δ := Real.one_le_rpow hN1 hδ.le
      _ ≤ H * Real.log N ^ (-B) := hq N H hNQ' hh
      _ ≤ meanOrder F N H B := by
        unfold meanOrder
        exact mul_le_mul_of_nonneg_right
          (le_self_pow₀ hH1 (by have := hF.1; omega)) (by positivity)
  have hQ : 0 < meanOrder F N H B := by linarith
  have hlog := hl N hNL'
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.rpow_one, abs_of_pos hN0, one_mul] at hlog
  have herror : Real.log N ^ (4 : ℕ) / meanOrder F N H B ≤
      N * Real.log N ^ (-D) := by
    have hp : Real.log N ^ (4 : ℕ) * Real.log N ^ D ≤ N := by
      calc
        _ = Real.log N ^ (D + 4) := by
          rw [← Real.rpow_natCast (Real.log N) 4, ← Real.rpow_add hL]
          congr 1
          ring
        _ ≤ N := hlog
    have hsmall : Real.log N ^ (4 : ℕ) ≤ N * Real.log N ^ (-D) := by
      rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hL D)).mpr hp
    exact (div_le_self (by positivity) hQ1).trans hsmall
  have hlocal (q : ℕ) (hqmem : q ∈ Icc 1 ⌊Real.log N ^ B⌋₊) :
      (∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∫ η in Set.Icc (-(1 / ((q : ℝ) * meanOrder F N H B)))
          (1 / ((q : ℝ) * meanOrder F N H B)),
          ‖characterRemainder ⌊c * N⌋₊ q (a : ℤ) η‖ ^ 2) ≤
        CO * (CW + 1) * N * Real.log N ^ (-D) := by
    have hq1 := (Finset.mem_Icc.mp hqmem).1
    have hqP : (q : ℝ) ≤ Real.log N ^ B :=
      (show (q : ℝ) ≤ (⌊Real.log N ^ B⌋₊ : ℝ) by
        exact_mod_cast (Finset.mem_Icc.mp hqmem).2).trans
        (Nat.floor_le (Real.rpow_nonneg hL.le _))
    have hh := ho N hNO' q hq1 hqP (meanOrder F N H B) hQ
    have hw' := hw N H hNW' hH hHu q hq1 hqP
    calc
      _ ≤ CO * (characterEnergy ⌊c * N⌋₊ q (meanOrder F N H B) +
          Real.log N ^ (4 : ℕ) / meanOrder F N H B) := hh
      _ ≤ CO * (CW * N * Real.log N ^ (-D) + N * Real.log N ^ (-D)) := by
        gcongr
      _ = _ := by ring
  calc
    remainderMass F c N H B ≤ Real.log N ^ B *
        (CO * (CW + 1) * N * Real.log N ^ (-D)) :=
      sum_moduli_bound _ _ (by positivity) (by positivity) _ hlocal
    _ = CO * (CW + 1) * N * Real.log N ^ (-2 * A - 1) := by
      have he : B + -D = -2 * A - 1 := by dsimp [D]; ring
      rw [show Real.log N ^ B * (CO * (CW + 1) * N * Real.log N ^ (-D)) =
        CO * (CW + 1) * N * (Real.log N ^ B * Real.log N ^ (-D)) by ring,
        ← Real.rpow_add hL, he]

end
end LeanLab.Perelli1996.Decomp582a
