import LeanLab.Halupczok2012.Resplit398c

/-!
The character expansion of a short interval prime sum in an arithmetic progression,
PPS1984 page 531, first display, called there a well known relation.
Source: Perelli, Pintz, Salerno, Bombieri's theorem in short intervals,
Ann. Sc. Norm. Sup. Pisa 11, 1984, pages 529 to 539, copy papers/PPS1984.pdf.

For `q ≥ 1`, `a` coprime to `q` and `h ≥ 0`,
`ψ(z+h; q, a) - ψ(z; q, a) - h/φ(q) = 1/φ(q) ∑_χ conj χ(a) E(z, h, χ)`,
summed over all Dirichlet characters mod `q`, with `E` the quantity `charE`.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Resplit398c

open Finset
open scoped Classical ArithmeticFunction.vonMangoldt

/-- The short interval difference of `psiAP` is the sum of `Λ` over `⌊z⌋ < n ≤ ⌊z+h⌋`
with `n ≡ a mod q`. Helper for PPS1984 page 531, first display. -/
lemma psiAP_add_sub {z h : ℝ} (hh : 0 ≤ h) (q : ℕ) (a : ℤ) :
    psiAP (z + h) q a - psiAP z q a =
      ∑ n ∈ (Ioc ⌊z⌋₊ ⌊z + h⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n := by
  unfold psiAP
  rw [sub_eq_iff_eq_add', sum_filter, sum_filter, sum_filter,
    Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor (by linarith))]

/-- A residue coprime to `q` is a unit in `ZMod q`. -/
lemma isUnit_of_gcd {q : ℕ} {a : ℤ} (ha : Int.gcd a q = 1) : IsUnit (a : ZMod q) := by
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr ha
  refine IsUnit.of_mul_eq_one (u : ZMod q) ?_
  have := congrArg (fun t : ℤ => (t : ZMod q)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
    add_zero, Int.cast_one] at this
  rw [mul_comm]; exact this

/-- PPS1984 page 531, first display, the well known relation:
for `q ≥ 1`, `a` coprime to `q` and `h ≥ 0`,
`ψ(z+h; q, a) - ψ(z; q, a) - h/φ(q) = 1/φ(q) ∑_χ conj χ(a) E(z, h, χ)`. -/
theorem char_expansion {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (ha : Int.gcd a q = 1) {z h : ℝ}
    (hh : 0 ≤ h) :
    ((psiAP (z + h) q a - psiAP z q a - h / q.totient : ℝ) : ℂ) =
      (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) * charE z h χ := by
  have : NeZero q := ⟨by omega⟩
  have hu := isUnit_of_gcd ha
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  have hstar : ∀ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) = χ (a : ZMod q)⁻¹ := by
    intro χ
    rw [← RCLike.star_def, MulChar.star_apply']
    have h1 : χ (a : ZMod q) * χ (a : ZMod q)⁻¹ = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
    have h2 : χ⁻¹ (a : ZMod q) * χ (a : ZMod q) = 1 := by
      rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply hu]
    calc χ⁻¹ (a : ZMod q) = χ⁻¹ (a : ZMod q) * (χ (a : ZMod q) * χ (a : ZMod q)⁻¹) := by
          rw [h1, mul_one]
      _ = χ (a : ZMod q)⁻¹ := by rw [← mul_assoc, h2, one_mul]
  have hprin : ∑ χ : DirichletCharacter ℂ q,
      χ (a : ZMod q)⁻¹ * (if χ = 1 then (h : ℂ) else 0) = h := by
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    rw [MulChar.one_apply (ZMod.isUnit_inv hu), one_mul]
  have hmain : ∑ χ : DirichletCharacter ℂ q,
      χ (a : ZMod q)⁻¹ * ∑ n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊, (Λ n : ℂ) * χ n =
      (q.totient : ℂ) * ∑ n ∈ (Ioc ⌊z⌋₊ ⌊z + h⌋₊).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), (Λ n : ℂ) := by
    simp only [mul_sum]
    rw [sum_comm, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    have : ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * ((Λ n : ℂ) * χ n) =
        (Λ n : ℂ) * ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * χ n := by
      rw [mul_sum]; exact sum_congr rfl fun χ _ => by ring
    rw [this, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
    have hiff : ((a : ZMod q) = (n : ZMod q)) ↔ (n : ℤ) ≡ a [ZMOD q] := by
      rw [← Int.cast_natCast (R := ZMod q), ZMod.intCast_eq_intCast_iff]
      exact ⟨Int.ModEq.symm, Int.ModEq.symm⟩
    simp only [hiff]
    split_ifs <;> ring
  simp only [charE, hstar, mul_sub, sum_sub_distrib, hmain]
  rw [psiAP_add_sub hh]
  push_cast
  field_simp
  rw [sub_right_inj]
  convert hprin.symm

/-- PPS1984 page 531, first display, in absolute value: `ppsTerm z h q a` is the norm of
`1/φ(q) ∑_χ conj χ(a) E(z, h, χ)`. -/
theorem ppsTerm_eq_norm_char {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (ha : Int.gcd a q = 1) {z h : ℝ}
    (hh : 0 ≤ h) :
    ppsTerm z h q a = ‖(1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) * charE z h χ‖ := by
  rw [← char_expansion hq ha hh, Complex.norm_real, Real.norm_eq_abs]
  rfl

/-- PPS1984 page 531, first display, with the triangle inequality:
`ppsTerm z h q a ≤ 1/φ(q) ∑_χ |E(z, h, χ)|`. -/
theorem ppsTerm_le_sum_norm_charE {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (ha : Int.gcd a q = 1)
    {z h : ℝ} (hh : 0 ≤ h) :
    ppsTerm z h q a ≤ (1 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q, ‖charE z h χ‖ := by
  rw [ppsTerm_eq_norm_char hq ha hh, norm_mul]
  have h1 : ‖(1 / (q.totient : ℂ))‖ = 1 / (q.totient : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun χ _ => ?_))
    (by positivity)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

end LeanLab.Halupczok2012.Resplit398c

#print axioms LeanLab.Halupczok2012.Resplit398c.char_expansion
#print axioms LeanLab.Halupczok2012.Resplit398c.ppsTerm_eq_norm_char
#print axioms LeanLab.Halupczok2012.Resplit398c.ppsTerm_le_sum_norm_charE
