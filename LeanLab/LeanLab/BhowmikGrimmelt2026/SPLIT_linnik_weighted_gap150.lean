/-
Split of `linnik_weighted_gap150` into three steps. Nothing here changes the
statement: `linnik_weighted_gap150_split` states it character for character and
proves it from the leaves below. In order, the leaves record (1) an upper bound
for the von Mangoldt mass carried by the non prime numbers of one residue class,
(2) a lower bound for the von Mangoldt mass of a whole residue class at the scale
`C * q ^ L`, and (3) one choice of `L` and one choice of `C` for which that lower
bound beats that upper bound at every modulus at least two. The assembly needs
nothing further: the two bounds meet at the floor of `C * q ^ L`, which is also
the witness of the polynomial scale.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150c

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-! ### Leaf 1: the mass of the non primes -/

/-- LEAF. Removal of the proper prime powers. The von Mangoldt mass of the non
prime numbers of the residue class of `a` modulo `q` up to `X` is at most
`4 * sqrt X * log (X + 2)`. A non prime carries weight only at a prime power
`p ^ k` with `k` at least two, of weight `log p` at most `log X`, and the powers
up to `X` number about `sqrt X`, which leaves a wide margin at the small `X`
where the two sides are comparable. -/
theorem leaf_nonprime_mass_upper (q a X : ℕ) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime), vonMangoldt n)
      ≤ 4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) := by
  sorry

/-! ### Leaf 2: the mass of a whole residue class -/

/-- LEAF. The von Mangoldt mass of the residue class of `a` modulo `q` up to the
floor of `C * q ^ L` is at least one hundredth of `X / q`, whenever the modulus is
at least two, `a` is coprime to it, the exponent is at least six and the constant
is at least one. This is the progressions input: the mass of a class is of the
order of `X / phi q`, and `phi q ≤ q` with a relative loss that one hundredth
absorbs once the scale is a fixed power of the modulus. -/
theorem leaf_ap_mass_lower (L C : ℝ) (hL : 6 ≤ L) (hC : 1 ≤ C)
    (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : Nat.Coprime a q) :
    (∑ n ∈ (Finset.Icc 1 (Nat.floor (C * (q : ℝ) ^ L))).filter (fun n => n % q = a % q),
        vonMangoldt n)
      ≥ (1 / 100) * (Nat.floor (C * (q : ℝ) ^ L) : ℝ) / (q : ℝ) := by
  sorry

/-! ### Leaf 3: the scale at which the two bounds meet -/

/-- LEAF. The scale. There are an exponent `L` at least six and a constant `C` at
least one such that at every modulus `q` at least two the upper bound of the first
leaf, multiplied by the hundredth and by `q`, is smaller than `sqrt` of the
witness `X = floor (C * q ^ L)`: in symbols `400 * q * log (X + 2) < sqrt X`. A
fixed power above the square and a large constant turn the left side into a
logarithmic quantity against a power of `q`. -/
theorem leaf_scale_margin :
    ∃ L C : ℝ, 6 ≤ L ∧ 1 ≤ C ∧ ∀ q : ℕ, 2 ≤ q →
      400 * (q : ℝ) * Real.log ((Nat.floor (C * (q : ℝ) ^ L) : ℝ) + 2)
        < Real.sqrt (Nat.floor (C * (q : ℝ) ^ L) : ℝ) := by
  sorry

/-! ### Assembly -/

/-- Exactly the statement of `linnik_weighted_gap150`, proved from the three
leaves above and not from the original theorem. -/
theorem linnik_weighted_gap150_split : ∃ L C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ a : ℕ, Nat.Coprime a q → ∃ X : ℕ,
      (X : ℝ) ≤ C * (q : ℝ) ^ L ∧
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) >
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime),
        vonMangoldt n := by
  obtain ⟨L, C, hL, hC, hmargin⟩ := leaf_scale_margin
  refine ⟨L, C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro q hq a ha
  set X : ℕ := Nat.floor (C * (q : ℝ) ^ L) with hX
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hbase : (0 : ℝ) ≤ C * (q : ℝ) ^ L :=
    mul_nonneg (le_trans zero_le_one hC) (Real.rpow_nonneg (Nat.cast_nonneg q) L)
  have hXle : (X : ℝ) ≤ C * (q : ℝ) ^ L := by
    rw [hX]
    exact Nat.floor_le hbase
  have hlog : (0 : ℝ) ≤ Real.log ((X : ℝ) + 2) :=
    Real.log_nonneg (by have h : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X; linarith)
  have hm : 400 * (q : ℝ) * Real.log ((X : ℝ) + 2) < Real.sqrt (X : ℝ) := hmargin q hq
  have hsqrtpos : 0 < Real.sqrt (X : ℝ) := by nlinarith [hm, hlog, hqpos]
  have hsq : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg X)
  have hmain : 4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) <
      (1 / 100) * (X : ℝ) / (q : ℝ) := by
    have hden : (0 : ℝ) < 100 * (q : ℝ) := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hm (div_pos hsqrtpos hden)
    have e1 : 400 * (q : ℝ) * Real.log ((X : ℝ) + 2) *
        (Real.sqrt (X : ℝ) / (100 * (q : ℝ))) =
        4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) := by
      field_simp
      ring
    have e2 : Real.sqrt (X : ℝ) * (Real.sqrt (X : ℝ) / (100 * (q : ℝ))) =
        (1 / 100) * (X : ℝ) / (q : ℝ) := by
      field_simp
      nlinarith [hsq]
    rw [e1, e2] at hmul
    exact hmul
  have hnon := leaf_nonprime_mass_upper q a X
  have hlow := leaf_ap_mass_lower L C hL hC q hq a ha
  refine ⟨X, hXle, ?_⟩
  linarith

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.linnik_weighted_gap150_split
