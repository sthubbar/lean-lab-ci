/- AI-written Lean code by OpenAI Codex, task113, 2026-10-26. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp113
namespace LeanLab.Tchudakov1938.PrimeValues113
open scoped BigOperators
open Finset
open LeanLab.Tchudakov1938.Decomp113
/-- P0064, page 28, first display of the Lemma 4 proof.
The reduced residue sum is p minus one if p divides m and minus one otherwise. -/
theorem residueSum_prime (p : ℕ+) (hp : (p : ℕ).Prime) (m : ℕ) :
    residueSum m p = if (p : ℕ) ∣ m then (p : ℂ) - 1 else -1 := by
  classical
  have : Fact (Nat.Prime (p : ℕ)) := ⟨hp⟩
  have hsum := AddChar.sum_mulShift (-(m : ZMod (p : ℕ))) (ZMod.isPrimitive_stdAddChar (p : ℕ))
  simp only [ZMod.card, neg_eq_zero, ZMod.natCast_eq_zero_iff] at hsum
  have hu : residueSum m p = ∑ a : {a : ZMod (p : ℕ) // a ≠ 0},
      ZMod.stdAddChar (-(m : ZMod (p : ℕ)) * a.val) := by
    unfold residueSum
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun a => rfl)
  rw [hu]
  have ht := Finset.sum_erase_add (univ : Finset (ZMod (p : ℕ)))
    (fun a => ZMod.stdAddChar (-(m : ZMod (p : ℕ)) * a)) (mem_univ 0)
  have hsub : (∑ a ∈ (univ : Finset (ZMod (p : ℕ))).erase 0,
      ZMod.stdAddChar (-(m : ZMod (p : ℕ)) * a)) =
      ∑ a : {a : ZMod (p : ℕ) // a ≠ 0}, ZMod.stdAddChar (-(m : ZMod (p : ℕ)) * a.val) :=
    Finset.sum_subtype _ (by simp) _
  rw [hsub] at ht
  simp only [mul_zero, AddChar.map_zero_eq_one] at ht
  simp_rw [mul_comm _ (-(m : ZMod (p : ℕ)))] at hsum
  rw [hsum] at ht
  by_cases hd : (p : ℕ) ∣ m
  · simp only [hd, ite_true] at ht ⊢
    linear_combination ht
  · simp only [hd, ite_false, Nat.cast_zero] at ht ⊢
    linear_combination ht

/-- P0064, page 28, first display of the Lemma 4 proof.
The two prime values of A_m follow from character orthogonality. -/
theorem coefficient_prime (p : ℕ+) (hp : (p : ℕ).Prime) (m : ℕ) :
    coefficient m p = if (p : ℕ) ∣ m then 1 / ((p : ℂ) - 1) else -1 / ((p : ℂ) - 1) ^ 2 := by
  have hp1 : (p : ℂ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hden : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hp1
  unfold coefficient
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, residueSum_prime p hp m]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : (p : ℕ) ∣ m <;> simp only [hd, ite_true, ite_false]
  · push_cast
    field_simp
  · push_cast
    ring

/-- P0064, page 28, last display.
The coefficient vanishes when the modulus is not squarefree. -/
theorem coefficient_not_squarefree (m : ℕ) (q : ℕ+) (hq : ¬ Squarefree (q : ℕ)) : coefficient m q = 0 := by
  simp [coefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

/-- P0064, page 27, the residue sum at modulus one is its single term one. -/
theorem residueSum_one (m : ℕ) : residueSum m 1 = 1 := by
  have hz (a : ZMod (1 : ℕ)) : a = 0 := Subsingleton.elim _ _
  unfold residueSum
  change (∑ a : (ZMod 1)ˣ, ZMod.stdAddChar (-(m : ZMod 1) * a.val)) = 1
  simp only [hz, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    ZMod.card_units_eq_totient, Nat.totient_one, one_smul]

/-- P0064, page 27, the coefficient at modulus one is one. -/
theorem coefficient_one (m : ℕ) : coefficient m 1 = 1 := by
  simp [coefficient, residueSum_one]

/-- P0064, page 28, last display at prime modulus.
The squared totient times the norm of A_m is at most gcd of p and m. -/
theorem coefficient_prime_norm_scaled (p : ℕ+) (hp : (p : ℕ).Prime) (m : ℕ) :
    (Nat.totient (p : ℕ) : ℝ)^2 * ‖coefficient m p‖ ≤ Nat.gcd (p : ℕ) m := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hn : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.norm_of_nonneg (by linarith)
  rw [coefficient_prime p hp m, Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : (p : ℕ) ∣ m
  · rw [ite_eq_left hd, Nat.gcd_eq_left hd]
    simp only [norm_div, norm_one, hn]
    have heq : ((p : ℝ) - 1) ^ 2 * (1 / ((p : ℝ) - 1)) = (p : ℝ) - 1 := by
      field_simp
    rw [heq]
    linarith
  · rw [ite_eq_right hd, (hp.coprime_iff_not_dvd.mpr hd).gcd_eq_one]
    simp only [norm_div, norm_neg, norm_one, norm_pow, hn, Nat.cast_one]
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [mul_one_div_cancel (pow_ne_zero 2 hne)]

end LeanLab.Tchudakov1938.PrimeValues113
