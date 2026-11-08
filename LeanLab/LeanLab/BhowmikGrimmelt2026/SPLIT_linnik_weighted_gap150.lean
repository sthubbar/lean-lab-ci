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
import LeanLab.BhowmikGrimmelt2026.Decomp384b

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
  classical
  by_cases hX : X = 0
  · subst X
    simp
  have hX1 : 1 ≤ X := by omega
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hsub : (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime) ⊆
      Finset.range (X + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2; omega)
  have hm : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime), vonMangoldt n) ≤
      Chebyshev.psi X - Chebyshev.theta X := by
    rw [← nonprime_mass_eq384]
    calc
      _ = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime),
          (vonMangoldt n - if n.Prime then vonMangoldt n else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [(Finset.mem_filter.mp hn).2.2, ite_false, sub_zero]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
        by_cases hp : n.Prime
        · simp only [hp, ite_true, sub_self, le_refl]
        · simpa only [hp, ite_false, sub_zero] using (vonMangoldt_nonneg (n := n)))
  have hb := Chebyshev.psi_sub_theta_le (show (1 : ℝ) ≤ X by exact_mod_cast hX1)
  have hlog := Real.log_le_log hXp (show (X : ℝ) ≤ X + 2 by linarith)
  have hlogp : 0 ≤ Real.log ((X : ℝ) + 2) := Real.log_nonneg (by have hx := Nat.cast_nonneg (α := ℝ) X; linarith)
  calc
    _ ≤ Chebyshev.psi X - Chebyshev.theta X := hm
    _ ≤ 2 * Real.sqrt X * Real.log X := hb
    _ ≤ 2 * Real.sqrt X * Real.log ((X : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (Real.sqrt_nonneg (X : ℝ)) hlogp]

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
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hE : (2 : ℝ) ^ 40 ≤ Real.exp 40 := by
    have h := pow_le_pow_left₀ (by norm_num) he1 40
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hE1 : (1 : ℝ) ≤ Real.exp 40 := by
    have : (1 : ℝ) ≤ 2 ^ 40 := by norm_num
    linarith
  refine ⟨6, Real.exp 40, le_rfl, hE1, fun q hq => ?_⟩
  set Q : ℝ := (q : ℝ) with hQdef
  have hQ2 : (2 : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hq
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hpow : Q ^ (6 : ℝ) = Q ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  set y : ℝ := Real.exp 40 * Q ^ 6 with hydef
  set M : ℝ := ((Nat.floor y : ℕ) : ℝ) with hMdef
  have hQsq : (4 : ℝ) ≤ Q ^ 2 := by nlinarith
  have hQ4 : (16 : ℝ) ≤ Q ^ 4 := by
    have e : Q ^ 4 = Q ^ 2 * Q ^ 2 := by ring
    rw [e]; nlinarith
  have hQ6 : 4 * Q ^ 4 ≤ Q ^ 6 := by
    have e : Q ^ 6 = Q ^ 4 * Q ^ 2 := by ring
    rw [e]; nlinarith
  have hy0 : 0 ≤ y := by positivity
  have hyb : 4 * 2 ^ 40 * Q ^ 4 ≤ y := by
    rw [hydef]
    have : (2 : ℝ) ^ 40 * (4 * Q ^ 4) ≤ Real.exp 40 * Q ^ 6 :=
      mul_le_mul hE hQ6 (by positivity) (by positivity)
    linarith
  have hMle : M ≤ y := Nat.floor_le hy0
  have hMgt : y - 1 < M := by
    have := Nat.lt_floor_add_one y; rw [hMdef]; linarith
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  -- log (M + 2) ≤ 27 Q
  have hy2 : 2 ≤ y := by nlinarith
  have hlogM : Real.log (M + 2) ≤ Real.log (2 * y) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2y : Real.log (2 * y) = Real.log 2 + 40 + 6 * Real.log Q := by
    rw [hydef, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_pow]
    push_cast; ring
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlQ : Real.log Q ≤ Q - 1 := Real.log_le_sub_one_of_pos hQ0
  have hlog27 : Real.log (M + 2) ≤ 27 * Q := by linarith
  have hlhs : 400 * Q * Real.log (M + 2) ≤ 10800 * Q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlog27 (by positivity : (0 : ℝ) ≤ 400 * Q)
    nlinarith
  have hsq : 10800 * Q ^ 2 < Real.sqrt M := by
    rw [Real.lt_sqrt (by positivity)]
    nlinarith
  linarith

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

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_nonprime_mass_upper
