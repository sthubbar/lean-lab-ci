/-
A reduction for the row `linnik_weighted_gap150`. The open leaf
`leaf_ap_mass_lower` of `SPLIT_linnik_weighted_gap150` asks for the mass
`X / (100 q)`, which is more than Linnik's theorem is known to give. This file
proves that the sealed statement of `linnik_weighted_gap150` already follows
from a lower bound at Linnik strength: mass at least `c * X / q ^ 2` for every
`X` from `q ^ L₀` up. The known form of Linnik's theorem, Iwaniec and Kowalski
chapter 18, gives `c * X / (φ(q) * sqrt q)`, which is at least `c * X / q ^ 2`.

The theorem below is CONDITIONAL ON that input, which it takes as a hypothesis.
Nothing here is a new leaf and no statement on main is changed.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_linnik_weighted_gap150

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-- CONDITIONAL ON the hypothesis `hlin`, a quantitative Linnik theorem with
mass `c * X / q ^ 2` from `X = q ^ L₀` up. The conclusion is the statement of
`linnik_weighted_gap150` character for character. The scale is
`X = M ^ 4 * q ^ (L₀ + 6)` for one natural `M` above `(4 / c) * (L₀ + 11) + 1`;
the non prime mass is bounded by `leaf_nonprime_mass_upper`. -/
theorem linnik_weighted_gap150_of_power_lower
    (L₀ : ℕ) (c : ℝ) (hc : 0 < c)
    (hlin : ∀ q : ℕ, 2 ≤ q → ∀ a : ℕ, Nat.Coprime a q → ∀ X : ℕ, q ^ L₀ ≤ X →
      c * (X : ℝ) / (q : ℝ) ^ 2 ≤
        ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) :
    ∃ L C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ a : ℕ, Nat.Coprime a q → ∃ X : ℕ,
      (X : ℝ) ≤ C * (q : ℝ) ^ L ∧
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) >
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime),
        vonMangoldt n := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((4 / c) * ((L₀ : ℝ) + 11) + 1)
  have hL0 : (0 : ℝ) ≤ (L₀ : ℝ) := Nat.cast_nonneg L₀
  have hpos : 0 < (4 / c) * ((L₀ : ℝ) + 11) := by positivity
  have hM1 : (1 : ℝ) < (M : ℝ) := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hMnat : 1 ≤ M := by exact_mod_cast hM1.le
  -- 4 (L₀ + 11) < c (M - 1)
  have hkey : 4 * ((L₀ : ℝ) + 11) < c * ((M : ℝ) - 1) := by
    have h1 : (4 / c) * ((L₀ : ℝ) + 11) < (M : ℝ) - 1 := by linarith
    have h2 := mul_lt_mul_of_pos_left h1 hc
    have e : c * ((4 / c) * ((L₀ : ℝ) + 11)) = 4 * ((L₀ : ℝ) + 11) := by
      field_simp
    linarith
  refine ⟨((L₀ + 6 : ℕ) : ℝ), ((M ^ 4 : ℕ) : ℝ), by push_cast; positivity, ?_⟩
  intro q hq a ha
  refine ⟨M ^ 4 * q ^ (L₀ + 6), by rw [Real.rpow_natCast]; push_cast; exact le_rfl, ?_⟩
  set X : ℕ := M ^ 4 * q ^ (L₀ + 6) with hXdef
  have hqX : q ^ L₀ ≤ X := by
    calc q ^ L₀ ≤ q ^ (L₀ + 6) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 1 * q ^ (L₀ + 6) := (one_mul _).symm
      _ ≤ M ^ 4 * q ^ (L₀ + 6) := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hMnat)
  have hlow := hlin q hq a ha X hqX
  have hnon := leaf_nonprime_mass_upper q a X
  set Q : ℝ := (q : ℝ) with hQdef
  have hQ2 : (2 : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hq
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hXr : (X : ℝ) = (M : ℝ) ^ 4 * Q ^ (L₀ + 6) := by
    rw [hXdef, hQdef]; push_cast; ring
  have hQL : (1 : ℝ) ≤ Q ^ L₀ := one_le_pow₀ hQ1
  -- the square root of X is at least M ^ 2 * Q ^ 3
  have hsq : (M : ℝ) ^ 2 * Q ^ 3 ≤ Real.sqrt (X : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [hXr]
    have e : (M : ℝ) ^ 4 * Q ^ (L₀ + 6) = ((M : ℝ) ^ 2 * Q ^ 3) ^ 2 * Q ^ L₀ := by ring
    rw [e]
    exact le_mul_of_one_le_right (by positivity) hQL
  have hXpos : (0 : ℝ) < (X : ℝ) := by rw [hXr]; positivity
  have hX2 : (2 : ℝ) ≤ (X : ℝ) := by
    rw [hXr]
    have h1 : (1 : ℝ) ≤ (M : ℝ) ^ 4 := one_le_pow₀ hM1.le
    have h2 : (2 : ℝ) ≤ Q ^ (L₀ + 6) := by
      calc (2 : ℝ) ≤ Q := hQ2
        _ = Q ^ 1 := (pow_one Q).symm
        _ ≤ Q ^ (L₀ + 6) := pow_le_pow_right₀ hQ1 (by omega)
    nlinarith
  -- the logarithm
  have hlogle : Real.log ((X : ℝ) + 2) ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2X : Real.log (2 * (X : ℝ)) =
      Real.log 2 + 4 * Real.log (M : ℝ) + ((L₀ : ℝ) + 6) * Real.log Q := by
    rw [hXr, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlM : Real.log (M : ℝ) ≤ (M : ℝ) - 1 := Real.log_le_sub_one_of_pos hM0
  have hlQ : Real.log Q ≤ Q - 1 := Real.log_le_sub_one_of_pos hQ0
  have hlog : Real.log ((X : ℝ) + 2) ≤ Q * (((L₀ : ℝ) + 11) * (M : ℝ)) := by
    have h1 : Real.log ((X : ℝ) + 2) ≤ 1 + 4 * ((M : ℝ) - 1) + ((L₀ : ℝ) + 6) * (Q - 1) := by
      have := mul_le_mul_of_nonneg_left hlQ (by linarith : (0 : ℝ) ≤ (L₀ : ℝ) + 6)
      linarith
    have h2 : 1 + 4 * ((M : ℝ) - 1) + ((L₀ : ℝ) + 6) * (Q - 1) ≤
        Q * (((L₀ : ℝ) + 11) * (M : ℝ)) := by
      have hp : 0 ≤ (Q - 1) * (M : ℝ) := mul_nonneg (by linarith) hM0.le
      have hp2 : 0 ≤ ((L₀ : ℝ) + 6) * Q * ((M : ℝ) - 1) :=
        mul_nonneg (mul_nonneg (by linarith) hQ0.le) (by linarith)
      have hp3 : 0 ≤ (L₀ : ℝ) * (M : ℝ) := mul_nonneg hL0 hM0.le
      nlinarith
    linarith
  have hlogpos : 0 ≤ Real.log ((X : ℝ) + 2) := Real.log_nonneg (by linarith)
  set s : ℝ := Real.sqrt (X : ℝ) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hXpos
  have hss : s * s = (X : ℝ) := Real.mul_self_sqrt hXpos.le
  -- 4 Q ^ 2 log (X + 2) < c s
  have hcore : 4 * Q ^ 2 * Real.log ((X : ℝ) + 2) < c * s := by
    have h1 : 4 * Q ^ 2 * Real.log ((X : ℝ) + 2) ≤
        4 * Q ^ 2 * (Q * (((L₀ : ℝ) + 11) * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : 4 * Q ^ 2 * (Q * (((L₀ : ℝ) + 11) * (M : ℝ))) =
        (4 * ((L₀ : ℝ) + 11)) * (Q ^ 3 * (M : ℝ)) := by ring
    have h3 : (4 * ((L₀ : ℝ) + 11)) * (Q ^ 3 * (M : ℝ)) <
        (c * ((M : ℝ) - 1)) * (Q ^ 3 * (M : ℝ)) :=
      mul_lt_mul_of_pos_right hkey (by positivity)
    have h4 : (c * ((M : ℝ) - 1)) * (Q ^ 3 * (M : ℝ)) ≤ c * ((M : ℝ) ^ 2 * Q ^ 3) := by
      have : 0 ≤ c * (Q ^ 3 * (M : ℝ)) := by positivity
      nlinarith
    have h5 : c * ((M : ℝ) ^ 2 * Q ^ 3) ≤ c * s := mul_le_mul_of_nonneg_left hsq hc.le
    linarith
  have hmain : 4 * s * Real.log ((X : ℝ) + 2) < c * (X : ℝ) / Q ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_right hcore hspos
    nlinarith
  linarith

/-- CONDITIONAL ON the hypothesis `hlin`, Linnik's theorem in the form of Iwaniec
and Kowalski chapter 18: mass at least `c * X / (φ(q) * sqrt q)` from `X = q ^ L₀`
up. Since `φ(q) ≤ q` and `sqrt q ≤ q`, this mass is at least `c * X / q ^ 2`, and
the previous theorem applies. The conclusion is the statement of
`linnik_weighted_gap150` character for character. -/
theorem linnik_weighted_gap150_of_linnik_mass
    (L₀ : ℕ) (c : ℝ) (hc : 0 < c)
    (hlin : ∀ q : ℕ, 2 ≤ q → ∀ a : ℕ, Nat.Coprime a q → ∀ X : ℕ, q ^ L₀ ≤ X →
      c * (X : ℝ) / ((Nat.totient q : ℝ) * Real.sqrt (q : ℝ)) ≤
        ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) :
    ∃ L C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ a : ℕ, Nat.Coprime a q → ∃ X : ℕ,
      (X : ℝ) ≤ C * (q : ℝ) ^ L ∧
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) >
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime),
        vonMangoldt n := by
  refine linnik_weighted_gap150_of_power_lower L₀ c hc ?_
  intro q hq a ha X hX
  refine le_trans ?_ (hlin q hq a ha X hX)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hphi0 : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hphi : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hsq0 : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq0
  have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
    rw [Real.sqrt_le_left hq0.le]
    nlinarith
  have hden : (Nat.totient q : ℝ) * Real.sqrt (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hphi hsq hsq0.le hq0.le
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.linnik_weighted_gap150_of_power_lower

#print axioms LeanLab.BhowmikGrimmelt2026.linnik_weighted_gap150_of_linnik_mass
