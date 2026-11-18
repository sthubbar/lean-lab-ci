import LeanLab.HelfgottMajor.RealAxisKernel

/-!
# Nonvanishing of `L(σ, χ)` on the positive real axis for the moduli 2, 3, 4, 5, 6, 8, 10, 12

For every non principal Dirichlet character `χ` modulo `q` in the list above and every real
`σ > 0` we prove `L(σ, χ) ≠ 0`. The proof applies the kernel criterion
`LFunction_ofReal_ne_zero_of_kernel` with the constant `c = 1`: the real part of
`∑_{a < q} χ(a) x^a` is an explicit real polynomial that is positive on the open unit interval.
Modulo 2 there is no non principal character.

This is standard mathematics. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

open Finset Complex

private lemma sum_range_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ a ∈ range q, χ ((a : ℕ) : ZMod q) = 0 := by
  have h := LeanLab.HelfgottMajor.StripBound123.sum_range_shift (q := q) (fun a => χ a) 0
  simp only [zero_add] at h
  rw [h]
  exact MulChar.sum_eq_zero_of_ne_one hχ

private lemma sum_one_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ a ∈ range q, χ ((a : ℕ) : ZMod q) * (1 : ℂ) ^ a = 0 := by
  rw [← sum_range_eq_zero χ hχ]
  apply Finset.sum_congr rfl
  intro a _
  rw [one_pow, mul_one]

private lemma nu {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) (h : ¬ Nat.Coprime k q) :
    χ ((k : ℕ) : ZMod q) = 0 :=
  MulChar.map_nonunit χ (by rw [ZMod.isUnit_iff_coprime]; exact h)

private lemma one' {q : ℕ} (χ : DirichletCharacter ℂ q) : χ ((1 : ℕ) : ZMod q) = 1 := by
  rw [Nat.cast_one, map_one]

private lemma up {q : ℕ} (χ : DirichletCharacter ℂ q) (k g j : ℕ)
    (h : ((k : ℕ) : ZMod q) = ((g : ℕ) : ZMod q) ^ j) :
    χ ((k : ℕ) : ZMod q) = χ ((g : ℕ) : ZMod q) ^ j := by
  rw [h, map_pow]

private lemma um {q : ℕ} (χ : DirichletCharacter ℂ q) (k g g' : ℕ)
    (h : ((k : ℕ) : ZMod q) = ((g : ℕ) : ZMod q) * ((g' : ℕ) : ZMod q)) :
    χ ((k : ℕ) : ZMod q) = χ ((g : ℕ) : ZMod q) * χ ((g' : ℕ) : ZMod q) := by
  rw [h, map_mul]

private lemma re_of_eq (w : ℂ) (p : ℝ) (h : w = (p : ℂ)) : w.re = p := by
  rw [h, Complex.ofReal_re]

private lemma re_of_eq' (w : ℂ) (p r : ℝ) (h : w = (p : ℂ) + (r : ℂ) * I) : w.re = p := by
  rw [h]; simp

private lemma pos1 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (n : ℕ) (hn : n ≠ 0) : 0 < 1 - x ^ n :=
  sub_pos.2 (pow_lt_one₀ h0.le h1 hn)

private lemma pos2 {x : ℝ} (h0 : 0 < x) (n : ℕ) : 0 < 1 + x ^ n := by positivity

private lemma finish {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (p : ℝ → ℝ)
    (hre : ∀ x : ℝ, (1 * ∑ a ∈ range q, χ (a : ZMod q) * (x : ℂ) ^ a).re = p x)
    (hp : ∀ x : ℝ, 0 < x → x < 1 → 0 < p x) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
  LFunction_ofReal_ne_zero_of_kernel χ hχ 1
    (fun x h0 h1 => by rw [hre]; exact (hp x h0 h1).le)
    ⟨1 / 2, by norm_num, by norm_num, by rw [hre]; exact hp _ (by norm_num) (by norm_num)⟩ hσ

private lemma sq_one_cases {z : ℂ} (h : z ^ 2 = 1) : z = 1 ∨ z = -1 := by
  have h' : (z - 1) * (z + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

private lemma quartic {z : ℂ} (h : 1 + z + z ^ 3 + z ^ 2 = 0) : z = -1 ∨ z = I ∨ z = -I := by
  have h' : (z + 1) * ((z - I) * (z + I)) = 0 := by
    linear_combination h - (z + 1) * Complex.I_sq
  rcases mul_eq_zero.1 h' with h1 | h1
  · left; linear_combination h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · right; left; linear_combination h2
    · right; right; linear_combination h2

private lemma klein {s t : ℂ} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (h : 1 + s + t + s * t = 0) :
    (s = -1 ∧ t = 1) ∨ (s = -1 ∧ t = -1) ∨ (s = 1 ∧ t = -1) := by
  rcases sq_one_cases hs with hs | hs <;> rcases sq_one_cases ht with ht | ht
  · exfalso; rw [hs, ht] at h; norm_num at h
  · right; right; exact ⟨hs, ht⟩
  · left; exact ⟨hs, ht⟩
  · right; left; exact ⟨hs, ht⟩

/-! ## Modulus 3 -/

private lemma expand_3 (χ : DirichletCharacter ℂ 3) (X : ℂ) :
    ∑ a ∈ range 3, χ ((a : ℕ) : ZMod 3) * X ^ a = X + χ ((2 : ℕ) : ZMod 3) * X ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide), one' χ]
  ring

theorem LFunction_ofReal_ne_zero_mod_3 (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h := sum_one_eq_zero χ hχ
  rw [expand_3] at h
  have hz : χ ((2 : ℕ) : ZMod 3) = -1 := by linear_combination h
  refine finish χ hχ (fun x => x * (1 - x)) (fun x => ?_)
    (fun x h0 h1 => mul_pos h0 (sub_pos.2 h1)) hσ
  rw [expand_3, hz]
  exact re_of_eq _ _ (by push_cast; ring)

/-! ## Modulus 4 -/

private lemma expand_4 (χ : DirichletCharacter ℂ 4) (X : ℂ) :
    ∑ a ∈ range 4, χ ((a : ℕ) : ZMod 4) * X ^ a = X + χ ((3 : ℕ) : ZMod 4) * X ^ 3 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide),
    nu χ 2 (by decide), one' χ]
  ring

theorem LFunction_ofReal_ne_zero_mod_4 (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h := sum_one_eq_zero χ hχ
  rw [expand_4] at h
  have hz : χ ((3 : ℕ) : ZMod 4) = -1 := by linear_combination h
  refine finish χ hχ (fun x => x * (1 - x ^ 2)) (fun x => ?_)
    (fun x h0 h1 => mul_pos h0 (pos1 h0 h1 2 (by norm_num))) hσ
  rw [expand_4, hz]
  exact re_of_eq _ _ (by push_cast; ring)

/-! ## Modulus 5 -/

private lemma expand_5 (χ : DirichletCharacter ℂ 5) (X : ℂ) :
    ∑ a ∈ range 5, χ ((a : ℕ) : ZMod 5) * X ^ a =
      X + χ ((2 : ℕ) : ZMod 5) * X ^ 2 + χ ((2 : ℕ) : ZMod 5) ^ 3 * X ^ 3
        + χ ((2 : ℕ) : ZMod 5) ^ 2 * X ^ 4 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide), one' χ,
    up χ 3 2 3 (by decide), up χ 4 2 2 (by decide)]
  ring

theorem LFunction_ofReal_ne_zero_mod_5 (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h := sum_one_eq_zero χ hχ
  rw [expand_5] at h
  have hz := quartic (z := χ ((2 : ℕ) : ZMod 5)) (by linear_combination h)
  rcases hz with hz | hz | hz
  · refine finish χ hχ (fun x => x * ((1 - x) * (1 - x ^ 2))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (mul_pos (sub_pos.2 h1) (pos1 h0 h1 2 (by norm_num)))) hσ
    rw [expand_5, hz]
    exact re_of_eq _ _ (by push_cast; ring)
  · refine finish χ hχ (fun x => x * (1 - x ^ 3)) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (pos1 h0 h1 3 (by norm_num))) hσ
    rw [expand_5, hz]
    refine re_of_eq' _ _ (x ^ 2 - x ^ 3) ?_
    push_cast
    linear_combination ((I : ℂ) * (x : ℂ) ^ 3 + (x : ℂ) ^ 4) * Complex.I_sq
  · refine finish χ hχ (fun x => x * (1 - x ^ 3)) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (pos1 h0 h1 3 (by norm_num))) hσ
    rw [expand_5, hz]
    refine re_of_eq' _ _ (x ^ 3 - x ^ 2) ?_
    push_cast
    linear_combination (-(I : ℂ) * (x : ℂ) ^ 3 + (x : ℂ) ^ 4) * Complex.I_sq

/-! ## Modulus 2 -/

theorem LFunction_ofReal_ne_zero_mod_2 (χ : DirichletCharacter ℂ 2) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have _ := hσ
  exfalso
  have h := sum_range_eq_zero χ hχ
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide), one' χ] at h
  norm_num at h

/-! ## Modulus 6 -/

private lemma expand_6 (χ : DirichletCharacter ℂ 6) (X : ℂ) :
    ∑ a ∈ range 6, χ ((a : ℕ) : ZMod 6) * X ^ a = X + χ ((5 : ℕ) : ZMod 6) * X ^ 5 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide),
    nu χ 2 (by decide), nu χ 3 (by decide), nu χ 4 (by decide), one' χ]
  ring

theorem LFunction_ofReal_ne_zero_mod_6 (χ : DirichletCharacter ℂ 6) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h := sum_one_eq_zero χ hχ
  rw [expand_6] at h
  have hz : χ ((5 : ℕ) : ZMod 6) = -1 := by linear_combination h
  refine finish χ hχ (fun x => x * (1 - x ^ 4)) (fun x => ?_)
    (fun x h0 h1 => mul_pos h0 (pos1 h0 h1 4 (by norm_num))) hσ
  rw [expand_6, hz]
  exact re_of_eq _ _ (by push_cast; ring)

/-! ## Modulus 8 -/

private lemma expand_8 (χ : DirichletCharacter ℂ 8) (X : ℂ) :
    ∑ a ∈ range 8, χ ((a : ℕ) : ZMod 8) * X ^ a =
      X + χ ((3 : ℕ) : ZMod 8) * X ^ 3 + χ ((5 : ℕ) : ZMod 8) * X ^ 5
        + χ ((3 : ℕ) : ZMod 8) * χ ((5 : ℕ) : ZMod 8) * X ^ 7 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide),
    nu χ 2 (by decide), nu χ 4 (by decide), nu χ 6 (by decide), one' χ,
    um χ 7 3 5 (by decide)]
  ring

theorem LFunction_ofReal_ne_zero_mod_8 (χ : DirichletCharacter ℂ 8) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h := sum_one_eq_zero χ hχ
  rw [expand_8] at h
  have hs : χ ((3 : ℕ) : ZMod 8) ^ 2 = 1 := (up χ 1 3 2 (by decide)).symm.trans (one' χ)
  have ht : χ ((5 : ℕ) : ZMod 8) ^ 2 = 1 := (up χ 1 5 2 (by decide)).symm.trans (one' χ)
  rcases klein hs ht (by linear_combination h) with ⟨h3, h5⟩ | ⟨h3, h5⟩ | ⟨h3, h5⟩
  · refine finish χ hχ (fun x => x * ((1 - x ^ 2) * (1 + x ^ 4))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (mul_pos (pos1 h0 h1 2 (by norm_num)) (pos2 h0 4))) hσ
    rw [expand_8, h3, h5]
    exact re_of_eq _ _ (by push_cast; ring)
  · refine finish χ hχ (fun x => x * ((1 - x ^ 2) * (1 - x ^ 4))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0
        (mul_pos (pos1 h0 h1 2 (by norm_num)) (pos1 h0 h1 4 (by norm_num)))) hσ
    rw [expand_8, h3, h5]
    exact re_of_eq _ _ (by push_cast; ring)
  · refine finish χ hχ (fun x => x * ((1 + x ^ 2) * (1 - x ^ 4))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (mul_pos (pos2 h0 2) (pos1 h0 h1 4 (by norm_num)))) hσ
    rw [expand_8, h3, h5]
    exact re_of_eq _ _ (by push_cast; ring)

/-! ## Modulus 10 -/

private lemma expand_10 (χ : DirichletCharacter ℂ 10) (X : ℂ) :
    ∑ a ∈ range 10, χ ((a : ℕ) : ZMod 10) * X ^ a =
      X + χ ((3 : ℕ) : ZMod 10) * X ^ 3 + χ ((3 : ℕ) : ZMod 10) ^ 3 * X ^ 7
        + χ ((3 : ℕ) : ZMod 10) ^ 2 * X ^ 9 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide),
    nu χ 2 (by decide), nu χ 4 (by decide), nu χ 5 (by decide), nu χ 6 (by decide),
    nu χ 8 (by decide), one' χ, up χ 7 3 3 (by decide), up χ 9 3 2 (by decide)]
  ring

theorem LFunction_ofReal_ne_zero_mod_10 (χ : DirichletCharacter ℂ 10) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h := sum_one_eq_zero χ hχ
  rw [expand_10] at h
  have hz := quartic (z := χ ((3 : ℕ) : ZMod 10)) (by linear_combination h)
  rcases hz with hz | hz | hz
  · refine finish χ hχ (fun x => x * ((1 - x ^ 2) * (1 - x ^ 6))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0
        (mul_pos (pos1 h0 h1 2 (by norm_num)) (pos1 h0 h1 6 (by norm_num)))) hσ
    rw [expand_10, hz]
    exact re_of_eq _ _ (by push_cast; ring)
  · refine finish χ hχ (fun x => x * (1 - x ^ 8)) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (pos1 h0 h1 8 (by norm_num))) hσ
    rw [expand_10, hz]
    refine re_of_eq' _ _ (x ^ 3 - x ^ 7) ?_
    push_cast
    linear_combination ((I : ℂ) * (x : ℂ) ^ 7 + (x : ℂ) ^ 9) * Complex.I_sq
  · refine finish χ hχ (fun x => x * (1 - x ^ 8)) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (pos1 h0 h1 8 (by norm_num))) hσ
    rw [expand_10, hz]
    refine re_of_eq' _ _ (x ^ 7 - x ^ 3) ?_
    push_cast
    linear_combination (-(I : ℂ) * (x : ℂ) ^ 7 + (x : ℂ) ^ 9) * Complex.I_sq

/-! ## Modulus 12 -/

private lemma expand_12 (χ : DirichletCharacter ℂ 12) (X : ℂ) :
    ∑ a ∈ range 12, χ ((a : ℕ) : ZMod 12) * X ^ a =
      X + χ ((5 : ℕ) : ZMod 12) * X ^ 5 + χ ((7 : ℕ) : ZMod 12) * X ^ 7
        + χ ((5 : ℕ) : ZMod 12) * χ ((7 : ℕ) : ZMod 12) * X ^ 11 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nu χ 0 (by decide),
    nu χ 2 (by decide), nu χ 3 (by decide), nu χ 4 (by decide), nu χ 6 (by decide),
    nu χ 8 (by decide), nu χ 9 (by decide), nu χ 10 (by decide), one' χ,
    um χ 11 5 7 (by decide)]
  ring

theorem LFunction_ofReal_ne_zero_mod_12 (χ : DirichletCharacter ℂ 12) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h := sum_one_eq_zero χ hχ
  rw [expand_12] at h
  have hs : χ ((5 : ℕ) : ZMod 12) ^ 2 = 1 := (up χ 1 5 2 (by decide)).symm.trans (one' χ)
  have ht : χ ((7 : ℕ) : ZMod 12) ^ 2 = 1 := (up χ 1 7 2 (by decide)).symm.trans (one' χ)
  rcases klein hs ht (by linear_combination h) with ⟨h5, h7⟩ | ⟨h5, h7⟩ | ⟨h5, h7⟩
  · refine finish χ hχ (fun x => x * ((1 - x ^ 4) * (1 + x ^ 6))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (mul_pos (pos1 h0 h1 4 (by norm_num)) (pos2 h0 6))) hσ
    rw [expand_12, h5, h7]
    exact re_of_eq _ _ (by push_cast; ring)
  · refine finish χ hχ (fun x => x * ((1 - x ^ 4) * (1 - x ^ 6))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0
        (mul_pos (pos1 h0 h1 4 (by norm_num)) (pos1 h0 h1 6 (by norm_num)))) hσ
    rw [expand_12, h5, h7]
    exact re_of_eq _ _ (by push_cast; ring)
  · refine finish χ hχ (fun x => x * ((1 + x ^ 4) * (1 - x ^ 6))) (fun x => ?_)
      (fun x h0 h1 => mul_pos h0 (mul_pos (pos2 h0 4) (pos1 h0 h1 6 (by norm_num)))) hσ
    rw [expand_12, h5, h7]
    exact re_of_eq _ _ (by push_cast; ring)

end LeanLab.HelfgottMajor.RealAxisKernel

#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_3
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_4
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_5
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_2
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_6
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_8
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_10
#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_12
