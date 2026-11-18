import LeanLab.HelfgottMajor.RealAxisKernel

/-!
# Nonvanishing of `L(σ, χ)` on the positive real axis for the odd characters modulo 17

What is proved: for each of the eight odd Dirichlet characters `χ` modulo 17, singled out by
`χ(3)^8 = -1` where 3 generates the unit group, `L(σ, χ) ≠ 0` for every real `σ > 0`.

Method: the kernel criterion `LFunction_ofReal_ne_zero_of_kernel`. The value `z = χ(3)` is one of
the eight primitive sixteenth roots of unity, written through `s = sqrt 2`, `C = cos(π/8)` and
`S = sin(π/8)`. For each root a complex constant `c` is chosen, the real part of `c * P(x)` with
`P(x) = ∑_{a < 17} χ(a) x^a` is factored exactly as `x (1 - x) R(x)`, and `R` is written in
Bernstein form of degree 14 with positive coefficients.

This is standard mathematics; nothing here is new. AI wrote this Lean code. The binary Goldbach
conjecture is open; this file does not touch it.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

namespace SeventeenOdd

open Complex

private lemma lower (a r t : ℝ) (ha : 0 ≤ a) (haa : a * a = t) (hr : r * r < t) : r < a := by
  by_contra hh
  rw [not_lt] at hh
  have := mul_self_le_mul_self ha hh
  linarith

private lemma upper (a r t : ℝ) (hr0 : 0 ≤ r) (haa : a * a = t) (hr : t < r * r) : a < r := by
  by_contra hh
  rw [not_lt] at hh
  have := mul_self_le_mul_self hr0 hh
  linarith

private lemma rels (s C S : ℝ) (h_CC : C * C = (2 + s) / 4) (h_SS : S * S = (2 - s) / 4)
    (h_CS : C * S = s / 4) : s * C = C + S ∧ s * S = C - S := by
  constructor
  · linear_combination (-2 * C - 2 * S) * h_CS + 2 * S * h_CC + 2 * C * h_SS
  · linear_combination (2 * C - 2 * S) * h_CS + 2 * C * h_SS - 2 * S * h_CC

/-- The real constants `s = sqrt 2`, `C = cos(π/8)`, `S = sin(π/8)` with their relations and
rational enclosures. -/
private lemma consts : ∃ s C S : ℝ, s * s = 2 ∧ C * C = (2 + s) / 4 ∧ S * S = (2 - s) / 4 ∧
    C * S = s / 4 ∧ s * C = C + S ∧ s * S = C - S ∧
    1414213 / 1000000 < s ∧ s < 1414214 / 1000000 ∧
    92387 / 100000 < C ∧ C < 92389 / 100000 ∧
    38268 / 100000 < S ∧ S < 38269 / 100000 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have s0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : (1414213 / 1000000 : ℝ) < Real.sqrt 2 := lower _ _ 2 s0 h2 (by norm_num)
  have hs2 : Real.sqrt 2 < (1414214 / 1000000 : ℝ) := upper _ _ 2 (by norm_num) h2 (by norm_num)
  have haa : Real.sqrt (2 + Real.sqrt 2) * Real.sqrt (2 + Real.sqrt 2) = 2 + Real.sqrt 2 :=
    Real.mul_self_sqrt (by linarith)
  have hbb : Real.sqrt (2 - Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) = 2 - Real.sqrt 2 :=
    Real.mul_self_sqrt (by linarith)
  have hab : Real.sqrt (2 + Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by linarith),
      show (2 + Real.sqrt 2) * (2 - Real.sqrt 2) = 2 from by linear_combination -h2]
  have a0 : 0 ≤ Real.sqrt (2 + Real.sqrt 2) / 2 := by positivity
  have b0 : 0 ≤ Real.sqrt (2 - Real.sqrt 2) / 2 := by positivity
  have h_CC : Real.sqrt (2 + Real.sqrt 2) / 2 * (Real.sqrt (2 + Real.sqrt 2) / 2) =
      (2 + Real.sqrt 2) / 4 := by linear_combination haa / 4
  have h_SS : Real.sqrt (2 - Real.sqrt 2) / 2 * (Real.sqrt (2 - Real.sqrt 2) / 2) =
      (2 - Real.sqrt 2) / 4 := by linear_combination hbb / 4
  have h_CS : Real.sqrt (2 + Real.sqrt 2) / 2 * (Real.sqrt (2 - Real.sqrt 2) / 2) =
      Real.sqrt 2 / 4 := by linear_combination hab / 4
  obtain ⟨h_sC, h_sS⟩ := rels _ _ _ h_CC h_SS h_CS
  have e1 : (92387 / 100000 : ℝ) * (92387 / 100000) < (2 + 1414213 / 1000000) / 4 := by norm_num
  have e2 : (2 + 1414214 / 1000000 : ℝ) / 4 < (92389 / 100000) * (92389 / 100000) := by norm_num
  have e3 : (38268 / 100000 : ℝ) * (38268 / 100000) < (2 - 1414214 / 1000000) / 4 := by norm_num
  have e4 : (2 - 1414213 / 1000000 : ℝ) / 4 < (38269 / 100000) * (38269 / 100000) := by norm_num
  exact ⟨_, _, _, h2, h_CC, h_SS, h_CS, h_sC, h_sS, hs1, hs2,
    lower _ _ _ a0 h_CC (by linarith), upper _ _ _ (by norm_num) h_CC (by linarith),
    lower _ _ _ b0 h_SS (by linarith), upper _ _ _ (by norm_num) h_SS (by linarith)⟩

private lemma mulI (u v p q u' v' : ℝ) (h1 : u * p - v * q = u') (h2 : u * q + v * p = v') :
    ((u : ℂ) + (v : ℂ) * I) * ((p : ℂ) + (q : ℂ) * I) = (u' : ℂ) + (v' : ℂ) * I := by
  subst h1 h2
  push_cast
  linear_combination ((v : ℂ) * (q : ℂ)) * Complex.I_mul_I

/-- The eight solutions of `z^8 = -1`. -/
private lemma roots (z : ℂ) (h : z ^ 8 = -1) (s C S : ℝ) (h_ss : s * s = 2)
    (h_CC : C * C = (2 + s) / 4) (h_SS : S * S = (2 - s) / 4) :
    ((z = ((C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I ∨ z = ((C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I) ∨
      (z = ((-C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I ∨ z = ((-C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I)) ∨
    ((z = ((S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I ∨ z = ((S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I) ∨
      (z = ((-S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I ∨ z = ((-S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I)) := by
  have hs' : (s : ℂ) * s = 2 := by exact_mod_cast h_ss
  have hC' : (C : ℂ) * C = (2 + s) / 4 := by exact_mod_cast h_CC
  have hS' : (S : ℂ) * S = (2 - s) / 4 := by exact_mod_cast h_SS
  have q1 : (z - (((C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I)) * (z - (((C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I)) = z ^ 2 - 2 * C * z + 1 := by
    push_cast; linear_combination hC' + hS' - (S : ℂ) ^ 2 * Complex.I_sq
  have q2 : (z - (((-C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I)) * (z - (((-C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I)) = z ^ 2 + 2 * C * z + 1 := by
    push_cast; linear_combination hC' + hS' - (S : ℂ) ^ 2 * Complex.I_sq
  have q3 : (z - (((S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I)) * (z - (((S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I)) = z ^ 2 - 2 * S * z + 1 := by
    push_cast; linear_combination hC' + hS' - (C : ℂ) ^ 2 * Complex.I_sq
  have q4 : (z - (((-S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I)) * (z - (((-S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I)) = z ^ 2 + 2 * S * z + 1 := by
    push_cast; linear_combination hC' + hS' - (C : ℂ) ^ 2 * Complex.I_sq
  have q12 : (z ^ 2 - 2 * C * z + 1) * (z ^ 2 + 2 * C * z + 1) = z ^ 4 - s * z ^ 2 + 1 := by
    linear_combination (-4 * z ^ 2) * hC'
  have q34 : (z ^ 2 - 2 * S * z + 1) * (z ^ 2 + 2 * S * z + 1) = z ^ 4 + s * z ^ 2 + 1 := by
    linear_combination (-4 * z ^ 2) * hS'
  have qq : (z ^ 4 - s * z ^ 2 + 1) * (z ^ 4 + s * z ^ 2 + 1) = z ^ 8 + 1 := by
    linear_combination (-z ^ 4) * hs'
  have hprod : (((z - (((C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I)) * (z - (((C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I))) *
      ((z - (((-C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I)) * (z - (((-C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I)))) *
      (((z - (((S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I)) * (z - (((S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I))) *
      ((z - (((-S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I)) * (z - (((-S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I)))) = 0 := by
    rw [q1, q2, q3, q4, q12, q34, qq]
    linear_combination h
  simpa only [mul_eq_zero, sub_eq_zero] using hprod

/-- The polynomial `∑_{a < 17} χ(a) x^a` in terms of `z = χ(3)` when `z^8 = -1`. -/
private lemma sum_expand (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (x : ℂ) :
    ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * x ^ a =
      x ^ 1 - z ^ 6 * x ^ 2 + z * x ^ 3 - z ^ 4 * x ^ 4 + z ^ 5 * x ^ 5 - z ^ 7 * x ^ 6 - z ^ 3 * x ^ 7 - z ^ 2 * x ^ 8 + z ^ 2 * x ^ 9 + z ^ 3 * x ^ 10 + z ^ 7 * x ^ 11 - z ^ 5 * x ^ 12 + z ^ 4 * x ^ 13 - z * x ^ 14 + z ^ 6 * x ^ 15 - x ^ 16 := by
  have p : ∀ n : ℕ, χ ((3 : ZMod 17) ^ n) = z ^ n := fun n => by rw [map_pow, hz]
  have : Fact (1 < 17) := ⟨by norm_num⟩
  have e0 : χ ((0 : ℕ) : ZMod 17) = 0 := by rw [Nat.cast_zero]; exact MulChar.map_zero χ
  have e1 : χ ((1 : ℕ) : ZMod 17) = 1 := by
    rw [show ((1 : ℕ) : ZMod 17) = 3 ^ 0 from by decide, p]; ring
  have e2 : χ ((2 : ℕ) : ZMod 17) = -z ^ 6 := by
    rw [show ((2 : ℕ) : ZMod 17) = 3 ^ 14 from by decide, p]; linear_combination z ^ 6 * h
  have e3 : χ ((3 : ℕ) : ZMod 17) = z := by
    rw [show ((3 : ℕ) : ZMod 17) = 3 ^ 1 from by decide, p]; ring
  have e4 : χ ((4 : ℕ) : ZMod 17) = -z ^ 4 := by
    rw [show ((4 : ℕ) : ZMod 17) = 3 ^ 12 from by decide, p]; linear_combination z ^ 4 * h
  have e5 : χ ((5 : ℕ) : ZMod 17) = z ^ 5 := by
    rw [show ((5 : ℕ) : ZMod 17) = 3 ^ 5 from by decide, p]
  have e6 : χ ((6 : ℕ) : ZMod 17) = -z ^ 7 := by
    rw [show ((6 : ℕ) : ZMod 17) = 3 ^ 15 from by decide, p]; linear_combination z ^ 7 * h
  have e7 : χ ((7 : ℕ) : ZMod 17) = -z ^ 3 := by
    rw [show ((7 : ℕ) : ZMod 17) = 3 ^ 11 from by decide, p]; linear_combination z ^ 3 * h
  have e8 : χ ((8 : ℕ) : ZMod 17) = -z ^ 2 := by
    rw [show ((8 : ℕ) : ZMod 17) = 3 ^ 10 from by decide, p]; linear_combination z ^ 2 * h
  have e9 : χ ((9 : ℕ) : ZMod 17) = z ^ 2 := by
    rw [show ((9 : ℕ) : ZMod 17) = 3 ^ 2 from by decide, p]
  have e10 : χ ((10 : ℕ) : ZMod 17) = z ^ 3 := by
    rw [show ((10 : ℕ) : ZMod 17) = 3 ^ 3 from by decide, p]
  have e11 : χ ((11 : ℕ) : ZMod 17) = z ^ 7 := by
    rw [show ((11 : ℕ) : ZMod 17) = 3 ^ 7 from by decide, p]
  have e12 : χ ((12 : ℕ) : ZMod 17) = -z ^ 5 := by
    rw [show ((12 : ℕ) : ZMod 17) = 3 ^ 13 from by decide, p]; linear_combination z ^ 5 * h
  have e13 : χ ((13 : ℕ) : ZMod 17) = z ^ 4 := by
    rw [show ((13 : ℕ) : ZMod 17) = 3 ^ 4 from by decide, p]
  have e14 : χ ((14 : ℕ) : ZMod 17) = -z := by
    rw [show ((14 : ℕ) : ZMod 17) = 3 ^ 9 from by decide, p]; linear_combination z ^ 1 * h
  have e15 : χ ((15 : ℕ) : ZMod 17) = z ^ 6 := by
    rw [show ((15 : ℕ) : ZMod 17) = 3 ^ 6 from by decide, p]
  have e16 : χ ((16 : ℕ) : ZMod 17) = -1 := by
    rw [show ((16 : ℕ) : ZMod 17) = 3 ^ 8 from by decide, p]; linear_combination z ^ 0 * h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16]
  ring

/-- Real part of `c * P(x)` from the real and imaginary parts of the powers of `z`. -/
private lemma re_formula (c1 c2 x u1 v1 u2 v2 u3 v3 u4 v4 u5 v5 u6 v6 u7 v7 : ℝ) (z : ℂ)
    (h1 : z = (u1 : ℂ) + (v1 : ℂ) * I)
    (h2 : z ^ 2 = (u2 : ℂ) + (v2 : ℂ) * I)
    (h3 : z ^ 3 = (u3 : ℂ) + (v3 : ℂ) * I)
    (h4 : z ^ 4 = (u4 : ℂ) + (v4 : ℂ) * I)
    (h5 : z ^ 5 = (u5 : ℂ) + (v5 : ℂ) * I)
    (h6 : z ^ 6 = (u6 : ℂ) + (v6 : ℂ) * I)
    (h7 : z ^ 7 = (u7 : ℂ) + (v7 : ℂ) * I) :
    (((c1 : ℂ) + (c2 : ℂ) * I) * ((x : ℂ) ^ 1 - z ^ 6 * (x : ℂ) ^ 2 + z * (x : ℂ) ^ 3 - z ^ 4 * (x : ℂ) ^ 4 + z ^ 5 * (x : ℂ) ^ 5 - z ^ 7 * (x : ℂ) ^ 6 - z ^ 3 * (x : ℂ) ^ 7 - z ^ 2 * (x : ℂ) ^ 8 + z ^ 2 * (x : ℂ) ^ 9 + z ^ 3 * (x : ℂ) ^ 10 + z ^ 7 * (x : ℂ) ^ 11 - z ^ 5 * (x : ℂ) ^ 12 + z ^ 4 * (x : ℂ) ^ 13 - z * (x : ℂ) ^ 14 + z ^ 6 * (x : ℂ) ^ 15 - (x : ℂ) ^ 16)).re =
      c1 * x ^ 1 - (c1 * u6 - c2 * v6) * x ^ 2 + (c1 * u1 - c2 * v1) * x ^ 3 - (c1 * u4 - c2 * v4) * x ^ 4 + (c1 * u5 - c2 * v5) * x ^ 5 - (c1 * u7 - c2 * v7) * x ^ 6 - (c1 * u3 - c2 * v3) * x ^ 7 - (c1 * u2 - c2 * v2) * x ^ 8 + (c1 * u2 - c2 * v2) * x ^ 9 + (c1 * u3 - c2 * v3) * x ^ 10 + (c1 * u7 - c2 * v7) * x ^ 11 - (c1 * u5 - c2 * v5) * x ^ 12 + (c1 * u4 - c2 * v4) * x ^ 13 - (c1 * u1 - c2 * v1) * x ^ 14 + (c1 * u6 - c2 * v6) * x ^ 15 - c1 * x ^ 16 := by
  have e : ((c1 : ℂ) + (c2 : ℂ) * I) * ((x : ℂ) ^ 1 - z ^ 6 * (x : ℂ) ^ 2 + z * (x : ℂ) ^ 3 - z ^ 4 * (x : ℂ) ^ 4 + z ^ 5 * (x : ℂ) ^ 5 - z ^ 7 * (x : ℂ) ^ 6 - z ^ 3 * (x : ℂ) ^ 7 - z ^ 2 * (x : ℂ) ^ 8 + z ^ 2 * (x : ℂ) ^ 9 + z ^ 3 * (x : ℂ) ^ 10 + z ^ 7 * (x : ℂ) ^ 11 - z ^ 5 * (x : ℂ) ^ 12 + z ^ 4 * (x : ℂ) ^ 13 - z * (x : ℂ) ^ 14 + z ^ 6 * (x : ℂ) ^ 15 - (x : ℂ) ^ 16) =
      ((c1 * x ^ 1 - (c1 * u6 - c2 * v6) * x ^ 2 + (c1 * u1 - c2 * v1) * x ^ 3 - (c1 * u4 - c2 * v4) * x ^ 4 + (c1 * u5 - c2 * v5) * x ^ 5 - (c1 * u7 - c2 * v7) * x ^ 6 - (c1 * u3 - c2 * v3) * x ^ 7 - (c1 * u2 - c2 * v2) * x ^ 8 + (c1 * u2 - c2 * v2) * x ^ 9 + (c1 * u3 - c2 * v3) * x ^ 10 + (c1 * u7 - c2 * v7) * x ^ 11 - (c1 * u5 - c2 * v5) * x ^ 12 + (c1 * u4 - c2 * v4) * x ^ 13 - (c1 * u1 - c2 * v1) * x ^ 14 + (c1 * u6 - c2 * v6) * x ^ 15 - c1 * x ^ 16 : ℝ) : ℂ) +
      ((c2 * x ^ 1 - (c1 * v6 + c2 * u6) * x ^ 2 + (c1 * v1 + c2 * u1) * x ^ 3 - (c1 * v4 + c2 * u4) * x ^ 4 + (c1 * v5 + c2 * u5) * x ^ 5 - (c1 * v7 + c2 * u7) * x ^ 6 - (c1 * v3 + c2 * u3) * x ^ 7 - (c1 * v2 + c2 * u2) * x ^ 8 + (c1 * v2 + c2 * u2) * x ^ 9 + (c1 * v3 + c2 * u3) * x ^ 10 + (c1 * v7 + c2 * u7) * x ^ 11 - (c1 * v5 + c2 * u5) * x ^ 12 + (c1 * v4 + c2 * u4) * x ^ 13 - (c1 * v1 + c2 * u1) * x ^ 14 + (c1 * v6 + c2 * u6) * x ^ 15 - c2 * x ^ 16 : ℝ) : ℂ) * I := by
    rw [h7, h6, h5, h4, h3, h2, h1]
    push_cast
    linear_combination (0 - (c2 : ℂ) * (v6 : ℂ) * (x : ℂ) ^ 2 + (c2 : ℂ) * (v1 : ℂ) * (x : ℂ) ^ 3 - (c2 : ℂ) * (v4 : ℂ) * (x : ℂ) ^ 4 + (c2 : ℂ) * (v5 : ℂ) * (x : ℂ) ^ 5 - (c2 : ℂ) * (v7 : ℂ) * (x : ℂ) ^ 6 - (c2 : ℂ) * (v3 : ℂ) * (x : ℂ) ^ 7 - (c2 : ℂ) * (v2 : ℂ) * (x : ℂ) ^ 8 + (c2 : ℂ) * (v2 : ℂ) * (x : ℂ) ^ 9 + (c2 : ℂ) * (v3 : ℂ) * (x : ℂ) ^ 10 + (c2 : ℂ) * (v7 : ℂ) * (x : ℂ) ^ 11 - (c2 : ℂ) * (v5 : ℂ) * (x : ℂ) ^ 12 + (c2 : ℂ) * (v4 : ℂ) * (x : ℂ) ^ 13 - (c2 : ℂ) * (v1 : ℂ) * (x : ℂ) ^ 14 + (c2 : ℂ) * (v6 : ℂ) * (x : ℂ) ^ 15) * Complex.I_mul_I
  rw [e, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]

private lemma pos_1 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 2 + ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 4 + ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 5 - ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 6 - ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 9 + ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 10 + ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 11 - ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 13 - ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 15 - (1 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 2 + ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 4 + ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 5 - ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 6 - ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 9 + ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 10 + ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 11 - ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 13 - ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 15 - (1 : ℝ) * x ^ 16 =
      x * (1 - x) * ((1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (105 + (7) * s + (1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) + (455 + (91/2) * s + (13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) + (1365 + (182) * s + (78) * C + (-1) * S) * (x ^ 4 * (1 - x) ^ 10) + (3003 + (1001/2) * s + (287) * C + (-11) * S) * (x ^ 5 * (1 - x) ^ 9) + (5005 + (1001) * s + (725) * C + (-56) * S) * (x ^ 6 * (1 - x) ^ 8) + (6435 + (1501) * s + (1332) * C + (-174) * S) * (x ^ 7 * (1 - x) ^ 7) + (6435 + (3425/2) * s + (1836) * C + (-366) * S) * (x ^ 8 * (1 - x) ^ 6) + (5005 + (1491) * s + (1926) * C + (-545) * S) * (x ^ 9 * (1 - x) ^ 5) + (3003 + (1967/2) * s + (1538) * C + (-582) * S) * (x ^ 10 * (1 - x) ^ 4) + (1365 + (483) * s + (920) * C + (-440) * S) * (x ^ 11 * (1 - x) ^ 3) + (455 + (343/2) * s + (396) * C + (-225) * S) * (x ^ 12 * (1 - x) ^ 2) + (105 + (42) * s + (112) * C + (-70) * S) * (x ^ 13 * (1 - x) ^ 1) + (15 + (6) * s + (16) * C + (-10) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (105 + (7) * s + (1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (455 + (91/2) * s + (13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (1365 + (182) * s + (78) * C + (-1) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (3003 + (1001/2) * s + (287) * C + (-11) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (5005 + (1001) * s + (725) * C + (-56) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (6435 + (1501) * s + (1332) * C + (-174) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (6435 + (3425/2) * s + (1836) * C + (-366) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (5005 + (1491) * s + (1926) * C + (-545) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (3003 + (1967/2) * s + (1538) * C + (-582) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1365 + (483) * s + (920) * C + (-440) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (455 + (343/2) * s + (396) * C + (-225) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (105 + (42) * s + (112) * C + (-70) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (15 + (6) * s + (16) * C + (-10) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_1 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((s/2 : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_CC + (-1) * h_SS) (by linear_combination (2) * h_CS)
  have h3 : z ^ 3 = ((S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sC + (-1/2) * h_sS) (by linear_combination (1/2) * h_sS + (1/2) * h_sC)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (1) * h_SS + (1) * h_CC)
  have h5 : z ^ 5 = ((-S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((-(s/2) : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-2) * h_CS) (by linear_combination (-1) * h_SS + (1) * h_CC)
  have h7 : z ^ 7 = ((-C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sC + (-1/2) * h_sS) (by linear_combination (-1/2) * h_sS + (1/2) * h_sC)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (1 : ℝ) (0 : ℝ) x (C) (S) (s/2) (s/2) (S) (C) (0) (1) (-S) (C) (-(s/2)) (s/2) (-C) (S) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_1 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

private lemma pos_15 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 2 + ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 4 + ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 5 - ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 6 - ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 9 + ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 10 + ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 11 - ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 13 - ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 15 - (1 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 2 + ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 4 + ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 5 - ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 6 - ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 9 + ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 10 + ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 11 - ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 13 - ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 15 - (1 : ℝ) * x ^ 16 =
      x * (1 - x) * ((1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (105 + (7) * s + (1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) + (455 + (91/2) * s + (13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) + (1365 + (182) * s + (78) * C + (-1) * S) * (x ^ 4 * (1 - x) ^ 10) + (3003 + (1001/2) * s + (287) * C + (-11) * S) * (x ^ 5 * (1 - x) ^ 9) + (5005 + (1001) * s + (725) * C + (-56) * S) * (x ^ 6 * (1 - x) ^ 8) + (6435 + (1501) * s + (1332) * C + (-174) * S) * (x ^ 7 * (1 - x) ^ 7) + (6435 + (3425/2) * s + (1836) * C + (-366) * S) * (x ^ 8 * (1 - x) ^ 6) + (5005 + (1491) * s + (1926) * C + (-545) * S) * (x ^ 9 * (1 - x) ^ 5) + (3003 + (1967/2) * s + (1538) * C + (-582) * S) * (x ^ 10 * (1 - x) ^ 4) + (1365 + (483) * s + (920) * C + (-440) * S) * (x ^ 11 * (1 - x) ^ 3) + (455 + (343/2) * s + (396) * C + (-225) * S) * (x ^ 12 * (1 - x) ^ 2) + (105 + (42) * s + (112) * C + (-70) * S) * (x ^ 13 * (1 - x) ^ 1) + (15 + (6) * s + (16) * C + (-10) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (105 + (7) * s + (1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (455 + (91/2) * s + (13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (1365 + (182) * s + (78) * C + (-1) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (3003 + (1001/2) * s + (287) * C + (-11) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (5005 + (1001) * s + (725) * C + (-56) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (6435 + (1501) * s + (1332) * C + (-174) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (6435 + (3425/2) * s + (1836) * C + (-366) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (5005 + (1491) * s + (1926) * C + (-545) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (3003 + (1967/2) * s + (1538) * C + (-582) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1365 + (483) * s + (920) * C + (-440) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (455 + (343/2) * s + (396) * C + (-225) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (105 + (42) * s + (112) * C + (-70) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (15 + (6) * s + (16) * C + (-10) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_15 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((s/2 : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_CC + (-1) * h_SS) (by linear_combination (-2) * h_CS)
  have h3 : z ^ 3 = ((S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sC + (-1/2) * h_sS) (by linear_combination (-1/2) * h_sS + (-1/2) * h_sC)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (-1) * h_SS + (-1) * h_CC)
  have h5 : z ^ 5 = ((-S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((-(s/2) : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-2) * h_CS) (by linear_combination (1) * h_SS + (-1) * h_CC)
  have h7 : z ^ 7 = ((-C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sC + (-1/2) * h_sS) (by linear_combination (1/2) * h_sS + (-1/2) * h_sC)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (1 : ℝ) (0 : ℝ) x (C) (-S) (s/2) (-(s/2)) (S) (-C) (0) (-1) (-S) (-C) (-(s/2)) (-(s/2)) (-C) (-S) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_15 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

private lemma pos_7 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 2 + ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 4 + ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 5 - ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 6 - ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 9 + ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 10 + ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 11 - ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 13 - ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 15 - (1 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 2 + ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 4 + ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 5 - ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 6 - ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 9 + ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 10 + ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 11 - ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 13 - ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 15 - (1 : ℝ) * x ^ 16 =
      x * (1 - x) * ((1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (105 + (7) * s + (-1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) + (455 + (91/2) * s + (-13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) + (1365 + (182) * s + (-78) * C + (1) * S) * (x ^ 4 * (1 - x) ^ 10) + (3003 + (1001/2) * s + (-287) * C + (11) * S) * (x ^ 5 * (1 - x) ^ 9) + (5005 + (1001) * s + (-725) * C + (56) * S) * (x ^ 6 * (1 - x) ^ 8) + (6435 + (1501) * s + (-1332) * C + (174) * S) * (x ^ 7 * (1 - x) ^ 7) + (6435 + (3425/2) * s + (-1836) * C + (366) * S) * (x ^ 8 * (1 - x) ^ 6) + (5005 + (1491) * s + (-1926) * C + (545) * S) * (x ^ 9 * (1 - x) ^ 5) + (3003 + (1967/2) * s + (-1538) * C + (582) * S) * (x ^ 10 * (1 - x) ^ 4) + (1365 + (483) * s + (-920) * C + (440) * S) * (x ^ 11 * (1 - x) ^ 3) + (455 + (343/2) * s + (-396) * C + (225) * S) * (x ^ 12 * (1 - x) ^ 2) + (105 + (42) * s + (-112) * C + (70) * S) * (x ^ 13 * (1 - x) ^ 1) + (15 + (6) * s + (-16) * C + (10) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (105 + (7) * s + (-1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (455 + (91/2) * s + (-13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (1365 + (182) * s + (-78) * C + (1) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (3003 + (1001/2) * s + (-287) * C + (11) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (5005 + (1001) * s + (-725) * C + (56) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (6435 + (1501) * s + (-1332) * C + (174) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (6435 + (3425/2) * s + (-1836) * C + (366) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (5005 + (1491) * s + (-1926) * C + (545) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (3003 + (1967/2) * s + (-1538) * C + (582) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1365 + (483) * s + (-920) * C + (440) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (455 + (343/2) * s + (-396) * C + (225) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (105 + (42) * s + (-112) * C + (70) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (15 + (6) * s + (-16) * C + (10) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_7 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((-C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((s/2 : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_CC + (-1) * h_SS) (by linear_combination (-2) * h_CS)
  have h3 : z ^ 3 = ((-S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sC + (1/2) * h_sS) (by linear_combination (1/2) * h_sS + (1/2) * h_sC)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (-1) * h_SS + (-1) * h_CC)
  have h5 : z ^ 5 = ((S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((-(s/2) : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-2) * h_CS) (by linear_combination (1) * h_SS + (-1) * h_CC)
  have h7 : z ^ 7 = ((C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sC + (1/2) * h_sS) (by linear_combination (-1/2) * h_sS + (1/2) * h_sC)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (1 : ℝ) (0 : ℝ) x (-C) (S) (s/2) (-(s/2)) (-S) (C) (0) (-1) (S) (C) (-(s/2)) (-(s/2)) (C) (S) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_7 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

private lemma pos_9 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 2 + ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 4 + ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 5 - ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 6 - ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 9 + ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 10 + ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 11 - ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 13 - ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 15 - (1 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 2 + ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 4 + ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 5 - ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 6 - ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 7 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 8 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 9 + ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 10 + ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 11 - ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 13 - ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 14 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 15 - (1 : ℝ) * x ^ 16 =
      x * (1 - x) * ((1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (105 + (7) * s + (-1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) + (455 + (91/2) * s + (-13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) + (1365 + (182) * s + (-78) * C + (1) * S) * (x ^ 4 * (1 - x) ^ 10) + (3003 + (1001/2) * s + (-287) * C + (11) * S) * (x ^ 5 * (1 - x) ^ 9) + (5005 + (1001) * s + (-725) * C + (56) * S) * (x ^ 6 * (1 - x) ^ 8) + (6435 + (1501) * s + (-1332) * C + (174) * S) * (x ^ 7 * (1 - x) ^ 7) + (6435 + (3425/2) * s + (-1836) * C + (366) * S) * (x ^ 8 * (1 - x) ^ 6) + (5005 + (1491) * s + (-1926) * C + (545) * S) * (x ^ 9 * (1 - x) ^ 5) + (3003 + (1967/2) * s + (-1538) * C + (582) * S) * (x ^ 10 * (1 - x) ^ 4) + (1365 + (483) * s + (-920) * C + (440) * S) * (x ^ 11 * (1 - x) ^ 3) + (455 + (343/2) * s + (-396) * C + (225) * S) * (x ^ 12 * (1 - x) ^ 2) + (105 + (42) * s + (-112) * C + (70) * S) * (x ^ 13 * (1 - x) ^ 1) + (15 + (6) * s + (-16) * C + (10) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (15 + (1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (105 + (7) * s + (-1) * C + (0) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (455 + (91/2) * s + (-13) * C + (0) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (1365 + (182) * s + (-78) * C + (1) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (3003 + (1001/2) * s + (-287) * C + (11) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (5005 + (1001) * s + (-725) * C + (56) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (6435 + (1501) * s + (-1332) * C + (174) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (6435 + (3425/2) * s + (-1836) * C + (366) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (5005 + (1491) * s + (-1926) * C + (545) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (3003 + (1967/2) * s + (-1538) * C + (582) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1365 + (483) * s + (-920) * C + (440) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (455 + (343/2) * s + (-396) * C + (225) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (105 + (42) * s + (-112) * C + (70) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (15 + (6) * s + (-16) * C + (10) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_9 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((-C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((s/2 : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_CC + (-1) * h_SS) (by linear_combination (2) * h_CS)
  have h3 : z ^ 3 = ((-S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sC + (1/2) * h_sS) (by linear_combination (-1/2) * h_sS + (-1/2) * h_sC)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (1) * h_SS + (1) * h_CC)
  have h5 : z ^ 5 = ((S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((-(s/2) : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-2) * h_CS) (by linear_combination (-1) * h_SS + (1) * h_CC)
  have h7 : z ^ 7 = ((C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sC + (1/2) * h_sS) (by linear_combination (1/2) * h_sS + (-1/2) * h_sC)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (1 : ℝ) (0 : ℝ) x (-C) (-S) (s/2) (s/2) (-S) (-C) (0) (1) (S) (-C) (-(s/2)) (s/2) (C) (-S) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_9 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

private lemma pos_3 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 2 + ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 4 + ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 5 - ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 6 - ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 7 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 8 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 9 + ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 10 + ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 11 - ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 13 - ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 14 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 15 - (1 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 2 + ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 4 + ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 5 - ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 6 - ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 7 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 8 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (s/2)) * x ^ 9 + ((1 : ℝ) * (-C) - (0 : ℝ) * (-S)) * x ^ 10 + ((1 : ℝ) * (-S) - (0 : ℝ) * (C)) * x ^ 11 - ((1 : ℝ) * (C) - (0 : ℝ) * (-S)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (-1)) * x ^ 13 - ((1 : ℝ) * (S) - (0 : ℝ) * (C)) * x ^ 14 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (s/2)) * x ^ 15 - (1 : ℝ) * x ^ 16 =
      x * (1 - x) * ((1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (15 + (-1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (105 + (-7) * s + (0) * C + (1) * S) * (x ^ 2 * (1 - x) ^ 12) + (455 + (-91/2) * s + (0) * C + (13) * S) * (x ^ 3 * (1 - x) ^ 11) + (1365 + (-182) * s + (1) * C + (78) * S) * (x ^ 4 * (1 - x) ^ 10) + (3003 + (-1001/2) * s + (11) * C + (287) * S) * (x ^ 5 * (1 - x) ^ 9) + (5005 + (-1001) * s + (56) * C + (725) * S) * (x ^ 6 * (1 - x) ^ 8) + (6435 + (-1501) * s + (174) * C + (1332) * S) * (x ^ 7 * (1 - x) ^ 7) + (6435 + (-3425/2) * s + (366) * C + (1836) * S) * (x ^ 8 * (1 - x) ^ 6) + (5005 + (-1491) * s + (545) * C + (1926) * S) * (x ^ 9 * (1 - x) ^ 5) + (3003 + (-1967/2) * s + (582) * C + (1538) * S) * (x ^ 10 * (1 - x) ^ 4) + (1365 + (-483) * s + (440) * C + (920) * S) * (x ^ 11 * (1 - x) ^ 3) + (455 + (-343/2) * s + (225) * C + (396) * S) * (x ^ 12 * (1 - x) ^ 2) + (105 + (-42) * s + (70) * C + (112) * S) * (x ^ 13 * (1 - x) ^ 1) + (15 + (-6) * s + (10) * C + (16) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (15 + (-1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (105 + (-7) * s + (0) * C + (1) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (455 + (-91/2) * s + (0) * C + (13) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (1365 + (-182) * s + (1) * C + (78) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (3003 + (-1001/2) * s + (11) * C + (287) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (5005 + (-1001) * s + (56) * C + (725) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (6435 + (-1501) * s + (174) * C + (1332) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (6435 + (-3425/2) * s + (366) * C + (1836) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (5005 + (-1491) * s + (545) * C + (1926) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (3003 + (-1967/2) * s + (582) * C + (1538) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1365 + (-483) * s + (440) * C + (920) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (455 + (-343/2) * s + (225) * C + (396) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (105 + (-42) * s + (70) * C + (112) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (15 + (-6) * s + (10) * C + (16) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_3 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((-(s/2) : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_SS + (-1) * h_CC) (by linear_combination (2) * h_CS)
  have h3 : z ^ 3 = ((-C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sS + (-1/2) * h_sC) (by linear_combination (-1/2) * h_sC + (1/2) * h_sS)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (-1) * h_CC + (-1) * h_SS)
  have h5 : z ^ 5 = ((C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((s/2 : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (2) * h_CS) (by linear_combination (1) * h_CC + (-1) * h_SS)
  have h7 : z ^ 7 = ((-S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sS + (-1/2) * h_sC) (by linear_combination (1/2) * h_sC + (1/2) * h_sS)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (1 : ℝ) (0 : ℝ) x (S) (C) (-(s/2)) (s/2) (-C) (-S) (0) (-1) (C) (-S) (s/2) (s/2) (-S) (C) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_3 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

private lemma pos_13 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 2 + ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 4 + ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 5 - ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 6 - ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 7 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 8 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 9 + ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 10 + ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 11 - ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 13 - ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 14 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 15 - (1 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (1 : ℝ) * x ^ 1 - ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 2 + ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 3 - ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 4 + ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 5 - ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 6 - ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 7 - ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 8 + ((1 : ℝ) * (-(s/2)) - (0 : ℝ) * (-(s/2))) * x ^ 9 + ((1 : ℝ) * (-C) - (0 : ℝ) * (S)) * x ^ 10 + ((1 : ℝ) * (-S) - (0 : ℝ) * (-C)) * x ^ 11 - ((1 : ℝ) * (C) - (0 : ℝ) * (S)) * x ^ 12 + ((1 : ℝ) * (0) - (0 : ℝ) * (1)) * x ^ 13 - ((1 : ℝ) * (S) - (0 : ℝ) * (-C)) * x ^ 14 + ((1 : ℝ) * (s/2) - (0 : ℝ) * (-(s/2))) * x ^ 15 - (1 : ℝ) * x ^ 16 =
      x * (1 - x) * ((1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (15 + (-1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (105 + (-7) * s + (0) * C + (1) * S) * (x ^ 2 * (1 - x) ^ 12) + (455 + (-91/2) * s + (0) * C + (13) * S) * (x ^ 3 * (1 - x) ^ 11) + (1365 + (-182) * s + (1) * C + (78) * S) * (x ^ 4 * (1 - x) ^ 10) + (3003 + (-1001/2) * s + (11) * C + (287) * S) * (x ^ 5 * (1 - x) ^ 9) + (5005 + (-1001) * s + (56) * C + (725) * S) * (x ^ 6 * (1 - x) ^ 8) + (6435 + (-1501) * s + (174) * C + (1332) * S) * (x ^ 7 * (1 - x) ^ 7) + (6435 + (-3425/2) * s + (366) * C + (1836) * S) * (x ^ 8 * (1 - x) ^ 6) + (5005 + (-1491) * s + (545) * C + (1926) * S) * (x ^ 9 * (1 - x) ^ 5) + (3003 + (-1967/2) * s + (582) * C + (1538) * S) * (x ^ 10 * (1 - x) ^ 4) + (1365 + (-483) * s + (440) * C + (920) * S) * (x ^ 11 * (1 - x) ^ 3) + (455 + (-343/2) * s + (225) * C + (396) * S) * (x ^ 12 * (1 - x) ^ 2) + (105 + (-42) * s + (70) * C + (112) * S) * (x ^ 13 * (1 - x) ^ 1) + (15 + (-6) * s + (10) * C + (16) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (1 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (15 + (-1/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (105 + (-7) * s + (0) * C + (1) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (455 + (-91/2) * s + (0) * C + (13) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (1365 + (-182) * s + (1) * C + (78) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (3003 + (-1001/2) * s + (11) * C + (287) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (5005 + (-1001) * s + (56) * C + (725) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (6435 + (-1501) * s + (174) * C + (1332) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (6435 + (-3425/2) * s + (366) * C + (1836) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (5005 + (-1491) * s + (545) * C + (1926) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (3003 + (-1967/2) * s + (582) * C + (1538) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1365 + (-483) * s + (440) * C + (920) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (455 + (-343/2) * s + (225) * C + (396) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (105 + (-42) * s + (70) * C + (112) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (15 + (-6) * s + (10) * C + (16) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_13 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((-(s/2) : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_SS + (-1) * h_CC) (by linear_combination (-2) * h_CS)
  have h3 : z ^ 3 = ((-C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sS + (-1/2) * h_sC) (by linear_combination (1/2) * h_sC + (-1/2) * h_sS)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (1) * h_CC + (1) * h_SS)
  have h5 : z ^ 5 = ((C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((s/2 : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (2) * h_CS) (by linear_combination (-1) * h_CC + (1) * h_SS)
  have h7 : z ^ 7 = ((-S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sS + (-1/2) * h_sC) (by linear_combination (-1/2) * h_sC + (-1/2) * h_sS)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (1 : ℝ) (0 : ℝ) x (S) (-C) (-(s/2)) (-(s/2)) (-C) (S) (0) (1) (C) (S) (s/2) (-(s/2)) (-S) (-C) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_13 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

private lemma pos_5 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (4 : ℝ) * x ^ 1 - ((4 : ℝ) * (s/2) - (-9 : ℝ) * (-(s/2))) * x ^ 2 + ((4 : ℝ) * (-S) - (-9 : ℝ) * (C)) * x ^ 3 - ((4 : ℝ) * (0) - (-9 : ℝ) * (1)) * x ^ 4 + ((4 : ℝ) * (-C) - (-9 : ℝ) * (-S)) * x ^ 5 - ((4 : ℝ) * (S) - (-9 : ℝ) * (C)) * x ^ 6 - ((4 : ℝ) * (C) - (-9 : ℝ) * (-S)) * x ^ 7 - ((4 : ℝ) * (-(s/2)) - (-9 : ℝ) * (-(s/2))) * x ^ 8 + ((4 : ℝ) * (-(s/2)) - (-9 : ℝ) * (-(s/2))) * x ^ 9 + ((4 : ℝ) * (C) - (-9 : ℝ) * (-S)) * x ^ 10 + ((4 : ℝ) * (S) - (-9 : ℝ) * (C)) * x ^ 11 - ((4 : ℝ) * (-C) - (-9 : ℝ) * (-S)) * x ^ 12 + ((4 : ℝ) * (0) - (-9 : ℝ) * (1)) * x ^ 13 - ((4 : ℝ) * (-S) - (-9 : ℝ) * (C)) * x ^ 14 + ((4 : ℝ) * (s/2) - (-9 : ℝ) * (-(s/2))) * x ^ 15 - (4 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (4 : ℝ) * x ^ 1 - ((4 : ℝ) * (s/2) - (-9 : ℝ) * (-(s/2))) * x ^ 2 + ((4 : ℝ) * (-S) - (-9 : ℝ) * (C)) * x ^ 3 - ((4 : ℝ) * (0) - (-9 : ℝ) * (1)) * x ^ 4 + ((4 : ℝ) * (-C) - (-9 : ℝ) * (-S)) * x ^ 5 - ((4 : ℝ) * (S) - (-9 : ℝ) * (C)) * x ^ 6 - ((4 : ℝ) * (C) - (-9 : ℝ) * (-S)) * x ^ 7 - ((4 : ℝ) * (-(s/2)) - (-9 : ℝ) * (-(s/2))) * x ^ 8 + ((4 : ℝ) * (-(s/2)) - (-9 : ℝ) * (-(s/2))) * x ^ 9 + ((4 : ℝ) * (C) - (-9 : ℝ) * (-S)) * x ^ 10 + ((4 : ℝ) * (S) - (-9 : ℝ) * (C)) * x ^ 11 - ((4 : ℝ) * (-C) - (-9 : ℝ) * (-S)) * x ^ 12 + ((4 : ℝ) * (0) - (-9 : ℝ) * (1)) * x ^ 13 - ((4 : ℝ) * (-S) - (-9 : ℝ) * (C)) * x ^ 14 + ((4 : ℝ) * (s/2) - (-9 : ℝ) * (-(s/2))) * x ^ 15 - (4 : ℝ) * x ^ 16 =
      x * (1 - x) * ((4 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (60 + (5/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (420 + (35) * s + (9) * C + (-4) * S) * (x ^ 2 * (1 - x) ^ 12) + (1811 + (455/2) * s + (117) * C + (-52) * S) * (x ^ 3 * (1 - x) ^ 11) + (5352 + (910) * s + (698) * C + (-321) * S) * (x ^ 4 * (1 - x) ^ 10) + (11418 + (5005/2) * s + (2521) * C + (-1247) * S) * (x ^ 5 * (1 - x) ^ 9) + (18040 + (5005) * s + (6121) * C + (-3386) * S) * (x ^ 6 * (1 - x) ^ 8) + (21285 + (7514) * s + (10482) * C + (-6732) * S) * (x ^ 7 * (1 - x) ^ 7) + (18612 + (17251/2) * s + (12900) * C + (-9990) * S) * (x ^ 8 * (1 - x) ^ 6) + (11704 + (7644) * s + (11374) * C + (-11115) * S) * (x ^ 9 * (1 - x) ^ 5) + (4884 + (10465/2) * s + (6996) * C + (-9230) * S) * (x ^ 10 * (1 - x) ^ 4) + (1005 + (2730) * s + (2830) * C + (-5642) * S) * (x ^ 11 * (1 - x) ^ 3) + (-151 + (2093/2) * s + (684) * C + (-2457) * S) * (x ^ 12 * (1 - x) ^ 2) + (-147 + (273) * s + (98) * C + (-700) * S) * (x ^ 13 * (1 - x) ^ 1) + (-21 + (39) * s + (14) * C + (-100) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (4 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (60 + (5/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (420 + (35) * s + (9) * C + (-4) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (1811 + (455/2) * s + (117) * C + (-52) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (5352 + (910) * s + (698) * C + (-321) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (11418 + (5005/2) * s + (2521) * C + (-1247) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (18040 + (5005) * s + (6121) * C + (-3386) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (21285 + (7514) * s + (10482) * C + (-6732) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (18612 + (17251/2) * s + (12900) * C + (-9990) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (11704 + (7644) * s + (11374) * C + (-11115) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (4884 + (10465/2) * s + (6996) * C + (-9230) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1005 + (2730) * s + (2830) * C + (-5642) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (-151 + (2093/2) * s + (684) * C + (-2457) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (-147 + (273) * s + (98) * C + (-700) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (-21 + (39) * s + (14) * C + (-100) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_5 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((-S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((-(s/2) : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_SS + (-1) * h_CC) (by linear_combination (-2) * h_CS)
  have h3 : z ^ 3 = ((C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sS + (1/2) * h_sC) (by linear_combination (-1/2) * h_sC + (1/2) * h_sS)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (1) * h_CC + (1) * h_SS)
  have h5 : z ^ 5 = ((-C : ℝ) : ℂ) + ((-S : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((s/2 : ℝ) : ℂ) + ((-(s/2) : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (2) * h_CS) (by linear_combination (-1) * h_CC + (1) * h_SS)
  have h7 : z ^ 7 = ((S : ℝ) : ℂ) + ((C : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sS + (1/2) * h_sC) (by linear_combination (1/2) * h_sC + (1/2) * h_sS)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((4 : ℝ) : ℂ) + ((-9 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (4 : ℝ) (-9 : ℝ) x (-S) (C) (-(s/2)) (-(s/2)) (C) (-S) (0) (1) (-C) (-S) (s/2) (-(s/2)) (S) (C) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_5 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((4 : ℝ) : ℂ) + ((-9 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

private lemma pos_11 (x s C S : ℝ) (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (hx : 0 < x) (hx1 : x < 1) :
    0 < (4 : ℝ) * x ^ 1 - ((4 : ℝ) * (s/2) - (9 : ℝ) * (s/2)) * x ^ 2 + ((4 : ℝ) * (-S) - (9 : ℝ) * (-C)) * x ^ 3 - ((4 : ℝ) * (0) - (9 : ℝ) * (-1)) * x ^ 4 + ((4 : ℝ) * (-C) - (9 : ℝ) * (S)) * x ^ 5 - ((4 : ℝ) * (S) - (9 : ℝ) * (-C)) * x ^ 6 - ((4 : ℝ) * (C) - (9 : ℝ) * (S)) * x ^ 7 - ((4 : ℝ) * (-(s/2)) - (9 : ℝ) * (s/2)) * x ^ 8 + ((4 : ℝ) * (-(s/2)) - (9 : ℝ) * (s/2)) * x ^ 9 + ((4 : ℝ) * (C) - (9 : ℝ) * (S)) * x ^ 10 + ((4 : ℝ) * (S) - (9 : ℝ) * (-C)) * x ^ 11 - ((4 : ℝ) * (-C) - (9 : ℝ) * (S)) * x ^ 12 + ((4 : ℝ) * (0) - (9 : ℝ) * (-1)) * x ^ 13 - ((4 : ℝ) * (-S) - (9 : ℝ) * (-C)) * x ^ 14 + ((4 : ℝ) * (s/2) - (9 : ℝ) * (s/2)) * x ^ 15 - (4 : ℝ) * x ^ 16 := by
  have hy : 0 < 1 - x := by linarith
  have e : (4 : ℝ) * x ^ 1 - ((4 : ℝ) * (s/2) - (9 : ℝ) * (s/2)) * x ^ 2 + ((4 : ℝ) * (-S) - (9 : ℝ) * (-C)) * x ^ 3 - ((4 : ℝ) * (0) - (9 : ℝ) * (-1)) * x ^ 4 + ((4 : ℝ) * (-C) - (9 : ℝ) * (S)) * x ^ 5 - ((4 : ℝ) * (S) - (9 : ℝ) * (-C)) * x ^ 6 - ((4 : ℝ) * (C) - (9 : ℝ) * (S)) * x ^ 7 - ((4 : ℝ) * (-(s/2)) - (9 : ℝ) * (s/2)) * x ^ 8 + ((4 : ℝ) * (-(s/2)) - (9 : ℝ) * (s/2)) * x ^ 9 + ((4 : ℝ) * (C) - (9 : ℝ) * (S)) * x ^ 10 + ((4 : ℝ) * (S) - (9 : ℝ) * (-C)) * x ^ 11 - ((4 : ℝ) * (-C) - (9 : ℝ) * (S)) * x ^ 12 + ((4 : ℝ) * (0) - (9 : ℝ) * (-1)) * x ^ 13 - ((4 : ℝ) * (-S) - (9 : ℝ) * (-C)) * x ^ 14 + ((4 : ℝ) * (s/2) - (9 : ℝ) * (s/2)) * x ^ 15 - (4 : ℝ) * x ^ 16 =
      x * (1 - x) * ((4 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) + (60 + (5/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) + (420 + (35) * s + (9) * C + (-4) * S) * (x ^ 2 * (1 - x) ^ 12) + (1811 + (455/2) * s + (117) * C + (-52) * S) * (x ^ 3 * (1 - x) ^ 11) + (5352 + (910) * s + (698) * C + (-321) * S) * (x ^ 4 * (1 - x) ^ 10) + (11418 + (5005/2) * s + (2521) * C + (-1247) * S) * (x ^ 5 * (1 - x) ^ 9) + (18040 + (5005) * s + (6121) * C + (-3386) * S) * (x ^ 6 * (1 - x) ^ 8) + (21285 + (7514) * s + (10482) * C + (-6732) * S) * (x ^ 7 * (1 - x) ^ 7) + (18612 + (17251/2) * s + (12900) * C + (-9990) * S) * (x ^ 8 * (1 - x) ^ 6) + (11704 + (7644) * s + (11374) * C + (-11115) * S) * (x ^ 9 * (1 - x) ^ 5) + (4884 + (10465/2) * s + (6996) * C + (-9230) * S) * (x ^ 10 * (1 - x) ^ 4) + (1005 + (2730) * s + (2830) * C + (-5642) * S) * (x ^ 11 * (1 - x) ^ 3) + (-151 + (2093/2) * s + (684) * C + (-2457) * S) * (x ^ 12 * (1 - x) ^ 2) + (-147 + (273) * s + (98) * C + (-700) * S) * (x ^ 13 * (1 - x) ^ 1) + (-21 + (39) * s + (14) * C + (-100) * S) * (x ^ 14 * (1 - x) ^ 0)) := by ring
  rw [e]
  have m0 : 0 < (4 + (0) * s + (0) * C + (0) * S) * (x ^ 0 * (1 - x) ^ 14) :=
    mul_pos (by linarith) (mul_pos (pow_pos hx _) (pow_pos hy _))
  have m1 : 0 ≤ (60 + (5/2) * s + (0) * C + (0) * S) * (x ^ 1 * (1 - x) ^ 13) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m2 : 0 ≤ (420 + (35) * s + (9) * C + (-4) * S) * (x ^ 2 * (1 - x) ^ 12) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m3 : 0 ≤ (1811 + (455/2) * s + (117) * C + (-52) * S) * (x ^ 3 * (1 - x) ^ 11) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m4 : 0 ≤ (5352 + (910) * s + (698) * C + (-321) * S) * (x ^ 4 * (1 - x) ^ 10) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m5 : 0 ≤ (11418 + (5005/2) * s + (2521) * C + (-1247) * S) * (x ^ 5 * (1 - x) ^ 9) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m6 : 0 ≤ (18040 + (5005) * s + (6121) * C + (-3386) * S) * (x ^ 6 * (1 - x) ^ 8) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m7 : 0 ≤ (21285 + (7514) * s + (10482) * C + (-6732) * S) * (x ^ 7 * (1 - x) ^ 7) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m8 : 0 ≤ (18612 + (17251/2) * s + (12900) * C + (-9990) * S) * (x ^ 8 * (1 - x) ^ 6) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m9 : 0 ≤ (11704 + (7644) * s + (11374) * C + (-11115) * S) * (x ^ 9 * (1 - x) ^ 5) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m10 : 0 ≤ (4884 + (10465/2) * s + (6996) * C + (-9230) * S) * (x ^ 10 * (1 - x) ^ 4) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m11 : 0 ≤ (1005 + (2730) * s + (2830) * C + (-5642) * S) * (x ^ 11 * (1 - x) ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m12 : 0 ≤ (-151 + (2093/2) * s + (684) * C + (-2457) * S) * (x ^ 12 * (1 - x) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m13 : 0 ≤ (-147 + (273) * s + (98) * C + (-700) * S) * (x ^ 13 * (1 - x) ^ 1) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  have m14 : 0 ≤ (-21 + (39) * s + (14) * C + (-100) * S) * (x ^ 14 * (1 - x) ^ 0) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hy.le _))
  exact mul_pos (mul_pos hx hy) (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (m0) m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) m14)

private lemma case_11 (χ : DirichletCharacter ℂ 17) (z : ℂ) (hz : χ (3 : ZMod 17) = z)
    (h : z ^ 8 = -1) (hχ : χ ≠ 1) (s C S : ℝ) (h_ss : s * s = 2) (h_CC : C * C = (2 + s) / 4)
    (h_SS : S * S = (2 - s) / 4) (h_CS : C * S = s / 4) (h_sC : s * C = C + S) (h_sS : s * S = C - S)
    (b1 : 1414213 / 1000000 < s) (b2 : s < 1414214 / 1000000)
    (b3 : 92387 / 100000 < C) (b4 : C < 92389 / 100000)
    (b5 : 38268 / 100000 < S) (b6 : S < 38269 / 100000)
    (h1 : z = ((-S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h2 : z ^ 2 = ((-(s/2) : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 2 = z * z from sq z, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1) * h_SS + (-1) * h_CC) (by linear_combination (2) * h_CS)
  have h3 : z ^ 3 = ((C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I := by
    rw [show z ^ 3 = z ^ 2 * z from pow_succ z 2, h2, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (1/2) * h_sS + (1/2) * h_sC) (by linear_combination (1/2) * h_sC + (-1/2) * h_sS)
  have h4 : z ^ 4 = ((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I := by
    rw [show z ^ 4 = z ^ 3 * z from pow_succ z 3, h3, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by linear_combination (-1) * h_CC + (-1) * h_SS)
  have h5 : z ^ 5 = ((-C : ℝ) : ℂ) + ((S : ℝ) : ℂ) * I := by
    rw [show z ^ 5 = z ^ 4 * z from pow_succ z 4, h4, h1]
    exact mulI _ _ _ _ _ _ (by ring) (by ring)
  have h6 : z ^ 6 = ((s/2 : ℝ) : ℂ) + ((s/2 : ℝ) : ℂ) * I := by
    rw [show z ^ 6 = z ^ 5 * z from pow_succ z 5, h5, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (2) * h_CS) (by linear_combination (1) * h_CC + (-1) * h_SS)
  have h7 : z ^ 7 = ((S : ℝ) : ℂ) + ((-C : ℝ) : ℂ) * I := by
    rw [show z ^ 7 = z ^ 6 * z from pow_succ z 6, h6, h1]
    exact mulI _ _ _ _ _ _ (by linear_combination (-1/2) * h_sS + (1/2) * h_sC) (by linear_combination (-1/2) * h_sC + (-1/2) * h_sS)
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      0 < ((((4 : ℝ) : ℂ) + ((9 : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range 17, χ (a : ZMod 17) * (x : ℂ) ^ a).re := by
    intro x hx hx1
    rw [sum_expand χ z hz h (x : ℂ),
      re_formula (4 : ℝ) (9 : ℝ) x (-S) (-C) (-(s/2)) (s/2) (C) (S) (0) (-1) (-C) (S) (s/2) (s/2) (S) (-C) z h1 h2 h3 h4 h5 h6 h7]
    exact pos_11 x s C S b1 b2 b3 b4 b5 b6 hx hx1
  exact LFunction_ofReal_ne_zero_of_kernel χ hχ (((4 : ℝ) : ℂ) + ((9 : ℝ) : ℂ) * I)
    (fun x hx hx1 => (key x hx hx1).le)
    ⟨1 / 2, by norm_num, by norm_num, key (1 / 2) (by norm_num) (by norm_num)⟩ hσ

end SeventeenOdd

/-- `L(σ, χ) ≠ 0` for real `σ > 0` and each odd character `χ` modulo 17, the oddness being stated
as `χ(3)^8 = -1` for the generator 3 of the unit group. -/
theorem LFunction_ofReal_ne_zero_mod_17_odd (χ : DirichletCharacter ℂ 17) (h : χ (3 : ZMod 17) ^ 8 = -1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have hχ : χ ≠ 1 := by
    rintro rfl
    rw [MulChar.one_apply (IsUnit.of_mul_eq_one (6 : ZMod 17) (by decide))] at h
    norm_num at h
  obtain ⟨s, C, S, h_ss, h_CC, h_SS, h_CS, h_sC, h_sS, b1, b2, b3, b4, b5, b6⟩ := SeventeenOdd.consts
  rcases SeventeenOdd.roots (χ 3) h s C S h_ss h_CC h_SS with
    ((h1 | h1) | (h1 | h1)) | ((h1 | h1) | (h1 | h1))
  · exact SeventeenOdd.case_1 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ
  · exact SeventeenOdd.case_15 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ
  · exact SeventeenOdd.case_7 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ
  · exact SeventeenOdd.case_9 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ
  · exact SeventeenOdd.case_3 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ
  · exact SeventeenOdd.case_13 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ
  · exact SeventeenOdd.case_5 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ
  · exact SeventeenOdd.case_11 χ (χ 3) rfl h hχ s C S h_ss h_CC h_SS h_CS h_sC h_sS b1 b2 b3 b4 b5 b6 h1 hσ

end LeanLab.HelfgottMajor.RealAxisKernel

#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_mod_17_odd
