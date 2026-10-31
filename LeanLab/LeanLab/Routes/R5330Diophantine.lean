/-
R-5330, CLOUD MANUAL-M3, unit U-7000, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The Diophantine route.  Jones, Sato, Wada and Wiens 1976, Amer. Math. Monthly 83,
449-464, give a polynomial F in 26 variables whose positive values over ℕ²⁶ are
exactly the primes, F = (k + 2)(1 - Σ αᵢ²) with 14 polynomials αᵢ.  Binary
Goldbach at N then becomes the solubility of one explicit Diophantine system,
two copies of α = 0, 28 equations, plus k + k' + 4 = N, 29 in all, in 52 unknowns.
* `pos_form_iff`: (k + 2)(1 - Σ sᵢ²) > 0 iff every sᵢ = 0, so positivity of the
  JSWW form is exactly the system α = 0.
* `F_pos_iff`, `F_eq_of_pos`: the same for the explicit `F`, whose positive value
  is k + 2.
* `goldbach_iff_of_rep`: for any F whose positive values are the primes,
  Goldbach at N iff N = F x + F y with both values positive.  Unconditional.
* `goldbach_iff_system`: CONDITIONAL ON `JSWW1976`, the cited theorem,
  Goldbach at N iff the 29 equations α(X) = 0, α(Y) = 0 and X k + Y k + 4 = N
  have a solution in ℕ.
* `expected_dim`, `goldbach_expected_dim`, `birch_fails`: the degree bookkeeping
  of the barrier, degrees from numerics/r5330_diophantine.py.
* `F_zero_neg`: vacuity check, F at the origin is negative.
-/
import Mathlib

namespace LeanLab.Routes.R5330

open Finset

/-- Positivity of an MRDP style form (k + 2)(1 - Σ sᵢ²) is the vanishing of every sᵢ. -/
theorem pos_form_iff {m : ℕ} (k : ℕ) (s : Fin m → ℤ) :
    0 < ((k : ℤ) + 2) * (1 - ∑ i, s i ^ 2) ↔ ∀ i, s i = 0 := by
  have hk : (0 : ℤ) < (k : ℤ) + 2 := by positivity
  have hnn : ∀ i ∈ (univ : Finset (Fin m)), 0 ≤ s i ^ 2 := fun i _ => sq_nonneg _
  constructor
  · intro h
    have h1 : 0 < 1 - ∑ i, s i ^ 2 := (pos_iff_pos_of_mul_pos h).mp hk
    have h0 : ∑ i, s i ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg hnn)
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 i (mem_univ i)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  · intro h
    have h0 : ∑ i, s i ^ 2 = 0 := Finset.sum_eq_zero (fun i _ => by simp [h i])
    rw [h0]; linarith

/-- The 14 polynomials of Jones-Sato-Wada-Wiens, variables a, ..., z as X 0, ..., X 25. -/
def alpha (X : Fin 26 → ℕ) : Fin 14 → ℤ :=
  let a : ℤ := X 0; let b : ℤ := X 1; let c : ℤ := X 2; let d : ℤ := X 3
  let e : ℤ := X 4; let f : ℤ := X 5; let g : ℤ := X 6; let h : ℤ := X 7
  let i : ℤ := X 8; let j : ℤ := X 9; let k : ℤ := X 10; let l : ℤ := X 11
  let m : ℤ := X 12; let n : ℤ := X 13; let o : ℤ := X 14; let p : ℤ := X 15
  let q : ℤ := X 16; let r : ℤ := X 17; let s : ℤ := X 18; let t : ℤ := X 19
  let u : ℤ := X 20; let v : ℤ := X 21; let w : ℤ := X 22; let x : ℤ := X 23
  let y : ℤ := X 24; let z : ℤ := X 25
  ![w * z + h + j - q,
    (g * k + 2 * g + k + 1) * (h + j) + h - z,
    2 * n + p + q + z - e,
    16 * (k + 1) ^ 3 * (k + 2) * (n + 1) ^ 2 + 1 - f ^ 2,
    e ^ 3 * (e + 2) * (a + 1) ^ 2 + 1 - o ^ 2,
    (a ^ 2 - 1) * y ^ 2 + 1 - x ^ 2,
    16 * r ^ 2 * y ^ 4 * (a ^ 2 - 1) + 1 - u ^ 2,
    ((a + u ^ 2 * (u ^ 2 - a)) ^ 2 - 1) * (n + 4 * d * y) ^ 2 + 1 - (x + c * u) ^ 2,
    n + l + v - y,
    (a ^ 2 - 1) * l ^ 2 + 1 - m ^ 2,
    a * i + k + 1 - l - i,
    p + l * (a - n - 1) + b * (2 * a * n + 2 * a - n ^ 2 - 2 * n - 2) - m,
    q + y * (a - p - 1) + s * (2 * a * p + 2 * a - p ^ 2 - 2 * p - 2) - x,
    z + p * l * (a - p) + t * (2 * a * p - p ^ 2 - 1) - p * m]

/-- The JSWW polynomial, k = X 10. -/
def F (X : Fin 26 → ℕ) : ℤ := ((X 10 : ℤ) + 2) * (1 - ∑ i, alpha X i ^ 2)

/-- The cited theorem, JSWW 1976: the positive values of F over ℕ²⁶ are the primes. -/
def JSWW1976 : Prop := ∀ n : ℕ, n.Prime ↔ ∃ X : Fin 26 → ℕ, 0 < F X ∧ F X = n

theorem F_pos_iff (X : Fin 26 → ℕ) : 0 < F X ↔ ∀ i, alpha X i = 0 :=
  pos_form_iff (X 10) (alpha X)

theorem F_eq_of_pos {X : Fin 26 → ℕ} (h : 0 < F X) : F X = (X 10 : ℤ) + 2 := by
  have h0 := (F_pos_iff X).mp h
  have : ∑ i, alpha X i ^ 2 = 0 := Finset.sum_eq_zero (fun i _ => by simp [h0 i])
  simp [F, this]

/-- For any F whose positive values are the primes, binary Goldbach at N is the
solubility of F x + F y = N with both values positive.  Unconditional. -/
theorem goldbach_iff_of_rep {V : Type*} (G : V → ℤ)
    (hG : ∀ n : ℕ, n.Prime ↔ ∃ x, 0 < G x ∧ G x = n) (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N) ↔
      ∃ x y, 0 < G x ∧ 0 < G y ∧ G x + G y = N := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    obtain ⟨x, hx0, hx⟩ := (hG p).mp hp
    obtain ⟨y, hy0, hy⟩ := (hG q).mp hq
    exact ⟨x, y, hx0, hy0, by rw [hx, hy]; exact_mod_cast hpq⟩
  · rintro ⟨x, y, hx0, hy0, hxy⟩
    refine ⟨(G x).toNat, (G y).toNat, (hG _).mpr ⟨x, hx0, ?_⟩, (hG _).mpr ⟨y, hy0, ?_⟩, ?_⟩
    · exact (Int.toNat_of_nonneg hx0.le).symm
    · exact (Int.toNat_of_nonneg hy0.le).symm
    · have := Int.toNat_of_nonneg hx0.le
      have := Int.toNat_of_nonneg hy0.le
      omega

/-- CONDITIONAL ON `JSWW1976`: binary Goldbach at N is the solubility in ℕ of the
explicit system α(X) = 0, α(Y) = 0, X k + Y k + 4 = N, 28 + 1 equations in 52 unknowns. -/
theorem goldbach_iff_system (hJ : JSWW1976) (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N) ↔
      ∃ X Y : Fin 26 → ℕ, (∀ i, alpha X i = 0) ∧ (∀ i, alpha Y i = 0) ∧
        X 10 + Y 10 + 4 = N := by
  rw [goldbach_iff_of_rep F hJ N]
  constructor
  · rintro ⟨X, Y, hX, hY, hXY⟩
    refine ⟨X, Y, (F_pos_iff X).mp hX, (F_pos_iff Y).mp hY, ?_⟩
    rw [F_eq_of_pos hX, F_eq_of_pos hY] at hXY
    omega
  · rintro ⟨X, Y, hX, hY, hXY⟩
    have hX' := (F_pos_iff X).mpr hX
    have hY' := (F_pos_iff Y).mpr hY
    refine ⟨X, Y, hX', hY', ?_⟩
    rw [F_eq_of_pos hX', F_eq_of_pos hY']
    push_cast [← hXY]; ring

/-- Degrees of α₀, ..., α₁₃, computed by numerics/r5330_diophantine.py. -/
def alphaDeg : List ℕ := [2, 3, 1, 6, 6, 4, 8, 12, 1, 4, 2, 3, 3, 3]

/-- Expected dimension n - Σ dᵢ of α = 0 is -32: the circle method heuristic
predicts P^(-32) solutions in a box of side P. -/
theorem expected_dim : (26 : ℤ) - (alphaDeg.sum : ℤ) = -32 := by decide

/-- For the binary Goldbach system, two copies plus one linear equation, it is -65. -/
theorem goldbach_expected_dim : (52 : ℤ) - (2 * alphaDeg.sum + 1 : ℕ) = -65 := by decide

/-- Birch's condition for the single form Σ αᵢ² of degree 24, n - dim V* > 23 · 2^23,
fails with 26 variables by a factor of more than seven million. -/
theorem birch_fails : 26 * 7000000 < 23 * 2 ^ 23 := by norm_num

/-- Vacuity check: F is negative at the origin. -/
theorem F_zero_neg : F 0 < 0 := by
  simp [F, alpha, Fin.sum_univ_succ]

end LeanLab.Routes.R5330

#print axioms LeanLab.Routes.R5330.pos_form_iff
#print axioms LeanLab.Routes.R5330.F_pos_iff
#print axioms LeanLab.Routes.R5330.F_eq_of_pos
#print axioms LeanLab.Routes.R5330.goldbach_iff_of_rep
#print axioms LeanLab.Routes.R5330.goldbach_iff_system
#print axioms LeanLab.Routes.R5330.expected_dim
#print axioms LeanLab.Routes.R5330.goldbach_expected_dim
#print axioms LeanLab.Routes.R5330.birch_fails
#print axioms LeanLab.Routes.R5330.F_zero_neg
