/-
P0054 J. Pintz, "An approximate formula for Goldbach's problem with applications",
Riv. Mat. Univ. Parma 12 (2021), 181-199. Read 2026-10-18 from the journal PDF, which has no
text layer, by the rendered page images, pages 182 to 197. Everything in ExceptionalSet/Pintz2021
stays as it is; this folder adds what that file left out: the singular series (2.4), Lemma 2
display (4.9), and the exponent bookkeeping of Sections 3 to 5.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Theorems 1 and 2 are sums over generalized exceptional zeros whose
notation is taken from Pin1 and Pin2; they are not stated.

Readings: `L = log₂ X - √(log₂ X)`, display (4.1); `m ≤ X`; the sum in (4.9) runs over
`1 ≤ ν ≤ L` with `2^ν < m` and `q ∣ m - 2^ν`.
-/
import Mathlib

namespace LeanLab.Pintz2021
open Finset Real

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `C₀ = ∏_{p>2} (1 - 1/(p-1)²) = 0.66016...`, display (2.4). -/
def C0 : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)

/-- `𝔖(m) = 2 C₀ ∏_{p ∣ m, p > 2} (1 + 1/(p-2))`, display (2.4). -/
def Sing (m : ℕ) : ℝ :=
  2 * C0 * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))

/-- The upper end of the range of `ν`, display (4.1). -/
def Lnu (X : ℝ) : ℝ := Real.logb 2 X - Real.sqrt (Real.logb 2 X)

/-- Lemma 2, display (4.9): for `m ≤ X`, `q` odd squarefree and any `η > 0`,
`∑_{ν ≤ L, 2^ν < m, q ∣ m - 2^ν} 𝔖(m - 2^ν) ≤ η L` if `min(q, X) > C₀(η)`.
`C₀(η)` is written `Cη`. -/
def Lemma2 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ Cη : ℝ, ∀ (X : ℝ) (m q : ℕ), (m : ℝ) ≤ X → Odd q → Squarefree q →
    Cη < min (q : ℝ) X →
      ∑ ν ∈ (Finset.Icc 1 ⌊Lnu X⌋₊).filter (fun ν => 2 ^ ν < m ∧ q ∣ m - 2 ^ ν),
        Sing (m - 2 ^ ν) ≤ η * Lnu X


/-! ### Elementary facts about the singular series -/

/-- Each local factor `1 + 1/(p-2)` is at least 1 for `p > 2`. -/
theorem one_le_factor {p : ℕ} (hp : 2 < p) : 1 ≤ 1 + 1 / ((p : ℝ) - 2) := by
  have : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  have : 0 ≤ 1 / ((p : ℝ) - 2) := by positivity
  linarith

/-- The product part of `𝔖(m)` is at least 1. -/
theorem one_le_prod (m : ℕ) :
    1 ≤ ∏ p ∈ m.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2)) :=
  Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => by nlinarith) le_rfl
    (fun p hp => one_le_factor (Finset.mem_filter.mp hp).2)

/-- `𝔖(m) = 2 C₀ ∏`, so `𝔖(m) ≥ 2 C₀` whenever `C₀ ≥ 0`. -/
theorem two_C0_le_Sing (m : ℕ) (hC : 0 ≤ C0) : 2 * C0 ≤ Sing m := by
  unfold Sing
  have h := one_le_prod m
  nlinarith

/-- `𝔖` of an odd number has empty 2-part, and of `2^a` it is `2 C₀`. -/
theorem Sing_two_pow (a : ℕ) : Sing (2 ^ a) = 2 * C0 := by
  unfold Sing
  have : (2 ^ a).primeFactors.filter (fun p => 2 < p) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hp, hpd, _⟩, h2⟩
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
    omega
  rw [this]; simp

/-! ### The exponent bookkeeping of Sections 3 to 5 -/

/-- Section 3: with `P = X^{7/25}` the exceptional set bound `X / P` is `X^{0.72}`. -/
theorem exponent_072 : (1 : ℝ) - 7 / 25 = 0.72 := by norm_num

/-- `P = X^{7/25}` is below the Vinogradov threshold `X^{2/5}` of (3.1). -/
theorem seven25_lt_two5 : (7 : ℝ) / 25 < 2 / 5 := by norm_num

/-- Theorem 2 is proved for `q ≤ X^{7/25}`, well below the `X^{4/9-ε}` range of Theorem 1. -/
theorem seven25_lt_four9 : (7 : ℝ) / 25 < 4 / 9 := by norm_num

/-- (4.7): `P ∈ [X^{0.4}, X^{0.41}]` lies inside the range `P ≤ X^{4/9-ε}` for `ε ≤ 0.03`. -/
theorem p_range_47 : (0.41 : ℝ) < 4 / 9 - 0.03 := by norm_num

/-- Theorem 5 by squaring: with `X = N²`, `P* = X^{7/25}`, the bound (5.17) `N / √P*` is
`N^{1 - 7/25} = N^{0.72}` since `√(N^{14/25})`... in exponents, `1 - (2 · 7/25)/2`. -/
theorem exponent_517 : (1 : ℝ) - (2 * (7 / 25)) / 2 = 0.72 := by norm_num

/-- (5.13): `X^{2/5} = N^{4/5}` for `X = N²`. -/
theorem exponent_513 : (2 : ℝ) * (2 / 5) = 4 / 5 := by norm_num

/-- (5.18): the larger of the two exponents `0.72` and `4/5` is `4/5`, as Theorem 5 states. -/
theorem exponent_518 : max (0.72 : ℝ) (4 / 5) = 4 / 5 := by norm_num

/-- (5.17) as a real identity: `N / √(N^{14/25}) = N^{18/25}` for `N > 0`. -/
theorem N_div_sqrt_P (N : ℝ) (hN : 0 < N) :
    N / Real.sqrt (N ^ (14 / 25 : ℝ)) = N ^ (18 / 25 : ℝ) := by
  have h1 : Real.sqrt (N ^ (14 / 25 : ℝ)) = N ^ (7 / 25 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]; norm_num
  rw [h1, div_eq_iff (Real.rpow_pos_of_pos hN _).ne', ← Real.rpow_add hN]
  have : (18 / 25 : ℝ) + 7 / 25 = 1 := by norm_num
  rw [this, Real.rpow_one]

/-! ### Linnik constants quoted in Section 4, as a chain -/

/-- The quoted unconditional values in order of appearance: 54000, 1906, 13, 12, 8, and the
GRH values 770, 160, 10, 8, 7: each list is strictly decreasing. -/
theorem linnik_chain_uncond : (54000 : ℕ) > 1906 ∧ 1906 > 13 ∧ 13 > 12 ∧ 12 > 8 := by norm_num

theorem linnik_chain_grh : (770 : ℕ) > 160 ∧ 160 > 10 ∧ 10 > 8 ∧ 8 > 7 := by norm_num

/-- (4.3) and (4.7): `0.789401` is in `(0, 1)`, and `X^{0.4} ≤ X^{0.41}` as exponents. -/
theorem c1_47 : (0 : ℝ) < 0.789401 ∧ (0.789401 : ℝ) < 1 ∧ (0.4 : ℝ) < 0.41 := by norm_num

end

end LeanLab.Pintz2021

