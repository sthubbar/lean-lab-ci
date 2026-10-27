/-
J. Liu, K.-M. Tsang 2005, Small prime solutions of ternary linear equations, Acta Arith. 118,
79-100. Unit U-1533, run 20261026T0004Z-24325, type DECOMPOSE, file b of three.

The bookkeeping of Section 2, pp. 80 to 82, that turns the major-arc and minor-arc estimates into
Theorem 1.1. Parameters, eq. 2.1: `P = (N/A)^{2/5}`, `L = log N`, `Q = N/(P L²)`, `Nⱼ = N/|aⱼ|`.
With `X = |a₁a₂a₃|`:
* eq. 2.7 gives `S₃ ≪ N L⁴ / √(|a₃| P)` on the minor arcs; eq. 2.8 gives
  `∫|S₁S₂| ≪ L N / √|a₁a₂|`; their product is eq. 2.9, `N² L⁵ / √(X P)`;
* major arcs give `S(n,P) I(n)` with error `N²/(X L)`; Lemmas 2.2 and 2.3 give
  `S(n,P) I(n) ≫ N²/X`;
* so `r(n) ≫ N²/X` once `P ≫ L^{10.4} X`, which is `N ≫ A X^{5/2} L^{26}`.
Each analytic estimate enters here as a real-number hypothesis; the leaves are the algebra.

AI-written Lean code, Claude, 2026-10-26. Ternary Goldbach is Helfgott 2013; binary Goldbach is
OPEN, nothing here is progress on it.
-/
import Mathlib

namespace LeanLab.LiuTsang2005.Decomp1533b
open Real

/-- LEAF. Unit U-1533. With `P = (N/A)^{2/5}` as in p. 80, eq. 2.1, for `N, A > 0` one has
`P^{5/2} = N/A`. -/
theorem P_rpow (N A : ℝ) (hN : 0 < N) (hA : 0 < A) :
    ((N / A) ^ (2 / 5 : ℝ)) ^ (5 / 2 : ℝ) = N / A := by
  rw [← Real.rpow_mul (div_pos hN hA).le]
  norm_num

/-- LEAF. Unit U-1533. The size condition at the end of the proof, p. 82: for `N, A, X > 0` and
`L ≥ 1`, `(N/A)^{2/5} ≥ L^{10.4} X` holds exactly when `N ≥ A X^{5/2} L^{26}`. -/
theorem P_cond_iff (N A X L : ℝ) (hN : 0 < N) (hA : 0 < A) (hX : 0 < X) (hL : 1 ≤ L) :
    L ^ (52 / 5 : ℝ) * X ≤ (N / A) ^ (2 / 5 : ℝ) ↔ A * X ^ (5 / 2 : ℝ) * L ^ (26 : ℝ) ≤ N := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [← Real.rpow_le_rpow_iff (by positivity : 0 ≤ L ^ (52 / 5 : ℝ) * X)
    (by positivity : 0 ≤ (N / A) ^ (2 / 5 : ℝ)) (by norm_num : (0 : ℝ) < 5 / 2)]
  rw [Real.mul_rpow (by positivity) hX.le, ← Real.rpow_mul hL0.le,
    ← Real.rpow_mul (div_pos hN hA).le]
  norm_num
  rw [le_div_iff₀ hA]
  constructor <;> intro h <;> nlinarith [h]

/-- LEAF. Unit U-1533. First term of p. 82, eq. 2.7: `N₃ P^{-1/2} |a₃|^{1/2} = N / √(|a₃| P)`
with `N₃ = N/|a₃|`, for `|a₃|, P > 0`. -/
theorem eq27_first (N a P : ℝ) (ha : 0 < a) (hP : 0 < P) :
    N / a * P ^ (-(1 / 2) : ℝ) * a ^ (1 / 2 : ℝ) = N / Real.sqrt (a * P) := by
  rw [Real.rpow_neg hP.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul ha.le]
  have hsa := Real.sqrt_pos.mpr ha
  have hsp := Real.sqrt_pos.mpr hP
  apply (eq_div_iff (mul_ne_zero hsa.ne' hsp.ne')).mpr
  field_simp
  rw [Real.sq_sqrt ha.le]

/-- LEAF. Unit U-1533. Third term of p. 82, eq. 2.7: with `Q = N/(P L²)` and `L ≥ 1`,
`N₃^{1/2} Q^{1/2} ≤ N / √(|a₃| P)`. -/
theorem eq27_third (N a P L : ℝ) (hN : 0 < N) (ha : 0 < a) (hP : 0 < P) (hL : 1 ≤ L) :
    Real.sqrt (N / a) * Real.sqrt (N / (P * L ^ 2)) ≤ N / Real.sqrt (a * P) := by
  have hL0 : 0 ≤ L := by linarith
  rw [Real.sqrt_div hN.le, Real.sqrt_div hN.le, Real.sqrt_mul ha.le,
    Real.sqrt_mul hP.le, Real.sqrt_sq hL0, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt hN.le]
  apply div_le_div_of_nonneg_left hN.le (by positivity)
  nlinarith [mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hP)]

/-- LEAF. Unit U-1533. Schwarz step of p. 82, eq. 2.8: `√(L N₁) √(L N₂) = L N / √(|a₁ a₂|)`
with `Nⱼ = N/|aⱼ|`, for `N, L, |a₁|, |a₂| > 0`. -/
theorem eq28_schwarz (N L a₁ a₂ : ℝ) (hN : 0 < N) (hL : 0 < L) (h1 : 0 < a₁) (h2 : 0 < a₂) :
    Real.sqrt (L * (N / a₁)) * Real.sqrt (L * (N / a₂)) = L * N / Real.sqrt (a₁ * a₂) := by
  calc
    _ = Real.sqrt ((L * N) ^ 2 / (a₁ * a₂)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    _ = _ := by rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- LEAF. Unit U-1533. Product giving p. 82, eq. 2.9:
`(N L⁴ / √(|a₃| P)) (L N / √(|a₁a₂|)) = N² L⁵ / √(|a₁a₂a₃| P)` for positive `|aⱼ|`, `P`. -/
theorem eq29_product (N L P a₁ a₂ a₃ : ℝ) (hP : 0 < P) (h1 : 0 < a₁) (h2 : 0 < a₂)
    (h3 : 0 < a₃) :
    N * L ^ 4 / Real.sqrt (a₃ * P) * (L * N / Real.sqrt (a₁ * a₂)) =
      N ^ 2 * L ^ 5 / Real.sqrt (a₁ * a₂ * a₃ * P) := by
  rw [show a₁ * a₂ * a₃ * P = (a₃ * P) * (a₁ * a₂) by ring,
    Real.sqrt_mul (mul_pos h3 hP).le]
  ring

/-- LEAF. Unit U-1533. The extra power in `L^{10.4}` on p. 82: if `P ≥ L^{10.4} X` and
`L^{2/5} ≥ k²` with `k ≥ 0`, `L ≥ 1`, `X ≥ 0`, then `P ≥ k² L^{10} X`. -/
theorem P_ge_of_extra (P L X k : ℝ) (hL : 1 ≤ L) (hX : 0 ≤ X) (hk : 0 ≤ k)
    (hP : L ^ (52 / 5 : ℝ) * X ≤ P) (hk2 : k ^ 2 ≤ L ^ (2 / 5 : ℝ)) :
    k ^ 2 * L ^ 10 * X ≤ P := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  calc
    k ^ 2 * L ^ 10 * X ≤ L ^ (2 / 5 : ℝ) * L ^ 10 * X := by gcongr
    _ = L ^ (52 / 5 : ℝ) * X := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
      norm_num
    _ ≤ P := hP

/-- LEAF. Unit U-1533. Square root step, p. 82: `P ≥ k² L^{10} X` with `k, X ≥ 0` gives
`√P ≥ k L⁵ √X`. -/
theorem sqrtP_ge (P L X k : ℝ) (hX : 0 ≤ X) (hk : 0 ≤ k) (hL : 0 ≤ L)
    (h : k ^ 2 * L ^ 10 * X ≤ P) : k * L ^ 5 * Real.sqrt X ≤ Real.sqrt P := by
  apply (Real.le_sqrt (by positivity) (le_trans (by positivity) h)).mpr
  calc
    (k * L ^ 5 * Real.sqrt X) ^ 2 = k ^ 2 * L ^ 10 * X := by
      rw [mul_pow, Real.sq_sqrt hX]
      ring
    _ ≤ P := h

/-- LEAF. Unit U-1533. The minor-arc error is small, p. 82: if `√P ≥ k L⁵ √X` with
`k, N, X, P > 0` then `N² L⁵ / √(X P) ≤ (1/k) N²/X`. -/
theorem minor_small (N L X P k : ℝ) (hN : 0 < N) (hX : 0 < X) (hP : 0 < P) (hk : 0 < k)
    (hL : 0 ≤ L) (h : k * L ^ 5 * Real.sqrt X ≤ Real.sqrt P) :
    N ^ 2 * L ^ 5 / Real.sqrt (X * P) ≤ 1 / k * (N ^ 2 / X) := by
  rw [Real.sqrt_mul hX.le]
  apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hX) (Real.sqrt_pos.mpr hP))).mpr
  calc
    N ^ 2 * L ^ 5 = (1 / k * (N ^ 2 / X)) * (Real.sqrt X * (k * L ^ 5 * Real.sqrt X)) := by
      field_simp
      rw [Real.sq_sqrt hX.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg X)) (by positivity)

/-- LEAF. Unit U-1533. The major-arc error is small, p. 82: if `L ≥ k > 0` and `N, X > 0`
then `N²/(X L) ≤ (1/k) N²/X`. -/
theorem major_small (N L X k : ℝ) (hX : 0 < X) (hk : 0 < k) (hL : k ≤ L) :
    N ^ 2 / (X * L) ≤ 1 / k * (N ^ 2 / X) := by
  calc
    N ^ 2 / (X * L) ≤ N ^ 2 / (X * k) := by gcongr
    _ = _ := by ring

/-- LEAF. Unit U-1533. The final comparison, p. 82: if `m ≥ c Y`, `|E| ≤ K (e₁ + e₂)` and
`e₁, e₂ ≤ c Y / (4K)` with `K > 0`, then `m + E ≥ c Y / 2`. -/
theorem main_beats_error (m E e₁ e₂ c Y K : ℝ) (hK : 0 < K) (hm : c * Y ≤ m)
    (hE : |E| ≤ K * (e₁ + e₂)) (h1 : e₁ ≤ c * Y / (4 * K)) (h2 : e₂ ≤ c * Y / (4 * K)) :
    c * Y / 2 ≤ m + E := by
  have he : -E ≤ K * (e₁ + e₂) := le_trans (neg_le_abs E) hE
  have h1' := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp h1
  have h2' := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp h2
  nlinarith

/-- **Assembly, p. 82.** `r(n) = S I + E` with `S I ≥ c N²/X`,
`|E| ≤ K (N²/(X L) + N² L⁵/√(X P))`, `L ≥ 4K/c` and `P ≥ L^{10.4} X` where
`L^{2/5} ≥ (4K/c)²`, gives `r(n) ≥ (c/2) N²/X`. CONDITIONAL ON the analytic inequalities hSI and hE.
All algebraic leaves are proved; zero sorry. -/
theorem r_lower (r SI E N L X P c K : ℝ) (hN : 0 < N) (hX : 0 < X) (hP : 0 < P)
    (hc : 0 < c) (hK : 0 < K) (hL1 : 1 ≤ L) (hr : r = SI + E) (hSI : c * (N ^ 2 / X) ≤ SI)
    (hE : |E| ≤ K * (N ^ 2 / (X * L) + N ^ 2 * L ^ 5 / Real.sqrt (X * P)))
    (hLk : 4 * K / c ≤ L) (hcond : L ^ (52 / 5 : ℝ) * X ≤ P)
    (hLk2 : (4 * K / c) ^ 2 ≤ L ^ (2 / 5 : ℝ)) :
    c * (N ^ 2 / X) / 2 ≤ r := by
  have hk : 0 < 4 * K / c := by positivity
  have hP2 := P_ge_of_extra P L X (4 * K / c) hL1 hX.le hk.le hcond hLk2
  have hs := sqrtP_ge P L X (4 * K / c) hX.le hk.le (by linarith) hP2
  have e2 := minor_small N L X P (4 * K / c) hN hX hP hk (by linarith) hs
  have e1 := major_small N L X (4 * K / c) hX hk hLk
  have key : 1 / (4 * K / c) * (N ^ 2 / X) = c * (N ^ 2 / X) / (4 * K) := by
    field_simp
  rw [key] at e1 e2
  rw [hr]
  exact main_beats_error SI E _ _ c (N ^ 2 / X) K hK hSI hE e1 e2

/-- **Assembly, p. 82, size condition.** If `N ≥ A X^{5/2} L^{26}` then `P = (N/A)^{2/5}`
satisfies `P ≥ L^{10.4} X`, the hypothesis `hcond` of `r_lower`. PROVED from P_cond_iff; zero sorry. -/
theorem P_cond_of_N (N A X L : ℝ) (hN : 0 < N) (hA : 0 < A) (hX : 0 < X) (hL : 1 ≤ L)
    (h : A * X ^ (5 / 2 : ℝ) * L ^ (26 : ℝ) ≤ N) :
    L ^ (52 / 5 : ℝ) * X ≤ (N / A) ^ (2 / 5 : ℝ) :=
  (P_cond_iff N A X L hN hA hX hL).2 h

/-- **Assembly, p. 82, eq. 2.9.** The two minor-arc factors multiply to the bound of eq. 2.9,
with the Schwarz factor written as in eq. 2.8. PROVED from eq28_schwarz and eq29_product; zero sorry. -/
theorem eq29_of_parts (N L P a₁ a₂ a₃ : ℝ) (hN : 0 < N) (hL : 0 < L) (hP : 0 < P)
    (h1 : 0 < a₁) (h2 : 0 < a₂) (h3 : 0 < a₃) :
    N * L ^ 4 / Real.sqrt (a₃ * P) * (Real.sqrt (L * (N / a₁)) * Real.sqrt (L * (N / a₂))) =
      N ^ 2 * L ^ 5 / Real.sqrt (a₁ * a₂ * a₃ * P) := by
  rw [eq28_schwarz N L a₁ a₂ hN hL h1 h2]
  exact eq29_product N L P a₁ a₂ a₃ hP h1 h2 h3

/-- Vacuity of every hypothesis of `r_lower` at once: `N = X = P = c = 1`, `K = 1/4`,
`L = 1`, `E = 0`, `r = SI = 1`. -/
example : ∃ r SI E N L X P c K : ℝ, 0 < N ∧ 0 < X ∧ 0 < P ∧ 0 < c ∧ 0 < K ∧ 1 ≤ L ∧
    r = SI + E ∧ c * (N ^ 2 / X) ≤ SI ∧
    |E| ≤ K * (N ^ 2 / (X * L) + N ^ 2 * L ^ 5 / Real.sqrt (X * P)) ∧
    4 * K / c ≤ L ∧ L ^ (52 / 5 : ℝ) * X ≤ P ∧ (4 * K / c) ^ 2 ≤ L ^ (2 / 5 : ℝ) := by
  refine ⟨1, 1, 0, 1, 1, 1, 1, 1, 1 / 4, ?_⟩
  simp only [Real.one_rpow, Real.sqrt_one]
  norm_num

end LeanLab.LiuTsang2005.Decomp1533b
