import Mathlib

/-!
# Heath-Brown and Puchta 2002, Section 4: the counts `H(3; N, K)` and `H(5; N, K)`

Lab proof, unit U-5311, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. P0012, arXiv
math/0201299, Section 4, the display before (25):
`H(d; N, K) = #{(ν₁, …, ν_K) : 1 ≤ νᵢ ≤ ε(d), d ∣ N - Σ 2^{νᵢ}}`, `ε(d)` the order of `2` mod `d`,
and for `d = 3, 5` the paper states `H = ((d - 1)^K - (-1)^K)/d` if `d ∤ N` and
`((d - 1)^K + (-1)^K (d - 1))/d` if `d ∣ N`, then "if `K ≥ 7`" the bounds
`H(3)/2^K ≥ (1/3)(1 - 2^{-6})`, `H(5)/4^K ≥ (1/5)(1 - 4^{-6})`, whence
`2 Σ_{d ≤ 5} k(d) H(d) ε(d)^{-K} ≥ 2.7895`, and (25) is stated "providing that `K ≥ 9`".

* `H d e K t`, the count with `ν` running over `Fin e`, `νᵢ = j + 1`, and the congruence read in
  `ZMod d` with `t = N mod d`; `H_succ` the recursion over the first coordinate;
* `H3_formula`, `H5_formula`: the paper's closed forms, `ε(3) = 2`, `ε(5) = 4`, for every `K`;
* `H3_bound`, `H5_bound`: the paper's two bounds for every `K ≥ 7` and every `N`;
* `step25`: `2 (1 + H(3)/2^K + (1/3) H(5)/4^K) ≥ 2.7895` for every `K ≥ 7` and every `N`, so this
  step needs only `K ≥ 7`, not the `K ≥ 9` printed with (25);
* `H3_bound_fails_5`: at `K = 5` and `3 ∣ N` the `H(3)` bound fails, so some lower limit is needed.
Binary Goldbach is OPEN.
-/

namespace LeanLab.HeathBrownPuchta

open Finset

/-- `H(d; N, K)` with `ν ∈ {1, …, e}` and `t = N mod d`. -/
def H (d e K : ℕ) (t : ZMod d) : ℕ :=
  (univ.filter (fun f : Fin K → Fin e => ∑ i, (2 : ZMod d) ^ ((f i).val + 1) = t)).card

lemma H_zero (d e : ℕ) (t : ZMod d) : H d e 0 t = if t = 0 then 1 else 0 := by
  unfold H
  by_cases ht : t = 0
  · subst ht; simp
  · rw [if_neg ht]
    simp only [univ_unique, Finset.sum_empty, card_eq_zero]
    ext f; simp [Finset.mem_filter, eq_comm, ht]

lemma H_succ (d e K : ℕ) (t : ZMod d) :
    H d e (K + 1) t = ∑ a : Fin e, H d e K (t - 2 ^ (a.val + 1)) := by
  unfold H
  simp only [card_eq_sum_ones, sum_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (K + 1) => Fin e)).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun h _ => ?_))
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply propext
  constructor
  · intro hx; rw [← hx]; ring
  · intro hx; rw [hx]; ring

lemma H3_succ (K : ℕ) (t : ZMod 3) : H 3 2 (K + 1) t = H 3 2 K (t - 2) + H 3 2 K (t - 1) := by
  rw [H_succ, Fin.sum_univ_two]
  have e0 : (2 : ZMod 3) ^ ((0 : Fin 2).val + 1) = 2 := by decide
  have e1 : (2 : ZMod 3) ^ ((1 : Fin 2).val + 1) = 1 := by decide
  rw [e0, e1]

lemma H5_succ (K : ℕ) (t : ZMod 5) :
    H 5 4 (K + 1) t = H 5 4 K (t - 2) + H 5 4 K (t - 4) + H 5 4 K (t - 3) + H 5 4 K (t - 1) := by
  rw [H_succ, Fin.sum_univ_four]
  have e0 : (2 : ZMod 5) ^ ((0 : Fin 4).val + 1) = 2 := by decide
  have e1 : (2 : ZMod 5) ^ ((1 : Fin 4).val + 1) = 4 := by decide
  have e2 : (2 : ZMod 5) ^ ((2 : Fin 4).val + 1) = 3 := by decide
  have e3 : (2 : ZMod 5) ^ ((3 : Fin 4).val + 1) = 1 := by decide
  rw [e0, e1, e2, e3]

lemma H3_all (K : ℕ) :
    (3 * H 3 2 K 0 : ℤ) = 2 ^ K + (-1) ^ K * 2 ∧ (3 * H 3 2 K 1 : ℤ) = 2 ^ K - (-1) ^ K ∧
      (3 * H 3 2 K 2 : ℤ) = 2 ^ K - (-1) ^ K := by
  induction K with
  | zero =>
      simp only [H_zero]
      refine ⟨by simp, ?_, ?_⟩ <;> simp (config := {decide := true})
  | succ K ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have a : (0 : ZMod 3) - 2 = 1 := by decide
      have b : (0 : ZMod 3) - 1 = 2 := by decide
      have c : (1 : ZMod 3) - 2 = 2 := by decide
      have d : (1 : ZMod 3) - 1 = 0 := by decide
      have e : (2 : ZMod 3) - 2 = 0 := by decide
      have g : (2 : ZMod 3) - 1 = 1 := by decide
      rw [H3_succ, H3_succ, H3_succ, a, b, c, d, e, g]
      push_cast
      refine ⟨?_, ?_, ?_⟩ <;> rw [pow_succ, pow_succ] <;> linarith

lemma H5_all (K : ℕ) :
    (5 * H 5 4 K 0 : ℤ) = 4 ^ K + (-1) ^ K * 4 ∧ (5 * H 5 4 K 1 : ℤ) = 4 ^ K - (-1) ^ K ∧
      (5 * H 5 4 K 2 : ℤ) = 4 ^ K - (-1) ^ K ∧ (5 * H 5 4 K 3 : ℤ) = 4 ^ K - (-1) ^ K ∧
      (5 * H 5 4 K 4 : ℤ) = 4 ^ K - (-1) ^ K := by
  induction K with
  | zero =>
      simp only [H_zero]
      refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true})
  | succ K ih =>
      obtain ⟨h0, h1, h2, h3, h4⟩ := ih
      simp only [H5_succ]
      rw [show (0 : ZMod 5) - 2 = 3 by decide, show (0 : ZMod 5) - 4 = 1 by decide, show (0 : ZMod 5) - 3 = 2 by decide, show (0 : ZMod 5) - 1 = 4 by decide, show (1 : ZMod 5) - 2 = 4 by decide, show (1 : ZMod 5) - 4 = 2 by decide, show (1 : ZMod 5) - 3 = 3 by decide, show (1 : ZMod 5) - 1 = 0 by decide, show (2 : ZMod 5) - 2 = 0 by decide, show (2 : ZMod 5) - 4 = 3 by decide, show (2 : ZMod 5) - 3 = 4 by decide, show (2 : ZMod 5) - 1 = 1 by decide, show (3 : ZMod 5) - 2 = 1 by decide, show (3 : ZMod 5) - 4 = 4 by decide, show (3 : ZMod 5) - 3 = 0 by decide, show (3 : ZMod 5) - 1 = 2 by decide, show (4 : ZMod 5) - 2 = 2 by decide, show (4 : ZMod 5) - 4 = 0 by decide, show (4 : ZMod 5) - 3 = 1 by decide, show (4 : ZMod 5) - 1 = 3 by decide]
      push_cast
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [pow_succ, pow_succ] <;> linarith

/-- The paper's closed form at `d = 3`: `3 H = 2^K + 2(-1)^K` if `3 ∣ N`, `2^K - (-1)^K` if not. -/
theorem H3_formula (K : ℕ) (t : ZMod 3) :
    (3 * H 3 2 K t : ℤ) = if t = 0 then 2 ^ K + (-1) ^ K * 2 else 2 ^ K - (-1) ^ K := by
  obtain ⟨h0, h1, h2⟩ := H3_all K
  have ht : t = 0 ∨ t = 1 ∨ t = 2 := by revert t; decide
  rcases ht with rfl | rfl | rfl
  · simpa using h0
  · simpa [show (1 : ZMod 3) ≠ 0 by decide] using h1
  · simpa [show (2 : ZMod 3) ≠ 0 by decide] using h2

/-- The paper's closed form at `d = 5`: `5 H = 4^K + 4(-1)^K` if `5 ∣ N`, `4^K - (-1)^K` if not. -/
theorem H5_formula (K : ℕ) (t : ZMod 5) :
    (5 * H 5 4 K t : ℤ) = if t = 0 then 4 ^ K + (-1) ^ K * 4 else 4 ^ K - (-1) ^ K := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := H5_all K
  have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by revert t; decide
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · simpa using h0
  · simpa [show (1 : ZMod 5) ≠ 0 by decide] using h1
  · simpa [show (2 : ZMod 5) ≠ 0 by decide] using h2
  · simpa [show (3 : ZMod 5) ≠ 0 by decide] using h3
  · simpa [show (4 : ZMod 5) ≠ 0 by decide] using h4

lemma H3_lower (K : ℕ) (t : ZMod 3) : (2 : ℤ) ^ K - 2 ≤ 3 * H 3 2 K t := by
  rw [H3_formula]
  rcases neg_one_pow_eq_or ℤ K with h | h <;> split_ifs <;> rw [h] <;> linarith

lemma H5_lower (K : ℕ) (t : ZMod 5) : (4 : ℤ) ^ K - 4 ≤ 5 * H 5 4 K t := by
  rw [H5_formula]
  rcases neg_one_pow_eq_or ℤ K with h | h <;> split_ifs <;> rw [h] <;> linarith

/-- "If `K ≥ 7`", `H(3; N, K) ε(3)^{-K} ≥ (1/3)(1 - 2^{-6})`, every `N`. -/
theorem H3_bound (K : ℕ) (hK : 7 ≤ K) (N : ℕ) :
    (1 / 3 : ℝ) * (1 - 1 / 2 ^ 6) ≤ (H 3 2 K (N : ZMod 3) : ℝ) / 2 ^ K := by
  have hl : (2 : ℝ) ^ K - 2 ≤ 3 * H 3 2 K (N : ZMod 3) := by exact_mod_cast H3_lower K _
  have hp : (2 : ℝ) ^ 7 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- "If `K ≥ 7`", `H(5; N, K) ε(5)^{-K} ≥ (1/5)(1 - 4^{-6})`, every `N`. -/
theorem H5_bound (K : ℕ) (hK : 7 ≤ K) (N : ℕ) :
    (1 / 5 : ℝ) * (1 - 1 / 4 ^ 6) ≤ (H 5 4 K (N : ZMod 5) : ℝ) / 4 ^ K := by
  have hl : (4 : ℝ) ^ K - 4 ≤ 5 * H 5 4 K (N : ZMod 5) := by exact_mod_cast H5_lower K _
  have hp : (4 : ℝ) ^ 7 ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The step to (25): `2 Σ_{d ≤ 5} k(d) H(d; N, K) ε(d)^{-K} ≥ 2.7895` for every `K ≥ 7` and every
`N`, with `k(1) = 1`, `k(3) = 1`, `k(5) = 1/3`, `H(1) = ε(1) = 1`; the terms `d = 2, 4` vanish
since `k(2) = k(4) = 0`. So this step needs `K ≥ 7`, not the `K ≥ 9` printed with (25). -/
theorem step25 (K : ℕ) (hK : 7 ≤ K) (N : ℕ) :
    (27895 / 10000 : ℝ) ≤ 2 * (1 + 1 * ((H 3 2 K (N : ZMod 3) : ℝ) / 2 ^ K) +
      1 / 3 * ((H 5 4 K (N : ZMod 5) : ℝ) / 4 ^ K)) := by
  have h3 := H3_bound K hK N
  have h5 := H5_bound K hK N
  nlinarith

/-- At `K = 5` and `3 ∣ N` the `H(3)` bound fails, so the step needs some lower limit on `K`. -/
theorem H3_bound_fails_5 : (H 3 2 5 0 : ℝ) / 2 ^ 5 < (1 / 3 : ℝ) * (1 - 1 / 2 ^ 6) := by
  have h := (H3_all 5).1
  have : (H 3 2 5 0 : ℝ) = 10 := by
    have h' : (3 * H 3 2 5 0 : ℤ) = 30 := by rw [h]; norm_num
    have : H 3 2 5 0 = 10 := by omega
    rw [this]; norm_num
  rw [this]; norm_num

end LeanLab.HeathBrownPuchta
