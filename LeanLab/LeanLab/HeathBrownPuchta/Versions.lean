import LeanLab.HeathBrownPuchta.HCount

/-!
# Heath-Brown and Puchta 2002, Section 4: the `K ≥ 9` of (25) is a carry-over from a preprint

Lab proof, unit U-1251, PC run 20261020T1703Z-9112. AI wrote the Lean code. P0012.

Versions read on 2026-10-20:
* a preprint on J.-C. Puchta's Rostock page, `Goldbach.Linnik.pdf`: 24 powers of 2, 9 under GRH,
  Section 4 constant `2.7973`, "Thus if K ≥ 9 we have", (26) "providing that K ≥ 9";
* arXiv math/0201299 v1 and v2: 13 powers, 7 under GRH, constant `2.7895`, "Thus if K ≥ 7 we
  have", but (25) still "providing that K ≥ 9" and Lemma 7 still "K ≥ 9";
* the Oxford ORA accepted version `jp.pdf`: 13 and 7, constant `2.7895`, and `K ≥ 7` in the
  H bounds, in (25) and in Lemma 7.

So the `K ≥ 9` printed with (25) and Lemma 7 on arXiv is the preprint's threshold, left in
after the constant was recomputed for `K ≥ 7`; the ORA version removes it. This file proves the
arithmetic behind that reading:

* `preprint_step`: for every `K ≥ 9` and every `N`, `2 Σ_{d ≤ 5} k(d) H(d) ε(d)^{-K} ≥ 2.7973`,
  the preprint's constant;
* `preprint_step_8`: the same at `K = 8`, so the preprint's own bound already held from `K = 8`;
* `preprint_fails_7`: at `K = 7`, `N ≡ 0 mod 15`, the sum is below `2.7973`, so the preprint's
  constant genuinely needs `K ≥ 8`, while the arXiv constant `2.7895` holds from `K = 7` by the
  cloud lemma `step25`;
* `arxiv_step_7`: `step25` restated at `K = 7`, the case the GRH theorem uses;
* `arxiv_step_6`, `arxiv_fails_5`: the arXiv constant `2.7895` holds from `K = 6` on and fails at
  `K = 5`, `N ≡ 0 mod 15`; the paper's `K ≥ 7` is a safe, not a sharp, threshold.

Plain math: with `S(K, N) = 2(1 + H(3; N, K)/2^K + (1/3) H(5; N, K)/4^K)`,
`S ≥ 2.7973` for `K ≥ 8`, `S(7, 15) = 2(1 + 42/128 + 3276/(3·16384)) < 2.7973`, and
`S ≥ 2.7895` for `K ≥ 7`. Vacuity: the hypotheses `K ≥ 9` and `K = 7` are met by `K = 9, 7`.
Binary Goldbach is OPEN.
-/

namespace LeanLab.HeathBrownPuchta

/-- The Section 4 sum, `2 (1 + k(3) H(3)/2^K + k(5) H(5)/4^K)` with `k(3) = 1`, `k(5) = 1/3`. -/
noncomputable def S4 (K N : ℕ) : ℝ :=
  2 * (1 + 1 * ((H 3 2 K (N : ZMod 3) : ℝ) / 2 ^ K) + 1 / 3 * ((H 5 4 K (N : ZMod 5) : ℝ) / 4 ^ K))

lemma H3_real (K : ℕ) (t : ZMod 3) :
    (3 * H 3 2 K t : ℝ) = if t = 0 then 2 ^ K + (-1) ^ K * 2 else 2 ^ K - (-1) ^ K := by
  have h := H3_formula K t
  split_ifs at h ⊢ <;> exact_mod_cast h

lemma H5_real (K : ℕ) (t : ZMod 5) :
    (5 * H 5 4 K t : ℝ) = if t = 0 then 4 ^ K + (-1) ^ K * 4 else 4 ^ K - (-1) ^ K := by
  have h := H5_formula K t
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- Lower bound `3 H(3) ≥ 2^K - 2^{K-8}·... `: for `K ≥ 9`, `3 H(3)/2^K ≥ 1 - 2^{-8}`. -/
lemma H3_ge9 (K : ℕ) (hK : 9 ≤ K) (t : ZMod 3) :
    (1 / 3 : ℝ) * (1 - 1 / 2 ^ 8) ≤ (H 3 2 K t : ℝ) / 2 ^ K := by
  have h := H3_real K t
  have hp : (2 : ℝ) ^ 9 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have hs : (-1 : ℝ) ^ K = 1 ∨ (-1 : ℝ) ^ K = -1 := by
    rcases neg_one_pow_eq_or ℝ K with h | h <;> simp [h]
  rw [le_div_iff₀ (by positivity)]
  split_ifs at h <;> rcases hs with hs | hs <;> rw [hs] at h <;> nlinarith

lemma H5_ge9 (K : ℕ) (hK : 9 ≤ K) (t : ZMod 5) :
    (1 / 5 : ℝ) * (1 - 1 / 4 ^ 8) ≤ (H 5 4 K t : ℝ) / 4 ^ K := by
  have h := H5_real K t
  have hp : (4 : ℝ) ^ 9 ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have hs : (-1 : ℝ) ^ K = 1 ∨ (-1 : ℝ) ^ K = -1 := by
    rcases neg_one_pow_eq_or ℝ K with h | h <;> simp [h]
  rw [le_div_iff₀ (by positivity)]
  split_ifs at h <;> rcases hs with hs | hs <;> rw [hs] at h <;> nlinarith

/-- The preprint's Section 4 constant `2.7973` holds for every `K ≥ 9` and every `N`. -/
theorem preprint_step (K : ℕ) (hK : 9 ≤ K) (N : ℕ) : (27973 / 10000 : ℝ) ≤ S4 K N := by
  have h3 := H3_ge9 K hK (N : ZMod 3)
  have h5 := H5_ge9 K hK (N : ZMod 5)
  unfold S4
  nlinarith

/-- At `K = 8` the preprint's constant also holds, for every `N`. -/
theorem preprint_step_8 (N : ℕ) : (27973 / 10000 : ℝ) ≤ S4 8 N := by
  have h3 := H3_real 8 (N : ZMod 3)
  have h5 := H5_real 8 (N : ZMod 5)
  unfold S4
  norm_num at h3 h5 ⊢
  split_ifs at h3 h5 <;> nlinarith

/-- At `K = 7`, `N ≡ 0 mod 15`, the sum is below the preprint's `2.7973`. -/
theorem preprint_fails_7 : S4 7 15 < (27973 / 10000 : ℝ) := by
  have h3 := H3_real 7 ((15 : ℕ) : ZMod 3)
  have h5 := H5_real 7 ((15 : ℕ) : ZMod 5)
  have e3 : ((15 : ℕ) : ZMod 3) = 0 := by decide
  have e5 : ((15 : ℕ) : ZMod 5) = 0 := by decide
  rw [e3, if_pos rfl] at h3
  rw [e5, if_pos rfl] at h5
  unfold S4
  rw [e3, e5]
  norm_num at h3 h5 ⊢
  nlinarith

/-- The arXiv constant `2.7895` at `K = 7`, every `N`: the case Theorem 2 under GRH needs. -/
theorem arxiv_step_7 (N : ℕ) : (27895 / 10000 : ℝ) ≤ S4 7 N := step25 7 le_rfl N

/-- The arXiv constant `2.7895` already holds at `K = 6`, every `N`. -/
theorem arxiv_step_6 (N : ℕ) : (27895 / 10000 : ℝ) ≤ S4 6 N := by
  have h3 := H3_real 6 (N : ZMod 3)
  have h5 := H5_real 6 (N : ZMod 5)
  unfold S4
  norm_num at h3 h5 ⊢
  split_ifs at h3 h5 <;> nlinarith

/-- At `K = 5`, `N ≡ 0 mod 15`, the sum is below `2.7895`, so `K ≥ 6` is the exact range. -/
theorem arxiv_fails_5 : S4 5 15 < (27895 / 10000 : ℝ) := by
  have h3 := H3_real 5 ((15 : ℕ) : ZMod 3)
  have h5 := H5_real 5 ((15 : ℕ) : ZMod 5)
  have e3 : ((15 : ℕ) : ZMod 3) = 0 := by decide
  have e5 : ((15 : ℕ) : ZMod 5) = 0 := by decide
  rw [e3, if_pos rfl] at h3
  rw [e5, if_pos rfl] at h5
  unfold S4
  rw [e3, e5]
  norm_num at h3 h5 ⊢
  nlinarith

/-- Vacuity: the `K ≥ 9` hypothesis is met. -/
theorem preprint_vacuity : (27973 / 10000 : ℝ) ≤ S4 9 15 := preprint_step 9 le_rfl 15

end LeanLab.HeathBrownPuchta
