import LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawada

/-!
S136 split of `leaf_major_arcs` of `Decomp598Theorem6LeavesKawada`, Halupczok P0077
page 339, Theorem 2.2, display 2.4, adapted from Kawada 1993 Theorem 2, section 3.
https://doi.org/10.5802/jtnb.839

Kawada's major arc argument for `k = 2`, `a0 = 1`, `b0 = 0`, `a1 = -1`, `b1 = 2k1`:
* section 3, first paragraph: the cases `σ(b;a,q) = 0`, here `Sqa = 0`, are admissible
  directly, since then the count is `≪ (log x)^{k+1}`; leaf `leaf_major_sigma_zero`;
* displays 3.7 to 3.11 with 3.14: the major arc integral equals the truncated singular series
  `S(b;a,q) N` of Kawada page 49 up to an admissible error; leaf `leaf_major_truncated`;
* displays 3.12 and 3.13, section 6: `S(b;a,q) = σ(b;a,q) + O(q^{-1} τ_K(q) τ_K(R(b)) L^{-C+1})`
  summed; leaf `leaf_singular_truncation`.
The assembly `leaf_major_arcs_of_leaves` has the statement of `leaf_major_arcs` byte for byte.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawadaS136Major

open Finset MeasureTheory
open scoped Classical
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawada

/-- The Ramanujan sum of Kawada page 49, `c_q(n) = ∑_{m=1, (m,q)=1}^{q} e(mn/q)`. -/
noncomputable def ramC (q : ℕ) (n : ℤ) : ℂ :=
  ∑ m ∈ (Icc 1 q).filter (fun m => Nat.Coprime m q), eA ((m : ℝ) / q * n)

/-- Kawada page 49, the truncated singular series `S(b;a,q)` below display 3.11, for `k = 2`,
`a0 = 1`, `b0 = 0`, `a1 = -1`, `b1 = m`, so `r = q1`, with `Q1 = L^C` of Kawada page 46:
`∑_{q1 ≤ Q1} μ(q1) / (φ([q,q1]) φ(q1)) ∑^#_d c_{q1}(m - d)`, where `d` runs over
`1 ≤ d ≤ q1`, `a ≡ d (mod (q,q1))`, `(d,q1) = 1`. -/
noncomputable def kTruncS (C Y : ℝ) (m q : ℕ) (a : ℤ) : ℂ :=
  ∑ q1 ∈ Icc 1 ⌊Real.log Y ^ C⌋₊,
    (((ArithmeticFunction.moebius q1 : ℤ) : ℝ) /
        ((Nat.totient (Nat.lcm q q1) : ℝ) * (Nat.totient q1 : ℝ)) : ℂ) *
      ∑ d ∈ (Icc 1 q1).filter (fun d : ℕ => (d : ℤ) ≡ a [ZMOD (Nat.gcd q q1 : ℤ)] ∧
          Nat.Coprime d q1),
        ramC q1 ((m : ℤ) - d)

/-- LEAF: Kawada 1993 section 3, first paragraph, for k = 2: when `σ(b;a,q) = 0`, here
`Sqa (2k) q2 a2 = 0`, the count is `≪ L^{k+1}` and the terms are admissible; with display 3.4
and the minor arc bound 3.6 this bounds the major arc integral. Class MEDIUM. -/
theorem leaf_major_sigma_zero :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
        ‖∫ α in unitDom X1 ∩ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  sorry

/-- LEAF: Kawada 1993 displays 3.7 to 3.11 with 3.14, for k = 2: Lemma 1, Siegel Walfisz
approximation `P(α) = μ(q)/φ(q) T(β) + O(y exp(-δ0 L^{1/5}))` on the major arcs, display 3.7,
the tail bound 3.8 via 3.10, the evaluation 3.9 of `J0`, and the Bombieri Vinogradov type
Lemma 3 in 3.14 using `Q2 ≪ Y X2^{-1/2} L^{-B}`; the main term is the truncated singular series
`S(b;a,q) N` of Kawada page 49 with `N = Y`. Class HARD. -/
theorem leaf_major_truncated :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
        ‖(∫ α in unitDom X1 ∩ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α) -
          kTruncS C Y (2 * k) q2 a2 * (Y : ℂ)‖ ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  sorry

/-- LEAF: Kawada 1993 display 3.12, proved in section 6, and display 3.13, for k = 2:
`S(b;a,q) = σ(b;a,q) + O(q^{-1} τ_K(q) τ_K(R(b)) L^{-C+1})` under 3.1 to 3.3, here
`Sqa ≠ 0`, summed with `∑ τ_K(q)/q ≪ L^K` and `∑_b τ_K(R(b)) ≪ y L^{K1}`. Class HARD. -/
theorem leaf_singular_truncation :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
        ‖kTruncS C Y (2 * k) q2 a2 - (Sqa (2 * k) q2 a2 : ℂ)‖ * Y ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  sorry

/-- Assembly: `leaf_major_arcs` from the three leaves. Statement identical to
`Decomp598Theorem6LeavesKawada.leaf_major_arcs`. -/
theorem leaf_major_arcs_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        ‖(∫ α in unitDom X1 ∩ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α) -
          (Sqa (2 * k) q2 a2 * Y : ℝ)‖ ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  intro A ε hA hε
  obtain ⟨C1, h1⟩ := leaf_major_sigma_zero A ε hA hε
  obtain ⟨C2, h2⟩ := leaf_major_truncated A ε hA hε
  obtain ⟨C3, h3⟩ := leaf_singular_truncation A ε hA hε
  refine ⟨max C1 (max C2 C3), fun C hC => ?_⟩
  obtain ⟨B1, hB1, g1⟩ := h1 C (le_trans (le_max_left _ _) hC)
  obtain ⟨B2, hB2, g2⟩ := h2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC)
  obtain ⟨B3, hB3, g3⟩ := h3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC)
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, fun c1 c3 hc1 hc3 a2 => ?_⟩
  obtain ⟨K1, Y1, g1⟩ := g1 c1 c3 hc1 hc3 a2
  obtain ⟨K2, Y2, g2⟩ := g2 c1 c3 hc1 hc3 a2
  obtain ⟨K3, Y3, g3⟩ := g3 c1 c3 hc1 hc3 a2
  refine ⟨K1 + K2 + K3, max (max Y1 (max Y2 Y3)) (Real.exp 1), ?_⟩
  intro X1 X2 Y Q2 hY0 e1 e2 e3 e4 hQ1 hQ2
  have hYe : Real.exp 1 ≤ Y := le_trans (le_max_right _ _) hY0
  have hYm : max Y1 (max Y2 Y3) ≤ Y := le_trans (le_max_left _ _) hY0
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos 1) hYe
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYe
  have hX2pos : 0 < X2 := lt_of_lt_of_le hYpos e3
  have hbase : 0 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) := by
    have := Real.rpow_pos_of_pos hX2pos (-(1 / 2) : ℝ)
    positivity
  have hQ : ∀ Bi, Bi ≤ max B1 (max B2 B3) →
      Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-Bi) := fun Bi hBi =>
    hQ2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hBi)) hbase)
  have b1 := g1 X1 X2 Y Q2 (le_trans (le_max_left _ _) hYm) e1 e2 e3 e4 hQ1
    (hQ B1 (le_max_left _ _))
  have b2 := g2 X1 X2 Y Q2 (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hYm)
    e1 e2 e3 e4 hQ1 (hQ B2 (le_trans (le_max_left _ _) (le_max_right _ _)))
  have b3 := g3 X1 X2 Y Q2 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hYm)
    e1 e2 e3 e4 hQ1 (hQ B3 (le_trans (le_max_right _ _) (le_max_right _ _)))
  set I : ℕ → ℕ → ℂ := fun q2 k => ∫ α in unitDom X1 ∩ kMajor A C Y,
    circF X1 X2 Y q2 a2 (2 * k) α with hI
  have hsplit : ∀ q2, ∑ k ∈ kRange X1 Y, ‖I q2 k - ((Sqa (2 * k) q2 a2 * Y : ℝ) : ℂ)‖ ≤
      ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0), ‖I q2 k‖ +
      (∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
        ‖I q2 k - kTruncS C Y (2 * k) q2 a2 * (Y : ℂ)‖ +
      ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
        ‖kTruncS C Y (2 * k) q2 a2 - (Sqa (2 * k) q2 a2 : ℂ)‖ * Y) := by
    intro q2
    rw [← sum_filter_add_sum_filter_not (kRange X1 Y) (fun k => Sqa (2 * k) q2 a2 = 0),
      ← sum_add_distrib]
    refine add_le_add (le_of_eq (sum_congr rfl fun k hk => ?_))
      (sum_le_sum fun k hk => ?_)
    · rw [(mem_filter.mp hk).2]
      simp
    · have hcalc : I q2 k - ((Sqa (2 * k) q2 a2 * Y : ℝ) : ℂ) =
          (I q2 k - kTruncS C Y (2 * k) q2 a2 * (Y : ℂ)) +
            (kTruncS C Y (2 * k) q2 a2 - (Sqa (2 * k) q2 a2 : ℂ)) * (Y : ℂ) := by
        push_cast
        ring
      rw [hcalc]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hYpos]
  calc _ ≤ ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, (∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
        ‖I q2 k‖ +
      (∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
        ‖I q2 k - kTruncS C Y (2 * k) q2 a2 * (Y : ℂ)‖ +
      ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
        ‖kTruncS C Y (2 * k) q2 a2 - (Sqa (2 * k) q2 a2 : ℂ)‖ * Y)) :=
        sum_le_sum fun q2 _ => hsplit q2
    _ = ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
          ‖I q2 k‖ +
        (∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
          ‖I q2 k - kTruncS C Y (2 * k) q2 a2 * (Y : ℂ)‖ +
        ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 ≠ 0),
          ‖kTruncS C Y (2 * k) q2 a2 - (Sqa (2 * k) q2 a2 : ℂ)‖ * Y) := by
      simp_rw [sum_add_distrib]
    _ ≤ K1 * Y ^ 2 * Real.log Y ^ (-A) +
        (K2 * Y ^ 2 * Real.log Y ^ (-A) + K3 * Y ^ 2 * Real.log Y ^ (-A)) :=
        add_le_add b1 (add_le_add b2 b3)
    _ = _ := by ring

end LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawadaS136Major
