import LeanLab.ExceptionalSet.SPLIT_feed1122_parity_removal_core
import LeanLab.ExceptionalSet.State1539

/-!
Split of `Feed1122ParityCore.leaf_lemma4_unit_upper`, the upper bound form of Lemma 4 at
`α = 1` used by the parity removal core, P0082, J. Brüdern and A. Perelli, Goldbach numbers
in sparse sequences, Ann. Inst. Fourier 48 (1998), Lemma 4 on page 359, as used in section 7
page 370 after display (40).

The leaf is a consequence of the lab statement `U1539.Lemma4` of the paper's Lemma 4, the
two sided asymptotic `#{N/2 < n ≤ N : z₂ ≤ {α F(n)} < z₁} = (z₁ - z₂) N / 2 + O(N exp(-κ̃
(log N) ^ (3 - 2 γ)))` for `F(N) ^ (-1/2) < |α| ≤ 1`. At `α = 1`, which is in range once
`N ≥ 2`, the upper half of the asymptotic gives the leaf: the main term `(z₂ - z₁) N / 2` is
at most `(z₂ - z₁) N`, and `exp(-κ̃ L) ≤ exp(-k L) = ℰ_k ^ (-1)` for `k < κ̃`; the case
`z₁ = z₂` is an empty count.

* `leaf_lemma4_unit_upper_of_Lemma4`, proved, takes `U1539.Lemma4` as a hypothesis, so it is
  CONDITIONAL ON that input and uses no sorry.
* `leaf_lemma4_unit_upper_of_leaves`, the leaf statement verbatim, is CONDITIONAL ON the open
  node `U1539.lemma4` of `State1539`, which has its own split in `SPLIT_lemma4`.

So the HARD leaf of the parity core is no longer a separate node: it rests on the lab's one
Lemma 4 node. No new sorry and no new definition. No existing file is edited.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Feed1122ParityCore

open Real Finset
open LeanLab.ExceptionalSet.U1539 (calE Lemma4)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- Proved, CONDITIONAL ON the hypothesis `U1539.Lemma4`, P0082 Lemma 4 page 359 at `α = 1`.
The upper half of the two sided count, with `N / 2` relaxed to `N` and `κ̃` to `k < κ̃`. -/
theorem leaf_lemma4_unit_upper_of_Lemma4 (hL : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℝ, 0 < k → k < K →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z₁ z₂ : ℝ, 0 ≤ z₁ → z₁ ≤ z₂ → z₂ ≤ 1 →
        (((Finset.Ioc (N / 2) N).filter
            (fun n : ℕ => z₁ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < z₂)).card : ℝ) ≤
          (z₂ - z₁) * N + C * N * (calE γ k N)⁻¹ := by
  obtain ⟨κ, B, hκ, hB⟩ := hL γ h1 h2
  refine ⟨κ, hκ, fun k hk hkK => ⟨max B 0, le_max_right _ _, 2,
    fun N hN z₁ z₂ hz1 hz12 hz2 => ?_⟩⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL0 : 0 ≤ Real.log N ^ (3 - 2 * γ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg N) _
  have hEinv : 0 ≤ (calE γ k N)⁻¹ := inv_nonneg.mpr (Real.exp_pos _).le
  have hexp : Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) ≤ (calE γ k N)⁻¹ := by
    unfold U1539.calE
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hC : 0 ≤ max B 0 := le_max_right _ _
  rcases eq_or_lt_of_le hz12 with heq | hlt
  · subst heq
    have hempty : (Finset.Ioc (N / 2) N).filter
        (fun n : ℕ => z₁ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < z₁) = ∅ :=
      Finset.filter_false_of_mem (fun n _ hn => lt_irrefl _ (lt_of_le_of_lt hn.1 hn.2))
    rw [hempty, Finset.card_empty, Nat.cast_zero, sub_self, zero_mul, zero_add]
    positivity
  · have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hF1 : 1 < F γ N := by
      unfold BrudernPerelli1998.F
      exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hlog γ)
    have hF : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
      rw [abs_one]; exact Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num)
    have hb := hB N hN1 1 hF (le_of_eq abs_one) z₂ z₁ hz1 hlt hz2
    simp only [one_mul] at hb
    have hup := (abs_le.mp hb).2
    have h3 : B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) ≤
        max B 0 * N * (calE γ k N)⁻¹ := by
      have hBm : B * N ≤ max B 0 * N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN0
      have hpos : 0 ≤ Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := (Real.exp_pos _).le
      calc B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))
          ≤ max B 0 * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) :=
            mul_le_mul_of_nonneg_right hBm hpos
        _ ≤ max B 0 * N * (calE γ k N)⁻¹ :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg hC hN0)
    have h4 : (z₂ - z₁) * N / 2 ≤ (z₂ - z₁) * N := by
      have : 0 ≤ (z₂ - z₁) * N := mul_nonneg (by linarith) hN0
      linarith
    linarith

/-- Assembly, statement copied verbatim from `leaf_lemma4_unit_upper`.
CONDITIONAL ON the open node `U1539.lemma4`. -/
theorem leaf_lemma4_unit_upper_of_leaves (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℝ, 0 < k → k < K →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z₁ z₂ : ℝ, 0 ≤ z₁ → z₁ ≤ z₂ → z₂ ≤ 1 →
        (((Finset.Ioc (N / 2) N).filter
            (fun n : ℕ => z₁ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < z₂)).card : ℝ) ≤
          (z₂ - z₁) * N + C * N * (calE γ k N)⁻¹ :=
  leaf_lemma4_unit_upper_of_Lemma4 U1539.lemma4 γ h1 h2

example : type_of% @Feed1122ParityCore.leaf_lemma4_unit_upper :=
  leaf_lemma4_unit_upper_of_leaves

end LeanLab.ExceptionalSet.Feed1122ParityCore

#print axioms LeanLab.ExceptionalSet.Feed1122ParityCore.leaf_lemma4_unit_upper_of_Lemma4
