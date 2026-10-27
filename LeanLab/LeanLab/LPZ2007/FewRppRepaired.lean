/-
P0045 Languasco, Pintz, Zaccagnini 2007, repaired chain, F-0038. The corollary `few_Rpp_zero`
of Elementary.lean took the printed main theorem `MainJ`, with the constant C(k, N), which is
false if F-0038 holds. Here the corollary is rederived from the repaired main theorem
`MainJ_twoC0`, constant 2c₀ C(k, N), using only 0 < 2c₀ and 1 ≤ C(k, N): almost every even
N ∈ J(X) is a sum of two primes and k powers of two, at most B X^{3/5} (log X)^{10} exceptions.
CONDITIONAL ON `MainJ_twoC0` and Lemma 6.1, as an implication.
Run 20261020T1003Z-31988, unit U-1211. AI-written Lean code, Claude. Checked only by the Lean
kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LPZ2007.Repaired
import LeanLab.ChenExplicit.Reductions


namespace LeanLab.LPZ2007

open Finset

/-- `2c₀ > 0`: every factor is positive and the logs are summable, as for `twinC_pos`. -/
theorem twoC0_pos : 0 < twoC0 := by
  set f : Nat.Primes → ℝ := fun p => if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2
    with hf
  have hpos : ∀ p, 0 < f p := by
    intro p
    simp only [hf]
    split_ifs with h2
    · norm_num
    · have h3 : (3 : ℝ) ≤ (p : ℕ) := by
        have := p.2.two_le
        exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
      have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
      linarith
  have hsum : Summable (fun p : Nat.Primes => 1 / ((p : ℝ) - 1) ^ 2) :=
    LeanLab.ChenExplicit.summable_inv_sub_one_sq.subtype {p | p.Prime}
  have hs : Summable (fun p : Nat.Primes =>
      if (p : ℕ) = 2 then (0 : ℝ) else -(1 / ((p : ℝ) - 1) ^ 2)) := by
    refine Summable.of_norm_bounded hsum fun p => ?_
    split_ifs
    · simp only [norm_zero]; positivity
    · rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  have hlog : Summable (fun p => Real.log (f p)) := by
    have := Real.summable_log_one_add_of_summable hs
    refine this.congr fun p => ?_
    simp only [hf]
    split_ifs <;> ring_nf
  have := Real.rexp_tsum_eq_tprod hpos hlog
  unfold twoC0
  rw [show (∏' p : Nat.Primes, (if (p : ℕ) = 2 then (1 : ℝ) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) =
      ∏' p, f p from rfl, ← this]
  positivity

open Classical in
/-- **The corollary on the repaired constant.** Almost every even `N ∈ J(X)` has
`R''_k(N) > 0`: at most `B X^{3/5} (log X)^{10}` exceptions. CONDITIONAL ON the repaired main
theorem `MainJ_twoC0` and Lemma 6.1. -/
theorem few_Rpp_zero_twoC0 (hM : MainJ_twoC0) (h61 : Lemma61) {k : ℕ} (hk : 1 ≤ k) :
    ∃ B : ℝ, 0 < B ∧ ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (((Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧ InJ X N ∧ Rpp k X N ≤ 0)).card : ℝ) ≤
        B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10 := by
  have hc0 := twoC0_pos
  obtain ⟨B, hB, H⟩ := hM k hk
  obtain ⟨X0, H⟩ := H (twoC0 / 2) (by positivity)
  refine ⟨B, hB, max X0 2, fun X hX => le_trans ?_ (H X ((le_max_left _ _).trans hX))⟩
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Lg X ^ k := pow_pos (Lg_pos (by linarith)) k
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hC := one_le_Ckn h61 j
  exact_mod_cast card_le_card fun N hN => by
    simp only [mem_filter, mem_Icc] at hN ⊢
    obtain ⟨⟨h1, h2⟩, he, hJ, hR⟩ := hN
    refine ⟨⟨h1, h2⟩, he, hJ, ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast h1
    have hc := hC N
    have hNL : 0 < (N : ℝ) * Lg X ^ (j + 1) := mul_pos hN0 hL
    have hprod : twoC0 * ((N : ℝ) * Lg X ^ (j + 1)) ≤
        twoC0 * Ckn (j + 1) N * (N : ℝ) * Lg X ^ (j + 1) := by
      have := mul_le_mul_of_nonneg_right hc (le_of_lt (mul_pos hc0 hNL))
      nlinarith
    rw [abs_sub_comm, abs_of_pos (by nlinarith)]
    nlinarith

/-- Vacuity side: the corollary's conclusion is not empty, the exceptional count is a real
count of a finite set, and the hypotheses `twoC0 > 0`, `C(k, N) ≥ 1` hold. -/
theorem hypotheses_hold (h61 : Lemma61) (j N : ℕ) : 0 < twoC0 ∧ 1 ≤ Ckn (j + 1) N :=
  ⟨twoC0_pos, one_le_Ckn h61 j N⟩

end LeanLab.LPZ2007
