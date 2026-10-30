/-
AI-written Lean code, Gemini task401, 2026-10-30.
Decomposition of theoremII_infinite_of_quant.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Chen1973TheoremII
import LeanLab.AlmostPrimeSums.S3Small

open Finset Filter Real

noncomputable section
attribute [local instance] Classical.propDecidable
namespace LeanLab.AlmostPrimeSums.Chen1973TheoremII

open Chen1973Own

/-- LEAF 1: p. 158. The double sieve constant CN for h is positive. -/
lemma CN_pos (h : ℕ) (_h_even : Even h) (_hpos : 0 < h) :
    0 < LeanLab.ChenDoubleSieve.CN h := by
  unfold LeanLab.ChenDoubleSieve.CN
  exact mul_pos (lt_of_lt_of_le zero_lt_one (LeanLab.ChenExplicit.one_le_oddFactor h))
    LeanLab.ChenExplicit.twinC_pos

/-- LEAF 2: p. 158. The scaled quantity tends to infinity. -/
lemma scaled_tendsto (h : ℕ) (hC : 0 < LeanLab.ChenDoubleSieve.CN h) :
    Tendsto (fun x : ℕ => 0.67 * LeanLab.ChenDoubleSieve.CN h * x / (log x) ^ 2) atTop atTop := by
  simpa only [mul_div_assoc] using
    Tendsto.const_mul_atTop (mul_pos (by norm_num : (0 : ℝ) < 0.67) hC) nat_scale_tendsto

/-- LEAF 3: p. 158. From the unbounded limit and lower bound, we find a large count. -/
lemma count_unbounded (h : ℕ) (B x₀ : ℕ)
    (hII : ∀ x : ℕ, x₀ ≤ x → 0.67 * LeanLab.ChenDoubleSieve.CN h * x / (log x) ^ 2 ≤ shiftedChenCount h x)
    (ht : Tendsto (fun x : ℕ => 0.67 * LeanLab.ChenDoubleSieve.CN h * x / (log x) ^ 2) atTop atTop) :
    ∃ x : ℕ, B + 1 < shiftedChenCount h x := by
  have hbig := ht.eventually_gt_atTop ((B : ℝ) + 1)
  obtain ⟨x, hx, hmain⟩ := ((eventually_ge_atTop x₀).and hbig).exists
  have hc : (B : ℝ) + 1 < shiftedChenCount h x := by
    have h := hmain.trans_le (hII x hx)
    exact_mod_cast h
  exact ⟨x, by exact_mod_cast hc⟩

/-- LEAF 4: p. 158. The count of primes up to B cannot exceed B + 1. -/
lemma shiftedChenCount_le (h : ℕ) (x B : ℕ)
    (hsub : (range (x + 1)).filter (fun p => p.Prime ∧ ChenRep (p + h)) ⊆ range (B + 1)) :
    shiftedChenCount h x ≤ B + 1 := by
  have hbound := card_le_card hsub
  rw [card_range] at hbound
  exact hbound

/-- theoremII_infinite_of_quant assembled from leaves. -/
theorem theoremII_infinite_of_quant_assembled (hII : ChenTheoremIIQuant) : ChenTheoremIIInfinite := by
  intro h he hpos
  obtain ⟨x₀, hx₀⟩ := hII h he hpos
  have hC : 0 < LeanLab.ChenDoubleSieve.CN h := CN_pos h he hpos
  have ht : Tendsto (fun x : ℕ => 0.67 * LeanLab.ChenDoubleSieve.CN h * x / (log x) ^ 2) atTop atTop := scaled_tendsto h hC
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨x, hc⟩ := count_unbounded h B x₀ hx₀ ht
  by_contra hh
  have hsub : (range (x + 1)).filter (fun p => p.Prime ∧ ChenRep (p + h)) ⊆ range (B + 1) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    have hle : p ≤ B := by
      by_contra hgt
      exact hh ⟨p, ⟨hp.2.1, hp.2.2⟩, by omega⟩
    omega
  have hbound := shiftedChenCount_le h x B hsub
  exact Nat.not_lt_of_ge hbound hc

end LeanLab.AlmostPrimeSums.Chen1973TheoremII
