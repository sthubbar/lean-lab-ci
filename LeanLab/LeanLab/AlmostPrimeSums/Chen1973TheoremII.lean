/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0002 Chen 1973, p. 157 count definition and p. 158 Theorem II.
The quantitative and infinite assertions are cited Prop inputs.
The quantitative-to-infinite link is conditional on the cited quantitative input.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Chen1973Own
import LeanLab.AlmostPrimeSums.S3Small

open Finset Filter Real

noncomputable section
attribute [local instance] Classical.propDecidable
namespace LeanLab.AlmostPrimeSums.Chen1973TheoremII

open Chen1973Own

/-- Chen p. 157: count primes p at most x with p+h prime or a product of two primes. -/
def shiftedChenCount (h x : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ ChenRep (p + h))).card

/-- Chen p. 158, Theorem II, quantitative part, as a cited input. -/
def ChenTheoremIIQuant : Prop :=
  ∀ h : ℕ, Even h → 0 < h → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    0.67 * LeanLab.ChenDoubleSieve.CN h * x / (log x) ^ 2 ≤ shiftedChenCount h x

/-- Chen p. 158, Theorem II, infinitude part, as a cited input. -/
def ChenTheoremIIInfinite : Prop :=
  ∀ h : ℕ, Even h → 0 < h → Set.Infinite {p : ℕ | p.Prime ∧ ChenRep (p + h)}

lemma nat_scale_tendsto :
    Tendsto (fun x : ℕ => (x : ℝ) / (log x) ^ 2) atTop atTop := by
  apply tendsto_atTop_mono _ S3Small.totient_scale_tendsto
  intro x
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.totient_le x)) (sq_nonneg _)

/-- CONDITIONAL ON ChenTheoremIIQuant, the quantitative assertion implies infinitude. -/
theorem theoremII_infinite_of_quant (hII : ChenTheoremIIQuant) : ChenTheoremIIInfinite := by
  intro h he hpos
  obtain ⟨x₀, hx₀⟩ := hII h he hpos
  have hC : 0 < LeanLab.ChenDoubleSieve.CN h := by
    unfold LeanLab.ChenDoubleSieve.CN
    exact mul_pos (lt_of_lt_of_le zero_lt_one (LeanLab.ChenExplicit.one_le_oddFactor h))
      LeanLab.ChenExplicit.twinC_pos
  have ht : Tendsto (fun x : ℕ => 0.67 * LeanLab.ChenDoubleSieve.CN h * x / (log x) ^ 2)
      atTop atTop := by
    simpa only [mul_div_assoc] using
      Tendsto.const_mul_atTop (mul_pos (by norm_num : (0 : ℝ) < 0.67) hC) nat_scale_tendsto
  apply Set.infinite_of_forall_exists_gt
  intro B
  have hbig := ht.eventually_gt_atTop ((B : ℝ) + 1)
  obtain ⟨x, hx, hmain⟩ := ((eventually_ge_atTop x₀).and hbig).exists
  have hc : B + 1 < shiftedChenCount h x := by
    have h := hmain.trans_le (hx₀ x hx)
    exact_mod_cast h
  by_contra hh
  have hsub : (range (x + 1)).filter (fun p => p.Prime ∧ ChenRep (p + h)) ⊆ range (B + 1) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    have hle : p ≤ B := by
      by_contra hgt
      exact hh ⟨p, ⟨hp.2.1, hp.2.2⟩, by omega⟩
    omega
  have hbound := card_le_card hsub
  rw [card_range] at hbound
  exact Nat.not_lt_of_ge hbound hc

example : Even 2 ∧ 0 < (2 : ℕ) ∧ Nat.Prime 3 ∧ ChenRep (3 + 2) := by
  exact ⟨even_two, by norm_num, Nat.prime_three, Or.inl Nat.prime_five⟩

end LeanLab.AlmostPrimeSums.Chen1973TheoremII

#print axioms LeanLab.AlmostPrimeSums.Chen1973TheoremII.nat_scale_tendsto

#print axioms LeanLab.AlmostPrimeSums.Chen1973TheoremII.theoremII_infinite_of_quant
