import LeanLab.GoldbachAverage.Decomp444b
import LeanLab.GoldbachAverage.Decomp444c

/-!
BHMS, https://arxiv.org/abs/1704.06103v2 page 7 Lemma 4 and page 17 zero range split.
The single endpoint truncated sum is finite and its difference splits at x over h.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.TruncatedRanges444
open MeasureTheory Complex Finset
open Decomp287d

/-- The single endpoint truncated zero term in BHMS page 7 Lemma 4 at q one. -/
def cutoffPrimitive (T u : ℝ) : ℂ :=
  zeroSum (fun ρ => if |ρ.im| ≤ T then (u : ℂ) ^ ρ / ρ else 0)

/-- BHMS page 7 finite cutoff formula, with the actual zeros and multiplicities. -/
theorem cutoff_sum_finite (T : ℝ) (hT : 0 ≤ T) :
    ∃ S : Finset NontrivialZero,
      (∀ ρ : NontrivialZero, ρ ∈ S ↔ |ρ.1.im| ≤ T) ∧
      ∀ f : ℂ → ℂ,
        zeroSum (fun ρ => if |ρ.im| ≤ T then f ρ else 0) =
          ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * f ρ.1 := by
  simpa only [div_one] using Decomp444b.low_sum_finite T 1 hT (by norm_num)

/-- BHMS page 17, the full truncated increment is exactly the low and high increment sum. -/
theorem cutoff_difference (x h t : ℝ) (hx : 0 ≤ x) (hh : 1 ≤ h) :
    cutoffPrimitive x (t + h) - cutoffPrimitive x t = lowZeros x h t + highZeros x h t := by
  classical
  have hh0 : 0 < h := by linarith
  have hcut : x / h ≤ x := (div_le_iff₀ hh0).mpr (by nlinarith)
  obtain ⟨S, hS, he⟩ := cutoff_sum_finite x hx
  have hl : lowZeros x h t = ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      (if |ρ.1.im| ≤ x / h then (((t + h : ℝ) : ℂ) ^ ρ.1 - (t : ℂ) ^ ρ.1) / ρ.1 else 0) := by
    unfold lowZeros zeroSum
    apply tsum_eq_sum (s := S)
    intro ρ hρ
    have hn : ¬ |ρ.1.im| ≤ x / h := fun hp => hρ ((hS ρ).mpr (hp.trans hcut))
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (if |ρ.1.im| ≤ x / h then _ else 0) = 0
    rw [if_neg hn, mul_zero]
  have hu : highZeros x h t = ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      (if x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x then
        (((t + h : ℝ) : ℂ) ^ ρ.1 - (t : ℂ) ^ ρ.1) / ρ.1 else 0) := by
    unfold highZeros zeroSum
    apply tsum_eq_sum (s := S)
    intro ρ hρ
    have hn : ¬ (x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x) := fun hp => hρ ((hS ρ).mpr hp.2)
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        (if x / h < |ρ.1.im| ∧ |ρ.1.im| ≤ x then _ else 0) = 0
    rw [if_neg hn, mul_zero]
  unfold cutoffPrimitive
  rw [he, he, hl, hu, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρx := (hS ρ).mp hρ
  by_cases hρcut : |ρ.1.im| ≤ x / h
  · simp only [hρcut, true_and, not_lt_of_ge hρcut, false_and, if_true, if_false, mul_zero, add_zero]
    ring
  · have hgt : x / h < |ρ.1.im| := lt_of_not_ge hρcut
    simp only [hρcut, hgt, hρx, and_self, if_true, if_false, mul_zero, zero_add]
    ring

end LeanLab.GoldbachAverage.TruncatedRanges444
