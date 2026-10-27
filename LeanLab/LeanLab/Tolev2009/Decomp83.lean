/-
AI wrote this Lean code. Codex task83.
Binary Goldbach is open.
Source records: https://arxiv.org/abs/0902.2669 pages 3, 4 and 7.
The two analytic leaves remain cited inputs.
The opaque legacy series has no identification equation.
-/
import LeanLab.Tolev2009.PublishedTheorem

namespace LeanLab.Tolev2009.Decomp83

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.SeriesIdentification

/-- LEAF. Page 2 display 5, invariance under equality on admissible inputs.
This is an implementation fact. Only positive moduli and reduced residues contribute. -/
theorem Estar_congr_admissible (S T : SSeries)
    (h : ∀ k l N, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      S k l N = T k l N)
    (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    Estar S lam l₃ B N = Estar T lam l₃ B N := by
  unfold Estar inner
  refine Finset.sum_congr rfl fun k₁ hk₁ => Finset.sum_congr rfl fun k₂ hk₂ => ?_
  congr 1
  funext l₁
  congr 1
  funext hl₁
  congr 1
  funext l₂
  congr 1
  funext hl₂
  congr 1
  refine Finset.sum_congr rfl fun k₃ hk₃ => ?_
  have h1 : 1 ≤ k₁ := (Finset.mem_Icc.mp hk₁).1
  have h2 : 1 ≤ k₂ := (Finset.mem_Icc.mp hk₂).1
  have h3 : 1 ≤ k₃ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk₃).1).1
  have hc1 : Nat.Coprime l₁ k₁ := (Finset.mem_filter.mp hl₁).2
  have hc2 : Nat.Coprime l₂ k₂ := (Finset.mem_filter.mp hl₂).2
  have hc3 : Nat.Coprime l₃ k₃ := (Finset.mem_filter.mp hk₃).2.symm
  have he := h ![k₁, k₂, k₃] ![l₁, l₂, l₃] N
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)
  simp only [Δ, M, he]

/-- LEAF. Page 2 display 5, the same estimate for two series agreeing on admissible data.
CONDITIONAL ON the stated agreement and the theorem for T. -/
theorem theorem_transfer_admissible (S T : SSeries)
    (h : ∀ k l N, (∀ i, 1 ≤ k i) → (∀ i, Nat.Coprime (l i) (k i)) →
      S k l N = T k l N)
    (hT : TheTheorem T) : TheTheorem S := by
  intro A hA
  obtain ⟨B, hB, hb⟩ := hT A hA
  refine ⟨B, hB, fun l₃ hl₃ => ?_⟩
  obtain ⟨C, N₀, hc⟩ := hb l₃ hl₃
  refine ⟨C, N₀, fun lam hlam N hodd hN => ?_⟩
  rw [Estar_congr_admissible S T h]
  exact hc lam hlam N hodd hN

/-- LEAF. Page 4 display 9. Major arc mean bound.
Published inputs: Tolev 1999 sections 4 and 5 and Halupczok 2008 Theorem 3.
The source references were reviewed by task45. Task83 checked the rendered paper page after network access was restored.
This cited analytic input is not proved here. -/
theorem major_arc_leaf : BoundE1 := by
  sorry

/-- LEAF. Page 4 display 12, supremum half only.
Published input: the adaptation of Tolev 1999 Lemma 12 cited by Tolev 2009.
The L2 half is already proved in L2Bound.display12_L2_cutoff.
The adaptation to general fixed l3 is part of this cited input. -/
theorem minor_arc_sup_leaf : Sup12Uniform := by
  sorry

/-- LEAF. Page 7, conclusion after display 20.
CONDITIONAL ON the two named analytic leaves.
All dyadic, divisor moment, L2 and minor arc bookkeeping is reused from task45.
There is no sorry in this assembly. -/
theorem published_assembly : TheTheorem halupczokSeries :=
  PublishedTheorem.publishedTheorem_of_display9_sup12 major_arc_leaf minor_arc_sup_leaf

/-- LEAF. Page 2 display 5, legacy representation transfer.
CONDITIONAL ON the explicit identity between the sealed opaque series and the
published series, as well as the two cited analytic inputs when h is assembled above.
The paper provides no equation for the Lean opaque constant. -/
theorem legacy_transfer (hSeries : halupczokS = halupczokSeries)
    (h : TheTheorem halupczokSeries) : TheTheorem halupczokS := by
  exact hSeries.substr h

/-- LEAF. Page 2 display 5, the exact legacy conclusion under its missing identity.
CONDITIONAL ON hSeries and the two cited analytic leaves.
This does not identify the opaque constant and does not discharge the original sorry. -/
theorem legacy_assembly (hSeries : halupczokS = halupczokSeries) :
    TheTheorem halupczokS :=
  legacy_transfer hSeries published_assembly

end LeanLab.Tolev2009.Decomp83
