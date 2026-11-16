/-
FREE-nv-minimax3 task570, split of paper_ternary_transference_input.

The transference input used in Remark 3.6 is a single quantified statement. It is split here
into four stages, each a LEAF lemma, and one assembly theorem that uses only the four leaves.

Stage 1 chooses the Bohr width eta.
Stage 2 chooses the frequency cutoff set Omega inside range N.
Stage 3 chooses the character chi with the Bohr cutoff properties and a bounded Fourier
complexity Cc that is uniform in N and in Omega of at most one frequency.
Stage 4 is the triple convolution estimate at the point N.

The two analytic stages remain open leaves. The two bookkeeping stages are proved.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputs

namespace LeanLab.Teravainen2016

open Finset

/-! ### Stage 1: the Bohr width -/

/-- LEAF. Stage 1 of the ternary transference input. For a Fourier moment bound K at least 1
and a positive density delta there is an eta strictly above 0 and strictly below 1 / 20. -/
theorem ms23_eta (K δ : ℝ) (hK : 1 ≤ K) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 20 := by
  refine ⟨1 / 40, by norm_num, by norm_num⟩

/-! ### Stage 2: the frequency cutoff set -/

/-- LEAF. Stage 2 of the ternary transference input. For a positive modulus N the frequency
cutoff set can be taken to be the singleton of one modulo N. It lies in range N, it contains
one modulo N, and it has at most one element. -/
theorem ms23_cutoff (N : ℕ) (hN : 0 < N) :
    ∃ Ω : Finset ℕ, Ω ⊆ range N ∧ 1 % N ∈ Ω ∧ Ω.card ≤ 1 := by
  refine ⟨{1 % N}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact Nat.mod_lt _ hN
  · simp
  · simp

/-! ### Stage 3: the character with bounded Fourier complexity -/

/-- LEAF. Stage 3 of the ternary transference input. For a Bohr width eta above 0 and below
1 / 20 there is a Fourier complexity constant Cc, the same for every positive modulus and
every cutoff set of at most one frequency, such that a character with the Bohr cutoff
properties for that width exists. -/
theorem ms23_character (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 20) :
    ∃ Cc : ℕ, ∀ N : ℕ, 0 < N → ∀ Ω : Finset ℕ, Ω ⊆ range N → Ω.card ≤ 1 →
      ∃ χ : ℤ → ℝ, ChiProps N Ω η χ ∧ FourierComplexityLE χ Cc := by
  sorry

/-! ### Stage 4: the triple convolution estimate -/

/-- LEAF. Stage 4 of the ternary transference input. With the Bohr cutoff properties of a
character, with the lower bounds for the convolutions of that character with the second and
the third function on the half interval from N over 4 to N over 2, and with the three Fourier
moment bounds of exponent 5 / 2, the triple convolution of the three functions at N is at
least delta cubed over 200. -/
theorem ms23_conv3 (K δ : ℝ) (hK : 1 ≤ K) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (f₁ f₂ f₃ : ℕ → ℝ) (hf₁ : ∀ n, 0 ≤ f₁ n) (hf₂ : ∀ n, 0 ≤ f₂ n) (hf₃ : ∀ n, 0 ≤ f₃ n)
    (Ω : Finset ℕ) (χ : ℤ → ℝ) (η : ℝ) (hη0 : 0 < η) (hχ : ChiProps N Ω η χ)
    (hdensity : ∀ t : ℤ, (N : ℝ) / 4 ≤ t → (t : ℝ) < N / 2 →
      δ * chiNorm N χ ≤ convChi N f₂ χ t ∧ δ * chiNorm N χ ≤ convChi N f₃ χ t)
    (henergy : ∑ ξ ∈ range N, ‖fhat N f₁ ξ‖ ^ ((5 : ℝ) / 2) ≤ K ∧
      ∑ ξ ∈ range N, ‖fhat N f₂ ξ‖ ^ ((5 : ℝ) / 2) ≤ K ∧
      ∑ ξ ∈ range N, ‖fhat N f₃ ξ‖ ^ ((5 : ℝ) / 2) ≤ K) :
    δ ^ 3 / 200 ≤ conv3 N f₁ f₂ f₃ N := by
  sorry

/-! ### Assembly -/

/-- The ternary transference input of Remark 3.6, assembled from the four stages. -/
theorem paper_ternary_transference_input_F570 : MSThm23 := by
  intro K δ hK hδ
  obtain ⟨η, hη0, hη1⟩ := ms23_eta K δ hK hδ
  obtain ⟨Cc, hCc⟩ := ms23_character η hη0 hη1
  refine ⟨η, hη0, hη1, 1, Cc, 1, ?_⟩
  intro N hN f₁ hf₁
  obtain ⟨Ω, hΩsub, hΩmem, hΩcard⟩ := ms23_cutoff N (by omega)
  obtain ⟨χ, hχ⟩ := hCc N (by omega) Ω hΩsub hΩcard
  refine ⟨Ω, hΩsub, hΩmem, hΩcard, χ, hχ, ?_⟩
  intro f₂ f₃ hf₂ hf₃ hdensity henergy
  exact ms23_conv3 K δ hK hδ N (by omega) f₁ f₂ f₃ hf₁ hf₂ hf₃ Ω χ η hη0 hχ hdensity henergy

end LeanLab.Teravainen2016
